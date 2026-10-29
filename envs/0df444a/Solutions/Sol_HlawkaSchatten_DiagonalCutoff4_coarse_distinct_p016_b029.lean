-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p016_b029
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:02:27.638505+00:00
-- url     : https://prove2.me/submissions/617eb339-d610-4364-bac1-8edae9c6e6cb

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
theorem collision_support_c316070_s0_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133855021/10000000000 : ℝ)*x 0 + (-2027185671/5000000000 : ℝ)*x 1 + (-611733457/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133855021/10000000000 : ℝ)^77 ≤ (14230106944571/100000000000000 : ℝ)^61 := by
    have hnat : (2133855021 : ℕ)^77*100000000000000^61 ≤ 14230106944571^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133855021 10000000000 14230106944571 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2027185671/5000000000 : ℝ)^77 ≤ (7998780893641/25000000000000 : ℝ)^61 := by
    have hnat : (2027185671 : ℕ)^77*25000000000000^61 ≤ 7998780893641^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027185671 5000000000 7998780893641 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (611733457/1000000000 : ℝ)^77 ≤ (6721846182927/12500000000000 : ℝ)^61 := by
    have hnat : (611733457 : ℕ)^77*12500000000000^61 ≤ 6721846182927^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611733457 1000000000 6721846182927 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133855021/10000000000 : ℝ), (-2027185671/5000000000 : ℝ), (-611733457/1000000000 : ℝ)] ![(14230106944571/100000000000000 : ℝ), (7998780893641/25000000000000 : ℝ), (6721846182927/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133855021/10000000000 : ℝ)|^77 ≤ (14230106944571/100000000000000 : ℝ)^61
        have hw : |(-2133855021/10000000000 : ℝ)|=(2133855021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2027185671/5000000000 : ℝ)|^77 ≤ (7998780893641/25000000000000 : ℝ)^61
        have hw : |(-2027185671/5000000000 : ℝ)|=(2027185671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-611733457/1000000000 : ℝ)|^77 ≤ (6721846182927/12500000000000 : ℝ)^61
        have hw : |(-611733457/1000000000 : ℝ)|=(611733457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316070_s0_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (764666833/1250000000 : ℝ)*x 0 + (4054371327/10000000000 : ℝ)*x 1 + (-426770983/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (764666833/1250000000 : ℝ)^77 ≤ (26887385253233/50000000000000 : ℝ)^61 := by
    have hnat : (764666833 : ℕ)^77*50000000000000^61 ≤ 26887385253233^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764666833 1250000000 26887385253233 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4054371327/10000000000 : ℝ)^77 ≤ (31995123425143/100000000000000 : ℝ)^61 := by
    have hnat : (4054371327 : ℕ)^77*100000000000000^61 ≤ 31995123425143^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4054371327 10000000000 31995123425143 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426770983/2000000000 : ℝ)^77 ≤ (14230106052273/100000000000000 : ℝ)^61 := by
    have hnat : (426770983 : ℕ)^77*100000000000000^61 ≤ 14230106052273^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426770983 2000000000 14230106052273 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(764666833/1250000000 : ℝ), (4054371327/10000000000 : ℝ), (-426770983/2000000000 : ℝ)] ![(26887385253233/50000000000000 : ℝ), (31995123425143/100000000000000 : ℝ), (14230106052273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(764666833/1250000000 : ℝ)|^77 ≤ (26887385253233/50000000000000 : ℝ)^61
        have hw : |(764666833/1250000000 : ℝ)|=(764666833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4054371327/10000000000 : ℝ)|^77 ≤ (31995123425143/100000000000000 : ℝ)^61
        have hw : |(4054371327/10000000000 : ℝ)|=(4054371327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426770983/2000000000 : ℝ)|^77 ≤ (14230106052273/100000000000000 : ℝ)^61
        have hw : |(-426770983/2000000000 : ℝ)|=(426770983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316070_s0_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (943226987/2500000000 : ℝ)*x 0 + (-1247085097/2500000000 : ℝ)*x 1 + (1886453887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (943226987/2500000000 : ℝ)^77 ≤ (5843465127903/20000000000000 : ℝ)^61 := by
    have hnat : (943226987 : ℕ)^77*20000000000000^61 ≤ 5843465127903^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943226987 2500000000 5843465127903 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1247085097/2500000000 : ℝ)^77 ≤ (41565350406461/100000000000000 : ℝ)^61 := by
    have hnat : (1247085097 : ℕ)^77*100000000000000^61 ≤ 41565350406461^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1247085097 2500000000 41565350406461 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1886453887/5000000000 : ℝ)^77 ≤ (3652165492329/12500000000000 : ℝ)^61 := by
    have hnat : (1886453887 : ℕ)^77*12500000000000^61 ≤ 3652165492329^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886453887 5000000000 3652165492329 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(943226987/2500000000 : ℝ), (-1247085097/2500000000 : ℝ), (1886453887/5000000000 : ℝ)] ![(5843465127903/20000000000000 : ℝ), (41565350406461/100000000000000 : ℝ), (3652165492329/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(943226987/2500000000 : ℝ)|^77 ≤ (5843465127903/20000000000000 : ℝ)^61
        have hw : |(943226987/2500000000 : ℝ)|=(943226987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1247085097/2500000000 : ℝ)|^77 ≤ (41565350406461/100000000000000 : ℝ)^61
        have hw : |(-1247085097/2500000000 : ℝ)|=(1247085097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1886453887/5000000000 : ℝ)|^77 ≤ (3652165492329/12500000000000 : ℝ)^61
        have hw : |(1886453887/5000000000 : ℝ)|=(1886453887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316070_s0_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2518573971/5000000000 : ℝ)*x 0 + (-2323096469/10000000000 : ℝ)*x 1 + (-1259286961/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2518573971/5000000000 : ℝ)^77 ≤ (1683174762931/4000000000000 : ℝ)^61 := by
    have hnat : (2518573971 : ℕ)^77*4000000000000^61 ≤ 1683174762931^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518573971 5000000000 1683174762931 4000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2323096469/10000000000 : ℝ)^77 ≤ (7920631434633/50000000000000 : ℝ)^61 := by
    have hnat : (2323096469 : ℕ)^77*50000000000000^61 ≤ 7920631434633^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2323096469 10000000000 7920631434633 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1259286961/2500000000 : ℝ)^77 ≤ (10519842009967/25000000000000 : ℝ)^61 := by
    have hnat : (1259286961 : ℕ)^77*25000000000000^61 ≤ 10519842009967^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259286961 2500000000 10519842009967 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2518573971/5000000000 : ℝ), (-2323096469/10000000000 : ℝ), (-1259286961/2500000000 : ℝ)] ![(1683174762931/4000000000000 : ℝ), (7920631434633/50000000000000 : ℝ), (10519842009967/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2518573971/5000000000 : ℝ)|^77 ≤ (1683174762931/4000000000000 : ℝ)^61
        have hw : |(2518573971/5000000000 : ℝ)|=(2518573971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2323096469/10000000000 : ℝ)|^77 ≤ (7920631434633/50000000000000 : ℝ)^61
        have hw : |(-2323096469/10000000000 : ℝ)|=(2323096469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1259286961/2500000000 : ℝ)|^77 ≤ (10519842009967/25000000000000 : ℝ)^61
        have hw : |(-1259286961/2500000000 : ℝ)|=(1259286961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316070 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2133855021/10000000000 : ℝ)*X 0 0+(-2027185671/5000000000 : ℝ)*X 0 1+(-611733457/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316070_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((764666833/1250000000 : ℝ)*X 1 0+(4054371327/10000000000 : ℝ)*X 1 1+(-426770983/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316070_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((943226987/2500000000 : ℝ)*X 2 0+(-1247085097/2500000000 : ℝ)*X 2 1+(1886453887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316070_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((2518573971/5000000000 : ℝ)*X 0 0+(-2323096469/10000000000 : ℝ)*X 0 1+(-1259286961/2500000000 : ℝ)*X 0 2+(2518573971/5000000000 : ℝ)*X 1 0+(-2323096469/10000000000 : ℝ)*X 1 1+(-1259286961/2500000000 : ℝ)*X 1 2+(2518573971/5000000000 : ℝ)*X 2 0+(-2323096469/10000000000 : ℝ)*X 2 1+(-1259286961/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316070_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-381771/50000 : ℝ) < ((-177257/100000 : ℝ)*P 0+(-177257/100000 : ℝ)*P 1+(-177257/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-381771/50000 : ℝ) < (-37941623101409314816658225223/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (235153/1000000000000 : ℝ)*(base12) + (44771/500000000000 : ℝ)*(base15) + (6969/62500000000 : ℝ)*(base25) + (59133/1000000000000 : ℝ)*(base33) + (546338778217/1000000000000 : ℝ)*(base39) + (7429/500000000000 : ℝ)*(base40) + (5269993527/40000000000 : ℝ)*(base49) + (10373767359/31250000000 : ℝ)*(base59) + (1772569940867/1000000000000 : ℝ)*(major_s0_0) + (177257/100000 : ℝ)*(major_s0_1) + (177257/100000 : ℝ)*(major_s0_2) + (316180163117/125000000000 : ℝ)*(sp_s0_0) + (505888278283/200000000000 : ℝ)*(sp_s0_1) + (632360342363/250000000000 : ℝ)*(sp_s0_2) + (1 : ℝ)*(sp_s0_6) + (2529441540089/1000000000000 : ℝ)*(f.sum) + (292418273/5000000000000000000000 : ℝ)*base63 + (549869337/2500000000000000000000 : ℝ)*base64 + (140369391/1000000000000000000000 : ℝ)*base66 + (706337813/1000000000000000000000 : ℝ)*base68 + (7449460125758467/10000000000000000000000000000 : ℝ)*base70 + (3637675124991637/5000000000000000000000000000 : ℝ)*base73 + (86454241/2500000000000000000000 : ℝ)*base75 + (6247453584758467/10000000000000000000000000000 : ℝ)*base76 + (3486872123491637/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c316071_s0_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3608106399/10000000000 : ℝ)*x 0 + (5124937019/10000000000 : ℝ)*x 1 + (1894621871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3608106399/10000000000 : ℝ)^77 ≤ (27615688992209/100000000000000 : ℝ)^61 := by
    have hnat : (3608106399 : ℕ)^77*100000000000000^61 ≤ 27615688992209^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3608106399 10000000000 27615688992209 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5124937019/10000000000 : ℝ)^77 ≤ (4300720930571/10000000000000 : ℝ)^61 := by
    have hnat : (5124937019 : ℕ)^77*10000000000000^61 ≤ 4300720930571^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5124937019 10000000000 4300720930571 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1894621871/5000000000 : ℝ)^77 ≤ (29377101684561/100000000000000 : ℝ)^61 := by
    have hnat : (1894621871 : ℕ)^77*100000000000000^61 ≤ 29377101684561^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894621871 5000000000 29377101684561 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3608106399/10000000000 : ℝ), (5124937019/10000000000 : ℝ), (1894621871/5000000000 : ℝ)] ![(27615688992209/100000000000000 : ℝ), (4300720930571/10000000000000 : ℝ), (29377101684561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3608106399/10000000000 : ℝ)|^77 ≤ (27615688992209/100000000000000 : ℝ)^61
        have hw : |(3608106399/10000000000 : ℝ)|=(3608106399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5124937019/10000000000 : ℝ)|^77 ≤ (4300720930571/10000000000000 : ℝ)^61
        have hw : |(5124937019/10000000000 : ℝ)|=(5124937019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1894621871/5000000000 : ℝ)|^77 ≤ (29377101684561/100000000000000 : ℝ)^61
        have hw : |(1894621871/5000000000 : ℝ)|=(1894621871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s0_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (799274999/1250000000 : ℝ)*x 0 + (-3668044181/10000000000 : ℝ)*x 1 + (-2217639531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (799274999/1250000000 : ℝ)^77 ≤ (5686498057453/10000000000000 : ℝ)^61 := by
    have hnat : (799274999 : ℕ)^77*10000000000000^61 ≤ 5686498057453^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      799274999 1250000000 5686498057453 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3668044181/10000000000 : ℝ)^77 ≤ (28196024855309/100000000000000 : ℝ)^61 := by
    have hnat : (3668044181 : ℕ)^77*100000000000000^61 ≤ 28196024855309^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3668044181 10000000000 28196024855309 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2217639531/10000000000 : ℝ)^77 ≤ (14938994553641/100000000000000 : ℝ)^61 := by
    have hnat : (2217639531 : ℕ)^77*100000000000000^61 ≤ 14938994553641^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217639531 10000000000 14938994553641 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(799274999/1250000000 : ℝ), (-3668044181/10000000000 : ℝ), (-2217639531/10000000000 : ℝ)] ![(5686498057453/10000000000000 : ℝ), (28196024855309/100000000000000 : ℝ), (14938994553641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(799274999/1250000000 : ℝ)|^77 ≤ (5686498057453/10000000000000 : ℝ)^61
        have hw : |(799274999/1250000000 : ℝ)|=(799274999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3668044181/10000000000 : ℝ)|^77 ≤ (28196024855309/100000000000000 : ℝ)^61
        have hw : |(-3668044181/10000000000 : ℝ)|=(3668044181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2217639531/10000000000 : ℝ)|^77 ≤ (14938994553641/100000000000000 : ℝ)^61
        have hw : |(-2217639531/10000000000 : ℝ)|=(2217639531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s0_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-470633301/1250000000 : ℝ)*x 0 + (-2664548159/5000000000 : ℝ)*x 1 + (1703034533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (470633301/1250000000 : ℝ)^77 ≤ (1457034700597/5000000000000 : ℝ)^61 := by
    have hnat : (470633301 : ℕ)^77*5000000000000^61 ≤ 1457034700597^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470633301 1250000000 1457034700597 5000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2664548159/5000000000 : ℝ)^77 ≤ (45181031875471/100000000000000 : ℝ)^61 := by
    have hnat : (2664548159 : ℕ)^77*100000000000000^61 ≤ 45181031875471^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2664548159 5000000000 45181031875471 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1703034533/5000000000 : ℝ)^77 ≤ (25678274100851/100000000000000 : ℝ)^61 := by
    have hnat : (1703034533 : ℕ)^77*100000000000000^61 ≤ 25678274100851^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1703034533 5000000000 25678274100851 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-470633301/1250000000 : ℝ), (-2664548159/5000000000 : ℝ), (1703034533/5000000000 : ℝ)] ![(1457034700597/5000000000000 : ℝ), (45181031875471/100000000000000 : ℝ), (25678274100851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-470633301/1250000000 : ℝ)|^77 ≤ (1457034700597/5000000000000 : ℝ)^61
        have hw : |(-470633301/1250000000 : ℝ)|=(470633301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2664548159/5000000000 : ℝ)|^77 ≤ (45181031875471/100000000000000 : ℝ)^61
        have hw : |(-2664548159/5000000000 : ℝ)|=(2664548159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1703034533/5000000000 : ℝ)|^77 ≤ (25678274100851/100000000000000 : ℝ)^61
        have hw : |(1703034533/5000000000 : ℝ)|=(1703034533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s0_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3094489053/10000000000 : ℝ)*x 0 + (1550469133/2500000000 : ℝ)*x 1 + (383930083/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3094489053/10000000000 : ℝ)^77 ≤ (22749556667087/100000000000000 : ℝ)^61 := by
    have hnat : (3094489053 : ℕ)^77*100000000000000^61 ≤ 22749556667087^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3094489053 10000000000 22749556667087 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1550469133/2500000000 : ℝ)^77 ≤ (27357282430787/50000000000000 : ℝ)^61 := by
    have hnat : (1550469133 : ℕ)^77*50000000000000^61 ≤ 27357282430787^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1550469133 2500000000 27357282430787 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (383930083/1250000000 : ℝ)^77 ≤ (22535878455589/100000000000000 : ℝ)^61 := by
    have hnat : (383930083 : ℕ)^77*100000000000000^61 ≤ 22535878455589^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383930083 1250000000 22535878455589 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3094489053/10000000000 : ℝ), (1550469133/2500000000 : ℝ), (383930083/1250000000 : ℝ)] ![(22749556667087/100000000000000 : ℝ), (27357282430787/50000000000000 : ℝ), (22535878455589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3094489053/10000000000 : ℝ)|^77 ≤ (22749556667087/100000000000000 : ℝ)^61
        have hw : |(3094489053/10000000000 : ℝ)|=(3094489053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1550469133/2500000000 : ℝ)|^77 ≤ (27357282430787/50000000000000 : ℝ)^61
        have hw : |(1550469133/2500000000 : ℝ)|=(1550469133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(383930083/1250000000 : ℝ)|^77 ≤ (22535878455589/100000000000000 : ℝ)^61
        have hw : |(383930083/1250000000 : ℝ)|=(383930083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s0_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1364666603/2000000000 : ℝ)*x 0 + (-3776062627/10000000000 : ℝ)*x 1 + (-743998017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1364666603/2000000000 : ℝ)^77 ≤ (964438879511/1562500000000 : ℝ)^61 := by
    have hnat : (1364666603 : ℕ)^77*1562500000000^61 ≤ 964438879511^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364666603 2000000000 964438879511 1562500000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3776062627/10000000000 : ℝ)^77 ≤ (14624083301173/50000000000000 : ℝ)^61 := by
    have hnat : (3776062627 : ℕ)^77*50000000000000^61 ≤ 14624083301173^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3776062627 10000000000 14624083301173 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (743998017/5000000000 : ℝ)^77 ≤ (9027745097573/100000000000000 : ℝ)^61 := by
    have hnat : (743998017 : ℕ)^77*100000000000000^61 ≤ 9027745097573^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743998017 5000000000 9027745097573 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1364666603/2000000000 : ℝ), (-3776062627/10000000000 : ℝ), (-743998017/5000000000 : ℝ)] ![(964438879511/1562500000000 : ℝ), (14624083301173/50000000000000 : ℝ), (9027745097573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1364666603/2000000000 : ℝ)|^77 ≤ (964438879511/1562500000000 : ℝ)^61
        have hw : |(1364666603/2000000000 : ℝ)|=(1364666603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3776062627/10000000000 : ℝ)|^77 ≤ (14624083301173/50000000000000 : ℝ)^61
        have hw : |(-3776062627/10000000000 : ℝ)|=(3776062627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-743998017/5000000000 : ℝ)|^77 ≤ (9027745097573/100000000000000 : ℝ)^61
        have hw : |(-743998017/5000000000 : ℝ)|=(743998017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s0_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-21184757/10000000000 : ℝ)*x 0 + (-1263054699/10000000000 : ℝ)*x 1 + (941051137/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21184757/10000000000 : ℝ)^77 ≤ (42135931379/100000000000000 : ℝ)^61 := by
    have hnat : (21184757 : ℕ)^77*100000000000000^61 ≤ 42135931379^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21184757 10000000000 42135931379 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1263054699/10000000000 : ℝ)^77 ≤ (734056705837/10000000000000 : ℝ)^61 := by
    have hnat : (1263054699 : ℕ)^77*10000000000000^61 ≤ 734056705837^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1263054699 10000000000 734056705837 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (941051137/1000000000 : ℝ)^77 ≤ (92617296999467/100000000000000 : ℝ)^61 := by
    have hnat : (941051137 : ℕ)^77*100000000000000^61 ≤ 92617296999467^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941051137 1000000000 92617296999467 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21184757/10000000000 : ℝ), (-1263054699/10000000000 : ℝ), (941051137/1000000000 : ℝ)] ![(42135931379/100000000000000 : ℝ), (734056705837/10000000000000 : ℝ), (92617296999467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21184757/10000000000 : ℝ)|^77 ≤ (42135931379/100000000000000 : ℝ)^61
        have hw : |(-21184757/10000000000 : ℝ)|=(21184757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1263054699/10000000000 : ℝ)|^77 ≤ (734056705837/10000000000000 : ℝ)^61
        have hw : |(-1263054699/10000000000 : ℝ)|=(1263054699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(941051137/1000000000 : ℝ)|^77 ≤ (92617296999467/100000000000000 : ℝ)^61
        have hw : |(941051137/1000000000 : ℝ)|=(941051137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s0_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1665607221/5000000000 : ℝ)*x 0 + (-2896418513/10000000000 : ℝ)*x 1 + (192095719/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1665607221/5000000000 : ℝ)^77 ≤ (12483995469239/50000000000000 : ℝ)^61 := by
    have hnat : (1665607221 : ℕ)^77*50000000000000^61 ≤ 12483995469239^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665607221 5000000000 12483995469239 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2896418513/10000000000 : ℝ)^77 ≤ (20927154669087/100000000000000 : ℝ)^61 := by
    have hnat : (2896418513 : ℕ)^77*100000000000000^61 ≤ 20927154669087^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2896418513 10000000000 20927154669087 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (192095719/312500000 : ℝ)^77 ≤ (270524271899/500000000000 : ℝ)^61 := by
    have hnat : (192095719 : ℕ)^77*500000000000^61 ≤ 270524271899^61*312500000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192095719 312500000 270524271899 500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1665607221/5000000000 : ℝ), (-2896418513/10000000000 : ℝ), (192095719/312500000 : ℝ)] ![(12483995469239/50000000000000 : ℝ), (20927154669087/100000000000000 : ℝ), (270524271899/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1665607221/5000000000 : ℝ)|^77 ≤ (12483995469239/50000000000000 : ℝ)^61
        have hw : |(-1665607221/5000000000 : ℝ)|=(1665607221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2896418513/10000000000 : ℝ)|^77 ≤ (20927154669087/100000000000000 : ℝ)^61
        have hw : |(-2896418513/10000000000 : ℝ)|=(2896418513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(192095719/312500000 : ℝ)|^77 ≤ (270524271899/500000000000 : ℝ)^61
        have hw : |(192095719/312500000 : ℝ)|=(192095719/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s0_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (362005247/625000000 : ℝ)*x 0 + (4267015703/10000000000 : ℝ)*x 1 + (1152231897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (362005247/625000000 : ℝ)^77 ≤ (25095600916833/50000000000000 : ℝ)^61 := by
    have hnat : (362005247 : ℕ)^77*50000000000000^61 ≤ 25095600916833^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362005247 625000000 25095600916833 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4267015703/10000000000 : ℝ)^77 ≤ (3412774936183/10000000000000 : ℝ)^61 := by
    have hnat : (4267015703 : ℕ)^77*10000000000000^61 ≤ 3412774936183^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4267015703 10000000000 3412774936183 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1152231897/5000000000 : ℝ)^77 ≤ (15681048788711/100000000000000 : ℝ)^61 := by
    have hnat : (1152231897 : ℕ)^77*100000000000000^61 ≤ 15681048788711^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152231897 5000000000 15681048788711 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(362005247/625000000 : ℝ), (4267015703/10000000000 : ℝ), (1152231897/5000000000 : ℝ)] ![(25095600916833/50000000000000 : ℝ), (3412774936183/10000000000000 : ℝ), (15681048788711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(362005247/625000000 : ℝ)|^77 ≤ (25095600916833/50000000000000 : ℝ)^61
        have hw : |(362005247/625000000 : ℝ)|=(362005247/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4267015703/10000000000 : ℝ)|^77 ≤ (3412774936183/10000000000000 : ℝ)^61
        have hw : |(4267015703/10000000000 : ℝ)|=(4267015703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1152231897/5000000000 : ℝ)|^77 ≤ (15681048788711/100000000000000 : ℝ)^61
        have hw : |(1152231897/5000000000 : ℝ)|=(1152231897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s0_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (813215939/1000000000 : ℝ)*x 0 + (-627450573/2500000000 : ℝ)*x 1 + (-251439031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (813215939/1000000000 : ℝ)^77 ≤ (4814302156073/6250000000000 : ℝ)^61 := by
    have hnat : (813215939 : ℕ)^77*6250000000000^61 ≤ 4814302156073^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      813215939 1000000000 4814302156073 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627450573/2500000000 : ℝ)^77 ≤ (139719780613/800000000000 : ℝ)^61 := by
    have hnat : (627450573 : ℕ)^77*800000000000^61 ≤ 139719780613^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627450573 2500000000 139719780613 800000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251439031/2500000000 : ℝ)^77 ≤ (5506192909947/100000000000000 : ℝ)^61 := by
    have hnat : (251439031 : ℕ)^77*100000000000000^61 ≤ 5506192909947^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251439031 2500000000 5506192909947 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(813215939/1000000000 : ℝ), (-627450573/2500000000 : ℝ), (-251439031/2500000000 : ℝ)] ![(4814302156073/6250000000000 : ℝ), (139719780613/800000000000 : ℝ), (5506192909947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(813215939/1000000000 : ℝ)|^77 ≤ (4814302156073/6250000000000 : ℝ)^61
        have hw : |(813215939/1000000000 : ℝ)|=(813215939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-627450573/2500000000 : ℝ)|^77 ≤ (139719780613/800000000000 : ℝ)^61
        have hw : |(-627450573/2500000000 : ℝ)|=(627450573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-251439031/2500000000 : ℝ)|^77 ≤ (5506192909947/100000000000000 : ℝ)^61
        have hw : |(-251439031/2500000000 : ℝ)|=(251439031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s0_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-42801/400000000 : ℝ)*x 0 + (-1670053289/10000000000 : ℝ)*x 1 + (916318123/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42801/400000000 : ℝ)^77 ≤ (243143961/25000000000000 : ℝ)^61 := by
    have hnat : (42801 : ℕ)^77*25000000000000^61 ≤ 243143961^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42801 400000000 243143961 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1670053289/10000000000 : ℝ)^77 ≤ (261093659701/2500000000000 : ℝ)^61 := by
    have hnat : (1670053289 : ℕ)^77*2500000000000^61 ≤ 261093659701^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1670053289 10000000000 261093659701 2500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (916318123/1000000000 : ℝ)^77 ≤ (22388820256461/25000000000000 : ℝ)^61 := by
    have hnat : (916318123 : ℕ)^77*25000000000000^61 ≤ 22388820256461^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916318123 1000000000 22388820256461 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42801/400000000 : ℝ), (-1670053289/10000000000 : ℝ), (916318123/1000000000 : ℝ)] ![(243143961/25000000000000 : ℝ), (261093659701/2500000000000 : ℝ), (22388820256461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42801/400000000 : ℝ)|^77 ≤ (243143961/25000000000000 : ℝ)^61
        have hw : |(-42801/400000000 : ℝ)|=(42801/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1670053289/10000000000 : ℝ)|^77 ≤ (261093659701/2500000000000 : ℝ)^61
        have hw : |(-1670053289/10000000000 : ℝ)|=(1670053289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(916318123/1000000000 : ℝ)|^77 ≤ (22388820256461/25000000000000 : ℝ)^61
        have hw : |(916318123/1000000000 : ℝ)|=(916318123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s0_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-690900917/2000000000 : ℝ)*x 0 + (-219472999/500000000 : ℝ)*x 1 + (4693769527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (690900917/2000000000 : ℝ)^77 ≤ (26140063126969/100000000000000 : ℝ)^61 := by
    have hnat : (690900917 : ℕ)^77*100000000000000^61 ≤ 26140063126969^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690900917 2000000000 26140063126969 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219472999/500000000 : ℝ)^77 ≤ (35368552187421/100000000000000 : ℝ)^61 := by
    have hnat : (219472999 : ℕ)^77*100000000000000^61 ≤ 35368552187421^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219472999 500000000 35368552187421 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4693769527/10000000000 : ℝ)^77 ≤ (3849138467317/10000000000000 : ℝ)^61 := by
    have hnat : (4693769527 : ℕ)^77*10000000000000^61 ≤ 3849138467317^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4693769527 10000000000 3849138467317 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-690900917/2000000000 : ℝ), (-219472999/500000000 : ℝ), (4693769527/10000000000 : ℝ)] ![(26140063126969/100000000000000 : ℝ), (35368552187421/100000000000000 : ℝ), (3849138467317/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-690900917/2000000000 : ℝ)|^77 ≤ (26140063126969/100000000000000 : ℝ)^61
        have hw : |(-690900917/2000000000 : ℝ)|=(690900917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219472999/500000000 : ℝ)|^77 ≤ (35368552187421/100000000000000 : ℝ)^61
        have hw : |(-219472999/500000000 : ℝ)|=(219472999/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4693769527/10000000000 : ℝ)|^77 ≤ (3849138467317/10000000000000 : ℝ)^61
        have hw : |(4693769527/10000000000 : ℝ)|=(4693769527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s0_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (732461587/2500000000 : ℝ)*x 0 + (1422545519/2500000000 : ℝ)*x 1 + (3821015607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (732461587/2500000000 : ℝ)^77 ≤ (5308121786541/25000000000000 : ℝ)^61 := by
    have hnat : (732461587 : ℕ)^77*25000000000000^61 ≤ 5308121786541^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732461587 2500000000 5308121786541 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1422545519/2500000000 : ℝ)^77 ≤ (6134892727689/12500000000000 : ℝ)^61 := by
    have hnat : (1422545519 : ℕ)^77*12500000000000^61 ≤ 6134892727689^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422545519 2500000000 6134892727689 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3821015607/10000000000 : ℝ)^77 ≤ (29688371012597/100000000000000 : ℝ)^61 := by
    have hnat : (3821015607 : ℕ)^77*100000000000000^61 ≤ 29688371012597^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3821015607 10000000000 29688371012597 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(732461587/2500000000 : ℝ), (1422545519/2500000000 : ℝ), (3821015607/10000000000 : ℝ)] ![(5308121786541/25000000000000 : ℝ), (6134892727689/12500000000000 : ℝ), (29688371012597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(732461587/2500000000 : ℝ)|^77 ≤ (5308121786541/25000000000000 : ℝ)^61
        have hw : |(732461587/2500000000 : ℝ)|=(732461587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1422545519/2500000000 : ℝ)|^77 ≤ (6134892727689/12500000000000 : ℝ)^61
        have hw : |(1422545519/2500000000 : ℝ)|=(1422545519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3821015607/10000000000 : ℝ)|^77 ≤ (29688371012597/100000000000000 : ℝ)^61
        have hw : |(3821015607/10000000000 : ℝ)|=(3821015607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s0_23 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1824979501/2500000000 : ℝ)*x 0 + (-1451278843/5000000000 : ℝ)*x 1 + (-919936567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1824979501/2500000000 : ℝ)^77 ≤ (67215117292663/100000000000000 : ℝ)^61 := by
    have hnat : (1824979501 : ℕ)^77*100000000000000^61 ≤ 67215117292663^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824979501 2500000000 67215117292663 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1451278843/5000000000 : ℝ)^77 ≤ (524579035167/2500000000000 : ℝ)^61 := by
    have hnat : (1451278843 : ℕ)^77*2500000000000^61 ≤ 524579035167^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1451278843 5000000000 524579035167 2500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (919936567/5000000000 : ℝ)^77 ≤ (11801721287157/100000000000000 : ℝ)^61 := by
    have hnat : (919936567 : ℕ)^77*100000000000000^61 ≤ 11801721287157^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919936567 5000000000 11801721287157 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1824979501/2500000000 : ℝ), (-1451278843/5000000000 : ℝ), (-919936567/5000000000 : ℝ)] ![(67215117292663/100000000000000 : ℝ), (524579035167/2500000000000 : ℝ), (11801721287157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1824979501/2500000000 : ℝ)|^77 ≤ (67215117292663/100000000000000 : ℝ)^61
        have hw : |(1824979501/2500000000 : ℝ)|=(1824979501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1451278843/5000000000 : ℝ)|^77 ≤ (524579035167/2500000000000 : ℝ)^61
        have hw : |(-1451278843/5000000000 : ℝ)|=(1451278843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-919936567/5000000000 : ℝ)|^77 ≤ (11801721287157/100000000000000 : ℝ)^61
        have hw : |(-919936567/5000000000 : ℝ)|=(919936567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3460333893/10000000000 : ℝ)*x 0 + (-3862927517/10000000000 : ℝ)*x 1 + (5190627231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3460333893/10000000000 : ℝ)^77 ≤ (26195755383173/100000000000000 : ℝ)^61 := by
    have hnat : (3460333893 : ℕ)^77*100000000000000^61 ≤ 26195755383173^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3460333893 10000000000 26195755383173 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3862927517/10000000000 : ℝ)^77 ≤ (7525005348463/25000000000000 : ℝ)^61 := by
    have hnat : (3862927517 : ℕ)^77*25000000000000^61 ≤ 7525005348463^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3862927517 10000000000 7525005348463 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5190627231/10000000000 : ℝ)^77 ≤ (43704223211771/100000000000000 : ℝ)^61 := by
    have hnat : (5190627231 : ℕ)^77*100000000000000^61 ≤ 43704223211771^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190627231 10000000000 43704223211771 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3460333893/10000000000 : ℝ), (-3862927517/10000000000 : ℝ), (5190627231/10000000000 : ℝ)] ![(26195755383173/100000000000000 : ℝ), (7525005348463/25000000000000 : ℝ), (43704223211771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3460333893/10000000000 : ℝ)|^77 ≤ (26195755383173/100000000000000 : ℝ)^61
        have hw : |(-3460333893/10000000000 : ℝ)|=(3460333893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3862927517/10000000000 : ℝ)|^77 ≤ (7525005348463/25000000000000 : ℝ)^61
        have hw : |(-3862927517/10000000000 : ℝ)|=(3862927517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5190627231/10000000000 : ℝ)|^77 ≤ (43704223211771/100000000000000 : ℝ)^61
        have hw : |(5190627231/10000000000 : ℝ)|=(5190627231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (529859031/1250000000 : ℝ)*x 0 + (4749809763/10000000000 : ℝ)*x 1 + (1776468291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529859031/1250000000 : ℝ)^77 ≤ (16921931256779/50000000000000 : ℝ)^61 := by
    have hnat : (529859031 : ℕ)^77*50000000000000^61 ≤ 16921931256779^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529859031 1250000000 16921931256779 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4749809763/10000000000 : ℝ)^77 ≤ (19536195007737/50000000000000 : ℝ)^61 := by
    have hnat : (4749809763 : ℕ)^77*50000000000000^61 ≤ 19536195007737^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4749809763 10000000000 19536195007737 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1776468291/5000000000 : ℝ)^77 ≤ (13541873725997/50000000000000 : ℝ)^61 := by
    have hnat : (1776468291 : ℕ)^77*50000000000000^61 ≤ 13541873725997^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776468291 5000000000 13541873725997 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529859031/1250000000 : ℝ), (4749809763/10000000000 : ℝ), (1776468291/5000000000 : ℝ)] ![(16921931256779/50000000000000 : ℝ), (19536195007737/50000000000000 : ℝ), (13541873725997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529859031/1250000000 : ℝ)|^77 ≤ (16921931256779/50000000000000 : ℝ)^61
        have hw : |(529859031/1250000000 : ℝ)|=(529859031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4749809763/10000000000 : ℝ)|^77 ≤ (19536195007737/50000000000000 : ℝ)^61
        have hw : |(4749809763/10000000000 : ℝ)|=(4749809763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1776468291/5000000000 : ℝ)|^77 ≤ (13541873725997/50000000000000 : ℝ)^61
        have hw : |(1776468291/5000000000 : ℝ)|=(1776468291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2601892141/5000000000 : ℝ)*x 0 + (-4199049201/10000000000 : ℝ)*x 1 + (-3090536829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2601892141/5000000000 : ℝ)^77 ≤ (5480513370421/12500000000000 : ℝ)^61 := by
    have hnat : (2601892141 : ℕ)^77*12500000000000^61 ≤ 5480513370421^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601892141 5000000000 5480513370421 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4199049201/10000000000 : ℝ)^77 ≤ (33443006589847/100000000000000 : ℝ)^61 := by
    have hnat : (4199049201 : ℕ)^77*100000000000000^61 ≤ 33443006589847^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199049201 10000000000 33443006589847 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3090536829/10000000000 : ℝ)^77 ≤ (11356443217637/50000000000000 : ℝ)^61 := by
    have hnat : (3090536829 : ℕ)^77*50000000000000^61 ≤ 11356443217637^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3090536829 10000000000 11356443217637 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2601892141/5000000000 : ℝ), (-4199049201/10000000000 : ℝ), (-3090536829/10000000000 : ℝ)] ![(5480513370421/12500000000000 : ℝ), (33443006589847/100000000000000 : ℝ), (11356443217637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2601892141/5000000000 : ℝ)|^77 ≤ (5480513370421/12500000000000 : ℝ)^61
        have hw : |(2601892141/5000000000 : ℝ)|=(2601892141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4199049201/10000000000 : ℝ)|^77 ≤ (33443006589847/100000000000000 : ℝ)^61
        have hw : |(-4199049201/10000000000 : ℝ)|=(4199049201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3090536829/10000000000 : ℝ)|^77 ≤ (11356443217637/50000000000000 : ℝ)^61
        have hw : |(-3090536829/10000000000 : ℝ)|=(3090536829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316071_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (379994781/1250000000 : ℝ)*x 0 + (-3187473583/10000000000 : ℝ)*x 1 + (6150180061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (379994781/1250000000 : ℝ)^77 ≤ (22244689013689/100000000000000 : ℝ)^61 := by
    have hnat : (379994781 : ℕ)^77*100000000000000^61 ≤ 22244689013689^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379994781 1250000000 22244689013689 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3187473583/10000000000 : ℝ)^77 ≤ (2361582260349/10000000000000 : ℝ)^61 := by
    have hnat : (3187473583 : ℕ)^77*10000000000000^61 ≤ 2361582260349^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3187473583 10000000000 2361582260349 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6150180061/10000000000 : ℝ)^77 ≤ (27069744184681/50000000000000 : ℝ)^61 := by
    have hnat : (6150180061 : ℕ)^77*50000000000000^61 ≤ 27069744184681^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6150180061 10000000000 27069744184681 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(379994781/1250000000 : ℝ), (-3187473583/10000000000 : ℝ), (6150180061/10000000000 : ℝ)] ![(22244689013689/100000000000000 : ℝ), (2361582260349/10000000000000 : ℝ), (27069744184681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(379994781/1250000000 : ℝ)|^77 ≤ (22244689013689/100000000000000 : ℝ)^61
        have hw : |(379994781/1250000000 : ℝ)|=(379994781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3187473583/10000000000 : ℝ)|^77 ≤ (2361582260349/10000000000000 : ℝ)^61
        have hw : |(-3187473583/10000000000 : ℝ)|=(3187473583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6150180061/10000000000 : ℝ)|^77 ≤ (27069744184681/50000000000000 : ℝ)^61
        have hw : |(6150180061/10000000000 : ℝ)|=(6150180061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316071 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (173433/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((3608106399/10000000000 : ℝ)*X 1 0+(5124937019/10000000000 : ℝ)*X 1 1+(1894621871/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((799274999/1250000000 : ℝ)*X 2 0+(-3668044181/10000000000 : ℝ)*X 2 1+(-2217639531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-470633301/1250000000 : ℝ)*X 0 0+(-2664548159/5000000000 : ℝ)*X 0 1+(1703034533/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3094489053/10000000000 : ℝ)*X 1 0+(1550469133/2500000000 : ℝ)*X 1 1+(383930083/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1364666603/2000000000 : ℝ)*X 2 0+(-3776062627/10000000000 : ℝ)*X 2 1+(-743998017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-21184757/10000000000 : ℝ)*X 0 0+(-1263054699/10000000000 : ℝ)*X 0 1+(941051137/1000000000 : ℝ)*X 0 2+(-21184757/10000000000 : ℝ)*X 1 0+(-1263054699/10000000000 : ℝ)*X 1 1+(941051137/1000000000 : ℝ)*X 1 2+(-21184757/10000000000 : ℝ)*X 2 0+(-1263054699/10000000000 : ℝ)*X 2 1+(941051137/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1665607221/5000000000 : ℝ)*X 0 0+(-2896418513/10000000000 : ℝ)*X 0 1+(192095719/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((362005247/625000000 : ℝ)*X 1 0+(4267015703/10000000000 : ℝ)*X 1 1+(1152231897/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((813215939/1000000000 : ℝ)*X 2 0+(-627450573/2500000000 : ℝ)*X 2 1+(-251439031/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-42801/400000000 : ℝ)*X 0 0+(-1670053289/10000000000 : ℝ)*X 0 1+(916318123/1000000000 : ℝ)*X 0 2+(-42801/400000000 : ℝ)*X 1 0+(-1670053289/10000000000 : ℝ)*X 1 1+(916318123/1000000000 : ℝ)*X 1 2+(-42801/400000000 : ℝ)*X 2 0+(-1670053289/10000000000 : ℝ)*X 2 1+(916318123/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-690900917/2000000000 : ℝ)*X 0 0+(-219472999/500000000 : ℝ)*X 0 1+(4693769527/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((732461587/2500000000 : ℝ)*X 1 0+(1422545519/2500000000 : ℝ)*X 1 1+(3821015607/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1824979501/2500000000 : ℝ)*X 2 0+(-1451278843/5000000000 : ℝ)*X 2 1+(-919936567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((46367/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(46367/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4400780445223671374001/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (573445787/8000000000 : ℝ)*(base1) + (236813716071/500000000000 : ℝ)*(base7) + (178320390991/250000000000 : ℝ)*(base54) + (189208149211/250000000000 : ℝ)*(base60) + (1281217592927/500000000000 : ℝ)*(major_s0_0) + (1281217592927/500000000000 : ℝ)*(major_s0_1) + (184915362189/100000000000 : ℝ)*(major_s0_2) + (126063313/1000000000000 : ℝ)*(sp_s0_2) + (1738567741721/500000000000 : ℝ)*(sp_s0_7) + (3405454760067/1000000000000 : ℝ)*(sp_s0_8) + (673011094899/250000000000 : ℝ)*(sp_s0_9) + (1134120583819/1000000000000 : ℝ)*(sp_s0_13) + (74535369/500000000000 : ℝ)*(sp_s0_20) + (550639/200000000000 : ℝ)*(sp_s0_23) + (1445604509753/1000000000000 : ℝ)*(f.failure) + (3405454760067/1000000000000 : ℝ)*(f.sum) + (2882286606477649/5000000000000000000000000000 : ℝ)*base62 + (87512850615221/500000000000000000000000000 : ℝ)*base65 + (125647024621473/5000000000000000000000000000 : ℝ)*base67 + (114112107178611/1000000000000000000000000000 : ℝ)*base68 + (3872055901773683/5000000000000000000000000000 : ℝ)*base71 + (185595192542297/2500000000000000000000000000 : ℝ)*base73 + (1220547207703/2500000000000000000000000000 : ℝ)*base75 + (260780565378527/5000000000000000000000000000 : ℝ)*base76 + (341462923206067/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (112479/100000000000000000 : ℝ)*base86 + (112479/100000000000000000 : ℝ)*base88 + (112479/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-73993/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-73993/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (995717012734449994743/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (304131988061/500000000000 : ℝ)*(base1) + (1205061025453/1000000000000 : ℝ)*(base7) + (147998926037/1000000000000 : ℝ)*(base40) + (85444212559/200000000000 : ℝ)*(base60) + (1046529339271/500000000000 : ℝ)*(major_s0_0) + (1046529339271/500000000000 : ℝ)*(major_s0_1) + (1046529339271/500000000000 : ℝ)*(major_s0_2) + (2250379/125000000000 : ℝ)*(sp_s0_1) + (791743/5000000000 : ℝ)*(sp_s0_13) + (2916916853643/1000000000000 : ℝ)*(sp_s0_14) + (2308634874489/1000000000000 : ℝ)*(sp_s0_15) + (2308650648053/1000000000000 : ℝ)*(sp_s0_16) + (1777443226669/1000000000000 : ℝ)*(sp_s0_20) + (2229467/1000000000000 : ℝ)*(sp_s0_23) + (590402262969/500000000000 : ℝ)*(f.failure) + (28858160969/12500000000 : ℝ)*(f.sum) + (708255369909509/5000000000000000000000000000 : ℝ)*base63 + (683428083979281/2500000000000000000000000000 : ℝ)*base64 + (738697779368071/5000000000000000000000000000 : ℝ)*base66 + (549668586868071/5000000000000000000000000000 : ℝ)*base69 + (2640400057326633/5000000000000000000000000000 : ℝ)*base70 + (489714763979281/2500000000000000000000000000 : ℝ)*base73 + (1617638612770719/2500000000000000000000000000 : ℝ)*base75 + (3087472982868071/5000000000000000000000000000 : ℝ)*base76 + (72124835590491/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (3967/50000000000000000 : ℝ)*base86 + (3967/50000000000000000 : ℝ)*base88 + (3967/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(11369/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(11369/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17907035955686106070749/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2846809409777/1000000000000 : ℝ)*(base1) + (1106019530853/1000000000000 : ℝ)*(base7) + (1500478620923/1000000000000 : ℝ)*(base40) + (490130488159/1000000000000 : ℝ)*(base60) + (771417978921/250000000000 : ℝ)*(major_s0_0) + (771417978921/250000000000 : ℝ)*(major_s0_1) + (771417978921/250000000000 : ℝ)*(major_s0_2) + (642859/31250000000 : ℝ)*(sp_s0_1) + (13705173/1000000000000 : ℝ)*(sp_s0_7) + (73301329/1000000000000 : ℝ)*(sp_s0_8) + (64397/1000000000000 : ℝ)*(sp_s0_9) + (1659485982713/250000000000 : ℝ)*(sp_s0_21) + (473881794179/125000000000 : ℝ)*(sp_s0_22) + (947787040463/250000000000 : ℝ)*(sp_s0_23) + (435197469731/250000000000 : ℝ)*(f.failure) + (3791148226249/1000000000000 : ℝ)*(f.sum) + (298081056093141/2500000000000000000000000000 : ℝ)*base62 + (716640978060431/1250000000000000000000000000 : ℝ)*base64 + (967225001972279/2500000000000000000000000000 : ℝ)*base67 + (680451271277721/2500000000000000000000000000 : ℝ)*base69 + (730682874851417/2500000000000000000000000000 : ℝ)*base71 + (287899997189569/1250000000000000000000000000 : ℝ)*base72 + (182095729814569/1250000000000000000000000000 : ℝ)*base75 + (695177705222279/2500000000000000000000000000 : ℝ)*base77 + (928376276406859/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (7867/25000000000000000 : ℝ)*base87 + (7867/25000000000000000 : ℝ)*base89 + (7867/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (46367/100000 : ℝ) ^ (19/4 : ℝ) ≤ (2597124312476460727/100000000000000000000 : ℝ) := by
    have hpowers : (46367/100000 : ℝ)^19 ≤ (2597124312476460727/100000000000000000000 : ℝ)^4 := by
      have hnat : (46367 : ℕ)^19*100000000000000000000^4 ≤ 2597124312476460727^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46367 100000 2597124312476460727 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (46367/100000 : ℝ)) (X := (2597124312476460727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (102597124312476460727/100000000000000000000 : ℝ) ≤ (2010824859949097/2000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (102597124312476460727/100000000000000000000 : ℝ)^4 ≤ (2010824859949097/2000000000000000 : ℝ)^19 := by
      have hnat : (102597124312476460727 : ℕ)^4*2000000000000000^19 ≤ 2010824859949097^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102597124312476460727 100000000000000000000 2010824859949097 2000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2010824859949097/2000000000000000 : ℝ)) (X := (102597124312476460727/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (52597124312476460727/50000000000000000000 : ℝ) ≤ (252679438155013/250000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (52597124312476460727/50000000000000000000 : ℝ)^4 ≤ (252679438155013/250000000000000 : ℝ)^19 := by
      have hnat : (52597124312476460727 : ℕ)^4*250000000000000^19 ≤ 252679438155013^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52597124312476460727 50000000000000000000 252679438155013 250000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (252679438155013/250000000000000 : ℝ)) (X := (52597124312476460727/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(10824859949097/927340000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(10610645291007/927340000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (46367/100000 : ℝ)) (alpha := (10824859949097/927340000000000 : ℝ)) (beta := (10610645291007/927340000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (46367/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(10824859949097/927340000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(10610645291007/927340000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (73993/100000 : ℝ) ^ (19/4 : ℝ) ≤ (11957090732327110641/50000000000000000000 : ℝ) := by
    have hpowers : (73993/100000 : ℝ)^19 ≤ (11957090732327110641/50000000000000000000 : ℝ)^4 := by
      have hnat : (73993 : ℕ)^19*50000000000000000000^4 ≤ 11957090732327110641^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73993 100000 11957090732327110641 50000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73993/100000 : ℝ)) (X := (11957090732327110641/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (61957090732327110641/50000000000000000000 : ℝ) ≤ (10461752071752311/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (61957090732327110641/50000000000000000000 : ℝ)^4 ≤ (10461752071752311/10000000000000000 : ℝ)^19 := by
      have hnat : (61957090732327110641 : ℕ)^4*10000000000000000^19 ≤ 10461752071752311^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61957090732327110641 50000000000000000000 10461752071752311 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10461752071752311/10000000000000000 : ℝ)) (X := (61957090732327110641/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (36957090732327110641/25000000000000000000 : ℝ) ≤ (5428857994111253/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (36957090732327110641/25000000000000000000 : ℝ)^4 ≤ (5428857994111253/5000000000000000 : ℝ)^19 := by
      have hnat : (36957090732327110641 : ℕ)^4*5000000000000000^19 ≤ 5428857994111253^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36957090732327110641 25000000000000000000 5428857994111253 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5428857994111253/5000000000000000 : ℝ)) (X := (36957090732327110641/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(461752071752311/7399300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(79192783294039/1479860000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (73993/100000 : ℝ)) (alpha := (461752071752311/7399300000000000 : ℝ)) (beta := (79192783294039/1479860000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (73993/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(461752071752311/7399300000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(79192783294039/1479860000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (11369/25000 : ℝ) ^ (19/4 : ℝ) ≤ (473691640183280261/20000000000000000000 : ℝ) := by
    have hpowers : (11369/25000 : ℝ)^19 ≤ (473691640183280261/20000000000000000000 : ℝ)^4 := by
      have hnat : (11369 : ℕ)^19*20000000000000000000^4 ≤ 473691640183280261^4*25000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11369 25000 473691640183280261 20000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11369/25000 : ℝ)) (X := (473691640183280261/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (20473691640183280261/20000000000000000000 : ℝ) ≤ (502470129284349/500000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (20473691640183280261/20000000000000000000 : ℝ)^4 ≤ (502470129284349/500000000000000 : ℝ)^19 := by
      have hnat : (20473691640183280261 : ℕ)^4*500000000000000^19 ≤ 502470129284349^19*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20473691640183280261 20000000000000000000 502470129284349 500000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (502470129284349/500000000000000 : ℝ)) (X := (20473691640183280261/20000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (10473691640183280261/10000000000000000000 : ℝ) ≤ (10097910877731189/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (10473691640183280261/10000000000000000000 : ℝ)^4 ≤ (10097910877731189/10000000000000000 : ℝ)^19 := by
      have hnat : (10473691640183280261 : ℕ)^4*10000000000000000^19 ≤ 10097910877731189^19*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10473691640183280261 10000000000000000000 10097910877731189 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10097910877731189/10000000000000000 : ℝ)) (X := (10473691640183280261/10000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(2470129284349/227380000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(48508292044209/4547600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (11369/25000 : ℝ)) (alpha := (2470129284349/227380000000000 : ℝ)) (beta := (48508292044209/4547600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (11369/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(2470129284349/227380000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(48508292044209/4547600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3460333893/10000000000 : ℝ)*X 0 0+(-3862927517/10000000000 : ℝ)*X 0 1+(5190627231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((529859031/1250000000 : ℝ)*X 1 0+(4749809763/10000000000 : ℝ)*X 1 1+(1776468291/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2601892141/5000000000 : ℝ)*X 2 0+(-4199049201/10000000000 : ℝ)*X 2 1+(-3090536829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((379994781/1250000000 : ℝ)*X 0 0+(-3187473583/10000000000 : ℝ)*X 0 1+(6150180061/10000000000 : ℝ)*X 0 2+(379994781/1250000000 : ℝ)*X 1 0+(-3187473583/10000000000 : ℝ)*X 1 1+(6150180061/10000000000 : ℝ)*X 1 2+(379994781/1250000000 : ℝ)*X 2 0+(-3187473583/10000000000 : ℝ)*X 2 1+(6150180061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316071_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-381771/50000 : ℝ) < ((-177257/100000 : ℝ)*P 0+(-177257/100000 : ℝ)*P 1+(-177257/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-381771/50000 : ℝ) < (-1463648302715642867701478067920724531/195025726385195000000000000000000000 : ℝ) := by norm_num
    linear_combination (316142319277/1000000000000 : ℝ)*(base1) + (171973/1000000000000 : ℝ)*(base13) + (97659/1000000000000 : ℝ)*(base17) + (140377/1000000000000 : ℝ)*(base22) + (151229/1000000000000 : ℝ)*(base39) + (483452891009/1000000000000 : ℝ)*(base40) + (42006908599/250000000000 : ℝ)*(base49) + (242506868459/500000000000 : ℝ)*(base60) + (177257/100000 : ℝ)*(major_s1_0) + (177257/100000 : ℝ)*(major_s1_1) + (177257/100000 : ℝ)*(major_s1_2) + (352221877131/125000000000 : ℝ)*(sp_s1_0) + (625408193021/250000000000 : ℝ)*(sp_s1_1) + (1250816364683/500000000000 : ℝ)*(sp_s1_2) + (683857680723/1000000000000 : ℝ)*(sp_s1_6) + (156352054359/62500000000 : ℝ)*(f.sum) + (4395411448795643/13144162765625000000000000000 : ℝ)*base63 + (699533471797/4547600000000000000000000 : ℝ)*base65 + (154558782246663/739930000000000000000000000 : ℝ)*base66 + (1643956346477/14211250000000000000000000 : ℝ)*base69 + (2770434354481940391/5271464230000000000000000000000 : ℝ)*base71 + (214788404170303/463670000000000000000000000 : ℝ)*base73 + (84688542591403/184982500000000000000000000 : ℝ)*base75 + (9495912686539/18546800000000000000000000 : ℝ)*base76 + (8251225440382433041/34308334310000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p016_b029 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=70 ∨ c=71 := by omega
  rcases hc with rfl|rfl
  · exact collision_c316070 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316071 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p016_b029 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

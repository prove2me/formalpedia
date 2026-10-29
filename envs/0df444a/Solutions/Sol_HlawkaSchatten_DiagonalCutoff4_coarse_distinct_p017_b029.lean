-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017_b029
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:14:15.558419+00:00
-- url     : https://prove2.me/submissions/a5c18875-6bec-4f45-adfc-bfde2cc4a7c6

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
theorem collision_support_c317068_s0_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7535894393/10000000000 : ℝ)*x 0 + (2688086411/10000000000 : ℝ)*x 1 + (-1704304707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7535894393/10000000000 : ℝ)^39 ≤ (70053148026007/100000000000000 : ℝ)^31 := by
    have hnat : (7535894393 : ℕ)^39*100000000000000^31 ≤ 70053148026007^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7535894393 10000000000 70053148026007 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688086411/10000000000 : ℝ)^39 ≤ (19151498792683/100000000000000 : ℝ)^31 := by
    have hnat : (2688086411 : ℕ)^39*100000000000000^31 ≤ 19151498792683^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688086411 10000000000 19151498792683 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1704304707/10000000000 : ℝ)^39 ≤ (2698838291323/25000000000000 : ℝ)^31 := by
    have hnat : (1704304707 : ℕ)^39*25000000000000^31 ≤ 2698838291323^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704304707 10000000000 2698838291323 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7535894393/10000000000 : ℝ), (2688086411/10000000000 : ℝ), (-1704304707/10000000000 : ℝ)] ![(70053148026007/100000000000000 : ℝ), (19151498792683/100000000000000 : ℝ), (2698838291323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7535894393/10000000000 : ℝ)|^39 ≤ (70053148026007/100000000000000 : ℝ)^31
        have hw : |(7535894393/10000000000 : ℝ)|=(7535894393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688086411/10000000000 : ℝ)|^39 ≤ (19151498792683/100000000000000 : ℝ)^31
        have hw : |(2688086411/10000000000 : ℝ)|=(2688086411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1704304707/10000000000 : ℝ)|^39 ≤ (2698838291323/25000000000000 : ℝ)^31
        have hw : |(-1704304707/10000000000 : ℝ)|=(1704304707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s0_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (805949039/2000000000 : ℝ)*x 0 + (-4402265677/10000000000 : ℝ)*x 1 + (2046619673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (805949039/2000000000 : ℝ)^39 ≤ (31872324422611/100000000000000 : ℝ)^31 := by
    have hnat : (805949039 : ℕ)^39*100000000000000^31 ≤ 31872324422611^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805949039 2000000000 31872324422611 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4402265677/10000000000 : ℝ)^39 ≤ (17811140789789/50000000000000 : ℝ)^31 := by
    have hnat : (4402265677 : ℕ)^39*50000000000000^31 ≤ 17811140789789^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402265677 10000000000 17811140789789 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2046619673/5000000000 : ℝ)^39 ≤ (16252696992659/50000000000000 : ℝ)^31 := by
    have hnat : (2046619673 : ℕ)^39*50000000000000^31 ≤ 16252696992659^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046619673 5000000000 16252696992659 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(805949039/2000000000 : ℝ), (-4402265677/10000000000 : ℝ), (2046619673/5000000000 : ℝ)] ![(31872324422611/100000000000000 : ℝ), (17811140789789/50000000000000 : ℝ), (16252696992659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(805949039/2000000000 : ℝ)|^39 ≤ (31872324422611/100000000000000 : ℝ)^31
        have hw : |(805949039/2000000000 : ℝ)|=(805949039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4402265677/10000000000 : ℝ)|^39 ≤ (17811140789789/50000000000000 : ℝ)^31
        have hw : |(-4402265677/10000000000 : ℝ)|=(4402265677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2046619673/5000000000 : ℝ)|^39 ≤ (16252696992659/50000000000000 : ℝ)^31
        have hw : |(2046619673/5000000000 : ℝ)|=(2046619673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s0_7 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-560560483/10000000000 : ℝ)*x 0 + (-1101521367/2000000000 : ℝ)*x 1 + (-360912377/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (560560483/10000000000 : ℝ)^39 ≤ (20819791431/781250000000 : ℝ)^31 := by
    have hnat : (560560483 : ℕ)^39*781250000000^31 ≤ 20819791431^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560560483 10000000000 20819791431 781250000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101521367/2000000000 : ℝ)^39 ≤ (944375365613/2000000000000 : ℝ)^31 := by
    have hnat : (1101521367 : ℕ)^39*2000000000000^31 ≤ 944375365613^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101521367 2000000000 944375365613 2000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (360912377/625000000 : ℝ)^39 ≤ (50116298409849/100000000000000 : ℝ)^31 := by
    have hnat : (360912377 : ℕ)^39*100000000000000^31 ≤ 50116298409849^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360912377 625000000 50116298409849 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-560560483/10000000000 : ℝ), (-1101521367/2000000000 : ℝ), (-360912377/625000000 : ℝ)] ![(20819791431/781250000000 : ℝ), (944375365613/2000000000000 : ℝ), (50116298409849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-560560483/10000000000 : ℝ)|^39 ≤ (20819791431/781250000000 : ℝ)^31
        have hw : |(-560560483/10000000000 : ℝ)|=(560560483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1101521367/2000000000 : ℝ)|^39 ≤ (944375365613/2000000000000 : ℝ)^31
        have hw : |(-1101521367/2000000000 : ℝ)|=(1101521367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-360912377/625000000 : ℝ)|^39 ≤ (50116298409849/100000000000000 : ℝ)^31
        have hw : |(-360912377/625000000 : ℝ)|=(360912377/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s0_8 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1513877637/2000000000 : ℝ)*x 0 + (782805401/2500000000 : ℝ)*x 1 + (-111782079/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1513877637/2000000000 : ℝ)^39 ≤ (70445078294411/100000000000000 : ℝ)^31 := by
    have hnat : (1513877637 : ℕ)^39*100000000000000^31 ≤ 70445078294411^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1513877637 2000000000 70445078294411 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (782805401/2500000000 : ℝ)^39 ≤ (5801167970387/25000000000000 : ℝ)^31 := by
    have hnat : (782805401 : ℕ)^39*25000000000000^31 ≤ 5801167970387^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782805401 2500000000 5801167970387 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111782079/1000000000 : ℝ)^39 ≤ (6350249814053/100000000000000 : ℝ)^31 := by
    have hnat : (111782079 : ℕ)^39*100000000000000^31 ≤ 6350249814053^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111782079 1000000000 6350249814053 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1513877637/2000000000 : ℝ), (782805401/2500000000 : ℝ), (-111782079/1000000000 : ℝ)] ![(70445078294411/100000000000000 : ℝ), (5801167970387/25000000000000 : ℝ), (6350249814053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1513877637/2000000000 : ℝ)|^39 ≤ (70445078294411/100000000000000 : ℝ)^31
        have hw : |(1513877637/2000000000 : ℝ)|=(1513877637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(782805401/2500000000 : ℝ)|^39 ≤ (5801167970387/25000000000000 : ℝ)^31
        have hw : |(782805401/2500000000 : ℝ)|=(782805401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111782079/1000000000 : ℝ)|^39 ≤ (6350249814053/100000000000000 : ℝ)^31
        have hw : |(-111782079/1000000000 : ℝ)|=(111782079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s0_9 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4647328477/10000000000 : ℝ)*x 0 + (-3090850513/10000000000 : ℝ)*x 1 + (73975979/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4647328477/10000000000 : ℝ)^39 ≤ (76269406027/200000000000 : ℝ)^31 := by
    have hnat : (4647328477 : ℕ)^39*200000000000^31 ≤ 76269406027^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4647328477 10000000000 76269406027 200000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3090850513/10000000000 : ℝ)^39 ≤ (22828912699699/100000000000000 : ℝ)^31 := by
    have hnat : (3090850513 : ℕ)^39*100000000000000^31 ≤ 22828912699699^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3090850513 10000000000 22828912699699 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73975979/156250000 : ℝ)^39 ≤ (39036384264103/100000000000000 : ℝ)^31 := by
    have hnat : (73975979 : ℕ)^39*100000000000000^31 ≤ 39036384264103^31*156250000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73975979 156250000 39036384264103 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4647328477/10000000000 : ℝ), (-3090850513/10000000000 : ℝ), (73975979/156250000 : ℝ)] ![(76269406027/200000000000 : ℝ), (22828912699699/100000000000000 : ℝ), (39036384264103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4647328477/10000000000 : ℝ)|^39 ≤ (76269406027/200000000000 : ℝ)^31
        have hw : |(4647328477/10000000000 : ℝ)|=(4647328477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3090850513/10000000000 : ℝ)|^39 ≤ (22828912699699/100000000000000 : ℝ)^31
        have hw : |(-3090850513/10000000000 : ℝ)|=(3090850513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(73975979/156250000 : ℝ)|^39 ≤ (39036384264103/100000000000000 : ℝ)^31
        have hw : |(73975979/156250000 : ℝ)|=(73975979/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s0_13 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (508714409/1250000000 : ℝ)*x 0 + (-266186407/1250000000 : ℝ)*x 1 + (-1519313487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (508714409/1250000000 : ℝ)^39 ≤ (32270549096759/100000000000000 : ℝ)^31 := by
    have hnat : (508714409 : ℕ)^39*100000000000000^31 ≤ 32270549096759^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508714409 1250000000 32270549096759 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266186407/1250000000 : ℝ)^39 ≤ (14286560881989/100000000000000 : ℝ)^31 := by
    have hnat : (266186407 : ℕ)^39*100000000000000^31 ≤ 14286560881989^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266186407 1250000000 14286560881989 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1519313487/2500000000 : ℝ)^39 ≤ (10688578001507/20000000000000 : ℝ)^31 := by
    have hnat : (1519313487 : ℕ)^39*20000000000000^31 ≤ 10688578001507^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519313487 2500000000 10688578001507 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(508714409/1250000000 : ℝ), (-266186407/1250000000 : ℝ), (-1519313487/2500000000 : ℝ)] ![(32270549096759/100000000000000 : ℝ), (14286560881989/100000000000000 : ℝ), (10688578001507/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(508714409/1250000000 : ℝ)|^39 ≤ (32270549096759/100000000000000 : ℝ)^31
        have hw : |(508714409/1250000000 : ℝ)|=(508714409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266186407/1250000000 : ℝ)|^39 ≤ (14286560881989/100000000000000 : ℝ)^31
        have hw : |(-266186407/1250000000 : ℝ)|=(266186407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1519313487/2500000000 : ℝ)|^39 ≤ (10688578001507/20000000000000 : ℝ)^31
        have hw : |(-1519313487/2500000000 : ℝ)|=(1519313487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s0_14 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-124447041/5000000000 : ℝ)*x 0 + (-2213176791/5000000000 : ℝ)*x 1 + (-3470697287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (124447041/5000000000 : ℝ)^39 ≤ (959583665691/100000000000000 : ℝ)^31 := by
    have hnat : (124447041 : ℕ)^39*100000000000000^31 ≤ 959583665691^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124447041 5000000000 959583665691 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213176791/5000000000 : ℝ)^39 ≤ (17933834848291/50000000000000 : ℝ)^31 := by
    have hnat : (2213176791 : ℕ)^39*50000000000000^31 ≤ 17933834848291^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213176791 5000000000 17933834848291 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3470697287/5000000000 : ℝ)^39 ≤ (31586373313857/50000000000000 : ℝ)^31 := by
    have hnat : (3470697287 : ℕ)^39*50000000000000^31 ≤ 31586373313857^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3470697287 5000000000 31586373313857 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-124447041/5000000000 : ℝ), (-2213176791/5000000000 : ℝ), (-3470697287/5000000000 : ℝ)] ![(959583665691/100000000000000 : ℝ), (17933834848291/50000000000000 : ℝ), (31586373313857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-124447041/5000000000 : ℝ)|^39 ≤ (959583665691/100000000000000 : ℝ)^31
        have hw : |(-124447041/5000000000 : ℝ)|=(124447041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2213176791/5000000000 : ℝ)|^39 ≤ (17933834848291/50000000000000 : ℝ)^31
        have hw : |(-2213176791/5000000000 : ℝ)|=(2213176791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3470697287/5000000000 : ℝ)|^39 ≤ (31586373313857/50000000000000 : ℝ)^31
        have hw : |(-3470697287/5000000000 : ℝ)|=(3470697287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s0_15 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8387184/9765625 : ℝ)*x 0 + (526456661/2500000000 : ℝ)*x 1 + (-670009343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8387184/9765625 : ℝ)^39 ≤ (20644398490261/25000000000000 : ℝ)^31 := by
    have hnat : (8387184 : ℕ)^39*25000000000000^31 ≤ 20644398490261^31*9765625^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8387184 9765625 20644398490261 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526456661/2500000000 : ℝ)^39 ≤ (14087113092057/100000000000000 : ℝ)^31 := by
    have hnat : (526456661 : ℕ)^39*100000000000000^31 ≤ 14087113092057^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526456661 2500000000 14087113092057 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (670009343/10000000000 : ℝ)^39 ≤ (3335292935991/100000000000000 : ℝ)^31 := by
    have hnat : (670009343 : ℕ)^39*100000000000000^31 ≤ 3335292935991^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670009343 10000000000 3335292935991 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8387184/9765625 : ℝ), (526456661/2500000000 : ℝ), (-670009343/10000000000 : ℝ)] ![(20644398490261/25000000000000 : ℝ), (14087113092057/100000000000000 : ℝ), (3335292935991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8387184/9765625 : ℝ)|^39 ≤ (20644398490261/25000000000000 : ℝ)^31
        have hw : |(8387184/9765625 : ℝ)|=(8387184/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526456661/2500000000 : ℝ)|^39 ≤ (14087113092057/100000000000000 : ℝ)^31
        have hw : |(526456661/2500000000 : ℝ)|=(526456661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-670009343/10000000000 : ℝ)|^39 ≤ (3335292935991/100000000000000 : ℝ)^31
        have hw : |(-670009343/10000000000 : ℝ)|=(670009343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s0_16 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4403779357/10000000000 : ℝ)*x 0 + (-113503807/250000000 : ℝ)*x 1 + (891558211/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4403779357/10000000000 : ℝ)^39 ≤ (35637691547531/100000000000000 : ℝ)^31 := by
    have hnat : (4403779357 : ℕ)^39*100000000000000^31 ≤ 35637691547531^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4403779357 10000000000 35637691547531 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113503807/250000000 : ℝ)^39 ≤ (4628949858281/12500000000000 : ℝ)^31 := by
    have hnat : (113503807 : ℕ)^39*12500000000000^31 ≤ 4628949858281^31*250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113503807 250000000 4628949858281 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (891558211/2500000000 : ℝ)^39 ≤ (13665354784587/50000000000000 : ℝ)^31 := by
    have hnat : (891558211 : ℕ)^39*50000000000000^31 ≤ 13665354784587^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891558211 2500000000 13665354784587 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4403779357/10000000000 : ℝ), (-113503807/250000000 : ℝ), (891558211/2500000000 : ℝ)] ![(35637691547531/100000000000000 : ℝ), (4628949858281/12500000000000 : ℝ), (13665354784587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4403779357/10000000000 : ℝ)|^39 ≤ (35637691547531/100000000000000 : ℝ)^31
        have hw : |(4403779357/10000000000 : ℝ)|=(4403779357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-113503807/250000000 : ℝ)|^39 ≤ (4628949858281/12500000000000 : ℝ)^31
        have hw : |(-113503807/250000000 : ℝ)|=(113503807/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(891558211/2500000000 : ℝ)|^39 ≤ (13665354784587/50000000000000 : ℝ)^31
        have hw : |(891558211/2500000000 : ℝ)|=(891558211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s0_20 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2583651797/10000000000 : ℝ)*x 0 + (-2627168197/10000000000 : ℝ)*x 1 + (-3470697287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2583651797/10000000000 : ℝ)^39 ≤ (1822017021263/10000000000000 : ℝ)^31 := by
    have hnat : (2583651797 : ℕ)^39*10000000000000^31 ≤ 1822017021263^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583651797 10000000000 1822017021263 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627168197/10000000000 : ℝ)^39 ≤ (9303541573699/50000000000000 : ℝ)^31 := by
    have hnat : (2627168197 : ℕ)^39*50000000000000^31 ≤ 9303541573699^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627168197 10000000000 9303541573699 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3470697287/5000000000 : ℝ)^39 ≤ (31586373313857/50000000000000 : ℝ)^31 := by
    have hnat : (3470697287 : ℕ)^39*50000000000000^31 ≤ 31586373313857^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3470697287 5000000000 31586373313857 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2583651797/10000000000 : ℝ), (-2627168197/10000000000 : ℝ), (-3470697287/5000000000 : ℝ)] ![(1822017021263/10000000000000 : ℝ), (9303541573699/50000000000000 : ℝ), (31586373313857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2583651797/10000000000 : ℝ)|^39 ≤ (1822017021263/10000000000000 : ℝ)^31
        have hw : |(2583651797/10000000000 : ℝ)|=(2583651797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2627168197/10000000000 : ℝ)|^39 ≤ (9303541573699/50000000000000 : ℝ)^31
        have hw : |(-2627168197/10000000000 : ℝ)|=(2627168197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3470697287/5000000000 : ℝ)|^39 ≤ (31586373313857/50000000000000 : ℝ)^31
        have hw : |(-3470697287/5000000000 : ℝ)|=(3470697287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s0_21 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-103022591/5000000000 : ℝ)*x 0 + (-1232987599/2000000000 : ℝ)*x 1 + (-5284835039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103022591/5000000000 : ℝ)^39 ≤ (151316399347/20000000000000 : ℝ)^31 := by
    have hnat : (103022591 : ℕ)^39*20000000000000^31 ≤ 151316399347^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103022591 5000000000 151316399347 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1232987599/2000000000 : ℝ)^39 ≤ (27207383125253/50000000000000 : ℝ)^31 := by
    have hnat : (1232987599 : ℕ)^39*50000000000000^31 ≤ 27207383125253^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232987599 2000000000 27207383125253 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5284835039/10000000000 : ℝ)^39 ≤ (358629213903/800000000000 : ℝ)^31 := by
    have hnat : (5284835039 : ℕ)^39*800000000000^31 ≤ 358629213903^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284835039 10000000000 358629213903 800000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103022591/5000000000 : ℝ), (-1232987599/2000000000 : ℝ), (-5284835039/10000000000 : ℝ)] ![(151316399347/20000000000000 : ℝ), (27207383125253/50000000000000 : ℝ), (358629213903/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103022591/5000000000 : ℝ)|^39 ≤ (151316399347/20000000000000 : ℝ)^31
        have hw : |(-103022591/5000000000 : ℝ)|=(103022591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1232987599/2000000000 : ℝ)|^39 ≤ (27207383125253/50000000000000 : ℝ)^31
        have hw : |(-1232987599/2000000000 : ℝ)|=(1232987599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5284835039/10000000000 : ℝ)|^39 ≤ (358629213903/800000000000 : ℝ)^31
        have hw : |(-5284835039/10000000000 : ℝ)|=(5284835039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s0_22 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2210356431/2500000000 : ℝ)*x 0 + (346463693/2000000000 : ℝ)*x 1 + (-33474777/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210356431/2500000000 : ℝ)^39 ≤ (21412215983703/25000000000000 : ℝ)^31 := by
    have hnat : (2210356431 : ℕ)^39*25000000000000^31 ≤ 21412215983703^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210356431 2500000000 21412215983703 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346463693/2000000000 : ℝ)^39 ≤ (2203812109069/20000000000000 : ℝ)^31 := by
    have hnat : (346463693 : ℕ)^39*20000000000000^31 ≤ 2203812109069^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346463693 2000000000 2203812109069 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33474777/500000000 : ℝ)^39 ≤ (333207550167/10000000000000 : ℝ)^31 := by
    have hnat : (33474777 : ℕ)^39*10000000000000^31 ≤ 333207550167^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33474777 500000000 333207550167 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2210356431/2500000000 : ℝ), (346463693/2000000000 : ℝ), (-33474777/500000000 : ℝ)] ![(21412215983703/25000000000000 : ℝ), (2203812109069/20000000000000 : ℝ), (333207550167/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2210356431/2500000000 : ℝ)|^39 ≤ (21412215983703/25000000000000 : ℝ)^31
        have hw : |(2210356431/2500000000 : ℝ)|=(2210356431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(346463693/2000000000 : ℝ)|^39 ≤ (2203812109069/20000000000000 : ℝ)^31
        have hw : |(346463693/2000000000 : ℝ)|=(346463693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33474777/500000000 : ℝ)|^39 ≤ (333207550167/10000000000000 : ℝ)^31
        have hw : |(-33474777/500000000 : ℝ)|=(33474777/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s0_23 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3513070161/10000000000 : ℝ)*x 0 + (-1122438321/2500000000 : ℝ)*x 1 + (2252228493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3513070161/10000000000 : ℝ)^39 ≤ (5363826343593/20000000000000 : ℝ)^31 := by
    have hnat : (3513070161 : ℕ)^39*20000000000000^31 ≤ 5363826343593^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3513070161 10000000000 5363826343593 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122438321/2500000000 : ℝ)^39 ≤ (18257589693829/50000000000000 : ℝ)^31 := by
    have hnat : (1122438321 : ℕ)^39*50000000000000^31 ≤ 18257589693829^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122438321 2500000000 18257589693829 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252228493/5000000000 : ℝ)^39 ≤ (18332844441843/50000000000000 : ℝ)^31 := by
    have hnat : (2252228493 : ℕ)^39*50000000000000^31 ≤ 18332844441843^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252228493 5000000000 18332844441843 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3513070161/10000000000 : ℝ), (-1122438321/2500000000 : ℝ), (2252228493/5000000000 : ℝ)] ![(5363826343593/20000000000000 : ℝ), (18257589693829/50000000000000 : ℝ), (18332844441843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3513070161/10000000000 : ℝ)|^39 ≤ (5363826343593/20000000000000 : ℝ)^31
        have hw : |(3513070161/10000000000 : ℝ)|=(3513070161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1122438321/2500000000 : ℝ)|^39 ≤ (18257589693829/50000000000000 : ℝ)^31
        have hw : |(-1122438321/2500000000 : ℝ)|=(1122438321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252228493/5000000000 : ℝ)|^39 ≤ (18332844441843/50000000000000 : ℝ)^31
        have hw : |(2252228493/5000000000 : ℝ)|=(2252228493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s0_27 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (54514587/156250000 : ℝ)*x 0 + (-1847801791/5000000000 : ℝ)*x 1 + (-5284835039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54514587/156250000 : ℝ)^39 ≤ (26587525116933/100000000000000 : ℝ)^31 := by
    have hnat : (54514587 : ℕ)^39*100000000000000^31 ≤ 26587525116933^31*156250000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54514587 156250000 26587525116933 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1847801791/5000000000 : ℝ)^39 ≤ (28583823136977/100000000000000 : ℝ)^31 := by
    have hnat : (1847801791 : ℕ)^39*100000000000000^31 ≤ 28583823136977^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847801791 5000000000 28583823136977 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5284835039/10000000000 : ℝ)^39 ≤ (358629213903/800000000000 : ℝ)^31 := by
    have hnat : (5284835039 : ℕ)^39*800000000000^31 ≤ 358629213903^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284835039 10000000000 358629213903 800000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54514587/156250000 : ℝ), (-1847801791/5000000000 : ℝ), (-5284835039/10000000000 : ℝ)] ![(26587525116933/100000000000000 : ℝ), (28583823136977/100000000000000 : ℝ), (358629213903/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54514587/156250000 : ℝ)|^39 ≤ (26587525116933/100000000000000 : ℝ)^31
        have hw : |(54514587/156250000 : ℝ)|=(54514587/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1847801791/5000000000 : ℝ)|^39 ≤ (28583823136977/100000000000000 : ℝ)^31
        have hw : |(-1847801791/5000000000 : ℝ)|=(1847801791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5284835039/10000000000 : ℝ)|^39 ≤ (358629213903/800000000000 : ℝ)^31
        have hw : |(-5284835039/10000000000 : ℝ)|=(5284835039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s1_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-139643911/625000000 : ℝ)*x 0 + (-4795482757/10000000000 : ℝ)*x 1 + (-5315193583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139643911/625000000 : ℝ)^39 ≤ (607069786967/4000000000000 : ℝ)^31 := by
    have hnat : (139643911 : ℕ)^39*4000000000000^31 ≤ 607069786967^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139643911 625000000 607069786967 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4795482757/10000000000 : ℝ)^39 ≤ (619849864223/1562500000000 : ℝ)^31 := by
    have hnat : (4795482757 : ℕ)^39*1562500000000^31 ≤ 619849864223^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795482757 10000000000 619849864223 1562500000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5315193583/10000000000 : ℝ)^39 ≤ (45152863992791/100000000000000 : ℝ)^31 := by
    have hnat : (5315193583 : ℕ)^39*100000000000000^31 ≤ 45152863992791^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5315193583 10000000000 45152863992791 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-139643911/625000000 : ℝ), (-4795482757/10000000000 : ℝ), (-5315193583/10000000000 : ℝ)] ![(607069786967/4000000000000 : ℝ), (619849864223/1562500000000 : ℝ), (45152863992791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-139643911/625000000 : ℝ)|^39 ≤ (607069786967/4000000000000 : ℝ)^31
        have hw : |(-139643911/625000000 : ℝ)|=(139643911/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4795482757/10000000000 : ℝ)|^39 ≤ (619849864223/1562500000000 : ℝ)^31
        have hw : |(-4795482757/10000000000 : ℝ)|=(4795482757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5315193583/10000000000 : ℝ)|^39 ≤ (45152863992791/100000000000000 : ℝ)^31
        have hw : |(-5315193583/10000000000 : ℝ)|=(5315193583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s1_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1232033571/2000000000 : ℝ)*x 0 + (404461693/1250000000 : ℝ)*x 1 + (-2942094251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1232033571/2000000000 : ℝ)^39 ≤ (54361802500919/100000000000000 : ℝ)^31 := by
    have hnat : (1232033571 : ℕ)^39*100000000000000^31 ≤ 54361802500919^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232033571 2000000000 54361802500919 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404461693/1250000000 : ℝ)^39 ≤ (24182842760001/100000000000000 : ℝ)^31 := by
    have hnat : (404461693 : ℕ)^39*100000000000000^31 ≤ 24182842760001^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404461693 1250000000 24182842760001 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2942094251/10000000000 : ℝ)^39 ≤ (21455354723649/100000000000000 : ℝ)^31 := by
    have hnat : (2942094251 : ℕ)^39*100000000000000^31 ≤ 21455354723649^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2942094251 10000000000 21455354723649 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1232033571/2000000000 : ℝ), (404461693/1250000000 : ℝ), (-2942094251/10000000000 : ℝ)] ![(54361802500919/100000000000000 : ℝ), (24182842760001/100000000000000 : ℝ), (21455354723649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1232033571/2000000000 : ℝ)|^39 ≤ (54361802500919/100000000000000 : ℝ)^31
        have hw : |(1232033571/2000000000 : ℝ)|=(1232033571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(404461693/1250000000 : ℝ)|^39 ≤ (24182842760001/100000000000000 : ℝ)^31
        have hw : |(404461693/1250000000 : ℝ)|=(404461693/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2942094251/10000000000 : ℝ)|^39 ≤ (21455354723649/100000000000000 : ℝ)^31
        have hw : |(-2942094251/10000000000 : ℝ)|=(2942094251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s1_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1030621383/2500000000 : ℝ)*x 0 + (-440097917/1000000000 : ℝ)*x 1 + (160065783/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1030621383/2500000000 : ℝ)^39 ≤ (32797849589099/100000000000000 : ℝ)^31 := by
    have hnat : (1030621383 : ℕ)^39*100000000000000^31 ≤ 32797849589099^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030621383 2500000000 32797849589099 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440097917/1000000000 : ℝ)^39 ≤ (7121837082709/20000000000000 : ℝ)^31 := by
    have hnat : (440097917 : ℕ)^39*20000000000000^31 ≤ 7121837082709^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440097917 1000000000 7121837082709 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160065783/400000000 : ℝ)^39 ≤ (15796482493597/50000000000000 : ℝ)^31 := by
    have hnat : (160065783 : ℕ)^39*50000000000000^31 ≤ 15796482493597^31*400000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160065783 400000000 15796482493597 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1030621383/2500000000 : ℝ), (-440097917/1000000000 : ℝ), (160065783/400000000 : ℝ)] ![(32797849589099/100000000000000 : ℝ), (7121837082709/20000000000000 : ℝ), (15796482493597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1030621383/2500000000 : ℝ)|^39 ≤ (32797849589099/100000000000000 : ℝ)^31
        have hw : |(1030621383/2500000000 : ℝ)|=(1030621383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440097917/1000000000 : ℝ)|^39 ≤ (7121837082709/20000000000000 : ℝ)^31
        have hw : |(-440097917/1000000000 : ℝ)|=(440097917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160065783/400000000 : ℝ)|^39 ≤ (15796482493597/50000000000000 : ℝ)^31
        have hw : |(160065783/400000000 : ℝ)|=(160065783/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317068_s1_6 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3880581983/10000000000 : ℝ)*x 0 + (-2048999621/5000000000 : ℝ)*x 1 + (-4542120237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3880581983/10000000000 : ℝ)^39 ≤ (7598812693343/25000000000000 : ℝ)^31 := by
    have hnat : (3880581983 : ℕ)^39*25000000000000^31 ≤ 7598812693343^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3880581983 10000000000 7598812693343 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2048999621/5000000000 : ℝ)^39 ≤ (16276477647897/50000000000000 : ℝ)^31 := by
    have hnat : (2048999621 : ℕ)^39*50000000000000^31 ≤ 16276477647897^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048999621 5000000000 16276477647897 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4542120237/10000000000 : ℝ)^39 ≤ (9262948478083/25000000000000 : ℝ)^31 := by
    have hnat : (4542120237 : ℕ)^39*25000000000000^31 ≤ 9262948478083^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542120237 10000000000 9262948478083 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3880581983/10000000000 : ℝ), (-2048999621/5000000000 : ℝ), (-4542120237/10000000000 : ℝ)] ![(7598812693343/25000000000000 : ℝ), (16276477647897/50000000000000 : ℝ), (9262948478083/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3880581983/10000000000 : ℝ)|^39 ≤ (7598812693343/25000000000000 : ℝ)^31
        have hw : |(3880581983/10000000000 : ℝ)|=(3880581983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2048999621/5000000000 : ℝ)|^39 ≤ (16276477647897/50000000000000 : ℝ)^31
        have hw : |(-2048999621/5000000000 : ℝ)|=(2048999621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4542120237/10000000000 : ℝ)|^39 ≤ (9262948478083/25000000000000 : ℝ)^31
        have hw : |(-4542120237/10000000000 : ℝ)|=(4542120237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317068 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]]) : False := by
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
  have main1 : (19897/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19897/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((7535894393/10000000000 : ℝ)*X 1 0+(2688086411/10000000000 : ℝ)*X 1 1+(-1704304707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((805949039/2000000000 : ℝ)*X 2 0+(-4402265677/10000000000 : ℝ)*X 2 1+(2046619673/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-560560483/10000000000 : ℝ)*X 0 0+(-1101521367/2000000000 : ℝ)*X 0 1+(-360912377/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1513877637/2000000000 : ℝ)*X 1 0+(782805401/2500000000 : ℝ)*X 1 1+(-111782079/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4647328477/10000000000 : ℝ)*X 2 0+(-3090850513/10000000000 : ℝ)*X 2 1+(73975979/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((508714409/1250000000 : ℝ)*X 0 0+(-266186407/1250000000 : ℝ)*X 0 1+(-1519313487/2500000000 : ℝ)*X 0 2+(508714409/1250000000 : ℝ)*X 1 0+(-266186407/1250000000 : ℝ)*X 1 1+(-1519313487/2500000000 : ℝ)*X 1 2+(508714409/1250000000 : ℝ)*X 2 0+(-266186407/1250000000 : ℝ)*X 2 1+(-1519313487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-124447041/5000000000 : ℝ)*X 0 0+(-2213176791/5000000000 : ℝ)*X 0 1+(-3470697287/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((8387184/9765625 : ℝ)*X 1 0+(526456661/2500000000 : ℝ)*X 1 1+(-670009343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4403779357/10000000000 : ℝ)*X 2 0+(-113503807/250000000 : ℝ)*X 2 1+(891558211/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2583651797/10000000000 : ℝ)*X 0 0+(-2627168197/10000000000 : ℝ)*X 0 1+(-3470697287/5000000000 : ℝ)*X 0 2+(2583651797/10000000000 : ℝ)*X 1 0+(-2627168197/10000000000 : ℝ)*X 1 1+(-3470697287/5000000000 : ℝ)*X 1 2+(2583651797/10000000000 : ℝ)*X 2 0+(-2627168197/10000000000 : ℝ)*X 2 1+(-3470697287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-103022591/5000000000 : ℝ)*X 0 0+(-1232987599/2000000000 : ℝ)*X 0 1+(-5284835039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2210356431/2500000000 : ℝ)*X 1 0+(346463693/2000000000 : ℝ)*X 1 1+(-33474777/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3513070161/10000000000 : ℝ)*X 2 0+(-1122438321/2500000000 : ℝ)*X 2 1+(2252228493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((54514587/156250000 : ℝ)*X 0 0+(-1847801791/5000000000 : ℝ)*X 0 1+(-5284835039/10000000000 : ℝ)*X 0 2+(54514587/156250000 : ℝ)*X 1 0+(-1847801791/5000000000 : ℝ)*X 1 1+(-5284835039/10000000000 : ℝ)*X 1 2+(54514587/156250000 : ℝ)*X 2 0+(-1847801791/5000000000 : ℝ)*X 2 1+(-5284835039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((97/625 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(97/625 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2203812827212348942269/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69714689587/50000000000 : ℝ)*(base1) + (924204436291/500000000000 : ℝ)*(base39) + (207533568619/500000000000 : ℝ)*(base49) + (200427/200000000000 : ℝ)*(base60) + (2507804699699/1000000000000 : ℝ)*(major_s0_0) + (2507804699699/1000000000000 : ℝ)*(major_s0_1) + (2507804699699/1000000000000 : ℝ)*(major_s0_2) + (1124997/40000000000 : ℝ)*(sp_s0_1) + (2507795367281/500000000000 : ℝ)*(sp_s0_7) + (1810643153681/500000000000 : ℝ)*(sp_s0_8) + (3621293910027/1000000000000 : ℝ)*(sp_s0_9) + (658021/100000000000 : ℝ)*(sp_s0_14) + (1363657/125000000000 : ℝ)*(sp_s0_21) + (1026113/50000000000 : ℝ)*(sp_s0_23) + (69714689587/50000000000 : ℝ)*(f.failure) + (3621314432287/1000000000000 : ℝ)*(f.sum) + (306255709095499/1000000000000000000000000000 : ℝ)*base63 + (6101639158682813/10000000000000000000000000000 : ℝ)*base65 + (6654175623727823/10000000000000000000000000000 : ℝ)*base67 + (2041044389272177/10000000000000000000000000000 : ℝ)*base69 + (171617900995499/1000000000000000000000000000 : ℝ)*base71 + (3209135993682813/10000000000000000000000000000 : ℝ)*base72 + (2449091209682813/10000000000000000000000000000 : ℝ)*base75 + (187696424727823/10000000000000000000000000000 : ℝ)*base76 + (217868190495499/1000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (997/2500000000000000 : ℝ)*base87 + (997/2500000000000000 : ℝ)*base89 + (997/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-45457/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-45457/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8603692585950644974683/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63885677723/62500000000 : ℝ)*(base1) + (155708626807/62500000000 : ℝ)*(base39) + (773684828477/1000000000000 : ℝ)*(base49) + (143375744731/200000000000 : ℝ)*(base60) + (535657758403/125000000000 : ℝ)*(major_s0_0) + (535657758403/125000000000 : ℝ)*(major_s0_1) + (535657758403/125000000000 : ℝ)*(major_s0_2) + (55578301/1000000000000 : ℝ)*(sp_s0_8) + (10336827/200000000000 : ℝ)*(sp_s0_9) + (7795003/200000000000 : ℝ)*(sp_s0_13) + (7210162636307/1000000000000 : ℝ)*(sp_s0_14) + (6187936214437/1000000000000 : ℝ)*(sp_s0_15) + (6187940108603/1000000000000 : ℝ)*(sp_s0_16) + (272063586897/200000000000 : ℝ)*(sp_s0_20) + (2382527753069/1000000000000 : ℝ)*(f.failure) + (3093995896369/500000000000 : ℝ)*(f.sum) + (27158294666497/125000000000000000000000000 : ℝ)*base62 + (605517945429061/1250000000000000000000000000 : ℝ)*base65 + (556442681844031/1250000000000000000000000000 : ℝ)*base67 + (80851283905969/1250000000000000000000000000 : ℝ)*base69 + (17460225383503/125000000000000000000000000 : ℝ)*base71 + (74482098320939/1250000000000000000000000000 : ℝ)*base73 + (558708723320939/1250000000000000000000000000 : ℝ)*base74 + (155696106655969/1250000000000000000000000000 : ℝ)*base77 + (884053003997/125000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (48239/50000000000000000 : ℝ)*base87 + (48239/50000000000000000 : ℝ)*base89 + (48239/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-637/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-637/2000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1444327383634001931639/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19168786109/250000000000 : ℝ)*(base1) + (68686771597/50000000000 : ℝ)*(base39) + (667975812389/1000000000000 : ℝ)*(base49) + (6287777/1000000000000 : ℝ)*(base60) + (130062626077/40000000000 : ℝ)*(major_s0_0) + (130062626077/40000000000 : ℝ)*(major_s0_1) + (130062626077/40000000000 : ℝ)*(major_s0_2) + (3144673/125000000000 : ℝ)*(sp_s0_2) + (4199901/100000000000 : ℝ)*(sp_s0_9) + (46560201/125000000000 : ℝ)*(sp_s0_15) + (4771992690187/1000000000000 : ℝ)*(sp_s0_21) + (4694945064143/1000000000000 : ℝ)*(sp_s0_22) + (1173812597339/250000000000 : ℝ)*(sp_s0_23) + (1731136206447/1000000000000 : ℝ)*(sp_s0_27) + (1807811350883/1000000000000 : ℝ)*(f.failure) + (4695317545751/1000000000000 : ℝ)*(f.sum) + (3996706518523/40000000000000000000000000 : ℝ)*base62 + (32929895835699/400000000000000000000000000 : ℝ)*base65 + (168154026820929/400000000000000000000000000 : ℝ)*base67 + (359991052020929/400000000000000000000000000 : ℝ)*base68 + (19051454642523/40000000000000000000000000 : ℝ)*base70 + (17888679195699/400000000000000000000000000 : ℝ)*base72 + (140604092595699/400000000000000000000000000 : ℝ)*base75 + (36674103540929/400000000000000000000000000 : ℝ)*base76 + (1826987042523/40000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (9073/50000000000000000 : ℝ)*base87 + (9073/50000000000000000 : ℝ)*base89 + (9073/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (97/625 : ℝ) ^ (77/16 : ℝ) ≤ (12769279340493073/100000000000000000000 : ℝ) := by
    have hpowers : (97/625 : ℝ)^77 ≤ (12769279340493073/100000000000000000000 : ℝ)^16 := by
      have hnat : (97 : ℕ)^77*100000000000000000000^16 ≤ 12769279340493073^16*625^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        97 625 12769279340493073 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (97/625 : ℝ)) (X := (12769279340493073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100012769279340493073/100000000000000000000 : ℝ) ≤ (625016582640941/625000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (100012769279340493073/100000000000000000000 : ℝ)^16 ≤ (625016582640941/625000000000000 : ℝ)^77 := by
      have hnat : (100012769279340493073 : ℕ)^16*625000000000000^77 ≤ 625016582640941^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100012769279340493073 100000000000000000000 625016582640941 625000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625016582640941/625000000000000 : ℝ)) (X := (100012769279340493073/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50012769279340493073/50000000000000000000 : ℝ) ≤ (5000265308837551/5000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (50012769279340493073/50000000000000000000 : ℝ)^16 ≤ (5000265308837551/5000000000000000 : ℝ)^77 := by
      have hnat : (50012769279340493073 : ℕ)^16*5000000000000000^77 ≤ 5000265308837551^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012769279340493073 50000000000000000000 5000265308837551 5000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000265308837551/5000000000000000 : ℝ)) (X := (50012769279340493073/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(16582640941/97000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(132647710023/776000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (97/625 : ℝ)) (alpha := (16582640941/97000000000000 : ℝ)) (beta := (132647710023/776000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (97/625 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(16582640941/97000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(132647710023/776000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (45457/100000 : ℝ) ^ (77/16 : ℝ) ≤ (2250109782433440709/100000000000000000000 : ℝ) := by
    have hpowers : (45457/100000 : ℝ)^77 ≤ (2250109782433440709/100000000000000000000 : ℝ)^16 := by
      have hnat : (45457 : ℕ)^77*100000000000000000000^16 ≤ 2250109782433440709^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45457 100000 2250109782433440709 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45457/100000 : ℝ)) (X := (2250109782433440709/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (102250109782433440709/100000000000000000000 : ℝ) ≤ (2511586080427643/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (102250109782433440709/100000000000000000000 : ℝ)^16 ≤ (2511586080427643/2500000000000000 : ℝ)^77 := by
      have hnat : (102250109782433440709 : ℕ)^16*2500000000000000^77 ≤ 2511586080427643^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102250109782433440709 100000000000000000000 2511586080427643 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511586080427643/2500000000000000 : ℝ)) (X := (102250109782433440709/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (52250109782433440709/50000000000000000000 : ℝ) ≤ (504594381112333/500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (52250109782433440709/50000000000000000000 : ℝ)^16 ≤ (504594381112333/500000000000000 : ℝ)^77 := by
      have hnat : (52250109782433440709 : ℕ)^16*500000000000000^77 ≤ 504594381112333^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52250109782433440709 50000000000000000000 504594381112333 500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (504594381112333/500000000000000 : ℝ)) (X := (52250109782433440709/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(11586080427643/1136425000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(5692912567011/568212500000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (45457/100000 : ℝ)) (alpha := (11586080427643/1136425000000000 : ℝ)) (beta := (5692912567011/568212500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (45457/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(11586080427643/1136425000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(5692912567011/568212500000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (637/2000 : ℝ) ^ (77/16 : ℝ) ≤ (16247036468856143/4000000000000000000 : ℝ) := by
    have hpowers : (637/2000 : ℝ)^77 ≤ (16247036468856143/4000000000000000000 : ℝ)^16 := by
      have hnat : (637 : ℕ)^77*4000000000000000000^16 ≤ 16247036468856143^16*2000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        637 2000 16247036468856143 4000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (637/2000 : ℝ)) (X := (16247036468856143/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (4016247036468856143/4000000000000000000 : ℝ) ≤ (10008426472835201/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (4016247036468856143/4000000000000000000 : ℝ)^16 ≤ (10008426472835201/10000000000000000 : ℝ)^77 := by
      have hnat : (4016247036468856143 : ℕ)^16*10000000000000000^77 ≤ 10008426472835201^77*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4016247036468856143 4000000000000000000 10008426472835201 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008426472835201/10000000000000000 : ℝ)) (X := (4016247036468856143/4000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (2016247036468856143/2000000000000000000 : ℝ) ≤ (2504206496033939/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2016247036468856143/2000000000000000000 : ℝ)^16 ≤ (2504206496033939/2500000000000000 : ℝ)^77 := by
      have hnat : (2016247036468856143 : ℕ)^16*2500000000000000^77 ≤ 2504206496033939^77*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2016247036468856143 2000000000000000000 2504206496033939 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504206496033939/2500000000000000 : ℝ)) (X := (2016247036468856143/2000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(8426472835201/3185000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1679902260111/637000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (637/2000 : ℝ)) (alpha := (8426472835201/3185000000000000 : ℝ)) (beta := (1679902260111/637000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (637/2000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(8426472835201/3185000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1679902260111/637000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-139643911/625000000 : ℝ)*X 0 0+(-4795482757/10000000000 : ℝ)*X 0 1+(-5315193583/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1232033571/2000000000 : ℝ)*X 1 0+(404461693/1250000000 : ℝ)*X 1 1+(-2942094251/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1030621383/2500000000 : ℝ)*X 2 0+(-440097917/1000000000 : ℝ)*X 2 1+(160065783/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3880581983/10000000000 : ℝ)*X 0 0+(-2048999621/5000000000 : ℝ)*X 0 1+(-4542120237/10000000000 : ℝ)*X 0 2+(3880581983/10000000000 : ℝ)*X 1 0+(-2048999621/5000000000 : ℝ)*X 1 1+(-4542120237/10000000000 : ℝ)*X 1 2+(3880581983/10000000000 : ℝ)*X 2 0+(-2048999621/5000000000 : ℝ)*X 2 1+(-4542120237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317068_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-194793/25000 : ℝ) < ((-89931/50000 : ℝ)*P 0+(-89931/50000 : ℝ)*P 1+(-89931/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-194793/25000 : ℝ) < (-5400933089567795373098190766453899/702185643250000000000000000000000 : ℝ) := by norm_num
    linear_combination (2103/1000000000000 : ℝ)*(base3) + (493/200000000000 : ℝ)*(base21) + (417/1000000000000 : ℝ)*(base25) + (169989261343/200000000000 : ℝ)*(base39) + (65039949673/250000000000 : ℝ)*(base40) + (167795370293/500000000000 : ℝ)*(base49) + (20508140131/125000000000 : ℝ)*(base60) + (112413750029/62500000000 : ℝ)*(major_s1_0) + (89931/50000 : ℝ)*(major_s1_1) + (89931/50000 : ℝ)*(major_s1_2) + (512773522553/200000000000 : ℝ)*(sp_s1_0) + (640966903833/250000000000 : ℝ)*(sp_s1_1) + (2563867610347/1000000000000 : ℝ)*(sp_s1_2) + (999999997897/1000000000000 : ℝ)*(sp_s1_6) + (512773522553/200000000000 : ℝ)*(f.sum) + (130677251049111099/289561090000000000000000000000 : ℝ)*base62 + (1489517033023/6370000000000000000000000 : ℝ)*base65 + (11318272667861/56821250000000000000000000 : ℝ)*base67 + (1977236896793/6370000000000000000000000 : ℝ)*base69 + (1194750289611/7723625000000000000000000000 : ℝ)*base71 + (12142119757517/48500000000000000000000000 : ℝ)*base73 + (28870193362047/90914000000000000000000000 : ℝ)*base74 + (80444138589/6062500000000000000000000 : ℝ)*base77 + (27704732923147381/2204664500000000000000000000000 : ℝ)*base78 + (29/62500000000 : ℝ)*base83 + (29/62500000000 : ℝ)*base85 + (29/62500000000 : ℝ)*base86 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c317069_s0_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-411293163/2000000000 : ℝ)*x 0 + (-22192997/31250000 : ℝ)*x 1 + (2926541221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411293163/2000000000 : ℝ)^39 ≤ (13672959437107/100000000000000 : ℝ)^31 := by
    have hnat : (411293163 : ℕ)^39*100000000000000^31 ≤ 13672959437107^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411293163 2000000000 13672959437107 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22192997/31250000 : ℝ)^39 ≤ (65014279521951/100000000000000 : ℝ)^31 := by
    have hnat : (22192997 : ℕ)^39*100000000000000^31 ≤ 65014279521951^31*31250000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22192997 31250000 65014279521951 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2926541221/10000000000 : ℝ)^39 ≤ (21312761031929/100000000000000 : ℝ)^31 := by
    have hnat : (2926541221 : ℕ)^39*100000000000000^31 ≤ 21312761031929^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2926541221 10000000000 21312761031929 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411293163/2000000000 : ℝ), (-22192997/31250000 : ℝ), (2926541221/10000000000 : ℝ)] ![(13672959437107/100000000000000 : ℝ), (65014279521951/100000000000000 : ℝ), (21312761031929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411293163/2000000000 : ℝ)|^39 ≤ (13672959437107/100000000000000 : ℝ)^31
        have hw : |(-411293163/2000000000 : ℝ)|=(411293163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-22192997/31250000 : ℝ)|^39 ≤ (65014279521951/100000000000000 : ℝ)^31
        have hw : |(-22192997/31250000 : ℝ)|=(22192997/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2926541221/10000000000 : ℝ)|^39 ≤ (21312761031929/100000000000000 : ℝ)^31
        have hw : |(2926541221/10000000000 : ℝ)|=(2926541221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317069_s0_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5786885957/10000000000 : ℝ)*x 0 + (645882703/2500000000 : ℝ)*x 1 + (1997672267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5786885957/10000000000 : ℝ)^39 ≤ (50250500060901/100000000000000 : ℝ)^31 := by
    have hnat : (5786885957 : ℕ)^39*100000000000000^31 ≤ 50250500060901^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5786885957 10000000000 50250500060901 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (645882703/2500000000 : ℝ)^39 ≤ (18219096840623/100000000000000 : ℝ)^31 := by
    have hnat : (645882703 : ℕ)^39*100000000000000^31 ≤ 18219096840623^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645882703 2500000000 18219096840623 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1997672267/5000000000 : ℝ)^39 ≤ (31530403092113/100000000000000 : ℝ)^31 := by
    have hnat : (1997672267 : ℕ)^39*100000000000000^31 ≤ 31530403092113^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997672267 5000000000 31530403092113 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5786885957/10000000000 : ℝ), (645882703/2500000000 : ℝ), (1997672267/5000000000 : ℝ)] ![(50250500060901/100000000000000 : ℝ), (18219096840623/100000000000000 : ℝ), (31530403092113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5786885957/10000000000 : ℝ)|^39 ≤ (50250500060901/100000000000000 : ℝ)^31
        have hw : |(5786885957/10000000000 : ℝ)|=(5786885957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(645882703/2500000000 : ℝ)|^39 ≤ (18219096840623/100000000000000 : ℝ)^31
        have hw : |(645882703/2500000000 : ℝ)|=(645882703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1997672267/5000000000 : ℝ)|^39 ≤ (31530403092113/100000000000000 : ℝ)^31
        have hw : |(1997672267/5000000000 : ℝ)|=(1997672267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317069_s0_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3813082519/10000000000 : ℝ)*x 0 + (-3208151257/10000000000 : ℝ)*x 1 + (-5426369399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3813082519/10000000000 : ℝ)^39 ≤ (29731611557999/100000000000000 : ℝ)^31 := by
    have hnat : (3813082519 : ℕ)^39*100000000000000^31 ≤ 29731611557999^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3813082519 10000000000 29731611557999 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3208151257/10000000000 : ℝ)^39 ≤ (23924161710269/100000000000000 : ℝ)^31 := by
    have hnat : (3208151257 : ℕ)^39*100000000000000^31 ≤ 23924161710269^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3208151257 10000000000 23924161710269 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426369399/10000000000 : ℝ)^39 ≤ (11586056679583/25000000000000 : ℝ)^31 := by
    have hnat : (5426369399 : ℕ)^39*25000000000000^31 ≤ 11586056679583^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426369399 10000000000 11586056679583 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3813082519/10000000000 : ℝ), (-3208151257/10000000000 : ℝ), (-5426369399/10000000000 : ℝ)] ![(29731611557999/100000000000000 : ℝ), (23924161710269/100000000000000 : ℝ), (11586056679583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3813082519/10000000000 : ℝ)|^39 ≤ (29731611557999/100000000000000 : ℝ)^31
        have hw : |(3813082519/10000000000 : ℝ)|=(3813082519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3208151257/10000000000 : ℝ)|^39 ≤ (23924161710269/100000000000000 : ℝ)^31
        have hw : |(-3208151257/10000000000 : ℝ)|=(3208151257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5426369399/10000000000 : ℝ)|^39 ≤ (11586056679583/25000000000000 : ℝ)^31
        have hw : |(-5426369399/10000000000 : ℝ)|=(5426369399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317069_s0_6 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5786885957/10000000000 : ℝ)*x 0 + (-645882703/2500000000 : ℝ)*x 1 + (1997672267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5786885957/10000000000 : ℝ)^39 ≤ (50250500060901/100000000000000 : ℝ)^31 := by
    have hnat : (5786885957 : ℕ)^39*100000000000000^31 ≤ 50250500060901^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5786885957 10000000000 50250500060901 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (645882703/2500000000 : ℝ)^39 ≤ (18219096840623/100000000000000 : ℝ)^31 := by
    have hnat : (645882703 : ℕ)^39*100000000000000^31 ≤ 18219096840623^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645882703 2500000000 18219096840623 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1997672267/5000000000 : ℝ)^39 ≤ (31530403092113/100000000000000 : ℝ)^31 := by
    have hnat : (1997672267 : ℕ)^39*100000000000000^31 ≤ 31530403092113^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997672267 5000000000 31530403092113 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5786885957/10000000000 : ℝ), (-645882703/2500000000 : ℝ), (1997672267/5000000000 : ℝ)] ![(50250500060901/100000000000000 : ℝ), (18219096840623/100000000000000 : ℝ), (31530403092113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5786885957/10000000000 : ℝ)|^39 ≤ (50250500060901/100000000000000 : ℝ)^31
        have hw : |(5786885957/10000000000 : ℝ)|=(5786885957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-645882703/2500000000 : ℝ)|^39 ≤ (18219096840623/100000000000000 : ℝ)^31
        have hw : |(-645882703/2500000000 : ℝ)|=(645882703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1997672267/5000000000 : ℝ)|^39 ≤ (31530403092113/100000000000000 : ℝ)^31
        have hw : |(1997672267/5000000000 : ℝ)|=(1997672267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317069 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]]) : False := by
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
  have main1 : (19897/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19897/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-411293163/2000000000 : ℝ)*X 0 0+(-22192997/31250000 : ℝ)*X 0 1+(2926541221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317069_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5786885957/10000000000 : ℝ)*X 1 0+(645882703/2500000000 : ℝ)*X 1 1+(1997672267/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317069_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3813082519/10000000000 : ℝ)*X 2 0+(-3208151257/10000000000 : ℝ)*X 2 1+(-5426369399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317069_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((5786885957/10000000000 : ℝ)*X 0 0+(-645882703/2500000000 : ℝ)*X 0 1+(1997672267/5000000000 : ℝ)*X 0 2+(5786885957/10000000000 : ℝ)*X 1 0+(-645882703/2500000000 : ℝ)*X 1 1+(1997672267/5000000000 : ℝ)*X 1 2+(5786885957/10000000000 : ℝ)*X 2 0+(-645882703/2500000000 : ℝ)*X 2 1+(1997672267/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317069_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-194793/25000 : ℝ) < ((-89931/50000 : ℝ)*P 0+(-89931/50000 : ℝ)*P 1+(-89931/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-194793/25000 : ℝ) < (-77688032759438791656771/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (11029/200000000000 : ℝ)*(base1) + (449798324353/1000000000000 : ℝ)*(base3) + (1477/40000000000 : ℝ)*(base22) + (3037/20000000000 : ℝ)*(base24) + (5063/200000000000 : ℝ)*(base39) + (8547646199/15625000000 : ℝ)*(base40) + (106560830829/125000000000 : ℝ)*(base49) + (108459372573/200000000000 : ℝ)*(base50) + (89931/50000 : ℝ)*(major_s0_0) + (89931/50000 : ℝ)*(major_s0_1) + (89931/50000 : ℝ)*(major_s0_2) + (1294800573561/500000000000 : ℝ)*(sp_s0_0) + (3039399416329/1000000000000 : ℝ)*(sp_s0_1) + (1294800451601/500000000000 : ℝ)*(sp_s0_2) + (275100810251/500000000000 : ℝ)*(sp_s0_6) + (2589601091977/1000000000000 : ℝ)*(f.sum) + (657553723/1250000000000000000000 : ℝ)*base62 + (237927389/2500000000000000000000 : ℝ)*base64 + (451232171/1000000000000000000000 : ℝ)*base67 + (3507443993/10000000000000000000000 : ℝ)*base69 + (922126169/2500000000000000000000 : ℝ)*base71 + (2617715847/5000000000000000000000 : ℝ)*base72 + (757189539/1250000000000000000000 : ℝ)*base74 + (729670601/5000000000000000000000 : ℝ)*base76 + (225785333/1000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p017_b029 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=68 ∨ c=69 := by omega
  rcases hc with rfl|rfl
  · exact collision_c317068 p hpa (by linarith only [hpb]) X hX
  · exact collision_c317069 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017_b029 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p008_b032
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:27:00.51567+00:00
-- url     : https://prove2.me/submissions/76540fd4-e529-43e9-b190-b5c3179f597d

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
theorem collision_support_c308069_s0_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1015886647/5000000000 : ℝ)*x 0 + (-370797953/500000000 : ℝ)*x 1 + (44831159/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1015886647/5000000000 : ℝ)^69 ≤ (12558331015007/100000000000000 : ℝ)^53 := by
    have hnat : (1015886647 : ℕ)^69*100000000000000^53 ≤ 12558331015007^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015886647 5000000000 12558331015007 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (370797953/500000000 : ℝ)^69 ≤ (8469983540641/12500000000000 : ℝ)^53 := by
    have hnat : (370797953 : ℕ)^69*12500000000000^53 ≤ 8469983540641^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370797953 500000000 8469983540641 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44831159/156250000 : ℝ)^69 ≤ (3936360127029/20000000000000 : ℝ)^53 := by
    have hnat : (44831159 : ℕ)^69*20000000000000^53 ≤ 3936360127029^53*156250000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44831159 156250000 3936360127029 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1015886647/5000000000 : ℝ), (-370797953/500000000 : ℝ), (44831159/156250000 : ℝ)] ![(12558331015007/100000000000000 : ℝ), (8469983540641/12500000000000 : ℝ), (3936360127029/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1015886647/5000000000 : ℝ)|^69 ≤ (12558331015007/100000000000000 : ℝ)^53
        have hw : |(-1015886647/5000000000 : ℝ)|=(1015886647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-370797953/500000000 : ℝ)|^69 ≤ (8469983540641/12500000000000 : ℝ)^53
        have hw : |(-370797953/500000000 : ℝ)|=(370797953/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(44831159/156250000 : ℝ)|^69 ≤ (3936360127029/20000000000000 : ℝ)^53
        have hw : |(44831159/156250000 : ℝ)|=(44831159/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s0_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1171682523/2000000000 : ℝ)*x 0 + (2692709529/10000000000 : ℝ)*x 1 + (4170537423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1171682523/2000000000 : ℝ)^69 ≤ (24925610056121/50000000000000 : ℝ)^53 := by
    have hnat : (1171682523 : ℕ)^69*50000000000000^53 ≤ 24925610056121^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171682523 2000000000 24925610056121 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692709529/10000000000 : ℝ)^69 ≤ (4530136142907/25000000000000 : ℝ)^53 := by
    have hnat : (2692709529 : ℕ)^69*25000000000000^53 ≤ 4530136142907^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692709529 10000000000 4530136142907 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170537423/10000000000 : ℝ)^69 ≤ (4003529412869/12500000000000 : ℝ)^53 := by
    have hnat : (4170537423 : ℕ)^69*12500000000000^53 ≤ 4003529412869^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170537423 10000000000 4003529412869 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1171682523/2000000000 : ℝ), (2692709529/10000000000 : ℝ), (4170537423/10000000000 : ℝ)] ![(24925610056121/50000000000000 : ℝ), (4530136142907/25000000000000 : ℝ), (4003529412869/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1171682523/2000000000 : ℝ)|^69 ≤ (24925610056121/50000000000000 : ℝ)^53
        have hw : |(1171682523/2000000000 : ℝ)|=(1171682523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692709529/10000000000 : ℝ)|^69 ≤ (4530136142907/25000000000000 : ℝ)^53
        have hw : |(2692709529/10000000000 : ℝ)|=(2692709529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170537423/10000000000 : ℝ)|^69 ≤ (4003529412869/12500000000000 : ℝ)^53
        have hw : |(4170537423/10000000000 : ℝ)|=(4170537423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s0_4 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (-1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^69 ≤ (0 : ℝ)^53 := by
    have hnat : (0 : ℕ)^69*1^53 ≤ 0^53*1^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^69 ≤ (1 : ℝ)^53 := by
    have hnat : (1 : ℕ)^69*1^53 ≤ 1^53*1^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^69 ≤ (0 : ℝ)^53 := by
    have hnat : (0 : ℕ)^69*1^53 ≤ 0^53*1^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^69 ≤ (0 : ℝ)^53
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1 : ℝ)|^69 ≤ (1 : ℝ)^53
        have hw : |(-1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^69 ≤ (0 : ℝ)^53
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s0_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-307376519/2000000000 : ℝ)*x 0 + (-8208016603/10000000000 : ℝ)*x 1 + (1100587901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (307376519/2000000000 : ℝ)^69 ≤ (2182922254543/25000000000000 : ℝ)^53 := by
    have hnat : (307376519 : ℕ)^69*25000000000000^53 ≤ 2182922254543^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307376519 2000000000 2182922254543 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8208016603/10000000000 : ℝ)^69 ≤ (773299767241/1000000000000 : ℝ)^53 := by
    have hnat : (8208016603 : ℕ)^69*1000000000000^53 ≤ 773299767241^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8208016603 10000000000 773299767241 1000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100587901/5000000000 : ℝ)^69 ≤ (13938334242837/100000000000000 : ℝ)^53 := by
    have hnat : (1100587901 : ℕ)^69*100000000000000^53 ≤ 13938334242837^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100587901 5000000000 13938334242837 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-307376519/2000000000 : ℝ), (-8208016603/10000000000 : ℝ), (1100587901/5000000000 : ℝ)] ![(2182922254543/25000000000000 : ℝ), (773299767241/1000000000000 : ℝ), (13938334242837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-307376519/2000000000 : ℝ)|^69 ≤ (2182922254543/25000000000000 : ℝ)^53
        have hw : |(-307376519/2000000000 : ℝ)|=(307376519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8208016603/10000000000 : ℝ)|^69 ≤ (773299767241/1000000000000 : ℝ)^53
        have hw : |(-8208016603/10000000000 : ℝ)|=(8208016603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1100587901/5000000000 : ℝ)|^69 ≤ (13938334242837/100000000000000 : ℝ)^53
        have hw : |(1100587901/5000000000 : ℝ)|=(1100587901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s0_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1128822431/2000000000 : ℝ)*x 0 + (2635867653/10000000000 : ℝ)*x 1 + (278341569/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1128822431/2000000000 : ℝ)^69 ≤ (23745189644177/50000000000000 : ℝ)^53 := by
    have hnat : (1128822431 : ℕ)^69*50000000000000^53 ≤ 23745189644177^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128822431 2000000000 23745189644177 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2635867653/10000000000 : ℝ)^69 ≤ (3524829214741/20000000000000 : ℝ)^53 := by
    have hnat : (2635867653 : ℕ)^69*20000000000000^53 ≤ 3524829214741^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635867653 10000000000 3524829214741 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (278341569/625000000 : ℝ)^69 ≤ (8721368653663/25000000000000 : ℝ)^53 := by
    have hnat : (278341569 : ℕ)^69*25000000000000^53 ≤ 8721368653663^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278341569 625000000 8721368653663 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1128822431/2000000000 : ℝ), (2635867653/10000000000 : ℝ), (278341569/625000000 : ℝ)] ![(23745189644177/50000000000000 : ℝ), (3524829214741/20000000000000 : ℝ), (8721368653663/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1128822431/2000000000 : ℝ)|^69 ≤ (23745189644177/50000000000000 : ℝ)^53
        have hw : |(1128822431/2000000000 : ℝ)|=(1128822431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2635867653/10000000000 : ℝ)|^69 ≤ (3524829214741/20000000000000 : ℝ)^53
        have hw : |(2635867653/10000000000 : ℝ)|=(2635867653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(278341569/625000000 : ℝ)|^69 ≤ (8721368653663/25000000000000 : ℝ)^53
        have hw : |(278341569/625000000 : ℝ)|=(278341569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s0_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (830062179/2000000000 : ℝ)*x 0 + (-1303309329/5000000000 : ℝ)*x 1 + (-5944217171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (830062179/2000000000 : ℝ)^69 ≤ (1591307909103/5000000000000 : ℝ)^53 := by
    have hnat : (830062179 : ℕ)^69*5000000000000^53 ≤ 1591307909103^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830062179 2000000000 1591307909103 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303309329/5000000000 : ℝ)^69 ≤ (17369967621161/100000000000000 : ℝ)^53 := by
    have hnat : (1303309329 : ℕ)^69*100000000000000^53 ≤ 17369967621161^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303309329 5000000000 17369967621161 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5944217171/10000000000 : ℝ)^69 ≤ (25401937091861/50000000000000 : ℝ)^53 := by
    have hnat : (5944217171 : ℕ)^69*50000000000000^53 ≤ 25401937091861^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5944217171 10000000000 25401937091861 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(830062179/2000000000 : ℝ), (-1303309329/5000000000 : ℝ), (-5944217171/10000000000 : ℝ)] ![(1591307909103/5000000000000 : ℝ), (17369967621161/100000000000000 : ℝ), (25401937091861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(830062179/2000000000 : ℝ)|^69 ≤ (1591307909103/5000000000000 : ℝ)^53
        have hw : |(830062179/2000000000 : ℝ)|=(830062179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1303309329/5000000000 : ℝ)|^69 ≤ (17369967621161/100000000000000 : ℝ)^53
        have hw : |(-1303309329/5000000000 : ℝ)|=(1303309329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5944217171/10000000000 : ℝ)|^69 ≤ (25401937091861/50000000000000 : ℝ)^53
        have hw : |(-5944217171/10000000000 : ℝ)|=(5944217171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s0_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2370008901/10000000000 : ℝ)*x 0 + (-7374009821/10000000000 : ℝ)*x 1 + (2609239159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2370008901/10000000000 : ℝ)^69 ≤ (15346002096159/100000000000000 : ℝ)^53 := by
    have hnat : (2370008901 : ℕ)^69*100000000000000^53 ≤ 15346002096159^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2370008901 10000000000 15346002096159 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7374009821/10000000000 : ℝ)^69 ≤ (67261292661133/100000000000000 : ℝ)^53 := by
    have hnat : (7374009821 : ℕ)^69*100000000000000^53 ≤ 67261292661133^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7374009821 10000000000 67261292661133 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609239159/10000000000 : ℝ)^69 ≤ (271761019343/1562500000000 : ℝ)^53 := by
    have hnat : (2609239159 : ℕ)^69*1562500000000^53 ≤ 271761019343^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609239159 10000000000 271761019343 1562500000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2370008901/10000000000 : ℝ), (-7374009821/10000000000 : ℝ), (2609239159/10000000000 : ℝ)] ![(15346002096159/100000000000000 : ℝ), (67261292661133/100000000000000 : ℝ), (271761019343/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2370008901/10000000000 : ℝ)|^69 ≤ (15346002096159/100000000000000 : ℝ)^53
        have hw : |(-2370008901/10000000000 : ℝ)|=(2370008901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7374009821/10000000000 : ℝ)|^69 ≤ (67261292661133/100000000000000 : ℝ)^53
        have hw : |(-7374009821/10000000000 : ℝ)|=(7374009821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609239159/10000000000 : ℝ)|^69 ≤ (271761019343/1562500000000 : ℝ)^53
        have hw : |(2609239159/10000000000 : ℝ)|=(2609239159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s0_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1177146689/2000000000 : ℝ)*x 0 + (2474551521/10000000000 : ℝ)*x 1 + (4328135549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1177146689/2000000000 : ℝ)^69 ≤ (10030819690879/20000000000000 : ℝ)^53 := by
    have hnat : (1177146689 : ℕ)^69*20000000000000^53 ≤ 10030819690879^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177146689 2000000000 10030819690879 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2474551521/10000000000 : ℝ)^69 ≤ (4058271638489/25000000000000 : ℝ)^53 := by
    have hnat : (2474551521 : ℕ)^69*25000000000000^53 ≤ 4058271638489^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2474551521 10000000000 4058271638489 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4328135549/10000000000 : ℝ)^69 ≤ (33612814973319/100000000000000 : ℝ)^53 := by
    have hnat : (4328135549 : ℕ)^69*100000000000000^53 ≤ 33612814973319^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328135549 10000000000 33612814973319 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1177146689/2000000000 : ℝ), (2474551521/10000000000 : ℝ), (4328135549/10000000000 : ℝ)] ![(10030819690879/20000000000000 : ℝ), (4058271638489/25000000000000 : ℝ), (33612814973319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1177146689/2000000000 : ℝ)|^69 ≤ (10030819690879/20000000000000 : ℝ)^53
        have hw : |(1177146689/2000000000 : ℝ)|=(1177146689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2474551521/10000000000 : ℝ)|^69 ≤ (4058271638489/25000000000000 : ℝ)^53
        have hw : |(2474551521/10000000000 : ℝ)|=(2474551521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4328135549/10000000000 : ℝ)|^69 ≤ (33612814973319/100000000000000 : ℝ)^53
        have hw : |(4328135549/10000000000 : ℝ)|=(4328135549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s0_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3672018797/10000000000 : ℝ)*x 0 + (-1566556457/5000000000 : ℝ)*x 1 + (-2971602427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3672018797/10000000000 : ℝ)^69 ≤ (13568299910513/50000000000000 : ℝ)^53 := by
    have hnat : (3672018797 : ℕ)^69*50000000000000^53 ≤ 13568299910513^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3672018797 10000000000 13568299910513 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1566556457/5000000000 : ℝ)^69 ≤ (22070789671499/100000000000000 : ℝ)^53 := by
    have hnat : (1566556457 : ℕ)^69*100000000000000^53 ≤ 22070789671499^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1566556457 5000000000 22070789671499 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2971602427/5000000000 : ℝ)^69 ≤ (25396305246067/50000000000000 : ℝ)^53 := by
    have hnat : (2971602427 : ℕ)^69*50000000000000^53 ≤ 25396305246067^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2971602427 5000000000 25396305246067 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3672018797/10000000000 : ℝ), (-1566556457/5000000000 : ℝ), (-2971602427/5000000000 : ℝ)] ![(13568299910513/50000000000000 : ℝ), (22070789671499/100000000000000 : ℝ), (25396305246067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3672018797/10000000000 : ℝ)|^69 ≤ (13568299910513/50000000000000 : ℝ)^53
        have hw : |(3672018797/10000000000 : ℝ)|=(3672018797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1566556457/5000000000 : ℝ)|^69 ≤ (22070789671499/100000000000000 : ℝ)^53
        have hw : |(-1566556457/5000000000 : ℝ)|=(1566556457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2971602427/5000000000 : ℝ)|^69 ≤ (25396305246067/50000000000000 : ℝ)^53
        have hw : |(-2971602427/5000000000 : ℝ)|=(2971602427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s0_19 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1177146689/2000000000 : ℝ)*x 0 + (-3782369767/10000000000 : ℝ)*x 1 + (3086341837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1177146689/2000000000 : ℝ)^69 ≤ (10030819690879/20000000000000 : ℝ)^53 := by
    have hnat : (1177146689 : ℕ)^69*20000000000000^53 ≤ 10030819690879^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177146689 2000000000 10030819690879 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3782369767/10000000000 : ℝ)^69 ≤ (14101538945201/50000000000000 : ℝ)^53 := by
    have hnat : (3782369767 : ℕ)^69*50000000000000^53 ≤ 14101538945201^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3782369767 10000000000 14101538945201 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3086341837/10000000000 : ℝ)^69 ≤ (21642823643201/100000000000000 : ℝ)^53 := by
    have hnat : (3086341837 : ℕ)^69*100000000000000^53 ≤ 21642823643201^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3086341837 10000000000 21642823643201 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1177146689/2000000000 : ℝ), (-3782369767/10000000000 : ℝ), (3086341837/10000000000 : ℝ)] ![(10030819690879/20000000000000 : ℝ), (14101538945201/50000000000000 : ℝ), (21642823643201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1177146689/2000000000 : ℝ)|^69 ≤ (10030819690879/20000000000000 : ℝ)^53
        have hw : |(1177146689/2000000000 : ℝ)|=(1177146689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3782369767/10000000000 : ℝ)|^69 ≤ (14101538945201/50000000000000 : ℝ)^53
        have hw : |(-3782369767/10000000000 : ℝ)|=(3782369767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3086341837/10000000000 : ℝ)|^69 ≤ (21642823643201/100000000000000 : ℝ)^53
        have hw : |(3086341837/10000000000 : ℝ)|=(3086341837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s0_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-315510399/2500000000 : ℝ)*x 0 + (-1026002073/1250000000 : ℝ)*x 1 + (1218544009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (315510399/2500000000 : ℝ)^69 ≤ (6756156211953/100000000000000 : ℝ)^53 := by
    have hnat : (315510399 : ℕ)^69*100000000000000^53 ≤ 6756156211953^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315510399 2500000000 6756156211953 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026002073/1250000000 : ℝ)^69 ≤ (77329976491057/100000000000000 : ℝ)^53 := by
    have hnat : (1026002073 : ℕ)^69*100000000000000^53 ≤ 77329976491057^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026002073 1250000000 77329976491057 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1218544009/5000000000 : ℝ)^69 ≤ (7956933645079/50000000000000 : ℝ)^53 := by
    have hnat : (1218544009 : ℕ)^69*50000000000000^53 ≤ 7956933645079^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1218544009 5000000000 7956933645079 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-315510399/2500000000 : ℝ), (-1026002073/1250000000 : ℝ), (1218544009/5000000000 : ℝ)] ![(6756156211953/100000000000000 : ℝ), (77329976491057/100000000000000 : ℝ), (7956933645079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-315510399/2500000000 : ℝ)|^69 ≤ (6756156211953/100000000000000 : ℝ)^53
        have hw : |(-315510399/2500000000 : ℝ)|=(315510399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1026002073/1250000000 : ℝ)|^69 ≤ (77329976491057/100000000000000 : ℝ)^53
        have hw : |(-1026002073/1250000000 : ℝ)|=(1026002073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1218544009/5000000000 : ℝ)|^69 ≤ (7956933645079/50000000000000 : ℝ)^53
        have hw : |(1218544009/5000000000 : ℝ)|=(1218544009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s0_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3481543287/5000000000 : ℝ)*x 0 + (1069778893/5000000000 : ℝ)*x 1 + (3356837339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3481543287/5000000000 : ℝ)^69 ≤ (7802894697383/12500000000000 : ℝ)^53 := by
    have hnat : (3481543287 : ℕ)^69*12500000000000^53 ≤ 7802894697383^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3481543287 5000000000 7802894697383 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1069778893/5000000000 : ℝ)^69 ≤ (6716262958187/50000000000000 : ℝ)^53 := by
    have hnat : (1069778893 : ℕ)^69*50000000000000^53 ≤ 6716262958187^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069778893 5000000000 6716262958187 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3356837339/10000000000 : ℝ)^69 ≤ (12072158246583/50000000000000 : ℝ)^53 := by
    have hnat : (3356837339 : ℕ)^69*50000000000000^53 ≤ 12072158246583^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3356837339 10000000000 12072158246583 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3481543287/5000000000 : ℝ), (1069778893/5000000000 : ℝ), (3356837339/10000000000 : ℝ)] ![(7802894697383/12500000000000 : ℝ), (6716262958187/50000000000000 : ℝ), (12072158246583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3481543287/5000000000 : ℝ)|^69 ≤ (7802894697383/12500000000000 : ℝ)^53
        have hw : |(3481543287/5000000000 : ℝ)|=(3481543287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1069778893/5000000000 : ℝ)|^69 ≤ (6716262958187/50000000000000 : ℝ)^53
        have hw : |(1069778893/5000000000 : ℝ)|=(1069778893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3356837339/10000000000 : ℝ)|^69 ≤ (12072158246583/50000000000000 : ℝ)^53
        have hw : |(3356837339/10000000000 : ℝ)|=(3356837339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s0_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (399729193/1250000000 : ℝ)*x 0 + (-3335477117/10000000000 : ℝ)*x 1 + (-6175233713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399729193/1250000000 : ℝ)^69 ≤ (22666182210181/100000000000000 : ℝ)^53 := by
    have hnat : (399729193 : ℕ)^69*100000000000000^53 ≤ 22666182210181^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399729193 1250000000 22666182210181 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3335477117/10000000000 : ℝ)^69 ≤ (23944493413277/100000000000000 : ℝ)^53 := by
    have hnat : (3335477117 : ℕ)^69*100000000000000^53 ≤ 23944493413277^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3335477117 10000000000 23944493413277 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6175233713/10000000000 : ℝ)^69 ≤ (26694662185257/50000000000000 : ℝ)^53 := by
    have hnat : (6175233713 : ℕ)^69*50000000000000^53 ≤ 26694662185257^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6175233713 10000000000 26694662185257 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(399729193/1250000000 : ℝ), (-3335477117/10000000000 : ℝ), (-6175233713/10000000000 : ℝ)] ![(22666182210181/100000000000000 : ℝ), (23944493413277/100000000000000 : ℝ), (26694662185257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(399729193/1250000000 : ℝ)|^69 ≤ (22666182210181/100000000000000 : ℝ)^53
        have hw : |(399729193/1250000000 : ℝ)|=(399729193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3335477117/10000000000 : ℝ)|^69 ≤ (23944493413277/100000000000000 : ℝ)^53
        have hw : |(-3335477117/10000000000 : ℝ)|=(3335477117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6175233713/10000000000 : ℝ)|^69 ≤ (26694662185257/50000000000000 : ℝ)^53
        have hw : |(-6175233713/10000000000 : ℝ)|=(6175233713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1665046441/5000000000 : ℝ)*x 0 + (-684911669/1250000000 : ℝ)*x 1 + (4008006211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1665046441/5000000000 : ℝ)^69 ≤ (1194709259129/5000000000000 : ℝ)^53 := by
    have hnat : (1665046441 : ℕ)^69*5000000000000^53 ≤ 1194709259129^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665046441 5000000000 1194709259129 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684911669/1250000000 : ℝ)^69 ≤ (45692923488543/100000000000000 : ℝ)^53 := by
    have hnat : (684911669 : ℕ)^69*100000000000000^53 ≤ 45692923488543^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684911669 1250000000 45692923488543 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4008006211/10000000000 : ℝ)^69 ≤ (3041289131257/10000000000000 : ℝ)^53 := by
    have hnat : (4008006211 : ℕ)^69*10000000000000^53 ≤ 3041289131257^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008006211 10000000000 3041289131257 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1665046441/5000000000 : ℝ), (-684911669/1250000000 : ℝ), (4008006211/10000000000 : ℝ)] ![(1194709259129/5000000000000 : ℝ), (45692923488543/100000000000000 : ℝ), (3041289131257/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1665046441/5000000000 : ℝ)|^69 ≤ (1194709259129/5000000000000 : ℝ)^53
        have hw : |(-1665046441/5000000000 : ℝ)|=(1665046441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-684911669/1250000000 : ℝ)|^69 ≤ (45692923488543/100000000000000 : ℝ)^53
        have hw : |(-684911669/1250000000 : ℝ)|=(684911669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4008006211/10000000000 : ℝ)|^69 ≤ (3041289131257/10000000000000 : ℝ)^53
        have hw : |(4008006211/10000000000 : ℝ)|=(4008006211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (654259653/1250000000 : ℝ)*x 0 + (13369357/39062500 : ℝ)*x 1 + (418667093/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (654259653/1250000000 : ℝ)^69 ≤ (21524430905623/50000000000000 : ℝ)^53 := by
    have hnat : (654259653 : ℕ)^69*50000000000000^53 ≤ 21524430905623^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654259653 1250000000 21524430905623 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13369357/39062500 : ℝ)^69 ≤ (6190376390713/25000000000000 : ℝ)^53 := by
    have hnat : (13369357 : ℕ)^69*25000000000000^53 ≤ 6190376390713^53*39062500^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13369357 39062500 6190376390713 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418667093/1000000000 : ℝ)^69 ≤ (6437926521761/20000000000000 : ℝ)^53 := by
    have hnat : (418667093 : ℕ)^69*20000000000000^53 ≤ 6437926521761^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418667093 1000000000 6437926521761 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(654259653/1250000000 : ℝ), (13369357/39062500 : ℝ), (418667093/1000000000 : ℝ)] ![(21524430905623/50000000000000 : ℝ), (6190376390713/25000000000000 : ℝ), (6437926521761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(654259653/1250000000 : ℝ)|^69 ≤ (21524430905623/50000000000000 : ℝ)^53
        have hw : |(654259653/1250000000 : ℝ)|=(654259653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13369357/39062500 : ℝ)|^69 ≤ (6190376390713/25000000000000 : ℝ)^53
        have hw : |(13369357/39062500 : ℝ)|=(13369357/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(418667093/1000000000 : ℝ)|^69 ≤ (6437926521761/20000000000000 : ℝ)^53
        have hw : |(418667093/1000000000 : ℝ)|=(418667093/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4050347199/10000000000 : ℝ)*x 0 + (-1979259309/5000000000 : ℝ)*x 1 + (-2437442033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4050347199/10000000000 : ℝ)^69 ≤ (616636664429/2000000000000 : ℝ)^53 := by
    have hnat : (4050347199 : ℕ)^69*2000000000000^53 ≤ 616636664429^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4050347199 10000000000 616636664429 2000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1979259309/5000000000 : ℝ)^69 ≤ (14962464448403/50000000000000 : ℝ)^53 := by
    have hnat : (1979259309 : ℕ)^69*50000000000000^53 ≤ 14962464448403^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979259309 5000000000 14962464448403 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2437442033/5000000000 : ℝ)^69 ≤ (39243237861039/100000000000000 : ℝ)^53 := by
    have hnat : (2437442033 : ℕ)^69*100000000000000^53 ≤ 39243237861039^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2437442033 5000000000 39243237861039 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4050347199/10000000000 : ℝ), (-1979259309/5000000000 : ℝ), (-2437442033/5000000000 : ℝ)] ![(616636664429/2000000000000 : ℝ), (14962464448403/50000000000000 : ℝ), (39243237861039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4050347199/10000000000 : ℝ)|^69 ≤ (616636664429/2000000000000 : ℝ)^53
        have hw : |(4050347199/10000000000 : ℝ)|=(4050347199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1979259309/5000000000 : ℝ)|^69 ≤ (14962464448403/50000000000000 : ℝ)^53
        have hw : |(-1979259309/5000000000 : ℝ)|=(1979259309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2437442033/5000000000 : ℝ)|^69 ≤ (39243237861039/100000000000000 : ℝ)^53
        have hw : |(-2437442033/5000000000 : ℝ)|=(2437442033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308069_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (957381579/2000000000 : ℝ)*x 0 + (-2134681691/5000000000 : ℝ)*x 1 + (765797189/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (957381579/2000000000 : ℝ)^69 ≤ (38323743343263/100000000000000 : ℝ)^53 := by
    have hnat : (957381579 : ℕ)^69*100000000000000^53 ≤ 38323743343263^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957381579 2000000000 38323743343263 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2134681691/5000000000 : ℝ)^69 ≤ (16509907246323/50000000000000 : ℝ)^53 := by
    have hnat : (2134681691 : ℕ)^69*50000000000000^53 ≤ 16509907246323^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134681691 5000000000 16509907246323 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (765797189/2000000000 : ℝ)^69 ≤ (14328221075797/50000000000000 : ℝ)^53 := by
    have hnat : (765797189 : ℕ)^69*50000000000000^53 ≤ 14328221075797^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765797189 2000000000 14328221075797 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(957381579/2000000000 : ℝ), (-2134681691/5000000000 : ℝ), (765797189/2000000000 : ℝ)] ![(38323743343263/100000000000000 : ℝ), (16509907246323/50000000000000 : ℝ), (14328221075797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(957381579/2000000000 : ℝ)|^69 ≤ (38323743343263/100000000000000 : ℝ)^53
        have hw : |(957381579/2000000000 : ℝ)|=(957381579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2134681691/5000000000 : ℝ)|^69 ≤ (16509907246323/50000000000000 : ℝ)^53
        have hw : |(-2134681691/5000000000 : ℝ)|=(2134681691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(765797189/2000000000 : ℝ)|^69 ≤ (14328221075797/50000000000000 : ℝ)^53
        have hw : |(765797189/2000000000 : ℝ)|=(765797189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308069 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1015886647/5000000000 : ℝ)*X 0 0+(-370797953/500000000 : ℝ)*X 0 1+(44831159/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1171682523/2000000000 : ℝ)*X 1 0+(2692709529/10000000000 : ℝ)*X 1 1+(4170537423/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_4 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s0_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-307376519/2000000000 : ℝ)*X 0 0+(-8208016603/10000000000 : ℝ)*X 0 1+(1100587901/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1128822431/2000000000 : ℝ)*X 1 0+(2635867653/10000000000 : ℝ)*X 1 1+(278341569/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((830062179/2000000000 : ℝ)*X 2 0+(-1303309329/5000000000 : ℝ)*X 2 1+(-5944217171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-2370008901/10000000000 : ℝ)*X 0 0+(-7374009821/10000000000 : ℝ)*X 0 1+(2609239159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((1177146689/2000000000 : ℝ)*X 1 0+(2474551521/10000000000 : ℝ)*X 1 1+(4328135549/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3672018797/10000000000 : ℝ)*X 2 0+(-1566556457/5000000000 : ℝ)*X 2 1+(-2971602427/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((1177146689/2000000000 : ℝ)*X 0 0+(-3782369767/10000000000 : ℝ)*X 0 1+(3086341837/10000000000 : ℝ)*X 0 2+(1177146689/2000000000 : ℝ)*X 1 0+(-3782369767/10000000000 : ℝ)*X 1 1+(3086341837/10000000000 : ℝ)*X 1 2+(1177146689/2000000000 : ℝ)*X 2 0+(-3782369767/10000000000 : ℝ)*X 2 1+(3086341837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-315510399/2500000000 : ℝ)*X 0 0+(-1026002073/1250000000 : ℝ)*X 0 1+(1218544009/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((3481543287/5000000000 : ℝ)*X 1 0+(1069778893/5000000000 : ℝ)*X 1 1+(3356837339/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((399729193/1250000000 : ℝ)*X 2 0+(-3335477117/10000000000 : ℝ)*X 2 1+(-6175233713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((5019/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5019/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9563373553234510729311/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2650897021979/1000000000000 : ℝ)*(base3) + (943608630851/1000000000000 : ℝ)*(base40) + (197903257293/1000000000000 : ℝ)*(base50) + (1546451/250000000000 : ℝ)*(base60) + (2077123616057/500000000000 : ℝ)*(major_s0_0) + (765185602121/50000000000 : ℝ)*(major_s0_1) + (2077123616057/500000000000 : ℝ)*(major_s0_2) + (25219629/1000000000000 : ℝ)*(sp_s0_0) + (5574732405153/500000000000 : ℝ)*(sp_s0_4) + (5657365300271/1000000000000 : ℝ)*(sp_s0_7) + (8308489363757/1000000000000 : ℝ)*(sp_s0_8) + (2828712004061/500000000000 : ℝ)*(sp_s0_9) + (21041707/125000000000 : ℝ)*(sp_s0_15) + (100910939/500000000000 : ℝ)*(sp_s0_20) + (2650897021979/1000000000000 : ℝ)*(f.failure) + (2828796170889/500000000000 : ℝ)*(f.sum) + (2573673563333249/5000000000000000000000000000 : ℝ)*base63 + (113067435737609/625000000000000000000000000 : ℝ)*base65 + (110783101844417/500000000000000000000000000 : ℝ)*base66 + (1786609064615089/5000000000000000000000000000 : ℝ)*base69 + (2298399105015961/5000000000000000000000000000 : ℝ)*base71 + (32006362175109/625000000000000000000000000 : ℝ)*base72 + (18842707383977/62500000000000000000000000 : ℝ)*base75 + (1048279162115089/5000000000000000000000000000 : ℝ)*base77 + (904579541922521/2500000000000000000000000000 : ℝ)*base78 + (48931/100000000000000000 : ℝ)*base86 + (48931/100000000000000000 : ℝ)*base88 + (48931/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-2689/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-2689/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (69040637920519684994871/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1003919630473/1000000000000 : ℝ)*(base3) + (1704933/200000000000 : ℝ)*(base39) + (720825900451/1000000000000 : ℝ)*(base40) + (121490271371/200000000000 : ℝ)*(base49) + (2550853432853/1000000000000 : ℝ)*(major_s0_0) + (2550853432853/1000000000000 : ℝ)*(major_s0_1) + (2550853432853/1000000000000 : ℝ)*(major_s0_2) + (226042209/1000000000000 : ℝ)*(sp_s0_0) + (218306197/1000000000000 : ℝ)*(sp_s0_9) + (138949300751/40000000000 : ℝ)*(sp_s0_13) + (2238926464969/500000000000 : ℝ)*(sp_s0_14) + (1736870127393/500000000000 : ℝ)*(sp_s0_15) + (311912035767/500000000000 : ℝ)*(sp_s0_19) + (12630759/500000000000 : ℝ)*(sp_s0_21) + (203467962751/125000000000 : ℝ)*(f.failure) + (3473958560983/1000000000000 : ℝ)*(f.sum) + (1009126755151531/10000000000000000000000000000 : ℝ)*base62 + (847613374789561/1250000000000000000000000000 : ℝ)*base65 + (3314056515531981/10000000000000000000000000000 : ℝ)*base66 + (3334113176531981/10000000000000000000000000000 : ℝ)*base69 + (3595957114151531/10000000000000000000000000000 : ℝ)*base70 + (445937984085439/1250000000000000000000000000 : ℝ)*base73 + (413930222710439/1250000000000000000000000000 : ℝ)*base74 + (3805553843468019/10000000000000000000000000000 : ℝ)*base76 + (1765526819151531/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (9461/12500000000000000 : ℝ)*base87 + (9461/12500000000000000 : ℝ)*base89 + (9461/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36139/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36139/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9792502585720865451057/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2961506412361/1000000000000 : ℝ)*(base3) + (1991167/500000000000 : ℝ)*(base22) + (106917272397/62500000000 : ℝ)*(base40) + (19942429611/25000000000 : ℝ)*(base49) + (2320507626207/500000000000 : ℝ)*(major_s0_0) + (7731621487521/500000000000 : ℝ)*(major_s0_1) + (2320507626207/500000000000 : ℝ)*(major_s0_2) + (47047/1000000000000 : ℝ)*(sp_s0_1) + (2705556930657/250000000000 : ℝ)*(sp_s0_4) + (89121383/500000000000 : ℝ)*(sp_s0_7) + (5703837/1000000000000 : ℝ)*(sp_s0_19) + (6320337534521/1000000000000 : ℝ)*(sp_s0_20) + (9282022142601/1000000000000 : ℝ)*(sp_s0_21) + (3160255897477/500000000000 : ℝ)*(sp_s0_22) + (2961512116197/1000000000000 : ℝ)*(f.failure) + (790064472161/125000000000 : ℝ)*(f.sum) + (777095671277629/1000000000000000000000000000 : ℝ)*base62 + (185522843686841/625000000000000000000000000 : ℝ)*base64 + (413250751160217/5000000000000000000000000000 : ℝ)*base66 + (328903716738361/5000000000000000000000000000 : ℝ)*base68 + (982899999733089/5000000000000000000000000000 : ℝ)*base70 + (154259653186841/625000000000000000000000000 : ℝ)*base73 + (604552805331223/625000000000000000000000000 : ℝ)*base74 + (849739246238361/5000000000000000000000000000 : ℝ)*base76 + (2887501024834511/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (51933/100000000000000000 : ℝ)*base86 + (51933/100000000000000000 : ℝ)*base88 + (51933/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (5019/25000 : ℝ) ^ (17/4 : ℝ) ≤ (108737174745539933/100000000000000000000 : ℝ) := by
    have hpowers : (5019/25000 : ℝ)^17 ≤ (108737174745539933/100000000000000000000 : ℝ)^4 := by
      have hnat : (5019 : ℕ)^17*100000000000000000000^4 ≤ 108737174745539933^4*25000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5019 25000 108737174745539933 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5019/25000 : ℝ)) (X := (108737174745539933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100108737174745539933/100000000000000000000 : ℝ) ≤ (625159841169259/625000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100108737174745539933/100000000000000000000 : ℝ)^4 ≤ (625159841169259/625000000000000 : ℝ)^17 := by
      have hnat : (100108737174745539933 : ℕ)^4*625000000000000^17 ≤ 625159841169259^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100108737174745539933 100000000000000000000 625159841169259 625000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625159841169259/625000000000000 : ℝ)) (X := (100108737174745539933/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50108737174745539933/50000000000000000000 : ℝ) ≤ (10005112794030591/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50108737174745539933/50000000000000000000 : ℝ)^4 ≤ (10005112794030591/10000000000000000 : ℝ)^17 := by
      have hnat : (50108737174745539933 : ℕ)^4*10000000000000000^17 ≤ 10005112794030591^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50108737174745539933 50000000000000000000 10005112794030591 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005112794030591/10000000000000000 : ℝ)) (X := (50108737174745539933/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(53280389753/41825000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2555335322447/2007600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (5019/25000 : ℝ)) (alpha := (53280389753/41825000000000 : ℝ)) (beta := (2555335322447/2007600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5019/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(53280389753/41825000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2555335322447/2007600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (2689/50000 : ℝ) ^ (17/4 : ℝ) ≤ (402845383417071/100000000000000000000 : ℝ) := by
    have hpowers : (2689/50000 : ℝ)^17 ≤ (402845383417071/100000000000000000000 : ℝ)^4 := by
      have hnat : (2689 : ℕ)^17*100000000000000000000^4 ≤ 402845383417071^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2689 50000 402845383417071 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2689/50000 : ℝ)) (X := (402845383417071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100000402845383417071/100000000000000000000 : ℝ) ≤ (625000592418769/625000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100000402845383417071/100000000000000000000 : ℝ)^4 ≤ (625000592418769/625000000000000 : ℝ)^17 := by
      have hnat : (100000402845383417071 : ℕ)^4*625000000000000^17 ≤ 625000592418769^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100000402845383417071 100000000000000000000 625000592418769 625000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000592418769/625000000000000 : ℝ)) (X := (100000402845383417071/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50000402845383417071/50000000000000000000 : ℝ) ≤ (10000018957371409/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50000402845383417071/50000000000000000000 : ℝ)^4 ≤ (10000018957371409/10000000000000000 : ℝ)^17 := by
      have hnat : (50000402845383417071 : ℕ)^4*10000000000000000^17 ≤ 10000018957371409^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000402845383417071 50000000000000000000 10000018957371409 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000018957371409/10000000000000000 : ℝ)) (X := (50000402845383417071/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(592418769/33612500000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1895734221/107560000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (2689/50000 : ℝ)) (alpha := (592418769/33612500000000 : ℝ)) (beta := (1895734221/107560000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (2689/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(592418769/33612500000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1895734221/107560000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (36139/100000 : ℝ) ^ (17/4 : ℝ) ≤ (1322508758787295513/100000000000000000000 : ℝ) := by
    have hpowers : (36139/100000 : ℝ)^17 ≤ (1322508758787295513/100000000000000000000 : ℝ)^4 := by
      have hnat : (36139 : ℕ)^17*100000000000000000000^4 ≤ 1322508758787295513^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36139 100000 1322508758787295513 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36139/100000 : ℝ)) (X := (1322508758787295513/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (101322508758787295513/100000000000000000000 : ℝ) ≤ (626935107128521/625000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (101322508758787295513/100000000000000000000 : ℝ)^4 ≤ (626935107128521/625000000000000 : ℝ)^17 := by
      have hnat : (101322508758787295513 : ℕ)^4*625000000000000^17 ≤ 626935107128521^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101322508758787295513 100000000000000000000 626935107128521 625000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626935107128521/625000000000000 : ℝ)) (X := (101322508758787295513/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (51322508758787295513/50000000000000000000 : ℝ) ≤ (2515403978791823/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (51322508758787295513/50000000000000000000 : ℝ)^4 ≤ (2515403978791823/2500000000000000 : ℝ)^17 := by
      have hnat : (51322508758787295513 : ℕ)^4*2500000000000000^17 ≤ 2515403978791823^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51322508758787295513 50000000000000000000 2515403978791823 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2515403978791823/2500000000000000 : ℝ)) (X := (51322508758787295513/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1935107128521/225868750000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(7663550277739/903475000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (36139/100000 : ℝ)) (alpha := (1935107128521/225868750000000 : ℝ)) (beta := (7663550277739/903475000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (36139/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1935107128521/225868750000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(7663550277739/903475000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1665046441/5000000000 : ℝ)*X 0 0+(-684911669/1250000000 : ℝ)*X 0 1+(4008006211/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((654259653/1250000000 : ℝ)*X 1 0+(13369357/39062500 : ℝ)*X 1 1+(418667093/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4050347199/10000000000 : ℝ)*X 2 0+(-1979259309/5000000000 : ℝ)*X 2 1+(-2437442033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((957381579/2000000000 : ℝ)*X 0 0+(-2134681691/5000000000 : ℝ)*X 0 1+(765797189/2000000000 : ℝ)*X 0 2+(957381579/2000000000 : ℝ)*X 1 0+(-2134681691/5000000000 : ℝ)*X 1 1+(765797189/2000000000 : ℝ)*X 1 2+(957381579/2000000000 : ℝ)*X 2 0+(-2134681691/5000000000 : ℝ)*X 2 1+(765797189/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308069_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-320133/50000 : ℝ) < ((-156711/100000 : ℝ)*P 0+(-156711/100000 : ℝ)*P 1+(-156711/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-320133/50000 : ℝ) < (-205349914143801337320937165898820527/32515682176600000000000000000000000 : ℝ) := by norm_num
    linear_combination (94747/1000000000000 : ℝ)*(base15) + (83737/250000000000 : ℝ)*(base22) + (341849/1000000000000 : ℝ)*(base33) + (209177/1000000000000 : ℝ)*(base39) + (304854800863/1000000000000 : ℝ)*(base40) + (288090686553/500000000000 : ℝ)*(base49) + (340443497269/1000000000000 : ℝ)*(base50) + (593/12500000000 : ℝ)*(base59) + (1567109658151/1000000000000 : ℝ)*(major_s1_0) + (156711/100000 : ℝ)*(major_s1_1) + (156711/100000 : ℝ)*(major_s1_2) + (2105137176867/1000000000000 : ℝ)*(sp_s1_0) + (210513674027/100000000000 : ℝ)*(sp_s1_1) + (210513650007/100000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2105137176867/1000000000000 : ℝ)*(f.sum) + (14058252454916537/485888855000000000000000000000 : ℝ)*base63 + (16334820289803/45173750000000000000000000 : ℝ)*base64 + (5867178200407/26890000000000000000000000 : ℝ)*base67 + (2776353048291/4517375000000000000000000 : ℝ)*base69 + (857889889341291483/1511513675000000000000000000000 : ℝ)*base70 + (369462599979497/2007600000000000000000000000 : ℝ)*base73 + (476816773223/2689000000000000000000000 : ℝ)*base75 + (781814211653/41825000000000000000000000 : ℝ)*base77 + (1934796745367688233/5398436400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p008_b032 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (c : Fin 88) (hlo : 69 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=69 := by omega
  rcases hc with rfl
  · exact collision_c308069 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (c : Fin 88) (hlo : 69 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p008_b032 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

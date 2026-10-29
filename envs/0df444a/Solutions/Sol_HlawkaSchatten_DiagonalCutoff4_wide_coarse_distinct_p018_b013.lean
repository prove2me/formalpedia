-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p018_b013
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:26:02.217813+00:00
-- url     : https://prove2.me/submissions/ded24963-8103-481c-b78c-217343d76619

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
theorem collision_support_c318029_s0_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-1939192917/5000000000 : ℝ)*x 0 + (3746711707/10000000000 : ℝ)*x 1 + (1203053513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1939192917/5000000000 : ℝ)^5 ≤ (15303253384779/50000000000000 : ℝ)^4 := by
    have hnat : (1939192917 : ℕ)^5*50000000000000^4 ≤ 15303253384779^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939192917 5000000000 15303253384779 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3746711707/10000000000 : ℝ)^5 ≤ (29313174048603/100000000000000 : ℝ)^4 := by
    have hnat : (3746711707 : ℕ)^5*100000000000000^4 ≤ 29313174048603^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3746711707 10000000000 29313174048603 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203053513/2500000000 : ℝ)^5 ≤ (5010039895149/12500000000000 : ℝ)^4 := by
    have hnat : (1203053513 : ℕ)^5*12500000000000^4 ≤ 5010039895149^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203053513 2500000000 5010039895149 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1939192917/5000000000 : ℝ), (3746711707/10000000000 : ℝ), (1203053513/2500000000 : ℝ)] ![(15303253384779/50000000000000 : ℝ), (29313174048603/100000000000000 : ℝ), (5010039895149/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1939192917/5000000000 : ℝ)|^5 ≤ (15303253384779/50000000000000 : ℝ)^4
        have hw : |(-1939192917/5000000000 : ℝ)|=(1939192917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3746711707/10000000000 : ℝ)|^5 ≤ (29313174048603/100000000000000 : ℝ)^4
        have hw : |(3746711707/10000000000 : ℝ)|=(3746711707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1203053513/2500000000 : ℝ)|^5 ≤ (5010039895149/12500000000000 : ℝ)^4
        have hw : |(1203053513/2500000000 : ℝ)|=(1203053513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s0_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (751245051/1250000000 : ℝ)*x 0 + (-498381789/5000000000 : ℝ)*x 1 + (247324029/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (751245051/1250000000 : ℝ)^5 ≤ (6614538167053/12500000000000 : ℝ)^4 := by
    have hnat : (751245051 : ℕ)^5*12500000000000^4 ≤ 6614538167053^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751245051 1250000000 6614538167053 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (498381789/5000000000 : ℝ)^5 ≤ (5600672789849/100000000000000 : ℝ)^4 := by
    have hnat : (498381789 : ℕ)^5*100000000000000^4 ≤ 5600672789849^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498381789 5000000000 5600672789849 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (247324029/500000000 : ℝ)^5 ≤ (5185377733701/12500000000000 : ℝ)^4 := by
    have hnat : (247324029 : ℕ)^5*12500000000000^4 ≤ 5185377733701^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247324029 500000000 5185377733701 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(751245051/1250000000 : ℝ), (-498381789/5000000000 : ℝ), (247324029/500000000 : ℝ)] ![(6614538167053/12500000000000 : ℝ), (5600672789849/100000000000000 : ℝ), (5185377733701/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(751245051/1250000000 : ℝ)|^5 ≤ (6614538167053/12500000000000 : ℝ)^4
        have hw : |(751245051/1250000000 : ℝ)|=(751245051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-498381789/5000000000 : ℝ)|^5 ≤ (5600672789849/100000000000000 : ℝ)^4
        have hw : |(-498381789/5000000000 : ℝ)|=(498381789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(247324029/500000000 : ℝ)|^5 ≤ (5185377733701/12500000000000 : ℝ)^4
        have hw : |(247324029/500000000 : ℝ)|=(247324029/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s0_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (189539253/1000000000 : ℝ)*x 0 + (7613365367/10000000000 : ℝ)*x 1 + (-2351760489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (189539253/1000000000 : ℝ)^5 ≤ (12506159286903/100000000000000 : ℝ)^4 := by
    have hnat : (189539253 : ℕ)^5*100000000000000^4 ≤ 12506159286903^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189539253 1000000000 12506159286903 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7613365367/10000000000 : ℝ)^5 ≤ (1111196503653/1562500000000 : ℝ)^4 := by
    have hnat : (7613365367 : ℕ)^5*1562500000000^4 ≤ 1111196503653^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7613365367 10000000000 1111196503653 1562500000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2351760489/10000000000 : ℝ)^5 ≤ (31986844651/195312500000 : ℝ)^4 := by
    have hnat : (2351760489 : ℕ)^5*195312500000^4 ≤ 31986844651^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351760489 10000000000 31986844651 195312500000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(189539253/1000000000 : ℝ), (7613365367/10000000000 : ℝ), (-2351760489/10000000000 : ℝ)] ![(12506159286903/100000000000000 : ℝ), (1111196503653/1562500000000 : ℝ), (31986844651/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(189539253/1000000000 : ℝ)|^5 ≤ (12506159286903/100000000000000 : ℝ)^4
        have hw : |(189539253/1000000000 : ℝ)|=(189539253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7613365367/10000000000 : ℝ)|^5 ≤ (1111196503653/1562500000000 : ℝ)^4
        have hw : |(7613365367/10000000000 : ℝ)|=(7613365367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2351760489/10000000000 : ℝ)|^5 ≤ (31986844651/195312500000 : ℝ)^4
        have hw : |(-2351760489/10000000000 : ℝ)|=(2351760489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s0_4 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^5 ≤ (0 : ℝ)^4 := by
    have hnat : (0 : ℕ)^5*1^4 ≤ 0^4*1^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^5 ≤ (1 : ℝ)^4 := by
    have hnat : (1 : ℕ)^5*1^4 ≤ 1^4*1^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^5 ≤ (0 : ℝ)^4 := by
    have hnat : (0 : ℕ)^5*1^4 ≤ 0^4*1^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^5 ≤ (0 : ℝ)^4
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1 : ℝ)|^5 ≤ (1 : ℝ)^4
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^5 ≤ (0 : ℝ)^4
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s0_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-4211786627/10000000000 : ℝ)*x 0 + (3030302913/10000000000 : ℝ)*x 1 + (160818057/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211786627/10000000000 : ℝ)^5 ≤ (6785985812109/20000000000000 : ℝ)^4 := by
    have hnat : (4211786627 : ℕ)^5*20000000000000^4 ≤ 6785985812109^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211786627 10000000000 6785985812109 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3030302913/10000000000 : ℝ)^5 ≤ (5620792627543/25000000000000 : ℝ)^4 := by
    have hnat : (3030302913 : ℕ)^5*25000000000000^4 ≤ 5620792627543^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3030302913 10000000000 5620792627543 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160818057/312500000 : ℝ)^5 ≤ (21793450208027/50000000000000 : ℝ)^4 := by
    have hnat : (160818057 : ℕ)^5*50000000000000^4 ≤ 21793450208027^4*312500000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160818057 312500000 21793450208027 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4211786627/10000000000 : ℝ), (3030302913/10000000000 : ℝ), (160818057/312500000 : ℝ)] ![(6785985812109/20000000000000 : ℝ), (5620792627543/25000000000000 : ℝ), (21793450208027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4211786627/10000000000 : ℝ)|^5 ≤ (6785985812109/20000000000000 : ℝ)^4
        have hw : |(-4211786627/10000000000 : ℝ)|=(4211786627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3030302913/10000000000 : ℝ)|^5 ≤ (5620792627543/25000000000000 : ℝ)^4
        have hw : |(3030302913/10000000000 : ℝ)|=(3030302913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160818057/312500000 : ℝ)|^5 ≤ (21793450208027/50000000000000 : ℝ)^4
        have hw : |(160818057/312500000 : ℝ)|=(160818057/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s0_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5536575657/10000000000 : ℝ)*x 0 + (-60265447/2000000000 : ℝ)*x 1 + (5833920007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5536575657/10000000000 : ℝ)^5 ≤ (47758595740709/100000000000000 : ℝ)^4 := by
    have hnat : (5536575657 : ℕ)^5*100000000000000^4 ≤ 47758595740709^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5536575657 10000000000 47758595740709 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60265447/2000000000 : ℝ)^5 ≤ (1255445843307/100000000000000 : ℝ)^4 := by
    have hnat : (60265447 : ℕ)^5*100000000000000^4 ≤ 1255445843307^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60265447 2000000000 1255445843307 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5833920007/10000000000 : ℝ)^5 ≤ (50985958410783/100000000000000 : ℝ)^4 := by
    have hnat : (5833920007 : ℕ)^5*100000000000000^4 ≤ 50985958410783^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5833920007 10000000000 50985958410783 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5536575657/10000000000 : ℝ), (-60265447/2000000000 : ℝ), (5833920007/10000000000 : ℝ)] ![(47758595740709/100000000000000 : ℝ), (1255445843307/100000000000000 : ℝ), (50985958410783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5536575657/10000000000 : ℝ)|^5 ≤ (47758595740709/100000000000000 : ℝ)^4
        have hw : |(5536575657/10000000000 : ℝ)|=(5536575657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-60265447/2000000000 : ℝ)|^5 ≤ (1255445843307/100000000000000 : ℝ)^4
        have hw : |(-60265447/2000000000 : ℝ)|=(60265447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5833920007/10000000000 : ℝ)|^5 ≤ (50985958410783/100000000000000 : ℝ)^4
        have hw : |(5833920007/10000000000 : ℝ)|=(5833920007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s0_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (216710943/2500000000 : ℝ)*x 0 + (4565337627/5000000000 : ℝ)*x 1 + (-1059154367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216710943/2500000000 : ℝ)^5 ≤ (4703552994883/100000000000000 : ℝ)^4 := by
    have hnat : (216710943 : ℕ)^5*100000000000000^4 ≤ 4703552994883^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216710943 2500000000 4703552994883 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4565337627/5000000000 : ℝ)^5 ≤ (3570167664761/4000000000000 : ℝ)^4 := by
    have hnat : (4565337627 : ℕ)^5*4000000000000^4 ≤ 3570167664761^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4565337627 5000000000 3570167664761 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059154367/10000000000 : ℝ)^5 ≤ (47205120093/781250000000 : ℝ)^4 := by
    have hnat : (1059154367 : ℕ)^5*781250000000^4 ≤ 47205120093^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059154367 10000000000 47205120093 781250000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216710943/2500000000 : ℝ), (4565337627/5000000000 : ℝ), (-1059154367/10000000000 : ℝ)] ![(4703552994883/100000000000000 : ℝ), (3570167664761/4000000000000 : ℝ), (47205120093/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216710943/2500000000 : ℝ)|^5 ≤ (4703552994883/100000000000000 : ℝ)^4
        have hw : |(216710943/2500000000 : ℝ)|=(216710943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4565337627/5000000000 : ℝ)|^5 ≤ (3570167664761/4000000000000 : ℝ)^4
        have hw : |(4565337627/5000000000 : ℝ)|=(4565337627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1059154367/10000000000 : ℝ)|^5 ≤ (47205120093/781250000000 : ℝ)^4
        have hw : |(-1059154367/10000000000 : ℝ)|=(1059154367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s0_12 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4362700807/10000000000 : ℝ)*x 0 + (3476121589/10000000000 : ℝ)*x 1 + (2298500833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362700807/10000000000 : ℝ)^5 ≤ (7091274277373/20000000000000 : ℝ)^4 := by
    have hnat : (4362700807 : ℕ)^5*20000000000000^4 ≤ 7091274277373^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362700807 10000000000 7091274277373 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3476121589/10000000000 : ℝ)^5 ≤ (26691236824203/100000000000000 : ℝ)^4 := by
    have hnat : (3476121589 : ℕ)^5*100000000000000^4 ≤ 26691236824203^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3476121589 10000000000 26691236824203 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2298500833/5000000000 : ℝ)^5 ≤ (37852391775619/100000000000000 : ℝ)^4 := by
    have hnat : (2298500833 : ℕ)^5*100000000000000^4 ≤ 37852391775619^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2298500833 5000000000 37852391775619 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362700807/10000000000 : ℝ), (3476121589/10000000000 : ℝ), (2298500833/5000000000 : ℝ)] ![(7091274277373/20000000000000 : ℝ), (26691236824203/100000000000000 : ℝ), (37852391775619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362700807/10000000000 : ℝ)|^5 ≤ (7091274277373/20000000000000 : ℝ)^4
        have hw : |(4362700807/10000000000 : ℝ)|=(4362700807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3476121589/10000000000 : ℝ)|^5 ≤ (26691236824203/100000000000000 : ℝ)^4
        have hw : |(3476121589/10000000000 : ℝ)|=(3476121589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2298500833/5000000000 : ℝ)|^5 ≤ (37852391775619/100000000000000 : ℝ)^4
        have hw : |(2298500833/5000000000 : ℝ)|=(2298500833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s0_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-1062617509/2500000000 : ℝ)*x 0 + (2723096629/10000000000 : ℝ)*x 1 + (5373708037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062617509/2500000000 : ℝ)^5 ≤ (54911863381/160000000000 : ℝ)^4 := by
    have hnat : (1062617509 : ℕ)^5*160000000000^4 ≤ 54911863381^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062617509 2500000000 54911863381 160000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2723096629/10000000000 : ℝ)^5 ≤ (19671107677559/100000000000000 : ℝ)^4 := by
    have hnat : (2723096629 : ℕ)^5*100000000000000^4 ≤ 19671107677559^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723096629 10000000000 19671107677559 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5373708037/10000000000 : ℝ)^5 ≤ (46008977690703/100000000000000 : ℝ)^4 := by
    have hnat : (5373708037 : ℕ)^5*100000000000000^4 ≤ 46008977690703^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373708037 10000000000 46008977690703 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1062617509/2500000000 : ℝ), (2723096629/10000000000 : ℝ), (5373708037/10000000000 : ℝ)] ![(54911863381/160000000000 : ℝ), (19671107677559/100000000000000 : ℝ), (46008977690703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1062617509/2500000000 : ℝ)|^5 ≤ (54911863381/160000000000 : ℝ)^4
        have hw : |(-1062617509/2500000000 : ℝ)|=(1062617509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2723096629/10000000000 : ℝ)|^5 ≤ (19671107677559/100000000000000 : ℝ)^4
        have hw : |(2723096629/10000000000 : ℝ)|=(2723096629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5373708037/10000000000 : ℝ)|^5 ≤ (46008977690703/100000000000000 : ℝ)^4
        have hw : |(5373708037/10000000000 : ℝ)|=(5373708037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s0_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3398715801/5000000000 : ℝ)*x 0 + (-81307327/625000000 : ℝ)*x 1 + (3864173349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3398715801/5000000000 : ℝ)^5 ≤ (61720730541189/100000000000000 : ℝ)^4 := by
    have hnat : (3398715801 : ℕ)^5*100000000000000^4 ≤ 61720730541189^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3398715801 5000000000 61720730541189 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81307327/625000000 : ℝ)^5 ≤ (7812896714157/100000000000000 : ℝ)^4 := by
    have hnat : (81307327 : ℕ)^5*100000000000000^4 ≤ 7812896714157^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81307327 625000000 7812896714157 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3864173349/10000000000 : ℝ)^5 ≤ (15233186368259/50000000000000 : ℝ)^4 := by
    have hnat : (3864173349 : ℕ)^5*50000000000000^4 ≤ 15233186368259^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3864173349 10000000000 15233186368259 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3398715801/5000000000 : ℝ), (-81307327/625000000 : ℝ), (3864173349/10000000000 : ℝ)] ![(61720730541189/100000000000000 : ℝ), (7812896714157/100000000000000 : ℝ), (15233186368259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3398715801/5000000000 : ℝ)|^5 ≤ (61720730541189/100000000000000 : ℝ)^4
        have hw : |(3398715801/5000000000 : ℝ)|=(3398715801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-81307327/625000000 : ℝ)|^5 ≤ (7812896714157/100000000000000 : ℝ)^4
        have hw : |(-81307327/625000000 : ℝ)|=(81307327/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3864173349/10000000000 : ℝ)|^5 ≤ (15233186368259/50000000000000 : ℝ)^4
        have hw : |(3864173349/10000000000 : ℝ)|=(3864173349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s0_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (792199709/5000000000 : ℝ)*x 0 + (7840429023/10000000000 : ℝ)*x 1 + (-145899749/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (792199709/5000000000 : ℝ)^5 ≤ (999610576889/10000000000000 : ℝ)^4 := by
    have hnat : (792199709 : ℕ)^5*10000000000000^4 ≤ 999610576889^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792199709 5000000000 999610576889 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7840429023/10000000000 : ℝ)^5 ≤ (18444411089329/25000000000000 : ℝ)^4 := by
    have hnat : (7840429023 : ℕ)^5*25000000000000^4 ≤ 18444411089329^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7840429023 10000000000 18444411089329 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (145899749/625000000 : ℝ)^5 ≤ (16226249862987/100000000000000 : ℝ)^4 := by
    have hnat : (145899749 : ℕ)^5*100000000000000^4 ≤ 16226249862987^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145899749 625000000 16226249862987 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(792199709/5000000000 : ℝ), (7840429023/10000000000 : ℝ), (-145899749/625000000 : ℝ)] ![(999610576889/10000000000000 : ℝ), (18444411089329/25000000000000 : ℝ), (16226249862987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(792199709/5000000000 : ℝ)|^5 ≤ (999610576889/10000000000000 : ℝ)^4
        have hw : |(792199709/5000000000 : ℝ)|=(792199709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7840429023/10000000000 : ℝ)|^5 ≤ (18444411089329/25000000000000 : ℝ)^4
        have hw : |(7840429023/10000000000 : ℝ)|=(7840429023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-145899749/625000000 : ℝ)|^5 ≤ (16226249862987/100000000000000 : ℝ)^4
        have hw : |(-145899749/625000000 : ℝ)|=(145899749/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s0_19 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3025719007/10000000000 : ℝ)*x 0 + (692691887/2000000000 : ℝ)*x 1 + (1166850193/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3025719007/10000000000 : ℝ)^5 ≤ (2244066599477/10000000000000 : ℝ)^4 := by
    have hnat : (3025719007 : ℕ)^5*10000000000000^4 ≤ 2244066599477^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3025719007 10000000000 2244066599477 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (692691887/2000000000 : ℝ)^5 ≤ (5313952003173/20000000000000 : ℝ)^4 := by
    have hnat : (692691887 : ℕ)^5*20000000000000^4 ≤ 5313952003173^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692691887 2000000000 5313952003173 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1166850193/2000000000 : ℝ)^5 ≤ (12747393493779/25000000000000 : ℝ)^4 := by
    have hnat : (1166850193 : ℕ)^5*25000000000000^4 ≤ 12747393493779^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166850193 2000000000 12747393493779 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3025719007/10000000000 : ℝ), (692691887/2000000000 : ℝ), (1166850193/2000000000 : ℝ)] ![(2244066599477/10000000000000 : ℝ), (5313952003173/20000000000000 : ℝ), (12747393493779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3025719007/10000000000 : ℝ)|^5 ≤ (2244066599477/10000000000000 : ℝ)^4
        have hw : |(3025719007/10000000000 : ℝ)|=(3025719007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(692691887/2000000000 : ℝ)|^5 ≤ (5313952003173/20000000000000 : ℝ)^4
        have hw : |(692691887/2000000000 : ℝ)|=(692691887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1166850193/2000000000 : ℝ)|^5 ≤ (12747393493779/25000000000000 : ℝ)^4
        have hw : |(1166850193/2000000000 : ℝ)|=(1166850193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s0_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-3058994077/10000000000 : ℝ)*x 0 + (184262753/500000000 : ℝ)*x 1 + (1121730689/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3058994077/10000000000 : ℝ)^5 ≤ (22749575386363/100000000000000 : ℝ)^4 := by
    have hnat : (3058994077 : ℕ)^5*100000000000000^4 ≤ 22749575386363^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3058994077 10000000000 22749575386363 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (184262753/500000000 : ℝ)^5 ≤ (28713387961063/100000000000000 : ℝ)^4 := by
    have hnat : (184262753 : ℕ)^5*100000000000000^4 ≤ 28713387961063^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184262753 500000000 28713387961063 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121730689/2000000000 : ℝ)^5 ≤ (24268518320829/50000000000000 : ℝ)^4 := by
    have hnat : (1121730689 : ℕ)^5*50000000000000^4 ≤ 24268518320829^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121730689 2000000000 24268518320829 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3058994077/10000000000 : ℝ), (184262753/500000000 : ℝ), (1121730689/2000000000 : ℝ)] ![(22749575386363/100000000000000 : ℝ), (28713387961063/100000000000000 : ℝ), (24268518320829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3058994077/10000000000 : ℝ)|^5 ≤ (22749575386363/100000000000000 : ℝ)^4
        have hw : |(-3058994077/10000000000 : ℝ)|=(3058994077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(184262753/500000000 : ℝ)|^5 ≤ (28713387961063/100000000000000 : ℝ)^4
        have hw : |(184262753/500000000 : ℝ)|=(184262753/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121730689/2000000000 : ℝ)|^5 ≤ (24268518320829/50000000000000 : ℝ)^4
        have hw : |(1121730689/2000000000 : ℝ)|=(1121730689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s0_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (926984153/1250000000 : ℝ)*x 0 + (-88772571/2500000000 : ℝ)*x 1 + (945034649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (926984153/1250000000 : ℝ)^5 ≤ (1720453264733/2500000000000 : ℝ)^4 := by
    have hnat : (926984153 : ℕ)^5*2500000000000^4 ≤ 1720453264733^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926984153 1250000000 1720453264733 2500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88772571/2500000000 : ℝ)^5 ≤ (1541428862201/100000000000000 : ℝ)^4 := by
    have hnat : (88772571 : ℕ)^5*100000000000000^4 ≤ 1541428862201^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88772571 2500000000 1541428862201 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945034649/2500000000 : ℝ)^5 ≤ (14820220264293/50000000000000 : ℝ)^4 := by
    have hnat : (945034649 : ℕ)^5*50000000000000^4 ≤ 14820220264293^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945034649 2500000000 14820220264293 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(926984153/1250000000 : ℝ), (-88772571/2500000000 : ℝ), (945034649/2500000000 : ℝ)] ![(1720453264733/2500000000000 : ℝ), (1541428862201/100000000000000 : ℝ), (14820220264293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(926984153/1250000000 : ℝ)|^5 ≤ (1720453264733/2500000000000 : ℝ)^4
        have hw : |(926984153/1250000000 : ℝ)|=(926984153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88772571/2500000000 : ℝ)|^5 ≤ (1541428862201/100000000000000 : ℝ)^4
        have hw : |(-88772571/2500000000 : ℝ)|=(88772571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(945034649/2500000000 : ℝ)|^5 ≤ (14820220264293/50000000000000 : ℝ)^4
        have hw : |(945034649/2500000000 : ℝ)|=(945034649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s0_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (440676489/5000000000 : ℝ)*x 0 + (2194218399/2500000000 : ℝ)*x 1 + (-403989293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440676489/5000000000 : ℝ)^5 ≤ (9379234287/195312500000 : ℝ)^4 := by
    have hnat : (440676489 : ℕ)^5*195312500000^4 ≤ 9379234287^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440676489 5000000000 9379234287 195312500000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194218399/2500000000 : ℝ)^5 ≤ (84952234116319/100000000000000 : ℝ)^4 := by
    have hnat : (2194218399 : ℕ)^5*100000000000000^4 ≤ 84952234116319^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194218399 2500000000 84952234116319 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403989293/2500000000 : ℝ)^5 ≤ (10245597912013/100000000000000 : ℝ)^4 := by
    have hnat : (403989293 : ℕ)^5*100000000000000^4 ≤ 10245597912013^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403989293 2500000000 10245597912013 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(440676489/5000000000 : ℝ), (2194218399/2500000000 : ℝ), (-403989293/2500000000 : ℝ)] ![(9379234287/195312500000 : ℝ), (84952234116319/100000000000000 : ℝ), (10245597912013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(440676489/5000000000 : ℝ)|^5 ≤ (9379234287/195312500000 : ℝ)^4
        have hw : |(440676489/5000000000 : ℝ)|=(440676489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2194218399/2500000000 : ℝ)|^5 ≤ (84952234116319/100000000000000 : ℝ)^4
        have hw : |(2194218399/2500000000 : ℝ)|=(2194218399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-403989293/2500000000 : ℝ)|^5 ≤ (10245597912013/100000000000000 : ℝ)^4
        have hw : |(-403989293/2500000000 : ℝ)|=(403989293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s0_25 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (6406693309/10000000000 : ℝ)*x 0 + (1267889731/5000000000 : ℝ)*x 1 + (3265723121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6406693309/10000000000 : ℝ)^5 ≤ (7164772934239/12500000000000 : ℝ)^4 := by
    have hnat : (6406693309 : ℕ)^5*12500000000000^4 ≤ 7164772934239^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6406693309 10000000000 7164772934239 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1267889731/5000000000 : ℝ)^5 ≤ (17994482031083/100000000000000 : ℝ)^4 := by
    have hnat : (1267889731 : ℕ)^5*100000000000000^4 ≤ 17994482031083^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267889731 5000000000 17994482031083 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3265723121/10000000000 : ℝ)^5 ≤ (12343667242271/50000000000000 : ℝ)^4 := by
    have hnat : (3265723121 : ℕ)^5*50000000000000^4 ≤ 12343667242271^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3265723121 10000000000 12343667242271 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6406693309/10000000000 : ℝ), (1267889731/5000000000 : ℝ), (3265723121/10000000000 : ℝ)] ![(7164772934239/12500000000000 : ℝ), (17994482031083/100000000000000 : ℝ), (12343667242271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6406693309/10000000000 : ℝ)|^5 ≤ (7164772934239/12500000000000 : ℝ)^4
        have hw : |(6406693309/10000000000 : ℝ)|=(6406693309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1267889731/5000000000 : ℝ)|^5 ≤ (17994482031083/100000000000000 : ℝ)^4
        have hw : |(1267889731/5000000000 : ℝ)|=(1267889731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3265723121/10000000000 : ℝ)|^5 ≤ (12343667242271/50000000000000 : ℝ)^4
        have hw : |(3265723121/10000000000 : ℝ)|=(3265723121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s1_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-249297619/625000000 : ℝ)*x 0 + (1023481991/2500000000 : ℝ)*x 1 + (136633303/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249297619/625000000 : ℝ)^5 ≤ (31699151802137/100000000000000 : ℝ)^4 := by
    have hnat : (249297619 : ℕ)^5*100000000000000^4 ≤ 31699151802137^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249297619 625000000 31699151802137 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023481991/2500000000 : ℝ)^5 ≤ (8186820237597/25000000000000 : ℝ)^4 := by
    have hnat : (1023481991 : ℕ)^5*25000000000000^4 ≤ 8186820237597^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023481991 2500000000 8186820237597 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136633303/312500000 : ℝ)^5 ≤ (35553567241587/100000000000000 : ℝ)^4 := by
    have hnat : (136633303 : ℕ)^5*100000000000000^4 ≤ 35553567241587^4*312500000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136633303 312500000 35553567241587 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-249297619/625000000 : ℝ), (1023481991/2500000000 : ℝ), (136633303/312500000 : ℝ)] ![(31699151802137/100000000000000 : ℝ), (8186820237597/25000000000000 : ℝ), (35553567241587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-249297619/625000000 : ℝ)|^5 ≤ (31699151802137/100000000000000 : ℝ)^4
        have hw : |(-249297619/625000000 : ℝ)|=(249297619/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1023481991/2500000000 : ℝ)|^5 ≤ (8186820237597/25000000000000 : ℝ)^4
        have hw : |(1023481991/2500000000 : ℝ)|=(1023481991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136633303/312500000 : ℝ)|^5 ≤ (35553567241587/100000000000000 : ℝ)^4
        have hw : |(136633303/312500000 : ℝ)|=(136633303/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s1_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1320737691/2500000000 : ℝ)*x 0 + (-276967811/1250000000 : ℝ)*x 1 + (119531551/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320737691/2500000000 : ℝ)^5 ≤ (5629965285283/12500000000000 : ℝ)^4 := by
    have hnat : (1320737691 : ℕ)^5*12500000000000^4 ≤ 5629965285283^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320737691 2500000000 5629965285283 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276967811/1250000000 : ℝ)^5 ≤ (15201943251759/100000000000000 : ℝ)^4 := by
    have hnat : (276967811 : ℕ)^5*100000000000000^4 ≤ 15201943251759^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276967811 1250000000 15201943251759 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119531551/250000000 : ℝ)^5 ≤ (39758334445009/100000000000000 : ℝ)^4 := by
    have hnat : (119531551 : ℕ)^5*100000000000000^4 ≤ 39758334445009^4*250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119531551 250000000 39758334445009 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320737691/2500000000 : ℝ), (-276967811/1250000000 : ℝ), (119531551/250000000 : ℝ)] ![(5629965285283/12500000000000 : ℝ), (15201943251759/100000000000000 : ℝ), (39758334445009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320737691/2500000000 : ℝ)|^5 ≤ (5629965285283/12500000000000 : ℝ)^4
        have hw : |(1320737691/2500000000 : ℝ)|=(1320737691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-276967811/1250000000 : ℝ)|^5 ≤ (15201943251759/100000000000000 : ℝ)^4
        have hw : |(-276967811/1250000000 : ℝ)|=(276967811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119531551/250000000 : ℝ)|^5 ≤ (39758334445009/100000000000000 : ℝ)^4
        have hw : |(119531551/250000000 : ℝ)|=(119531551/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s1_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (292762949/1000000000 : ℝ)*x 0 + (1534098147/2500000000 : ℝ)*x 1 + (-50142337/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (292762949/1000000000 : ℝ)^5 ≤ (21535013157437/100000000000000 : ℝ)^4 := by
    have hnat : (292762949 : ℕ)^5*100000000000000^4 ≤ 21535013157437^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292762949 1000000000 21535013157437 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1534098147/2500000000 : ℝ)^5 ≤ (27155726449159/50000000000000 : ℝ)^4 := by
    have hnat : (1534098147 : ℕ)^5*50000000000000^4 ≤ 27155726449159^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1534098147 2500000000 27155726449159 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50142337/156250000 : ℝ)^5 ≤ (754797935117/3125000000000 : ℝ)^4 := by
    have hnat : (50142337 : ℕ)^5*3125000000000^4 ≤ 754797935117^4*156250000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50142337 156250000 754797935117 3125000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(292762949/1000000000 : ℝ), (1534098147/2500000000 : ℝ), (-50142337/156250000 : ℝ)] ![(21535013157437/100000000000000 : ℝ), (27155726449159/50000000000000 : ℝ), (754797935117/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(292762949/1000000000 : ℝ)|^5 ≤ (21535013157437/100000000000000 : ℝ)^4
        have hw : |(292762949/1000000000 : ℝ)|=(292762949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1534098147/2500000000 : ℝ)|^5 ≤ (27155726449159/50000000000000 : ℝ)^4
        have hw : |(1534098147/2500000000 : ℝ)|=(1534098147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50142337/156250000 : ℝ)|^5 ≤ (754797935117/3125000000000 : ℝ)^4
        have hw : |(-50142337/156250000 : ℝ)|=(50142337/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318029_s1_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1127156219/2500000000 : ℝ)*x 0 + (3861728751/10000000000 : ℝ)*x 1 + (4080469029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1127156219/2500000000 : ℝ)^5 ≤ (18472476934377/50000000000000 : ℝ)^4 := by
    have hnat : (1127156219 : ℕ)^5*50000000000000^4 ≤ 18472476934377^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127156219 2500000000 18472476934377 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3861728751/10000000000 : ℝ)^5 ≤ (1217691286241/4000000000000 : ℝ)^4 := by
    have hnat : (3861728751 : ℕ)^5*4000000000000^4 ≤ 1217691286241^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3861728751 10000000000 1217691286241 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4080469029/10000000000 : ℝ)^5 ≤ (32612763971669/100000000000000 : ℝ)^4 := by
    have hnat : (4080469029 : ℕ)^5*100000000000000^4 ≤ 32612763971669^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4080469029 10000000000 32612763971669 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1127156219/2500000000 : ℝ), (3861728751/10000000000 : ℝ), (4080469029/10000000000 : ℝ)] ![(18472476934377/50000000000000 : ℝ), (1217691286241/4000000000000 : ℝ), (32612763971669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1127156219/2500000000 : ℝ)|^5 ≤ (18472476934377/50000000000000 : ℝ)^4
        have hw : |(1127156219/2500000000 : ℝ)|=(1127156219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3861728751/10000000000 : ℝ)|^5 ≤ (1217691286241/4000000000000 : ℝ)^4
        have hw : |(3861728751/10000000000 : ℝ)|=(3861728751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4080469029/10000000000 : ℝ)|^5 ≤ (32612763971669/100000000000000 : ℝ)^4
        have hw : |(4080469029/10000000000 : ℝ)|=(4080469029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318029 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1939192917/5000000000 : ℝ)*X 0 0+(3746711707/10000000000 : ℝ)*X 0 1+(1203053513/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((751245051/1250000000 : ℝ)*X 1 0+(-498381789/5000000000 : ℝ)*X 1 1+(247324029/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((189539253/1000000000 : ℝ)*X 2 0+(7613365367/10000000000 : ℝ)*X 2 1+(-2351760489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_4 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-4211786627/10000000000 : ℝ)*X 0 0+(3030302913/10000000000 : ℝ)*X 0 1+(160818057/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((5536575657/10000000000 : ℝ)*X 1 0+(-60265447/2000000000 : ℝ)*X 1 1+(5833920007/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((216710943/2500000000 : ℝ)*X 2 0+(4565337627/5000000000 : ℝ)*X 2 1+(-1059154367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((4362700807/10000000000 : ℝ)*X 0 0+(3476121589/10000000000 : ℝ)*X 0 1+(2298500833/5000000000 : ℝ)*X 0 2+(4362700807/10000000000 : ℝ)*X 1 0+(3476121589/10000000000 : ℝ)*X 1 1+(2298500833/5000000000 : ℝ)*X 1 2+(4362700807/10000000000 : ℝ)*X 2 0+(3476121589/10000000000 : ℝ)*X 2 1+(2298500833/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-1062617509/2500000000 : ℝ)*X 0 0+(2723096629/10000000000 : ℝ)*X 0 1+(5373708037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((3398715801/5000000000 : ℝ)*X 1 0+(-81307327/625000000 : ℝ)*X 1 1+(3864173349/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((792199709/5000000000 : ℝ)*X 2 0+(7840429023/10000000000 : ℝ)*X 2 1+(-145899749/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((3025719007/10000000000 : ℝ)*X 0 0+(692691887/2000000000 : ℝ)*X 0 1+(1166850193/2000000000 : ℝ)*X 0 2+(3025719007/10000000000 : ℝ)*X 1 0+(692691887/2000000000 : ℝ)*X 1 1+(1166850193/2000000000 : ℝ)*X 1 2+(3025719007/10000000000 : ℝ)*X 2 0+(692691887/2000000000 : ℝ)*X 2 1+(1166850193/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-3058994077/10000000000 : ℝ)*X 0 0+(184262753/500000000 : ℝ)*X 0 1+(1121730689/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((926984153/1250000000 : ℝ)*X 1 0+(-88772571/2500000000 : ℝ)*X 1 1+(945034649/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((440676489/5000000000 : ℝ)*X 2 0+(2194218399/2500000000 : ℝ)*X 2 1+(-403989293/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((6406693309/10000000000 : ℝ)*X 0 0+(1267889731/5000000000 : ℝ)*X 0 1+(3265723121/10000000000 : ℝ)*X 0 2+(6406693309/10000000000 : ℝ)*X 1 0+(1267889731/5000000000 : ℝ)*X 1 1+(3265723121/10000000000 : ℝ)*X 1 2+(6406693309/10000000000 : ℝ)*X 2 0+(1267889731/5000000000 : ℝ)*X 2 1+(3265723121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((30293/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30293/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7330607242085938424637/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (541336353/200000000000 : ℝ)*(base40) + (143645009497/250000000000 : ℝ)*(base50) + (743555239547/1000000000000 : ℝ)*(base59) + (2758751411133/1000000000000 : ℝ)*(major_s0_0) + (5723218051803/1000000000000 : ℝ)*(major_s0_1) + (2758751411133/1000000000000 : ℝ)*(major_s0_2) + (39826579/1000000000000 : ℝ)*(sp_s0_0) + (296446664067/100000000000 : ℝ)*(sp_s0_4) + (1001393817361/250000000000 : ℝ)*(sp_s0_7) + (4005647200789/1000000000000 : ℝ)*(sp_s0_8) + (4005647200789/1000000000000 : ℝ)*(sp_s0_9) + (1511815364123/1000000000000 : ℝ)*(sp_s0_12) + (9086923/250000000000 : ℝ)*(sp_s0_19) + (16052383/500000000000 : ℝ)*(sp_s0_20) + (755925855907/500000000000 : ℝ)*(f.failure) + (4005647200789/1000000000000 : ℝ)*(f.sum) + (178109123378847/500000000000000000000000000 : ℝ)*base62 + (1983552919994263/5000000000000000000000000000 : ℝ)*base64 + (1170325174476367/5000000000000000000000000000 : ℝ)*base66 + (1687373977085647/5000000000000000000000000000 : ℝ)*base68 + (226218810807991/500000000000000000000000000 : ℝ)*base70 + (1094161766505737/5000000000000000000000000000 : ℝ)*base72 + (1949385677702823/5000000000000000000000000000 : ℝ)*base74 + (1498013174585647/5000000000000000000000000000 : ℝ)*base76 + (63439016497763/625000000000000000000000000 : ℝ)*base78 + (807/2000000000000000 : ℝ)*base86 + (807/2000000000000000 : ℝ)*base88 + (807/2000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4847/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(4847/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (130772655869847743139/19531250000000000000000000 : ℝ) := by norm_num
    linear_combination (30351295711/62500000000 : ℝ)*(base40) + (562679/1000000000000 : ℝ)*(base50) + (60059340313/100000000000 : ℝ)*(base59) + (69237971201/31250000000 : ℝ)*(major_s0_0) + (69237971201/31250000000 : ℝ)*(major_s0_1) + (69237971201/31250000000 : ℝ)*(major_s0_2) + (2428771/125000000000 : ℝ)*(sp_s0_1) + (147096193/1000000000000 : ℝ)*(sp_s0_2) + (3216998502727/1000000000000 : ℝ)*(sp_s0_13) + (3216958579539/1000000000000 : ℝ)*(sp_s0_14) + (1608439420177/500000000000 : ℝ)*(sp_s0_15) + (242840397691/200000000000 : ℝ)*(sp_s0_19) + (27433821/1000000000000 : ℝ)*(sp_s0_20) + (1198171/25000000000 : ℝ)*(sp_s0_21) + (242840397691/200000000000 : ℝ)*(f.failure) + (3217025936547/1000000000000 : ℝ)*(f.sum) + (390449449/2500000000000000000000 : ℝ)*base62 + (179014861490311/156250000000000000000000000 : ℝ)*base64 + (56954502545391/39062500000000000000000000 : ℝ)*base66 + (41965734054417/78125000000000000000000000 : ℝ)*base68 + (15361992101079/31250000000000000000000000 : ℝ)*base70 + (104997384353439/156250000000000000000000000 : ℝ)*base72 + (30068667402479/39062500000000000000000000 : ℝ)*base74 + (67287538905709/156250000000000000000000000 : ℝ)*base76 + (29330777450157/39062500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1009/800000000000000 : ℝ)*base87 + (1009/800000000000000 : ℝ)*base89 + (1009/800000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10141/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10141/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10455913024116990876609/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (947218733343/1000000000000 : ℝ)*(base40) + (518510718163/1000000000000 : ℝ)*(base50) + (821443992647/1000000000000 : ℝ)*(base59) + (3635311810207/1000000000000 : ℝ)*(major_s0_0) + (4500430206523/500000000000 : ℝ)*(major_s0_1) + (3635311810207/1000000000000 : ℝ)*(major_s0_2) + (16093769/250000000000 : ℝ)*(sp_s0_0) + (5365548602839/1000000000000 : ℝ)*(sp_s0_4) + (18168343/500000000000 : ℝ)*(sp_s0_14) + (2491277/500000000000 : ℝ)*(sp_s0_15) + (5278331872789/1000000000000 : ℝ)*(sp_s0_20) + (5278359911179/1000000000000 : ℝ)*(sp_s0_21) + (5278391265311/1000000000000 : ℝ)*(sp_s0_22) + (1992224584303/1000000000000 : ℝ)*(sp_s0_25) + (1992224584303/1000000000000 : ℝ)*(f.failure) + (1055679249573/200000000000 : ℝ)*(f.sum) + (378699147037901/5000000000000000000000000000 : ℝ)*base63 + (1208830366595523/5000000000000000000000000000 : ℝ)*base65 + (1087435865337553/2500000000000000000000000000 : ℝ)*base67 + (1390553558702587/5000000000000000000000000000 : ℝ)*base69 + (59592680279811/500000000000000000000000000 : ℝ)*base71 + (648930723904477/5000000000000000000000000000 : ℝ)*base73 + (540449153667657/2500000000000000000000000000 : ℝ)*base75 + (2019239864202587/5000000000000000000000000000 : ℝ)*base77 + (617810177579583/5000000000000000000000000000 : ℝ)*base79 + (403/4000000000000000 : ℝ)*base86 + (403/4000000000000000 : ℝ)*base88 + (403/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (30293/100000 : ℝ) ^ (39/8 : ℝ) ≤ (74042938722803011/25000000000000000000 : ℝ) := by
    have hpowers : (30293/100000 : ℝ)^39 ≤ (74042938722803011/25000000000000000000 : ℝ)^8 := by
      have hnat : (30293 : ℕ)^39*25000000000000000000^8 ≤ 74042938722803011^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30293 100000 74042938722803011 25000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30293/100000 : ℝ)) (X := (74042938722803011/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (25074042938722803011/25000000000000000000 : ℝ) ≤ (2501517044870259/2500000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (25074042938722803011/25000000000000000000 : ℝ)^8 ≤ (2501517044870259/2500000000000000 : ℝ)^39 := by
      have hnat : (25074042938722803011 : ℕ)^8*2500000000000000^39 ≤ 2501517044870259^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25074042938722803011 25000000000000000000 2501517044870259 2500000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501517044870259/2500000000000000 : ℝ)) (X := (25074042938722803011/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (12574042938722803011/12500000000000000000 : ℝ) ≤ (10012122132199889/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (12574042938722803011/12500000000000000000 : ℝ)^8 ≤ (10012122132199889/10000000000000000 : ℝ)^39 := by
      have hnat : (12574042938722803011 : ℕ)^8*10000000000000000^39 ≤ 10012122132199889^39*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12574042938722803011 12500000000000000000 10012122132199889 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012122132199889/10000000000000000 : ℝ)) (X := (12574042938722803011/12500000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1517044870259/757325000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(6053952718853/3029300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (30293/100000 : ℝ)) (alpha := (1517044870259/757325000000000 : ℝ)) (beta := (6053952718853/3029300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (30293/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1517044870259/757325000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(6053952718853/3029300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (4847/50000 : ℝ) ^ (39/8 : ℝ) ≤ (286511599165451/25000000000000000000 : ℝ) := by
    have hpowers : (4847/50000 : ℝ)^39 ≤ (286511599165451/25000000000000000000 : ℝ)^8 := by
      have hnat : (4847 : ℕ)^39*25000000000000000000^8 ≤ 286511599165451^8*50000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4847 50000 286511599165451 25000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4847/50000 : ℝ)) (X := (286511599165451/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25000286511599165451/25000000000000000000 : ℝ) ≤ (5000011754268479/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (25000286511599165451/25000000000000000000 : ℝ)^8 ≤ (5000011754268479/5000000000000000 : ℝ)^39 := by
      have hnat : (25000286511599165451 : ℕ)^8*5000000000000000^39 ≤ 5000011754268479^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000286511599165451 25000000000000000000 5000011754268479 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000011754268479/5000000000000000 : ℝ)) (X := (25000286511599165451/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12500286511599165451/12500000000000000000 : ℝ) ≤ (5000023508429883/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (12500286511599165451/12500000000000000000 : ℝ)^8 ≤ (5000023508429883/5000000000000000 : ℝ)^39 := by
      have hnat : (12500286511599165451 : ℕ)^8*5000000000000000^39 ≤ 5000023508429883^39*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500286511599165451 12500000000000000000 5000023508429883 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000023508429883/5000000000000000 : ℝ)) (X := (12500286511599165451/12500000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(11754268479/484700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(2938540351/121175000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (4847/50000 : ℝ)) (alpha := (11754268479/484700000000000 : ℝ)) (beta := (2938540351/121175000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (4847/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(11754268479/484700000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(2938540351/121175000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (10141/25000 : ℝ) ^ (39/8 : ℝ) ≤ (614690183832901503/50000000000000000000 : ℝ) := by
    have hpowers : (10141/25000 : ℝ)^39 ≤ (614690183832901503/50000000000000000000 : ℝ)^8 := by
      have hnat : (10141 : ℕ)^39*50000000000000000000^8 ≤ 614690183832901503^8*25000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10141 25000 614690183832901503 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10141/25000 : ℝ)) (X := (614690183832901503/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50614690183832901503/50000000000000000000 : ℝ) ≤ (1002509574198561/1000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (50614690183832901503/50000000000000000000 : ℝ)^8 ≤ (1002509574198561/1000000000000000 : ℝ)^39 := by
      have hnat : (50614690183832901503 : ℕ)^8*1000000000000000^39 ≤ 1002509574198561^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50614690183832901503 50000000000000000000 1002509574198561 1000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002509574198561/1000000000000000 : ℝ)) (X := (50614690183832901503/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25614690183832901503/25000000000000000000 : ℝ) ≤ (10049950383997009/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (25614690183832901503/25000000000000000000 : ℝ)^8 ≤ (10049950383997009/10000000000000000 : ℝ)^39 := by
      have hnat : (25614690183832901503 : ℕ)^8*10000000000000000^39 ≤ 10049950383997009^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25614690183832901503 25000000000000000000 10049950383997009 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10049950383997009/10000000000000000 : ℝ)) (X := (25614690183832901503/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(2509574198561/405640000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(24854642011399/4056400000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (10141/25000 : ℝ)) (alpha := (2509574198561/405640000000000 : ℝ)) (beta := (24854642011399/4056400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (10141/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(2509574198561/405640000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(24854642011399/4056400000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-249297619/625000000 : ℝ)*X 0 0+(1023481991/2500000000 : ℝ)*X 0 1+(136633303/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1320737691/2500000000 : ℝ)*X 1 0+(-276967811/1250000000 : ℝ)*X 1 1+(119531551/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((292762949/1000000000 : ℝ)*X 2 0+(1534098147/2500000000 : ℝ)*X 2 1+(-50142337/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1127156219/2500000000 : ℝ)*X 0 0+(3861728751/10000000000 : ℝ)*X 0 1+(4080469029/10000000000 : ℝ)*X 0 2+(1127156219/2500000000 : ℝ)*X 1 0+(3861728751/10000000000 : ℝ)*X 1 1+(4080469029/10000000000 : ℝ)*X 1 2+(1127156219/2500000000 : ℝ)*X 2 0+(3861728751/10000000000 : ℝ)*X 2 1+(4080469029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318029_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15897/2000 : ℝ) < ((-7299/4000 : ℝ)*P 0+(-7299/4000 : ℝ)*P 1+(-7299/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15897/2000 : ℝ) < (-146405021297837678439940291865460939/18612559551387500000000000000000000 : ℝ) := by norm_num
    linear_combination (447/500000000000 : ℝ)*(base8) + (14839/1000000000000 : ℝ)*(base11) + (166714648671/1000000000000 : ℝ)*(base40) + (335875967721/1000000000000 : ℝ)*(base49) + (151556501649/250000000000 : ℝ)*(base50) + (176989273361/500000000000 : ℝ)*(base59) + (7299/4000 : ℝ)*(major_s1_0) + (1824750005921/1000000000000 : ℝ)*(major_s1_1) + (7299/4000 : ℝ)*(major_s1_2) + (2621975398619/1000000000000 : ℝ)*(sp_s1_0) + (2621975408527/1000000000000 : ℝ)*(sp_s1_1) + (163873463397/62500000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2621975408431/1000000000000 : ℝ)*(f.sum) + (940833029058796899/4915342700000000000000000000000 : ℝ)*base62 + (3909317732989/25352500000000000000000000 : ℝ)*base64 + (75218573355951/121175000000000000000000000 : ℝ)*base67 + (2435064533148137/25352500000000000000000000 : ℝ)*base68 + (24062283079102011/384001641250000000000000000000 : ℝ)*base71 + (2842073999539/7573250000000000000000000 : ℝ)*base73 + (149108896270241/484700000000000000000000000 : ℝ)*base75 + (3065034137687/4733281250000000000000000 : ℝ)*base76 + (3356839451611656043/3670754275000000000000000000000 : ℝ)*base79 + (5921/1000000000000 : ℝ)*base81 + (3/31250000000 : ℝ)*base83 + (5921/1000000000000 : ℝ)*base85 + (5921/1000000000000 : ℝ)*base88 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p018_b013 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 29 ≤ c.val) (hhi : c.val < 30)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=29 := by omega
  rcases hc with rfl
  · exact collision_c318029 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 29 ≤ c.val) (hhi : c.val < 30)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p018_b013 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

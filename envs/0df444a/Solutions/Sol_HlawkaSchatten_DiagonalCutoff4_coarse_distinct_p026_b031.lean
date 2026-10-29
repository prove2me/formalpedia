-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b031
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:09:31.60083+00:00
-- url     : https://prove2.me/submissions/a38adc84-ff7e-4ee5-8070-d5deae6252d1

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
theorem collision_support_c326059_s0_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-583841617/2000000000 : ℝ)*x 0 + (2919207337/10000000000 : ℝ)*x 1 + (6162829111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (583841617/2000000000 : ℝ)^89 ≤ (5571894460981/25000000000000 : ℝ)^73 := by
    have hnat : (583841617 : ℕ)^89*25000000000000^73 ≤ 5571894460981^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583841617 2000000000 5571894460981 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2919207337/10000000000 : ℝ)^89 ≤ (22287570881403/100000000000000 : ℝ)^73 := by
    have hnat : (2919207337 : ℕ)^89*100000000000000^73 ≤ 22287570881403^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2919207337 10000000000 22287570881403 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6162829111/10000000000 : ℝ)^89 ≤ (55424851271167/100000000000000 : ℝ)^73 := by
    have hnat : (6162829111 : ℕ)^89*100000000000000^73 ≤ 55424851271167^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6162829111 10000000000 55424851271167 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-583841617/2000000000 : ℝ), (2919207337/10000000000 : ℝ), (6162829111/10000000000 : ℝ)] ![(5571894460981/25000000000000 : ℝ), (22287570881403/100000000000000 : ℝ), (55424851271167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-583841617/2000000000 : ℝ)|^89 ≤ (5571894460981/25000000000000 : ℝ)^73
        have hw : |(-583841617/2000000000 : ℝ)|=(583841617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2919207337/10000000000 : ℝ)|^89 ≤ (22287570881403/100000000000000 : ℝ)^73
        have hw : |(2919207337/10000000000 : ℝ)|=(2919207337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6162829111/10000000000 : ℝ)|^89 ≤ (55424851271167/100000000000000 : ℝ)^73
        have hw : |(6162829111/10000000000 : ℝ)|=(6162829111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s0_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1459603831/5000000000 : ℝ)*x 0 + (-583841333/2000000000 : ℝ)*x 1 + (154070751/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1459603831/5000000000 : ℝ)^89 ≤ (11143786953281/50000000000000 : ℝ)^73 := by
    have hnat : (1459603831 : ℕ)^89*50000000000000^73 ≤ 11143786953281^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459603831 5000000000 11143786953281 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (583841333/2000000000 : ℝ)^89 ≤ (22287564626303/100000000000000 : ℝ)^73 := by
    have hnat : (583841333 : ℕ)^89*100000000000000^73 ≤ 22287564626303^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583841333 2000000000 22287564626303 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (154070751/250000000 : ℝ)^89 ≤ (13856215364313/25000000000000 : ℝ)^73 := by
    have hnat : (154070751 : ℕ)^89*25000000000000^73 ≤ 13856215364313^73*250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154070751 250000000 13856215364313 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1459603831/5000000000 : ℝ), (-583841333/2000000000 : ℝ), (154070751/250000000 : ℝ)] ![(11143786953281/50000000000000 : ℝ), (22287564626303/100000000000000 : ℝ), (13856215364313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1459603831/5000000000 : ℝ)|^89 ≤ (11143786953281/50000000000000 : ℝ)^73
        have hw : |(1459603831/5000000000 : ℝ)|=(1459603831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-583841333/2000000000 : ℝ)|^89 ≤ (22287564626303/100000000000000 : ℝ)^73
        have hw : |(-583841333/2000000000 : ℝ)|=(583841333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(154070751/250000000 : ℝ)|^89 ≤ (13856215364313/25000000000000 : ℝ)^73
        have hw : |(154070751/250000000 : ℝ)|=(154070751/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s0_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2895450431/10000000000 : ℝ)*x 0 + (1270646447/2000000000 : ℝ)*x 1 + (543266237/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2895450431/10000000000 : ℝ)^89 ≤ (2206663487547/10000000000000 : ℝ)^73 := by
    have hnat : (2895450431 : ℕ)^89*10000000000000^73 ≤ 2206663487547^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2895450431 10000000000 2206663487547 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270646447/2000000000 : ℝ)^89 ≤ (11503910369309/20000000000000 : ℝ)^73 := by
    have hnat : (1270646447 : ℕ)^89*20000000000000^73 ≤ 11503910369309^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270646447 2000000000 11503910369309 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543266237/2000000000 : ℝ)^89 ≤ (20413813257779/100000000000000 : ℝ)^73 := by
    have hnat : (543266237 : ℕ)^89*100000000000000^73 ≤ 20413813257779^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543266237 2000000000 20413813257779 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2895450431/10000000000 : ℝ), (1270646447/2000000000 : ℝ), (543266237/2000000000 : ℝ)] ![(2206663487547/10000000000000 : ℝ), (11503910369309/20000000000000 : ℝ), (20413813257779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2895450431/10000000000 : ℝ)|^89 ≤ (2206663487547/10000000000000 : ℝ)^73
        have hw : |(2895450431/10000000000 : ℝ)|=(2895450431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270646447/2000000000 : ℝ)|^89 ≤ (11503910369309/20000000000000 : ℝ)^73
        have hw : |(1270646447/2000000000 : ℝ)|=(1270646447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543266237/2000000000 : ℝ)|^89 ≤ (20413813257779/100000000000000 : ℝ)^73
        have hw : |(543266237/2000000000 : ℝ)|=(543266237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s0_7 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1133872013/5000000000 : ℝ)*x 0 + (548228927/10000000000 : ℝ)*x 1 + (8388645373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1133872013/5000000000 : ℝ)^89 ≤ (8190763221909/50000000000000 : ℝ)^73 := by
    have hnat : (1133872013 : ℕ)^89*50000000000000^73 ≤ 8190763221909^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133872013 5000000000 8190763221909 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548228927/10000000000 : ℝ)^89 ≤ (2901149072339/100000000000000 : ℝ)^73 := by
    have hnat : (548228927 : ℕ)^89*100000000000000^73 ≤ 2901149072339^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548228927 10000000000 2901149072339 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8388645373/10000000000 : ℝ)^89 ≤ (16143464892643/20000000000000 : ℝ)^73 := by
    have hnat : (8388645373 : ℕ)^89*20000000000000^73 ≤ 16143464892643^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8388645373 10000000000 16143464892643 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1133872013/5000000000 : ℝ), (548228927/10000000000 : ℝ), (8388645373/10000000000 : ℝ)] ![(8190763221909/50000000000000 : ℝ), (2901149072339/100000000000000 : ℝ), (16143464892643/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1133872013/5000000000 : ℝ)|^89 ≤ (8190763221909/50000000000000 : ℝ)^73
        have hw : |(-1133872013/5000000000 : ℝ)|=(1133872013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548228927/10000000000 : ℝ)|^89 ≤ (2901149072339/100000000000000 : ℝ)^73
        have hw : |(548228927/10000000000 : ℝ)|=(548228927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8388645373/10000000000 : ℝ)|^89 ≤ (16143464892643/20000000000000 : ℝ)^73
        have hw : |(8388645373/10000000000 : ℝ)|=(8388645373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s0_8 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (819975883/5000000000 : ℝ)*x 0 + (-80735597/625000000 : ℝ)*x 1 + (4194322313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (819975883/5000000000 : ℝ)^89 ≤ (11034159453741/100000000000000 : ℝ)^73 := by
    have hnat : (819975883 : ℕ)^89*100000000000000^73 ≤ 11034159453741^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819975883 5000000000 11034159453741 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80735597/625000000 : ℝ)^89 ≤ (1031065603879/12500000000000 : ℝ)^73 := by
    have hnat : (80735597 : ℕ)^89*12500000000000^73 ≤ 1031065603879^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80735597 625000000 1031065603879 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4194322313/5000000000 : ℝ)^89 ≤ (5044832231251/6250000000000 : ℝ)^73 := by
    have hnat : (4194322313 : ℕ)^89*6250000000000^73 ≤ 5044832231251^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4194322313 5000000000 5044832231251 6250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(819975883/5000000000 : ℝ), (-80735597/625000000 : ℝ), (4194322313/5000000000 : ℝ)] ![(11034159453741/100000000000000 : ℝ), (1031065603879/12500000000000 : ℝ), (5044832231251/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(819975883/5000000000 : ℝ)|^89 ≤ (11034159453741/100000000000000 : ℝ)^73
        have hw : |(819975883/5000000000 : ℝ)|=(819975883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-80735597/625000000 : ℝ)|^89 ≤ (1031065603879/12500000000000 : ℝ)^73
        have hw : |(-80735597/625000000 : ℝ)|=(80735597/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4194322313/5000000000 : ℝ)|^89 ≤ (5044832231251/6250000000000 : ℝ)^73
        have hw : |(4194322313/5000000000 : ℝ)|=(4194322313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s0_9 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2070792167/5000000000 : ℝ)*x 0 + (7099227601/10000000000 : ℝ)*x 1 + (-2352563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070792167/5000000000 : ℝ)^89 ≤ (8534887629763/25000000000000 : ℝ)^73 := by
    have hnat : (2070792167 : ℕ)^89*25000000000000^73 ≤ 8534887629763^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070792167 5000000000 8534887629763 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7099227601/10000000000 : ℝ)^89 ≤ (16464170038833/25000000000000 : ℝ)^73 := by
    have hnat : (7099227601 : ℕ)^89*25000000000000^73 ≤ 16464170038833^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7099227601 10000000000 16464170038833 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2352563/10000000000 : ℝ)^89 ≤ (753863351/20000000000000 : ℝ)^73 := by
    have hnat : (2352563 : ℕ)^89*20000000000000^73 ≤ 753863351^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2352563 10000000000 753863351 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2070792167/5000000000 : ℝ), (7099227601/10000000000 : ℝ), (-2352563/10000000000 : ℝ)] ![(8534887629763/25000000000000 : ℝ), (16464170038833/25000000000000 : ℝ), (753863351/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2070792167/5000000000 : ℝ)|^89 ≤ (8534887629763/25000000000000 : ℝ)^73
        have hw : |(2070792167/5000000000 : ℝ)|=(2070792167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7099227601/10000000000 : ℝ)|^89 ≤ (16464170038833/25000000000000 : ℝ)^73
        have hw : |(7099227601/10000000000 : ℝ)|=(7099227601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2352563/10000000000 : ℝ)|^89 ≤ (753863351/20000000000000 : ℝ)^73
        have hw : |(-2352563/10000000000 : ℝ)|=(2352563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s0_13 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (194313983/1000000000 : ℝ)*x 0 + (8106723067/10000000000 : ℝ)*x 1 + (694292037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (194313983/1000000000 : ℝ)^89 ≤ (1696171454323/12500000000000 : ℝ)^73 := by
    have hnat : (194313983 : ℕ)^89*12500000000000^73 ≤ 1696171454323^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194313983 1000000000 1696171454323 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8106723067/10000000000 : ℝ)^89 ≤ (77422329306511/100000000000000 : ℝ)^73 := by
    have hnat : (8106723067 : ℕ)^89*100000000000000^73 ≤ 77422329306511^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8106723067 10000000000 77422329306511 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (694292037/5000000000 : ℝ)^89 ≤ (4504149520931/50000000000000 : ℝ)^73 := by
    have hnat : (694292037 : ℕ)^89*50000000000000^73 ≤ 4504149520931^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694292037 5000000000 4504149520931 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(194313983/1000000000 : ℝ), (8106723067/10000000000 : ℝ), (694292037/5000000000 : ℝ)] ![(1696171454323/12500000000000 : ℝ), (77422329306511/100000000000000 : ℝ), (4504149520931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(194313983/1000000000 : ℝ)|^89 ≤ (1696171454323/12500000000000 : ℝ)^73
        have hw : |(194313983/1000000000 : ℝ)|=(194313983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8106723067/10000000000 : ℝ)|^89 ≤ (77422329306511/100000000000000 : ℝ)^73
        have hw : |(8106723067/10000000000 : ℝ)|=(8106723067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(694292037/5000000000 : ℝ)|^89 ≤ (4504149520931/50000000000000 : ℝ)^73
        have hw : |(694292037/5000000000 : ℝ)|=(694292037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s0_14 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-923092101/10000000000 : ℝ)*x 0 + (23818569/125000000 : ℝ)*x 1 + (4218064187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (923092101/10000000000 : ℝ)^89 ≤ (1368955826427/25000000000000 : ℝ)^73 := by
    have hnat : (923092101 : ℕ)^89*25000000000000^73 ≤ 1368955826427^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923092101 10000000000 1368955826427 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23818569/125000000 : ℝ)^89 ≤ (2649895016091/20000000000000 : ℝ)^73 := by
    have hnat : (23818569 : ℕ)^89*20000000000000^73 ≤ 2649895016091^73*125000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23818569 125000000 2649895016091 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4218064187/5000000000 : ℝ)^89 ≤ (81274701598943/100000000000000 : ℝ)^73 := by
    have hnat : (4218064187 : ℕ)^89*100000000000000^73 ≤ 81274701598943^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218064187 5000000000 81274701598943 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-923092101/10000000000 : ℝ), (23818569/125000000 : ℝ), (4218064187/5000000000 : ℝ)] ![(1368955826427/25000000000000 : ℝ), (2649895016091/20000000000000 : ℝ), (81274701598943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-923092101/10000000000 : ℝ)|^89 ≤ (1368955826427/25000000000000 : ℝ)^73
        have hw : |(-923092101/10000000000 : ℝ)|=(923092101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(23818569/125000000 : ℝ)|^89 ≤ (2649895016091/20000000000000 : ℝ)^73
        have hw : |(23818569/125000000 : ℝ)|=(23818569/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4218064187/5000000000 : ℝ)|^89 ≤ (81274701598943/100000000000000 : ℝ)^73
        have hw : |(4218064187/5000000000 : ℝ)|=(4218064187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s0_15 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (834520349/10000000000 : ℝ)*x 0 + (-989958747/5000000000 : ℝ)*x 1 + (8436128259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (834520349/10000000000 : ℝ)^89 ≤ (193686582961/4000000000000 : ℝ)^73 := by
    have hnat : (834520349 : ℕ)^89*4000000000000^73 ≤ 193686582961^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834520349 10000000000 193686582961 4000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (989958747/5000000000 : ℝ)^89 ≤ (13883135157443/100000000000000 : ℝ)^73 := by
    have hnat : (989958747 : ℕ)^89*100000000000000^73 ≤ 13883135157443^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989958747 5000000000 13883135157443 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8436128259/10000000000 : ℝ)^89 ≤ (40637350124093/50000000000000 : ℝ)^73 := by
    have hnat : (8436128259 : ℕ)^89*50000000000000^73 ≤ 40637350124093^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8436128259 10000000000 40637350124093 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(834520349/10000000000 : ℝ), (-989958747/5000000000 : ℝ), (8436128259/10000000000 : ℝ)] ![(193686582961/4000000000000 : ℝ), (13883135157443/100000000000000 : ℝ), (40637350124093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(834520349/10000000000 : ℝ)|^89 ≤ (193686582961/4000000000000 : ℝ)^73
        have hw : |(834520349/10000000000 : ℝ)|=(834520349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-989958747/5000000000 : ℝ)|^89 ≤ (13883135157443/100000000000000 : ℝ)^73
        have hw : |(-989958747/5000000000 : ℝ)|=(989958747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8436128259/10000000000 : ℝ)|^89 ≤ (40637350124093/50000000000000 : ℝ)^73
        have hw : |(8436128259/10000000000 : ℝ)|=(8436128259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s0_16 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8400351597/10000000000 : ℝ)*x 0 + (2577013997/10000000000 : ℝ)*x 1 + (-604059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8400351597/10000000000 : ℝ)^89 ≤ (80854673395227/100000000000000 : ℝ)^73 := by
    have hnat : (8400351597 : ℕ)^89*100000000000000^73 ≤ 80854673395227^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8400351597 10000000000 80854673395227 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2577013997/10000000000 : ℝ)^89 ≤ (9572304083419/50000000000000 : ℝ)^73 := by
    have hnat : (2577013997 : ℕ)^89*50000000000000^73 ≤ 9572304083419^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577013997 10000000000 9572304083419 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (604059/10000000000 : ℝ)^89 ≤ (718429943/100000000000000 : ℝ)^73 := by
    have hnat : (604059 : ℕ)^89*100000000000000^73 ≤ 718429943^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604059 10000000000 718429943 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8400351597/10000000000 : ℝ), (2577013997/10000000000 : ℝ), (-604059/10000000000 : ℝ)] ![(80854673395227/100000000000000 : ℝ), (9572304083419/50000000000000 : ℝ), (718429943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8400351597/10000000000 : ℝ)|^89 ≤ (80854673395227/100000000000000 : ℝ)^73
        have hw : |(8400351597/10000000000 : ℝ)|=(8400351597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2577013997/10000000000 : ℝ)|^89 ≤ (9572304083419/50000000000000 : ℝ)^73
        have hw : |(2577013997/10000000000 : ℝ)|=(2577013997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-604059/10000000000 : ℝ)|^89 ≤ (718429943/100000000000000 : ℝ)^73
        have hw : |(-604059/10000000000 : ℝ)|=(604059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s0_20 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3350797779/5000000000 : ℝ)*x 0 + (3399530101/10000000000 : ℝ)*x 1 + (345984051/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3350797779/5000000000 : ℝ)^89 ≤ (61387548321821/100000000000000 : ℝ)^73 := by
    have hnat : (3350797779 : ℕ)^89*100000000000000^73 ≤ 61387548321821^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3350797779 5000000000 61387548321821 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3399530101/10000000000 : ℝ)^89 ≤ (26835901067051/100000000000000 : ℝ)^73 := by
    have hnat : (3399530101 : ℕ)^89*100000000000000^73 ≤ 26835901067051^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3399530101 10000000000 26835901067051 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345984051/2000000000 : ℝ)^89 ≤ (2944137647317/25000000000000 : ℝ)^73 := by
    have hnat : (345984051 : ℕ)^89*25000000000000^73 ≤ 2944137647317^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345984051 2000000000 2944137647317 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3350797779/5000000000 : ℝ), (3399530101/10000000000 : ℝ), (345984051/2000000000 : ℝ)] ![(61387548321821/100000000000000 : ℝ), (26835901067051/100000000000000 : ℝ), (2944137647317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3350797779/5000000000 : ℝ)|^89 ≤ (61387548321821/100000000000000 : ℝ)^73
        have hw : |(3350797779/5000000000 : ℝ)|=(3350797779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3399530101/10000000000 : ℝ)|^89 ≤ (26835901067051/100000000000000 : ℝ)^73
        have hw : |(3399530101/10000000000 : ℝ)|=(3399530101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(345984051/2000000000 : ℝ)|^89 ≤ (2944137647317/25000000000000 : ℝ)^73
        have hw : |(345984051/2000000000 : ℝ)|=(345984051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s0_21 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5319146171/10000000000 : ℝ)*x 0 + (104256477/500000000 : ℝ)*x 1 + (1152262181/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5319146171/10000000000 : ℝ)^89 ≤ (11579571602341/25000000000000 : ℝ)^73 := by
    have hnat : (5319146171 : ℕ)^89*25000000000000^73 ≤ 11579571602341^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5319146171 10000000000 11579571602341 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104256477/500000000 : ℝ)^89 ≤ (2957548820713/20000000000000 : ℝ)^73 := by
    have hnat : (104256477 : ℕ)^89*20000000000000^73 ≤ 2957548820713^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104256477 500000000 2957548820713 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1152262181/2500000000 : ℝ)^89 ≤ (4861746183463/12500000000000 : ℝ)^73 := by
    have hnat : (1152262181 : ℕ)^89*12500000000000^73 ≤ 4861746183463^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152262181 2500000000 4861746183463 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5319146171/10000000000 : ℝ), (104256477/500000000 : ℝ), (1152262181/2500000000 : ℝ)] ![(11579571602341/25000000000000 : ℝ), (2957548820713/20000000000000 : ℝ), (4861746183463/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5319146171/10000000000 : ℝ)|^89 ≤ (11579571602341/25000000000000 : ℝ)^73
        have hw : |(-5319146171/10000000000 : ℝ)|=(5319146171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104256477/500000000 : ℝ)|^89 ≤ (2957548820713/20000000000000 : ℝ)^73
        have hw : |(104256477/500000000 : ℝ)|=(104256477/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1152262181/2500000000 : ℝ)|^89 ≤ (4861746183463/12500000000000 : ℝ)^73
        have hw : |(1152262181/2500000000 : ℝ)|=(1152262181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s0_22 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1731848113/10000000000 : ℝ)*x 0 + (-479594197/2000000000 : ℝ)*x 1 + (3761131161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1731848113/10000000000 : ℝ)^89 ≤ (737034566679/6250000000000 : ℝ)^73 := by
    have hnat : (1731848113 : ℕ)^89*6250000000000^73 ≤ 737034566679^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1731848113 10000000000 737034566679 6250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (479594197/2000000000 : ℝ)^89 ≤ (17535546466249/100000000000000 : ℝ)^73 := by
    have hnat : (479594197 : ℕ)^89*100000000000000^73 ≤ 17535546466249^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479594197 2000000000 17535546466249 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3761131161/5000000000 : ℝ)^89 ≤ (70671900449143/100000000000000 : ℝ)^73 := by
    have hnat : (3761131161 : ℕ)^89*100000000000000^73 ≤ 70671900449143^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3761131161 5000000000 70671900449143 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1731848113/10000000000 : ℝ), (-479594197/2000000000 : ℝ), (3761131161/5000000000 : ℝ)] ![(737034566679/6250000000000 : ℝ), (17535546466249/100000000000000 : ℝ), (70671900449143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1731848113/10000000000 : ℝ)|^89 ≤ (737034566679/6250000000000 : ℝ)^73
        have hw : |(1731848113/10000000000 : ℝ)|=(1731848113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-479594197/2000000000 : ℝ)|^89 ≤ (17535546466249/100000000000000 : ℝ)^73
        have hw : |(-479594197/2000000000 : ℝ)|=(479594197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3761131161/5000000000 : ℝ)|^89 ≤ (70671900449143/100000000000000 : ℝ)^73
        have hw : |(3761131161/5000000000 : ℝ)|=(3761131161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s0_23 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1698719403/2000000000 : ℝ)*x 0 + (613873597/2500000000 : ℝ)*x 1 + (-7093/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1698719403/2000000000 : ℝ)^89 ≤ (81950214742257/100000000000000 : ℝ)^73 := by
    have hnat : (1698719403 : ℕ)^89*100000000000000^73 ≤ 81950214742257^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1698719403 2000000000 81950214742257 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (613873597/2500000000 : ℝ)^89 ≤ (18049732486631/100000000000000 : ℝ)^73 := by
    have hnat : (613873597 : ℕ)^89*100000000000000^73 ≤ 18049732486631^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613873597 2500000000 18049732486631 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7093/1000000000 : ℝ)^89 ≤ (52752707/100000000000000 : ℝ)^73 := by
    have hnat : (7093 : ℕ)^89*100000000000000^73 ≤ 52752707^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7093 1000000000 52752707 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1698719403/2000000000 : ℝ), (613873597/2500000000 : ℝ), (-7093/1000000000 : ℝ)] ![(81950214742257/100000000000000 : ℝ), (18049732486631/100000000000000 : ℝ), (52752707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1698719403/2000000000 : ℝ)|^89 ≤ (81950214742257/100000000000000 : ℝ)^73
        have hw : |(1698719403/2000000000 : ℝ)|=(1698719403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(613873597/2500000000 : ℝ)|^89 ≤ (18049732486631/100000000000000 : ℝ)^73
        have hw : |(613873597/2500000000 : ℝ)|=(613873597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7093/1000000000 : ℝ)|^89 ≤ (52752707/100000000000000 : ℝ)^73
        have hw : |(-7093/1000000000 : ℝ)|=(7093/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s0_27 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (961051833/10000000000 : ℝ)*x 0 + (8681597273/10000000000 : ℝ)*x 1 + (304573881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (961051833/10000000000 : ℝ)^89 ≤ (2875790288161/50000000000000 : ℝ)^73 := by
    have hnat : (961051833 : ℕ)^89*50000000000000^73 ≤ 2875790288161^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961051833 10000000000 2875790288161 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8681597273/10000000000 : ℝ)^89 ≤ (3366681347723/4000000000000 : ℝ)^73 := by
    have hnat : (8681597273 : ℕ)^89*4000000000000^73 ≤ 3366681347723^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8681597273 10000000000 3366681347723 4000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (304573881/2000000000 : ℝ)^89 ≤ (10081385716927/100000000000000 : ℝ)^73 := by
    have hnat : (304573881 : ℕ)^89*100000000000000^73 ≤ 10081385716927^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304573881 2000000000 10081385716927 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(961051833/10000000000 : ℝ), (8681597273/10000000000 : ℝ), (304573881/2000000000 : ℝ)] ![(2875790288161/50000000000000 : ℝ), (3366681347723/4000000000000 : ℝ), (10081385716927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(961051833/10000000000 : ℝ)|^89 ≤ (2875790288161/50000000000000 : ℝ)^73
        have hw : |(961051833/10000000000 : ℝ)|=(961051833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8681597273/10000000000 : ℝ)|^89 ≤ (3366681347723/4000000000000 : ℝ)^73
        have hw : |(8681597273/10000000000 : ℝ)|=(8681597273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(304573881/2000000000 : ℝ)|^89 ≤ (10081385716927/100000000000000 : ℝ)^73
        have hw : |(304573881/2000000000 : ℝ)|=(304573881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s1_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1612110261/5000000000 : ℝ)*x 0 + (3222564741/10000000000 : ℝ)*x 1 + (1408890237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1612110261/5000000000 : ℝ)^89 ≤ (6289588369427/25000000000000 : ℝ)^73 := by
    have hnat : (1612110261 : ℕ)^89*25000000000000^73 ≤ 6289588369427^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1612110261 5000000000 6289588369427 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3222564741/10000000000 : ℝ)^89 ≤ (5028520532237/20000000000000 : ℝ)^73 := by
    have hnat : (3222564741 : ℕ)^89*20000000000000^73 ≤ 5028520532237^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3222564741 10000000000 5028520532237 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1408890237/2500000000 : ℝ)^89 ≤ (49699043837933/100000000000000 : ℝ)^73 := by
    have hnat : (1408890237 : ℕ)^89*100000000000000^73 ≤ 49699043837933^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1408890237 2500000000 49699043837933 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1612110261/5000000000 : ℝ), (3222564741/10000000000 : ℝ), (1408890237/2500000000 : ℝ)] ![(6289588369427/25000000000000 : ℝ), (5028520532237/20000000000000 : ℝ), (49699043837933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1612110261/5000000000 : ℝ)|^89 ≤ (6289588369427/25000000000000 : ℝ)^73
        have hw : |(-1612110261/5000000000 : ℝ)|=(1612110261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3222564741/10000000000 : ℝ)|^89 ≤ (5028520532237/20000000000000 : ℝ)^73
        have hw : |(3222564741/10000000000 : ℝ)|=(3222564741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1408890237/2500000000 : ℝ)|^89 ≤ (49699043837933/100000000000000 : ℝ)^73
        have hw : |(1408890237/2500000000 : ℝ)|=(1408890237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s1_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (805661189/2500000000 : ℝ)*x 0 + (-644193683/2000000000 : ℝ)*x 1 + (2819183581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (805661189/2500000000 : ℝ)^89 ≤ (12571681886373/50000000000000 : ℝ)^73 := by
    have hnat : (805661189 : ℕ)^89*50000000000000^73 ≤ 12571681886373^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805661189 2500000000 12571681886373 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (644193683/2000000000 : ℝ)^89 ≤ (25127419096811/100000000000000 : ℝ)^73 := by
    have hnat : (644193683 : ℕ)^89*100000000000000^73 ≤ 25127419096811^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644193683 2000000000 25127419096811 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2819183581/5000000000 : ℝ)^89 ≤ (49729217117137/100000000000000 : ℝ)^73 := by
    have hnat : (2819183581 : ℕ)^89*100000000000000^73 ≤ 49729217117137^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2819183581 5000000000 49729217117137 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(805661189/2500000000 : ℝ), (-644193683/2000000000 : ℝ), (2819183581/5000000000 : ℝ)] ![(12571681886373/50000000000000 : ℝ), (25127419096811/100000000000000 : ℝ), (49729217117137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(805661189/2500000000 : ℝ)|^89 ≤ (12571681886373/50000000000000 : ℝ)^73
        have hw : |(805661189/2500000000 : ℝ)|=(805661189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-644193683/2000000000 : ℝ)|^89 ≤ (25127419096811/100000000000000 : ℝ)^73
        have hw : |(-644193683/2000000000 : ℝ)|=(644193683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2819183581/5000000000 : ℝ)|^89 ≤ (49729217117137/100000000000000 : ℝ)^73
        have hw : |(2819183581/5000000000 : ℝ)|=(2819183581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s1_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1371632807/2500000000 : ℝ)*x 0 + (1349212683/2500000000 : ℝ)*x 1 + (-411022683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1371632807/2500000000 : ℝ)^89 ≤ (48101393642057/100000000000000 : ℝ)^73 := by
    have hnat : (1371632807 : ℕ)^89*100000000000000^73 ≤ 48101393642057^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371632807 2500000000 48101393642057 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349212683/2500000000 : ℝ)^89 ≤ (23572272808691/50000000000000 : ℝ)^73 := by
    have hnat : (1349212683 : ℕ)^89*50000000000000^73 ≤ 23572272808691^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349212683 2500000000 23572272808691 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411022683/5000000000 : ℝ)^89 ≤ (2377030362421/50000000000000 : ℝ)^73 := by
    have hnat : (411022683 : ℕ)^89*50000000000000^73 ≤ 2377030362421^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411022683 5000000000 2377030362421 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1371632807/2500000000 : ℝ), (1349212683/2500000000 : ℝ), (-411022683/5000000000 : ℝ)] ![(48101393642057/100000000000000 : ℝ), (23572272808691/50000000000000 : ℝ), (2377030362421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1371632807/2500000000 : ℝ)|^89 ≤ (48101393642057/100000000000000 : ℝ)^73
        have hw : |(1371632807/2500000000 : ℝ)|=(1371632807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349212683/2500000000 : ℝ)|^89 ≤ (23572272808691/50000000000000 : ℝ)^73
        have hw : |(1349212683/2500000000 : ℝ)|=(1349212683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-411022683/5000000000 : ℝ)|^89 ≤ (2377030362421/50000000000000 : ℝ)^73
        have hw : |(-411022683/5000000000 : ℝ)|=(411022683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326059_s1_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (258149089/625000000 : ℝ)*x 0 + (4419731749/10000000000 : ℝ)*x 1 + (3624639451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258149089/625000000 : ℝ)^89 ≤ (17013518412177/50000000000000 : ℝ)^73 := by
    have hnat : (258149089 : ℕ)^89*50000000000000^73 ≤ 17013518412177^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258149089 625000000 17013518412177 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4419731749/10000000000 : ℝ)^89 ≤ (36955107245221/100000000000000 : ℝ)^73 := by
    have hnat : (4419731749 : ℕ)^89*100000000000000^73 ≤ 36955107245221^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419731749 10000000000 36955107245221 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3624639451/10000000000 : ℝ)^89 ≤ (5803571184187/20000000000000 : ℝ)^73 := by
    have hnat : (3624639451 : ℕ)^89*20000000000000^73 ≤ 5803571184187^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3624639451 10000000000 5803571184187 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258149089/625000000 : ℝ), (4419731749/10000000000 : ℝ), (3624639451/10000000000 : ℝ)] ![(17013518412177/50000000000000 : ℝ), (36955107245221/100000000000000 : ℝ), (5803571184187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258149089/625000000 : ℝ)|^89 ≤ (17013518412177/50000000000000 : ℝ)^73
        have hw : |(258149089/625000000 : ℝ)|=(258149089/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4419731749/10000000000 : ℝ)|^89 ≤ (36955107245221/100000000000000 : ℝ)^73
        have hw : |(4419731749/10000000000 : ℝ)|=(4419731749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3624639451/10000000000 : ℝ)|^89 ≤ (5803571184187/20000000000000 : ℝ)^73
        have hw : |(3624639451/10000000000 : ℝ)|=(3624639451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326059 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (163929/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(27191371846757/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(27191371846757/200000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-583841617/2000000000 : ℝ)*X 0 0+(2919207337/10000000000 : ℝ)*X 0 1+(6162829111/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1459603831/5000000000 : ℝ)*X 1 0+(-583841333/2000000000 : ℝ)*X 1 1+(154070751/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((2895450431/10000000000 : ℝ)*X 0 0+(1270646447/2000000000 : ℝ)*X 0 1+(543266237/2000000000 : ℝ)*X 0 2+(2895450431/10000000000 : ℝ)*X 1 0+(1270646447/2000000000 : ℝ)*X 1 1+(543266237/2000000000 : ℝ)*X 1 2+(2895450431/10000000000 : ℝ)*X 2 0+(1270646447/2000000000 : ℝ)*X 2 1+(543266237/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1133872013/5000000000 : ℝ)*X 0 0+(548228927/10000000000 : ℝ)*X 0 1+(8388645373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((819975883/5000000000 : ℝ)*X 1 0+(-80735597/625000000 : ℝ)*X 1 1+(4194322313/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2070792167/5000000000 : ℝ)*X 2 0+(7099227601/10000000000 : ℝ)*X 2 1+(-2352563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((194313983/1000000000 : ℝ)*X 0 0+(8106723067/10000000000 : ℝ)*X 0 1+(694292037/5000000000 : ℝ)*X 0 2+(194313983/1000000000 : ℝ)*X 1 0+(8106723067/10000000000 : ℝ)*X 1 1+(694292037/5000000000 : ℝ)*X 1 2+(194313983/1000000000 : ℝ)*X 2 0+(8106723067/10000000000 : ℝ)*X 2 1+(694292037/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-923092101/10000000000 : ℝ)*X 0 0+(23818569/125000000 : ℝ)*X 0 1+(4218064187/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((834520349/10000000000 : ℝ)*X 1 0+(-989958747/5000000000 : ℝ)*X 1 1+(8436128259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((8400351597/10000000000 : ℝ)*X 2 0+(2577013997/10000000000 : ℝ)*X 2 1+(-604059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((3350797779/5000000000 : ℝ)*X 0 0+(3399530101/10000000000 : ℝ)*X 0 1+(345984051/2000000000 : ℝ)*X 0 2+(3350797779/5000000000 : ℝ)*X 1 0+(3399530101/10000000000 : ℝ)*X 1 1+(345984051/2000000000 : ℝ)*X 1 2+(3350797779/5000000000 : ℝ)*X 2 0+(3399530101/10000000000 : ℝ)*X 2 1+(345984051/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-5319146171/10000000000 : ℝ)*X 0 0+(104256477/500000000 : ℝ)*X 0 1+(1152262181/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1731848113/10000000000 : ℝ)*X 1 0+(-479594197/2000000000 : ℝ)*X 1 1+(3761131161/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1698719403/2000000000 : ℝ)*X 2 0+(613873597/2500000000 : ℝ)*X 2 1+(-7093/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((961051833/10000000000 : ℝ)*X 0 0+(8681597273/10000000000 : ℝ)*X 0 1+(304573881/2000000000 : ℝ)*X 0 2+(961051833/10000000000 : ℝ)*X 1 0+(8681597273/10000000000 : ℝ)*X 1 1+(304573881/2000000000 : ℝ)*X 1 2+(961051833/10000000000 : ℝ)*X 2 0+(8681597273/10000000000 : ℝ)*X 2 1+(304573881/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((16539/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16539/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (47300992820014102202949/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1180199665371/1000000000000 : ℝ)*(base7) + (48827/500000000000 : ℝ)*(base23) + (11229/500000000000 : ℝ)*(base60) + (1505932406139/1000000000000 : ℝ)*(major_s0_0) + (1505932406139/1000000000000 : ℝ)*(major_s0_1) + (1505932406139/1000000000000 : ℝ)*(major_s0_2) + (1660147/1000000000000 : ℝ)*(sp_s0_0) + (6497841/1000000000000 : ℝ)*(sp_s0_6) + (163681232457/100000000000 : ℝ)*(sp_s0_7) + (818433027403/500000000000 : ℝ)*(sp_s0_8) + (51152061161/31250000000 : ℝ)*(sp_s0_9) + (955117257281/500000000000 : ℝ)*(sp_s0_13) + (52070089/1000000000000 : ℝ)*(sp_s0_14) + (54600481/1000000000000 : ℝ)*(sp_s0_27) + (730095947513/1000000000000 : ℝ)*(f.failure) + (818433027403/500000000000 : ℝ)*(f.sum) + (58194813/100000000000000000000 : ℝ)*base62 + (2857489890099017/10000000000000000000000000000 : ℝ)*base65 + (8242430510099017/10000000000000000000000000000 : ℝ)*base67 + (1738145958777/200000000000000000000000000 : ℝ)*base69 + (2732447286839833/10000000000000000000000000000 : ℝ)*base70 + (9083517167099017/10000000000000000000000000000 : ℝ)*base73 + (134084746601223/200000000000000000000000000 : ℝ)*base75 + (208478054961223/200000000000000000000000000 : ℝ)*base77 + (670050500099017/5000000000000000000000000000 : ℝ)*base79 + (26211/20000000000000000 : ℝ)*base86 + (26211/20000000000000000 : ℝ)*base88 + (26211/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(527/800 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(527/800 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13933676505019958876673/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (194438592311/500000000000 : ℝ)*(base5) + (1178750104741/1000000000000 : ℝ)*(base7) + (1036759/500000000000 : ℝ)*(base19) + (261751/1000000000000 : ℝ)*(base53) + (136681643831/1000000000000 : ℝ)*(base60) + (1483600539233/1000000000000 : ℝ)*(major_s0_0) + (1483600539233/1000000000000 : ℝ)*(major_s0_1) + (741800138741/500000000000 : ℝ)*(major_s0_2) + (64406967/1000000000000 : ℝ)*(sp_s0_8) + (200477823667/125000000000 : ℝ)*(sp_s0_14) + (32075122177/20000000000 : ℝ)*(sp_s0_15) + (1992471814679/1000000000000 : ℝ)*(sp_s0_16) + (754571041601/500000000000 : ℝ)*(sp_s0_20) + (228221029/1000000000000 : ℝ)*(sp_s0_23) + (719269163083/1000000000000 : ℝ)*(f.failure) + (801911425543/500000000000 : ℝ)*(f.sum) + (49548624891507/200000000000000000000000000 : ℝ)*base63 + (3443092839487623/5000000000000000000000000000 : ℝ)*base65 + (1268643807214101/10000000000000000000000000000 : ℝ)*base66 + (67056418207063/100000000000000000000000000 : ℝ)*base69 + (327012899855537/1250000000000000000000000000 : ℝ)*base71 + (7344274364785899/10000000000000000000000000000 : ℝ)*base73 + (47901492037381/200000000000000000000000000 : ℝ)*base75 + (78668029977381/200000000000000000000000000 : ℝ)*base77 + (138688627285899/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (2999/20000000000000000 : ℝ)*base87 + (2999/20000000000000000 : ℝ)*base89 + (2999/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(48049/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(48049/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6359839388008753052451/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (611753810889/1000000000000 : ℝ)*(base7) + (163103/100000000000 : ℝ)*(base40) + (568400040011/1000000000000 : ℝ)*(base44) + (49659825989/500000000000 : ℝ)*(base50) + (763762754789/500000000000 : ℝ)*(major_s0_0) + (959125469567/1000000000000 : ℝ)*(major_s0_1) + (763762754789/500000000000 : ℝ)*(major_s0_2) + (33112007/1000000000000 : ℝ)*(sp_s0_1) + (6216287/250000000000 : ℝ)*(sp_s0_13) + (153229607/1000000000000 : ℝ)*(sp_s0_16) + (990101847339/500000000000 : ℝ)*(sp_s0_21) + (70588527133/50000000000 : ℝ)*(sp_s0_22) + (1980050465071/1000000000000 : ℝ)*(sp_s0_23) + (6271147803/8000000000 : ℝ)*(sp_s0_27) + (148112913929/200000000000 : ℝ)*(f.failure) + (990101847339/500000000000 : ℝ)*(f.sum) + (26757346134327/200000000000000000000000000 : ℝ)*base62 + (1956473875145033/5000000000000000000000000000 : ℝ)*base64 + (2622213624239499/10000000000000000000000000000 : ℝ)*base66 + (17058230159273/100000000000000000000000000 : ℝ)*base68 + (677377355818617/5000000000000000000000000000 : ℝ)*base71 + (2590269983145033/5000000000000000000000000000 : ℝ)*base72 + (20673462035781/200000000000000000000000000 : ℝ)*base74 + (4544844310727/100000000000000000000000000 : ℝ)*base76 + (883160049705913/2000000000000000000000000000 : ℝ)*base78 + (1037/4000000000000000 : ℝ)*base87 + (1037/4000000000000000 : ℝ)*base89 + (1037/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (16539/25000 : ℝ) ^ (87/16 : ℝ) ≤ (5288289705234678467/50000000000000000000 : ℝ) := by
    have hpowers : (16539/25000 : ℝ)^87 ≤ (5288289705234678467/50000000000000000000 : ℝ)^16 := by
      have hnat : (16539 : ℕ)^87*50000000000000000000^16 ≤ 5288289705234678467^16*25000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16539 25000 5288289705234678467 50000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16539/25000 : ℝ)) (X := (5288289705234678467/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (55288289705234678467/50000000000000000000 : ℝ) ≤ (5093308818130171/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (55288289705234678467/50000000000000000000 : ℝ)^16 ≤ (5093308818130171/5000000000000000 : ℝ)^87 := by
      have hnat : (55288289705234678467 : ℕ)^16*5000000000000000^87 ≤ 5093308818130171^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55288289705234678467 50000000000000000000 5093308818130171 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5093308818130171/5000000000000000 : ℝ)) (X := (55288289705234678467/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (30288289705234678467/25000000000000000000 : ℝ) ≤ (5179596561544239/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (30288289705234678467/25000000000000000000 : ℝ)^16 ≤ (5179596561544239/5000000000000000 : ℝ)^87 := by
      have hnat : (30288289705234678467 : ℕ)^16*5000000000000000^87 ≤ 5179596561544239^87*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30288289705234678467 25000000000000000000 5179596561544239 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5179596561544239/5000000000000000 : ℝ)) (X := (30288289705234678467/25000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(93308818130171/3307800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(21571935853517/826950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (16539/25000 : ℝ)) (alpha := (93308818130171/3307800000000000 : ℝ)) (beta := (21571935853517/826950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (16539/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(93308818130171/3307800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(21571935853517/826950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (527/800 : ℝ) ^ (87/16 : ℝ) ≤ (5167296954071785879/50000000000000000000 : ℝ) := by
    have hpowers : (527/800 : ℝ)^87 ≤ (5167296954071785879/50000000000000000000 : ℝ)^16 := by
      have hnat : (527 : ℕ)^87*50000000000000000000^16 ≤ 5167296954071785879^16*800^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        527 800 5167296954071785879 50000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (527/800 : ℝ)) (X := (5167296954071785879/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (55167296954071785879/50000000000000000000 : ℝ) ≤ (1272814278081439/1250000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (55167296954071785879/50000000000000000000 : ℝ)^16 ≤ (1272814278081439/1250000000000000 : ℝ)^87 := by
      have hnat : (55167296954071785879 : ℕ)^16*1250000000000000^87 ≤ 1272814278081439^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55167296954071785879 50000000000000000000 1272814278081439 1250000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1272814278081439/1250000000000000 : ℝ)) (X := (55167296954071785879/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (30167296954071785879/25000000000000000000 : ℝ) ≤ (414062808863249/400000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (30167296954071785879/25000000000000000000 : ℝ)^16 ≤ (414062808863249/400000000000000 : ℝ)^87 := by
      have hnat : (30167296954071785879 : ℕ)^16*400000000000000^87 ≤ 414062808863249^87*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30167296954071785879 25000000000000000000 414062808863249 400000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (414062808863249/400000000000000 : ℝ)) (X := (30167296954071785879/25000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(22814278081439/823437500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(169055996929713/6587500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (527/800 : ℝ)) (alpha := (22814278081439/823437500000000 : ℝ)) (beta := (169055996929713/6587500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (527/800 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(22814278081439/823437500000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(169055996929713/6587500000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (48049/100000 : ℝ) ^ (87/16 : ℝ) ≤ (464620834980665221/25000000000000000000 : ℝ) := by
    have hpowers : (48049/100000 : ℝ)^87 ≤ (464620834980665221/25000000000000000000 : ℝ)^16 := by
      have hnat : (48049 : ℕ)^87*25000000000000000000^16 ≤ 464620834980665221^16*100000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48049 100000 464620834980665221 25000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48049/100000 : ℝ)) (X := (464620834980665221/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25464620834980665221/25000000000000000000 : ℝ) ≤ (2006784537419941/2000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (25464620834980665221/25000000000000000000 : ℝ)^16 ≤ (2006784537419941/2000000000000000 : ℝ)^87 := by
      have hnat : (25464620834980665221 : ℕ)^16*2000000000000000^87 ≤ 2006784537419941^87*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25464620834980665221 25000000000000000000 2006784537419941 2000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2006784537419941/2000000000000000 : ℝ)) (X := (25464620834980665221/25000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12964620834980665221/12500000000000000000 : ℝ) ≤ (2013468792344359/2000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (12964620834980665221/12500000000000000000 : ℝ)^16 ≤ (2013468792344359/2000000000000000 : ℝ)^87 := by
      have hnat : (12964620834980665221 : ℕ)^16*2000000000000000^87 ≤ 2013468792344359^87*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12964620834980665221 12500000000000000000 2013468792344359 2000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2013468792344359/2000000000000000 : ℝ)) (X := (12964620834980665221/12500000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(6784537419941/960980000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(3342127462209/480490000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (48049/100000 : ℝ)) (alpha := (6784537419941/960980000000000 : ℝ)) (beta := (3342127462209/480490000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (48049/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(6784537419941/960980000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(3342127462209/480490000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1612110261/5000000000 : ℝ)*X 0 0+(3222564741/10000000000 : ℝ)*X 0 1+(1408890237/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((805661189/2500000000 : ℝ)*X 1 0+(-644193683/2000000000 : ℝ)*X 1 1+(2819183581/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1371632807/2500000000 : ℝ)*X 2 0+(1349212683/2500000000 : ℝ)*X 2 1+(-411022683/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((258149089/625000000 : ℝ)*X 0 0+(4419731749/10000000000 : ℝ)*X 0 1+(3624639451/10000000000 : ℝ)*X 0 2+(258149089/625000000 : ℝ)*X 1 0+(4419731749/10000000000 : ℝ)*X 1 1+(3624639451/10000000000 : ℝ)*X 1 2+(258149089/625000000 : ℝ)*X 2 0+(4419731749/10000000000 : ℝ)*X 2 1+(3624639451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326059_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-93759/10000 : ℝ) < ((-41253/20000 : ℝ)*P 0+(-41253/20000 : ℝ)*P 1+(-41253/20000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-93759/10000 : ℝ) < (-65140142419710062310959858129780387/6979960509950000000000000000000000 : ℝ) := by norm_num
    linear_combination (371909/1000000000000 : ℝ)*(base13) + (212263/1000000000000 : ℝ)*(base15) + (104523/500000000000 : ℝ)*(base16) + (26311/500000000000 : ℝ)*(base33) + (9413/500000000000 : ℝ)*(base39) + (27453/1000000000000 : ℝ)*(base50) + (57973/1000000000000 : ℝ)*(base59) + (632543141447/1000000000000 : ℝ)*(base60) + (1031324973689/500000000000 : ℝ)*(major_s1_0) + (41253/20000 : ℝ)*(major_s1_1) + (41253/20000 : ℝ)*(major_s1_2) + (97213024073/31250000000 : ℝ)*(sp_s1_0) + (1555408334157/500000000000 : ℝ)*(sp_s1_1) + (3110817089623/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (622163428449/200000000000 : ℝ)*(f.sum) + (854440056021561/989133710937500000000000000 : ℝ)*base63 + (946131853943/15015312500000000000000000 : ℝ)*base65 + (37647774129/82343750000000000000000 : ℝ)*base66 + (9568294870023/60061250000000000000000000 : ℝ)*base69 + (1550620458102523769/79468241100000000000000000000000 : ℝ)*base70 + (167284384415417/413475000000000000000000000 : ℝ)*base72 + (762230811953/1317500000000000000000000 : ℝ)*base75 + (336736553943221/1653900000000000000000000000 : ℝ)*base76 + (318087479738447/425588525390625000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p026_b031 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 59 ≤ c.val) (hhi : c.val < 60)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=59 := by omega
  rcases hc with rfl
  · exact collision_c326059 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 59 ≤ c.val) (hhi : c.val < 60)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b031 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

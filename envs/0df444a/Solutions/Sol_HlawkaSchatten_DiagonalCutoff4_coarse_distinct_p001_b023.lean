-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b023
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:17:20.466894+00:00
-- url     : https://prove2.me/submissions/cf60b8a4-e4a7-47f1-a748-ce968729faca

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
theorem collision_support_c301041_s0_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7560459469/10000000000 : ℝ)*x 0 + (-2619790799/10000000000 : ℝ)*x 1 + (-1140443633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7560459469/10000000000 : ℝ)^65 ≤ (34503286138507/50000000000000 : ℝ)^49 := by
    have hnat : (7560459469 : ℕ)^65*50000000000000^49 ≤ 34503286138507^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7560459469 10000000000 34503286138507 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619790799/10000000000 : ℝ)^65 ≤ (1057286947321/6250000000000 : ℝ)^49 := by
    have hnat : (2619790799 : ℕ)^65*6250000000000^49 ≤ 1057286947321^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619790799 10000000000 1057286947321 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140443633/5000000000 : ℝ)^65 ≤ (14076836556267/100000000000000 : ℝ)^49 := by
    have hnat : (1140443633 : ℕ)^65*100000000000000^49 ≤ 14076836556267^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140443633 5000000000 14076836556267 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7560459469/10000000000 : ℝ), (-2619790799/10000000000 : ℝ), (-1140443633/5000000000 : ℝ)] ![(34503286138507/50000000000000 : ℝ), (1057286947321/6250000000000 : ℝ), (14076836556267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7560459469/10000000000 : ℝ)|^65 ≤ (34503286138507/50000000000000 : ℝ)^49
        have hw : |(7560459469/10000000000 : ℝ)|=(7560459469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2619790799/10000000000 : ℝ)|^65 ≤ (1057286947321/6250000000000 : ℝ)^49
        have hw : |(-2619790799/10000000000 : ℝ)|=(2619790799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1140443633/5000000000 : ℝ)|^65 ≤ (14076836556267/100000000000000 : ℝ)^49
        have hw : |(-1140443633/5000000000 : ℝ)|=(1140443633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s0_3 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1 : ℝ)*x 0 + (0 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1 : ℝ)^65 ≤ (1 : ℝ)^49 := by
    have hnat : (1 : ℕ)^65*1^49 ≤ 1^49*1^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^65 ≤ (0 : ℝ)^49 := by
    have hnat : (0 : ℕ)^65*1^49 ≤ 0^49*1^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^65 ≤ (0 : ℝ)^49 := by
    have hnat : (0 : ℕ)^65*1^49 ≤ 0^49*1^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1 : ℝ)|^65 ≤ (1 : ℝ)^49
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^65 ≤ (0 : ℝ)^49
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^65 ≤ (0 : ℝ)^49
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s0_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-549180939/2000000000 : ℝ)*x 0 + (-5769522897/10000000000 : ℝ)*x 1 + (4412855803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549180939/2000000000 : ℝ)^65 ≤ (18005246818707/100000000000000 : ℝ)^49 := by
    have hnat : (549180939 : ℕ)^65*100000000000000^49 ≤ 18005246818707^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549180939 2000000000 18005246818707 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5769522897/10000000000 : ℝ)^65 ≤ (24105423801149/50000000000000 : ℝ)^49 := by
    have hnat : (5769522897 : ℕ)^65*50000000000000^49 ≤ 24105423801149^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5769522897 10000000000 24105423801149 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4412855803/10000000000 : ℝ)^65 ≤ (16891952782121/50000000000000 : ℝ)^49 := by
    have hnat : (4412855803 : ℕ)^65*50000000000000^49 ≤ 16891952782121^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412855803 10000000000 16891952782121 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549180939/2000000000 : ℝ), (-5769522897/10000000000 : ℝ), (4412855803/10000000000 : ℝ)] ![(18005246818707/100000000000000 : ℝ), (24105423801149/50000000000000 : ℝ), (16891952782121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549180939/2000000000 : ℝ)|^65 ≤ (18005246818707/100000000000000 : ℝ)^49
        have hw : |(-549180939/2000000000 : ℝ)|=(549180939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5769522897/10000000000 : ℝ)|^65 ≤ (24105423801149/50000000000000 : ℝ)^49
        have hw : |(-5769522897/10000000000 : ℝ)|=(5769522897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4412855803/10000000000 : ℝ)|^65 ≤ (16891952782121/50000000000000 : ℝ)^49
        have hw : |(4412855803/10000000000 : ℝ)|=(4412855803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s0_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2426287377/10000000000 : ℝ)*x 0 + (5484408037/10000000000 : ℝ)*x 1 + (248920363/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2426287377/10000000000 : ℝ)^65 ≤ (15279426420477/100000000000000 : ℝ)^49 := by
    have hnat : (2426287377 : ℕ)^65*100000000000000^49 ≤ 15279426420477^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2426287377 10000000000 15279426420477 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5484408037/10000000000 : ℝ)^65 ≤ (22538117737781/50000000000000 : ℝ)^49 := by
    have hnat : (5484408037 : ℕ)^65*50000000000000^49 ≤ 22538117737781^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484408037 10000000000 22538117737781 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248920363/500000000 : ℝ)^65 ≤ (19822169042447/50000000000000 : ℝ)^49 := by
    have hnat : (248920363 : ℕ)^65*50000000000000^49 ≤ 19822169042447^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248920363 500000000 19822169042447 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2426287377/10000000000 : ℝ), (5484408037/10000000000 : ℝ), (248920363/500000000 : ℝ)] ![(15279426420477/100000000000000 : ℝ), (22538117737781/50000000000000 : ℝ), (19822169042447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2426287377/10000000000 : ℝ)|^65 ≤ (15279426420477/100000000000000 : ℝ)^49
        have hw : |(2426287377/10000000000 : ℝ)|=(2426287377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5484408037/10000000000 : ℝ)|^65 ≤ (22538117737781/50000000000000 : ℝ)^49
        have hw : |(5484408037/10000000000 : ℝ)|=(5484408037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(248920363/500000000 : ℝ)|^65 ≤ (19822169042447/50000000000000 : ℝ)^49
        have hw : |(248920363/500000000 : ℝ)|=(248920363/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s0_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7501539881/10000000000 : ℝ)*x 0 + (-2648057613/10000000000 : ℝ)*x 1 + (-2338053431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7501539881/10000000000 : ℝ)^65 ≤ (68294104301949/100000000000000 : ℝ)^49 := by
    have hnat : (7501539881 : ℕ)^65*100000000000000^49 ≤ 68294104301949^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7501539881 10000000000 68294104301949 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2648057613/10000000000 : ℝ)^65 ≤ (2144892758623/12500000000000 : ℝ)^49 := by
    have hnat : (2648057613 : ℕ)^65*12500000000000^49 ≤ 2144892758623^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648057613 10000000000 2144892758623 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2338053431/10000000000 : ℝ)^65 ≤ (14546753611939/100000000000000 : ℝ)^49 := by
    have hnat : (2338053431 : ℕ)^65*100000000000000^49 ≤ 14546753611939^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2338053431 10000000000 14546753611939 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7501539881/10000000000 : ℝ), (-2648057613/10000000000 : ℝ), (-2338053431/10000000000 : ℝ)] ![(68294104301949/100000000000000 : ℝ), (2144892758623/12500000000000 : ℝ), (14546753611939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7501539881/10000000000 : ℝ)|^65 ≤ (68294104301949/100000000000000 : ℝ)^49
        have hw : |(7501539881/10000000000 : ℝ)|=(7501539881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2648057613/10000000000 : ℝ)|^65 ≤ (2144892758623/12500000000000 : ℝ)^49
        have hw : |(-2648057613/10000000000 : ℝ)|=(2648057613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2338053431/10000000000 : ℝ)|^65 ≤ (14546753611939/100000000000000 : ℝ)^49
        have hw : |(-2338053431/10000000000 : ℝ)|=(2338053431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s0_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (377968223/1000000000 : ℝ)*x 0 + (-471607229/2000000000 : ℝ)*x 1 + (1653291283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (377968223/1000000000 : ℝ)^65 ≤ (27509424538549/100000000000000 : ℝ)^49 := by
    have hnat : (377968223 : ℕ)^65*100000000000000^49 ≤ 27509424538549^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377968223 1000000000 27509424538549 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (471607229/2000000000 : ℝ)^65 ≤ (1838988391229/12500000000000 : ℝ)^49 := by
    have hnat : (471607229 : ℕ)^65*12500000000000^49 ≤ 1838988391229^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471607229 2000000000 1838988391229 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1653291283/2500000000 : ℝ)^65 ≤ (28889334157831/50000000000000 : ℝ)^49 := by
    have hnat : (1653291283 : ℕ)^65*50000000000000^49 ≤ 28889334157831^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1653291283 2500000000 28889334157831 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(377968223/1000000000 : ℝ), (-471607229/2000000000 : ℝ), (1653291283/2500000000 : ℝ)] ![(27509424538549/100000000000000 : ℝ), (1838988391229/12500000000000 : ℝ), (28889334157831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(377968223/1000000000 : ℝ)|^65 ≤ (27509424538549/100000000000000 : ℝ)^49
        have hw : |(377968223/1000000000 : ℝ)|=(377968223/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-471607229/2000000000 : ℝ)|^65 ≤ (1838988391229/12500000000000 : ℝ)^49
        have hw : |(-471607229/2000000000 : ℝ)|=(471607229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1653291283/2500000000 : ℝ)|^65 ≤ (28889334157831/50000000000000 : ℝ)^49
        have hw : |(1653291283/2500000000 : ℝ)|=(1653291283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s0_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-67715153/312500000 : ℝ)*x 0 + (-2287533357/5000000000 : ℝ)*x 1 + (3027818289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67715153/312500000 : ℝ)^65 ≤ (13151216077447/100000000000000 : ℝ)^49 := by
    have hnat : (67715153 : ℕ)^65*100000000000000^49 ≤ 13151216077447^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67715153 312500000 13151216077447 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2287533357/5000000000 : ℝ)^65 ≤ (17720533838321/50000000000000 : ℝ)^49 := by
    have hnat : (2287533357 : ℕ)^65*50000000000000^49 ≤ 17720533838321^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287533357 5000000000 17720533838321 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3027818289/5000000000 : ℝ)^65 ≤ (1028154324547/2000000000000 : ℝ)^49 := by
    have hnat : (3027818289 : ℕ)^65*2000000000000^49 ≤ 1028154324547^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3027818289 5000000000 1028154324547 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67715153/312500000 : ℝ), (-2287533357/5000000000 : ℝ), (3027818289/5000000000 : ℝ)] ![(13151216077447/100000000000000 : ℝ), (17720533838321/50000000000000 : ℝ), (1028154324547/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67715153/312500000 : ℝ)|^65 ≤ (13151216077447/100000000000000 : ℝ)^49
        have hw : |(-67715153/312500000 : ℝ)|=(67715153/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2287533357/5000000000 : ℝ)|^65 ≤ (17720533838321/50000000000000 : ℝ)^49
        have hw : |(-2287533357/5000000000 : ℝ)|=(2287533357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3027818289/5000000000 : ℝ)|^65 ≤ (1028154324547/2000000000000 : ℝ)^49
        have hw : |(3027818289/5000000000 : ℝ)|=(3027818289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s0_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1088614431/5000000000 : ℝ)*x 0 + (5724966237/10000000000 : ℝ)*x 1 + (4921836493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088614431/5000000000 : ℝ)^65 ≤ (1654319963517/12500000000000 : ℝ)^49 := by
    have hnat : (1088614431 : ℕ)^65*12500000000000^49 ≤ 1654319963517^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088614431 5000000000 1654319963517 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5724966237/10000000000 : ℝ)^65 ≤ (190870305029/400000000000 : ℝ)^49 := by
    have hnat : (5724966237 : ℕ)^65*400000000000^49 ≤ 190870305029^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5724966237 10000000000 190870305029 400000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4921836493/10000000000 : ℝ)^65 ≤ (97619660053/250000000000 : ℝ)^49 := by
    have hnat : (4921836493 : ℕ)^65*250000000000^49 ≤ 97619660053^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4921836493 10000000000 97619660053 250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088614431/5000000000 : ℝ), (5724966237/10000000000 : ℝ), (4921836493/10000000000 : ℝ)] ![(1654319963517/12500000000000 : ℝ), (190870305029/400000000000 : ℝ), (97619660053/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088614431/5000000000 : ℝ)|^65 ≤ (1654319963517/12500000000000 : ℝ)^49
        have hw : |(1088614431/5000000000 : ℝ)|=(1088614431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5724966237/10000000000 : ℝ)|^65 ≤ (190870305029/400000000000 : ℝ)^49
        have hw : |(5724966237/10000000000 : ℝ)|=(5724966237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4921836493/10000000000 : ℝ)|^65 ≤ (97619660053/250000000000 : ℝ)^49
        have hw : |(4921836493/10000000000 : ℝ)|=(4921836493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s0_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2095325471/2500000000 : ℝ)*x 0 + (-1956486987/10000000000 : ℝ)*x 1 + (-841010117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095325471/2500000000 : ℝ)^65 ≤ (791170955319/1000000000000 : ℝ)^49 := by
    have hnat : (2095325471 : ℕ)^65*1000000000000^49 ≤ 791170955319^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095325471 2500000000 791170955319 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1956486987/10000000000 : ℝ)^65 ≤ (2871193826261/25000000000000 : ℝ)^49 := by
    have hnat : (1956486987 : ℕ)^65*25000000000000^49 ≤ 2871193826261^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956486987 10000000000 2871193826261 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (841010117/5000000000 : ℝ)^65 ≤ (9398129149311/100000000000000 : ℝ)^49 := by
    have hnat : (841010117 : ℕ)^65*100000000000000^49 ≤ 9398129149311^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841010117 5000000000 9398129149311 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2095325471/2500000000 : ℝ), (-1956486987/10000000000 : ℝ), (-841010117/5000000000 : ℝ)] ![(791170955319/1000000000000 : ℝ), (2871193826261/25000000000000 : ℝ), (9398129149311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2095325471/2500000000 : ℝ)|^65 ≤ (791170955319/1000000000000 : ℝ)^49
        have hw : |(2095325471/2500000000 : ℝ)|=(2095325471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1956486987/10000000000 : ℝ)|^65 ≤ (2871193826261/25000000000000 : ℝ)^49
        have hw : |(-1956486987/10000000000 : ℝ)|=(1956486987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-841010117/5000000000 : ℝ)|^65 ≤ (9398129149311/100000000000000 : ℝ)^49
        have hw : |(-841010117/5000000000 : ℝ)|=(841010117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s0_19 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2331164801/5000000000 : ℝ)*x 0 + (-1809976159/5000000000 : ℝ)*x 1 + (2395715411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2331164801/5000000000 : ℝ)^65 ≤ (7268113387809/20000000000000 : ℝ)^49 := by
    have hnat : (2331164801 : ℕ)^65*20000000000000^49 ≤ 7268113387809^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2331164801 5000000000 7268113387809 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1809976159/5000000000 : ℝ)^65 ≤ (25978006521453/100000000000000 : ℝ)^49 := by
    have hnat : (1809976159 : ℕ)^65*100000000000000^49 ≤ 25978006521453^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1809976159 5000000000 25978006521453 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2395715411/5000000000 : ℝ)^65 ≤ (18840713257909/50000000000000 : ℝ)^49 := by
    have hnat : (2395715411 : ℕ)^65*50000000000000^49 ≤ 18840713257909^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395715411 5000000000 18840713257909 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2331164801/5000000000 : ℝ), (-1809976159/5000000000 : ℝ), (2395715411/5000000000 : ℝ)] ![(7268113387809/20000000000000 : ℝ), (25978006521453/100000000000000 : ℝ), (18840713257909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2331164801/5000000000 : ℝ)|^65 ≤ (7268113387809/20000000000000 : ℝ)^49
        have hw : |(2331164801/5000000000 : ℝ)|=(2331164801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1809976159/5000000000 : ℝ)|^65 ≤ (25978006521453/100000000000000 : ℝ)^49
        have hw : |(-1809976159/5000000000 : ℝ)|=(1809976159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2395715411/5000000000 : ℝ)|^65 ≤ (18840713257909/50000000000000 : ℝ)^49
        have hw : |(2395715411/5000000000 : ℝ)|=(2395715411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s0_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-56323517/200000000 : ℝ)*x 0 + (-104867643/200000000 : ℝ)*x 1 + (2454533781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56323517/200000000 : ℝ)^65 ≤ (9309510411059/50000000000000 : ℝ)^49 := by
    have hnat : (56323517 : ℕ)^65*50000000000000^49 ≤ 9309510411059^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56323517 200000000 9309510411059 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104867643/200000000 : ℝ)^65 ≤ (21233720220491/50000000000000 : ℝ)^49 := by
    have hnat : (104867643 : ℕ)^65*50000000000000^49 ≤ 21233720220491^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104867643 200000000 21233720220491 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2454533781/5000000000 : ℝ)^65 ≤ (38913538721471/100000000000000 : ℝ)^49 := by
    have hnat : (2454533781 : ℕ)^65*100000000000000^49 ≤ 38913538721471^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2454533781 5000000000 38913538721471 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-56323517/200000000 : ℝ), (-104867643/200000000 : ℝ), (2454533781/5000000000 : ℝ)] ![(9309510411059/50000000000000 : ℝ), (21233720220491/50000000000000 : ℝ), (38913538721471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-56323517/200000000 : ℝ)|^65 ≤ (9309510411059/50000000000000 : ℝ)^49
        have hw : |(-56323517/200000000 : ℝ)|=(56323517/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104867643/200000000 : ℝ)|^65 ≤ (21233720220491/50000000000000 : ℝ)^49
        have hw : |(-104867643/200000000 : ℝ)|=(104867643/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2454533781/5000000000 : ℝ)|^65 ≤ (38913538721471/100000000000000 : ℝ)^49
        have hw : |(2454533781/5000000000 : ℝ)|=(2454533781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s0_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2066460809/10000000000 : ℝ)*x 0 + (5637306811/10000000000 : ℝ)*x 1 + (5096847983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066460809/10000000000 : ℝ)^65 ≤ (6174444441333/50000000000000 : ℝ)^49 := by
    have hnat : (2066460809 : ℕ)^65*50000000000000^49 ≤ 6174444441333^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066460809 10000000000 6174444441333 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5637306811/10000000000 : ℝ)^65 ≤ (46750789850011/100000000000000 : ℝ)^49 := by
    have hnat : (5637306811 : ℕ)^65*100000000000000^49 ≤ 46750789850011^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5637306811 10000000000 46750789850011 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5096847983/10000000000 : ℝ)^65 ≤ (10225080313901/25000000000000 : ℝ)^49 := by
    have hnat : (5096847983 : ℕ)^65*25000000000000^49 ≤ 10225080313901^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5096847983 10000000000 10225080313901 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2066460809/10000000000 : ℝ), (5637306811/10000000000 : ℝ), (5096847983/10000000000 : ℝ)] ![(6174444441333/50000000000000 : ℝ), (46750789850011/100000000000000 : ℝ), (10225080313901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2066460809/10000000000 : ℝ)|^65 ≤ (6174444441333/50000000000000 : ℝ)^49
        have hw : |(2066460809/10000000000 : ℝ)|=(2066460809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5637306811/10000000000 : ℝ)|^65 ≤ (46750789850011/100000000000000 : ℝ)^49
        have hw : |(5637306811/10000000000 : ℝ)|=(5637306811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5096847983/10000000000 : ℝ)|^65 ≤ (10225080313901/25000000000000 : ℝ)^49
        have hw : |(5096847983/10000000000 : ℝ)|=(5096847983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s0_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8785424881/10000000000 : ℝ)*x 0 + (-96752627/625000000 : ℝ)*x 1 + (-279925687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8785424881/10000000000 : ℝ)^65 ≤ (1684339323831/2000000000000 : ℝ)^49 := by
    have hnat : (8785424881 : ℕ)^65*2000000000000^49 ≤ 1684339323831^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8785424881 10000000000 1684339323831 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96752627/625000000 : ℝ)^65 ≤ (2104563440603/25000000000000 : ℝ)^49 := by
    have hnat : (96752627 : ℕ)^65*25000000000000^49 ≤ 2104563440603^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96752627 625000000 2104563440603 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279925687/2000000000 : ℝ)^65 ≤ (3682390013751/50000000000000 : ℝ)^49 := by
    have hnat : (279925687 : ℕ)^65*50000000000000^49 ≤ 3682390013751^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279925687 2000000000 3682390013751 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8785424881/10000000000 : ℝ), (-96752627/625000000 : ℝ), (-279925687/2000000000 : ℝ)] ![(1684339323831/2000000000000 : ℝ), (2104563440603/25000000000000 : ℝ), (3682390013751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8785424881/10000000000 : ℝ)|^65 ≤ (1684339323831/2000000000000 : ℝ)^49
        have hw : |(8785424881/10000000000 : ℝ)|=(8785424881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-96752627/625000000 : ℝ)|^65 ≤ (2104563440603/25000000000000 : ℝ)^49
        have hw : |(-96752627/625000000 : ℝ)|=(96752627/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279925687/2000000000 : ℝ)|^65 ≤ (3682390013751/50000000000000 : ℝ)^49
        have hw : |(-279925687/2000000000 : ℝ)|=(279925687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s0_25 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (56323517/200000000 : ℝ)*x 0 + (-104867643/200000000 : ℝ)*x 1 + (2454533781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56323517/200000000 : ℝ)^65 ≤ (9309510411059/50000000000000 : ℝ)^49 := by
    have hnat : (56323517 : ℕ)^65*50000000000000^49 ≤ 9309510411059^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56323517 200000000 9309510411059 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104867643/200000000 : ℝ)^65 ≤ (21233720220491/50000000000000 : ℝ)^49 := by
    have hnat : (104867643 : ℕ)^65*50000000000000^49 ≤ 21233720220491^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104867643 200000000 21233720220491 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2454533781/5000000000 : ℝ)^65 ≤ (38913538721471/100000000000000 : ℝ)^49 := by
    have hnat : (2454533781 : ℕ)^65*100000000000000^49 ≤ 38913538721471^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2454533781 5000000000 38913538721471 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(56323517/200000000 : ℝ), (-104867643/200000000 : ℝ), (2454533781/5000000000 : ℝ)] ![(9309510411059/50000000000000 : ℝ), (21233720220491/50000000000000 : ℝ), (38913538721471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(56323517/200000000 : ℝ)|^65 ≤ (9309510411059/50000000000000 : ℝ)^49
        have hw : |(56323517/200000000 : ℝ)|=(56323517/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104867643/200000000 : ℝ)|^65 ≤ (21233720220491/50000000000000 : ℝ)^49
        have hw : |(-104867643/200000000 : ℝ)|=(104867643/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2454533781/5000000000 : ℝ)|^65 ≤ (38913538721471/100000000000000 : ℝ)^49
        have hw : |(2454533781/5000000000 : ℝ)|=(2454533781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-886311563/2500000000 : ℝ)*x 0 + (-2161680447/5000000000 : ℝ)*x 1 + (1037212577/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (886311563/2500000000 : ℝ)^65 ≤ (25269239519159/100000000000000 : ℝ)^49 := by
    have hnat : (886311563 : ℕ)^65*100000000000000^49 ≤ 25269239519159^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886311563 2500000000 25269239519159 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2161680447/5000000000 : ℝ)^65 ≤ (16439025245073/50000000000000 : ℝ)^49 := by
    have hnat : (2161680447 : ℕ)^65*50000000000000^49 ≤ 16439025245073^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161680447 5000000000 16439025245073 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037212577/2000000000 : ℝ)^65 ≤ (4185270997029/10000000000000 : ℝ)^49 := by
    have hnat : (1037212577 : ℕ)^65*10000000000000^49 ≤ 4185270997029^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037212577 2000000000 4185270997029 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-886311563/2500000000 : ℝ), (-2161680447/5000000000 : ℝ), (1037212577/2000000000 : ℝ)] ![(25269239519159/100000000000000 : ℝ), (16439025245073/50000000000000 : ℝ), (4185270997029/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-886311563/2500000000 : ℝ)|^65 ≤ (25269239519159/100000000000000 : ℝ)^49
        have hw : |(-886311563/2500000000 : ℝ)|=(886311563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2161680447/5000000000 : ℝ)|^65 ≤ (16439025245073/50000000000000 : ℝ)^49
        have hw : |(-2161680447/5000000000 : ℝ)|=(2161680447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037212577/2000000000 : ℝ)|^65 ≤ (4185270997029/10000000000000 : ℝ)^49
        have hw : |(1037212577/2000000000 : ℝ)|=(1037212577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s1_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3991559981/10000000000 : ℝ)*x 0 + (97885709/200000000 : ℝ)*x 1 + (4202885449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3991559981/10000000000 : ℝ)^65 ≤ (7393388658421/25000000000000 : ℝ)^49 := by
    have hnat : (3991559981 : ℕ)^65*25000000000000^49 ≤ 7393388658421^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3991559981 10000000000 7393388658421 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97885709/200000000 : ℝ)^65 ≤ (7751635560851/20000000000000 : ℝ)^49 := by
    have hnat : (97885709 : ℕ)^65*20000000000000^49 ≤ 7751635560851^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97885709 200000000 7751635560851 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4202885449/10000000000 : ℝ)^65 ≤ (6333653510137/20000000000000 : ℝ)^49 := by
    have hnat : (4202885449 : ℕ)^65*20000000000000^49 ≤ 6333653510137^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4202885449 10000000000 6333653510137 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3991559981/10000000000 : ℝ), (97885709/200000000 : ℝ), (4202885449/10000000000 : ℝ)] ![(7393388658421/25000000000000 : ℝ), (7751635560851/20000000000000 : ℝ), (6333653510137/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3991559981/10000000000 : ℝ)|^65 ≤ (7393388658421/25000000000000 : ℝ)^49
        have hw : |(3991559981/10000000000 : ℝ)|=(3991559981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(97885709/200000000 : ℝ)|^65 ≤ (7751635560851/20000000000000 : ℝ)^49
        have hw : |(97885709/200000000 : ℝ)|=(97885709/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4202885449/10000000000 : ℝ)|^65 ≤ (6333653510137/20000000000000 : ℝ)^49
        have hw : |(4202885449/10000000000 : ℝ)|=(4202885449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2728807823/5000000000 : ℝ)*x 0 + (-814812379/2000000000 : ℝ)*x 1 + (-3498532243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2728807823/5000000000 : ℝ)^65 ≤ (44784358575787/100000000000000 : ℝ)^49 := by
    have hnat : (2728807823 : ℕ)^65*100000000000000^49 ≤ 44784358575787^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728807823 5000000000 44784358575787 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (814812379/2000000000 : ℝ)^65 ≤ (30387131383677/100000000000000 : ℝ)^49 := by
    have hnat : (814812379 : ℕ)^65*100000000000000^49 ≤ 30387131383677^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814812379 2000000000 30387131383677 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3498532243/10000000000 : ℝ)^65 ≤ (24828510033457/100000000000000 : ℝ)^49 := by
    have hnat : (3498532243 : ℕ)^65*100000000000000^49 ≤ 24828510033457^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3498532243 10000000000 24828510033457 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2728807823/5000000000 : ℝ), (-814812379/2000000000 : ℝ), (-3498532243/10000000000 : ℝ)] ![(44784358575787/100000000000000 : ℝ), (30387131383677/100000000000000 : ℝ), (24828510033457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2728807823/5000000000 : ℝ)|^65 ≤ (44784358575787/100000000000000 : ℝ)^49
        have hw : |(2728807823/5000000000 : ℝ)|=(2728807823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-814812379/2000000000 : ℝ)|^65 ≤ (30387131383677/100000000000000 : ℝ)^49
        have hw : |(-814812379/2000000000 : ℝ)|=(814812379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3498532243/10000000000 : ℝ)|^65 ≤ (24828510033457/100000000000000 : ℝ)^49
        have hw : |(-3498532243/10000000000 : ℝ)|=(3498532243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301041_s1_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2243420791/5000000000 : ℝ)*x 0 + (-3912650539/10000000000 : ℝ)*x 1 + (4693397623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2243420791/5000000000 : ℝ)^65 ≤ (6907465543077/20000000000000 : ℝ)^49 := by
    have hnat : (2243420791 : ℕ)^65*20000000000000^49 ≤ 6907465543077^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243420791 5000000000 6907465543077 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3912650539/10000000000 : ℝ)^65 ≤ (7200130945601/25000000000000 : ℝ)^49 := by
    have hnat : (3912650539 : ℕ)^65*25000000000000^49 ≤ 7200130945601^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3912650539 10000000000 7200130945601 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4693397623/10000000000 : ℝ)^65 ≤ (36662148484031/100000000000000 : ℝ)^49 := by
    have hnat : (4693397623 : ℕ)^65*100000000000000^49 ≤ 36662148484031^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4693397623 10000000000 36662148484031 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2243420791/5000000000 : ℝ), (-3912650539/10000000000 : ℝ), (4693397623/10000000000 : ℝ)] ![(6907465543077/20000000000000 : ℝ), (7200130945601/25000000000000 : ℝ), (36662148484031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2243420791/5000000000 : ℝ)|^65 ≤ (6907465543077/20000000000000 : ℝ)^49
        have hw : |(2243420791/5000000000 : ℝ)|=(2243420791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3912650539/10000000000 : ℝ)|^65 ≤ (7200130945601/25000000000000 : ℝ)^49
        have hw : |(-3912650539/10000000000 : ℝ)|=(3912650539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4693397623/10000000000 : ℝ)|^65 ≤ (36662148484031/100000000000000 : ℝ)^49
        have hw : |(4693397623/10000000000 : ℝ)|=(4693397623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301041 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_2 : ((7560459469/10000000000 : ℝ)*X 2 0+(-2619790799/10000000000 : ℝ)*X 2 1+(-1140443633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-549180939/2000000000 : ℝ)*X 0 0+(-5769522897/10000000000 : ℝ)*X 0 1+(4412855803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2426287377/10000000000 : ℝ)*X 1 0+(5484408037/10000000000 : ℝ)*X 1 1+(248920363/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((7501539881/10000000000 : ℝ)*X 2 0+(-2648057613/10000000000 : ℝ)*X 2 1+(-2338053431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((377968223/1000000000 : ℝ)*X 0 0+(-471607229/2000000000 : ℝ)*X 0 1+(1653291283/2500000000 : ℝ)*X 0 2+(377968223/1000000000 : ℝ)*X 1 0+(-471607229/2000000000 : ℝ)*X 1 1+(1653291283/2500000000 : ℝ)*X 1 2+(377968223/1000000000 : ℝ)*X 2 0+(-471607229/2000000000 : ℝ)*X 2 1+(1653291283/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-67715153/312500000 : ℝ)*X 0 0+(-2287533357/5000000000 : ℝ)*X 0 1+(3027818289/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1088614431/5000000000 : ℝ)*X 1 0+(5724966237/10000000000 : ℝ)*X 1 1+(4921836493/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((2095325471/2500000000 : ℝ)*X 2 0+(-1956486987/10000000000 : ℝ)*X 2 1+(-841010117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((2331164801/5000000000 : ℝ)*X 0 0+(-1809976159/5000000000 : ℝ)*X 0 1+(2395715411/5000000000 : ℝ)*X 0 2+(2331164801/5000000000 : ℝ)*X 1 0+(-1809976159/5000000000 : ℝ)*X 1 1+(2395715411/5000000000 : ℝ)*X 1 2+(2331164801/5000000000 : ℝ)*X 2 0+(-1809976159/5000000000 : ℝ)*X 2 1+(2395715411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-56323517/200000000 : ℝ)*X 0 0+(-104867643/200000000 : ℝ)*X 0 1+(2454533781/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((2066460809/10000000000 : ℝ)*X 1 0+(5637306811/10000000000 : ℝ)*X 1 1+(5096847983/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8785424881/10000000000 : ℝ)*X 2 0+(-96752627/625000000 : ℝ)*X 2 1+(-279925687/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((56323517/200000000 : ℝ)*X 0 0+(-104867643/200000000 : ℝ)*X 0 1+(2454533781/5000000000 : ℝ)*X 0 2+(56323517/200000000 : ℝ)*X 1 0+(-104867643/200000000 : ℝ)*X 1 1+(2454533781/5000000000 : ℝ)*X 1 2+(56323517/200000000 : ℝ)*X 2 0+(-104867643/200000000 : ℝ)*X 2 1+(2454533781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((2351/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2351/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (265952277076833191823/78125000000000000000000000 : ℝ) := by norm_num
    linear_combination (1218199/250000000000 : ℝ)*(base1) + (17205007861/250000000000 : ℝ)*(base40) + (333482827307/1000000000000 : ℝ)*(base50) + (357677896631/500000000000 : ℝ)*(base60) + (883660311379/250000000000 : ℝ)*(major_s0_0) + (883660311379/250000000000 : ℝ)*(major_s0_1) + (883660311379/250000000000 : ℝ)*(major_s0_2) + (467974695949/100000000000 : ℝ)*(sp_s0_7) + (2339842400873/500000000000 : ℝ)*(sp_s0_8) + (4679782263597/1000000000000 : ℝ)*(sp_s0_9) + (238949327863/100000000000 : ℝ)*(sp_s0_13) + (470637/500000000000 : ℝ)*(sp_s0_16) + (41118177/1000000000000 : ℝ)*(sp_s0_20) + (31489/320000000 : ℝ)*(sp_s0_21) + (1194749075713/500000000000 : ℝ)*(f.failure) + (4679783204871/1000000000000 : ℝ)*(f.sum) + (3794861/100000000000000000000 : ℝ)*base63 + (1407633758993303/2500000000000000000000000000 : ℝ)*base65 + (693523677493303/2500000000000000000000000000 : ℝ)*base66 + (1195389545995169/2500000000000000000000000000 : ℝ)*base68 + (109073746748559/312500000000000000000000000 : ℝ)*base71 + (18344349756697/2500000000000000000000000000 : ℝ)*base73 + (754876960995169/2500000000000000000000000000 : ℝ)*base75 + (251430416495169/2500000000000000000000000000 : ℝ)*base77 + (187760118618303/1250000000000000000000000000 : ℝ)*base78 + (7547/12500000000000000 : ℝ)*base86 + (7547/12500000000000000 : ℝ)*base88 + (7547/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-873/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-873/3125 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3146323755980865146397/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97213939193/250000000000 : ℝ)*(base39) + (510802264787/500000000000 : ℝ)*(base40) + (880738240437/1000000000000 : ℝ)*(base60) + (421517736907/100000000000 : ℝ)*(major_s0_0) + (421517736907/100000000000 : ℝ)*(major_s0_1) + (421517736907/100000000000 : ℝ)*(major_s0_2) + (456829/100000000000 : ℝ)*(sp_s0_2) + (164358283/1000000000000 : ℝ)*(sp_s0_8) + (9570781/1000000000000 : ℝ)*(sp_s0_13) + (5580796538081/1000000000000 : ℝ)*(sp_s0_14) + (1116114364357/200000000000 : ℝ)*(sp_s0_15) + (5580791969791/1000000000000 : ℝ)*(sp_s0_16) + (712386632931/250000000000 : ℝ)*(sp_s0_19) + (60358013/1000000000000 : ℝ)*(sp_s0_21) + (1424778051253/500000000000 : ℝ)*(f.failure) + (5580796538081/1000000000000 : ℝ)*(f.sum) + (1348754549/5000000000000000000000 : ℝ)*base63 + (177235558698799/1000000000000000000000000000 : ℝ)*base65 + (11073631398799/1000000000000000000000000000 : ℝ)*base66 + (2904814765977/1000000000000000000000000000 : ℝ)*base68 + (22396656429403/125000000000000000000000000 : ℝ)*base70 + (391211814001201/1000000000000000000000000000 : ℝ)*base73 + (90267194034023/1000000000000000000000000000 : ℝ)*base74 + (96055669565977/1000000000000000000000000000 : ℝ)*base77 + (318116623101201/500000000000000000000000000 : ℝ)*base79 + (12193/12500000000000000 : ℝ)*base87 + (12193/12500000000000000 : ℝ)*base89 + (12193/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4243/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4243/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (51495811358457991482063/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (481923176083/500000000000 : ℝ)*(base1) + (822690090299/1000000000000 : ℝ)*(base40) + (1391830083/8000000000 : ℝ)*(base50) + (25831737059/125000000000 : ℝ)*(base60) + (461221327301/100000000000 : ℝ)*(major_s0_0) + (2684219966209/1000000000000 : ℝ)*(major_s0_1) + (2684219966209/1000000000000 : ℝ)*(major_s0_2) + (1927993306801/1000000000000 : ℝ)*(sp_s0_3) + (1958759/1000000000000 : ℝ)*(sp_s0_7) + (25514657/62500000000 : ℝ)*(sp_s0_15) + (4517686934917/1000000000000 : ℝ)*(sp_s0_20) + (1776717153499/500000000000 : ℝ)*(sp_s0_21) + (355384254151/100000000000 : ℝ)*(sp_s0_22) + (850747605683/1000000000000 : ℝ)*(sp_s0_25) + (1814593957849/1000000000000 : ℝ)*(f.failure) + (355384254151/100000000000 : ℝ)*(f.sum) + (95145519/2000000000000000000000 : ℝ)*base62 + (786499396862387/10000000000000000000000000000 : ℝ)*base64 + (325148542862387/10000000000000000000000000000 : ℝ)*base67 + (439948282848299/10000000000000000000000000000 : ℝ)*base68 + (6385775739940723/10000000000000000000000000000 : ℝ)*base71 + (373158557635457/1000000000000000000000000000 : ℝ)*base72 + (3203600146848299/10000000000000000000000000000 : ℝ)*base75 + (361605300180311/1000000000000000000000000000 : ℝ)*base77 + (7868023056492183/10000000000000000000000000000 : ℝ)*base78 + (11131/25000000000000000 : ℝ)*base86 + (11131/25000000000000000 : ℝ)*base88 + (11131/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (2351/20000 : ℝ) ^ (129/32 : ℝ) ≤ (8929044666461787/50000000000000000000 : ℝ) := by
    have hpowers : (2351/20000 : ℝ)^129 ≤ (8929044666461787/50000000000000000000 : ℝ)^32 := by
      have hnat : (2351 : ℕ)^129*50000000000000000000^32 ≤ 8929044666461787^32*20000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2351 20000 8929044666461787 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2351/20000 : ℝ)) (X := (8929044666461787/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50008929044666461787/50000000000000000000 : ℝ) ≤ (1000044296162357/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (50008929044666461787/50000000000000000000 : ℝ)^32 ≤ (1000044296162357/1000000000000000 : ℝ)^129 := by
      have hnat : (50008929044666461787 : ℕ)^32*1000000000000000^129 ≤ 1000044296162357^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008929044666461787 50000000000000000000 1000044296162357 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000044296162357/1000000000000000 : ℝ)) (X := (50008929044666461787/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25008929044666461787/25000000000000000000 : ℝ) ≤ (5000442931890043/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (25008929044666461787/25000000000000000000 : ℝ)^32 ≤ (5000442931890043/5000000000000000 : ℝ)^129 := by
      have hnat : (25008929044666461787 : ℕ)^32*5000000000000000^129 ≤ 5000442931890043^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008929044666461787 25000000000000000000 5000442931890043 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000442931890043/5000000000000000 : ℝ)) (X := (25008929044666461787/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(44296162357/117550000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(110725539129/293875000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (2351/20000 : ℝ)) (alpha := (44296162357/117550000000000 : ℝ)) (beta := (110725539129/293875000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2351/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(44296162357/117550000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(110725539129/293875000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (873/3125 : ℝ) ^ (129/32 : ℝ) ≤ (146315228106530807/25000000000000000000 : ℝ) := by
    have hpowers : (873/3125 : ℝ)^129 ≤ (146315228106530807/25000000000000000000 : ℝ)^32 := by
      have hnat : (873 : ℕ)^129*25000000000000000000^32 ≤ 146315228106530807^32*3125^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        873 3125 146315228106530807 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (873/3125 : ℝ)) (X := (146315228106530807/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25146315228106530807/25000000000000000000 : ℝ) ≤ (5007243131639111/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (25146315228106530807/25000000000000000000 : ℝ)^32 ≤ (5007243131639111/5000000000000000 : ℝ)^129 := by
      have hnat : (25146315228106530807 : ℕ)^32*5000000000000000^129 ≤ 5007243131639111^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25146315228106530807 25000000000000000000 5007243131639111 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007243131639111/5000000000000000 : ℝ)) (X := (25146315228106530807/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12646315228106530807/12500000000000000000 : ℝ) ≤ (10028909284319779/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (12646315228106530807/12500000000000000000 : ℝ)^32 ≤ (10028909284319779/10000000000000000 : ℝ)^129 := by
      have hnat : (12646315228106530807 : ℕ)^32*10000000000000000^129 ≤ 10028909284319779^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12646315228106530807 12500000000000000000 10028909284319779 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10028909284319779/10000000000000000 : ℝ)) (X := (12646315228106530807/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(2414377213037/465600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(4807673680519/931200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (873/3125 : ℝ)) (alpha := (2414377213037/465600000000000 : ℝ)) (beta := (4807673680519/931200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (873/3125 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(2414377213037/465600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(4807673680519/931200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (4243/20000 : ℝ) ^ (129/32 : ℝ) ≤ (6030867138607401/3125000000000000000 : ℝ) := by
    have hpowers : (4243/20000 : ℝ)^129 ≤ (6030867138607401/3125000000000000000 : ℝ)^32 := by
      have hnat : (4243 : ℕ)^129*3125000000000000000^32 ≤ 6030867138607401^32*20000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4243 20000 6030867138607401 3125000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4243/20000 : ℝ)) (X := (6030867138607401/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (3131030867138607401/3125000000000000000 : ℝ) ≤ (2000956764671639/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3131030867138607401/3125000000000000000 : ℝ)^32 ≤ (2000956764671639/2000000000000000 : ℝ)^129 := by
      have hnat : (3131030867138607401 : ℕ)^32*2000000000000000^129 ≤ 2000956764671639^129*3125000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3131030867138607401 3125000000000000000 2000956764671639 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000956764671639/2000000000000000 : ℝ)) (X := (3131030867138607401/3125000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1568530867138607401/1562500000000000000 : ℝ) ≤ (2001912144612109/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (1568530867138607401/1562500000000000000 : ℝ)^32 ≤ (2001912144612109/2000000000000000 : ℝ)^129 := by
      have hnat : (1568530867138607401 : ℕ)^32*2000000000000000^129 ≤ 2001912144612109^129*1562500000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1568530867138607401 1562500000000000000 2001912144612109 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001912144612109/2000000000000000 : ℝ)) (X := (1568530867138607401/1562500000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(956764671639/424300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(95537994047/42430000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (4243/20000 : ℝ)) (alpha := (956764671639/424300000000000 : ℝ)) (beta := (95537994047/42430000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (4243/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(956764671639/424300000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(95537994047/42430000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-886311563/2500000000 : ℝ)*X 0 0+(-2161680447/5000000000 : ℝ)*X 0 1+(1037212577/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3991559981/10000000000 : ℝ)*X 1 0+(97885709/200000000 : ℝ)*X 1 1+(4202885449/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2728807823/5000000000 : ℝ)*X 2 0+(-814812379/2000000000 : ℝ)*X 2 1+(-3498532243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2243420791/5000000000 : ℝ)*X 0 0+(-3912650539/10000000000 : ℝ)*X 0 1+(4693397623/10000000000 : ℝ)*X 0 2+(2243420791/5000000000 : ℝ)*X 1 0+(-3912650539/10000000000 : ℝ)*X 1 1+(4693397623/10000000000 : ℝ)*X 1 2+(2243420791/5000000000 : ℝ)*X 2 0+(-3912650539/10000000000 : ℝ)*X 2 1+(4693397623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301041_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-73443/12500 : ℝ) < ((-36981/25000 : ℝ)*P 0+(-36981/25000 : ℝ)*P 1+(-36981/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-73443/12500 : ℝ) < (-68112263357138171581409781/11755000000000000000000000 : ℝ) := by norm_num
    linear_combination (50453/500000000000 : ℝ)*(base5) + (58633/100000000000 : ℝ)*(base17) + (152157/250000000000 : ℝ)*(base21) + (10184140501/100000000000 : ℝ)*(base39) + (150268397731/500000000000 : ℝ)*(base40) + (15880026513/1000000000000 : ℝ)*(base50) + (49519/250000000000 : ℝ)*(base59) + (51254865091/200000000000 : ℝ)*(base60) + (36981/25000 : ℝ)*(major_s1_0) + (36981/25000 : ℝ)*(major_s1_1) + (36981/25000 : ℝ)*(major_s1_2) + (965720450263/500000000000 : ℝ)*(sp_s1_0) + (482860078549/250000000000 : ℝ)*(sp_s1_1) + (386288078561/200000000000 : ℝ)*(sp_s1_2) + (499999949547/500000000000 : ℝ)*(sp_s1_6) + (965720450263/500000000000 : ℝ)*(f.sum) + (27253946046731/1028927500000000000000000000 : ℝ)*base63 + (685578687587/4243000000000000000000000 : ℝ)*base64 + (29766736123/121250000000000000000000 : ℝ)*base66 + (663325170389/5303750000000000000000000 : ℝ)*base68 + (10100909733072769/49876465000000000000000000000 : ℝ)*base71 + (381694983833/11755000000000000000000000 : ℝ)*base72 + (112894581293/485000000000000000000000 : ℝ)*base74 + (8397839658491/23510000000000000000000000 : ℝ)*base77 + (305487091687491/2280470000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c301042_s0_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1545196007/5000000000 : ℝ)*x 0 + (-620228431/1250000000 : ℝ)*x 1 + (-1240457039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1545196007/5000000000 : ℝ)^65 ≤ (526535189379/2500000000000 : ℝ)^49 := by
    have hnat : (1545196007 : ℕ)^65*2500000000000^49 ≤ 526535189379^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545196007 5000000000 526535189379 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620228431/1250000000 : ℝ)^65 ≤ (39469292464921/100000000000000 : ℝ)^49 := by
    have hnat : (620228431 : ℕ)^65*100000000000000^49 ≤ 39469292464921^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620228431 1250000000 39469292464921 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1240457039/2500000000 : ℝ)^65 ≤ (1973464996787/5000000000000 : ℝ)^49 := by
    have hnat : (1240457039 : ℕ)^65*5000000000000^49 ≤ 1973464996787^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240457039 2500000000 1973464996787 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1545196007/5000000000 : ℝ), (-620228431/1250000000 : ℝ), (-1240457039/2500000000 : ℝ)] ![(526535189379/2500000000000 : ℝ), (39469292464921/100000000000000 : ℝ), (1973464996787/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1545196007/5000000000 : ℝ)|^65 ≤ (526535189379/2500000000000 : ℝ)^49
        have hw : |(-1545196007/5000000000 : ℝ)|=(1545196007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-620228431/1250000000 : ℝ)|^65 ≤ (39469292464921/100000000000000 : ℝ)^49
        have hw : |(-620228431/1250000000 : ℝ)|=(620228431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1240457039/2500000000 : ℝ)|^65 ≤ (1973464996787/5000000000000 : ℝ)^49
        have hw : |(-1240457039/2500000000 : ℝ)|=(1240457039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301042_s0_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1545196007/5000000000 : ℝ)*x 0 + (620228431/1250000000 : ℝ)*x 1 + (-1240457039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1545196007/5000000000 : ℝ)^65 ≤ (526535189379/2500000000000 : ℝ)^49 := by
    have hnat : (1545196007 : ℕ)^65*2500000000000^49 ≤ 526535189379^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545196007 5000000000 526535189379 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620228431/1250000000 : ℝ)^65 ≤ (39469292464921/100000000000000 : ℝ)^49 := by
    have hnat : (620228431 : ℕ)^65*100000000000000^49 ≤ 39469292464921^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620228431 1250000000 39469292464921 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1240457039/2500000000 : ℝ)^65 ≤ (1973464996787/5000000000000 : ℝ)^49 := by
    have hnat : (1240457039 : ℕ)^65*5000000000000^49 ≤ 1973464996787^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240457039 2500000000 1973464996787 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1545196007/5000000000 : ℝ), (620228431/1250000000 : ℝ), (-1240457039/2500000000 : ℝ)] ![(526535189379/2500000000000 : ℝ), (39469292464921/100000000000000 : ℝ), (1973464996787/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1545196007/5000000000 : ℝ)|^65 ≤ (526535189379/2500000000000 : ℝ)^49
        have hw : |(1545196007/5000000000 : ℝ)|=(1545196007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(620228431/1250000000 : ℝ)|^65 ≤ (39469292464921/100000000000000 : ℝ)^49
        have hw : |(620228431/1250000000 : ℝ)|=(620228431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1240457039/2500000000 : ℝ)|^65 ≤ (1973464996787/5000000000000 : ℝ)^49
        have hw : |(-1240457039/2500000000 : ℝ)|=(1240457039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301042_s0_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (596668887/1000000000 : ℝ)*x 0 + (-174752669/500000000 : ℝ)*x 1 + (3495053879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (596668887/1000000000 : ℝ)^65 ≤ (12602116448291/25000000000000 : ℝ)^49 := by
    have hnat : (596668887 : ℕ)^65*25000000000000^49 ≤ 12602116448291^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596668887 1000000000 12602116448291 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174752669/500000000 : ℝ)^65 ≤ (2479576474261/10000000000000 : ℝ)^49 := by
    have hnat : (174752669 : ℕ)^65*10000000000000^49 ≤ 2479576474261^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174752669 500000000 2479576474261 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3495053879/10000000000 : ℝ)^65 ≤ (4959153887751/20000000000000 : ℝ)^49 := by
    have hnat : (3495053879 : ℕ)^65*20000000000000^49 ≤ 4959153887751^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3495053879 10000000000 4959153887751 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(596668887/1000000000 : ℝ), (-174752669/500000000 : ℝ), (3495053879/10000000000 : ℝ)] ![(12602116448291/25000000000000 : ℝ), (2479576474261/10000000000000 : ℝ), (4959153887751/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(596668887/1000000000 : ℝ)|^65 ≤ (12602116448291/25000000000000 : ℝ)^49
        have hw : |(596668887/1000000000 : ℝ)|=(596668887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-174752669/500000000 : ℝ)|^65 ≤ (2479576474261/10000000000000 : ℝ)^49
        have hw : |(-174752669/500000000 : ℝ)|=(174752669/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3495053879/10000000000 : ℝ)|^65 ≤ (4959153887751/20000000000000 : ℝ)^49
        have hw : |(3495053879/10000000000 : ℝ)|=(3495053879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301042_s0_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (596668887/1000000000 : ℝ)*x 0 + (-174752669/500000000 : ℝ)*x 1 + (-3495053879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (596668887/1000000000 : ℝ)^65 ≤ (12602116448291/25000000000000 : ℝ)^49 := by
    have hnat : (596668887 : ℕ)^65*25000000000000^49 ≤ 12602116448291^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596668887 1000000000 12602116448291 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174752669/500000000 : ℝ)^65 ≤ (2479576474261/10000000000000 : ℝ)^49 := by
    have hnat : (174752669 : ℕ)^65*10000000000000^49 ≤ 2479576474261^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174752669 500000000 2479576474261 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3495053879/10000000000 : ℝ)^65 ≤ (4959153887751/20000000000000 : ℝ)^49 := by
    have hnat : (3495053879 : ℕ)^65*20000000000000^49 ≤ 4959153887751^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3495053879 10000000000 4959153887751 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(596668887/1000000000 : ℝ), (-174752669/500000000 : ℝ), (-3495053879/10000000000 : ℝ)] ![(12602116448291/25000000000000 : ℝ), (2479576474261/10000000000000 : ℝ), (4959153887751/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(596668887/1000000000 : ℝ)|^65 ≤ (12602116448291/25000000000000 : ℝ)^49
        have hw : |(596668887/1000000000 : ℝ)|=(596668887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-174752669/500000000 : ℝ)|^65 ≤ (2479576474261/10000000000000 : ℝ)^49
        have hw : |(-174752669/500000000 : ℝ)|=(174752669/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3495053879/10000000000 : ℝ)|^65 ≤ (4959153887751/20000000000000 : ℝ)^49
        have hw : |(-3495053879/10000000000 : ℝ)|=(3495053879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301042 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1545196007/5000000000 : ℝ)*X 0 0+(-620228431/1250000000 : ℝ)*X 0 1+(-1240457039/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301042_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1545196007/5000000000 : ℝ)*X 1 0+(620228431/1250000000 : ℝ)*X 1 1+(-1240457039/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301042_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((596668887/1000000000 : ℝ)*X 2 0+(-174752669/500000000 : ℝ)*X 2 1+(3495053879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301042_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((596668887/1000000000 : ℝ)*X 0 0+(-174752669/500000000 : ℝ)*X 0 1+(-3495053879/10000000000 : ℝ)*X 0 2+(596668887/1000000000 : ℝ)*X 1 0+(-174752669/500000000 : ℝ)*X 1 1+(-3495053879/10000000000 : ℝ)*X 1 2+(596668887/1000000000 : ℝ)*X 2 0+(-174752669/500000000 : ℝ)*X 2 1+(-3495053879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301042_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-73443/12500 : ℝ) < ((-36981/25000 : ℝ)*P 0+(-36981/25000 : ℝ)*P 1+(-36981/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-73443/12500 : ℝ) < (-3645528010087768749399538941/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59718279697/1000000000000 : ℝ)*(base5) + (42223/100000000000 : ℝ)*(base10) + (111183/250000000000 : ℝ)*(base15) + (28661/250000000000 : ℝ)*(base33) + (43169182911/250000000000 : ℝ)*(base39) + (43169162297/250000000000 : ℝ)*(base40) + (19911009481/500000000000 : ℝ)*(base59) + (39822256617/1000000000000 : ℝ)*(base60) + (369809971339/250000000000 : ℝ)*(major_s0_0) + (36981/25000 : ℝ)*(major_s0_1) + (36981/25000 : ℝ)*(major_s0_2) + (1944281183147/1000000000000 : ℝ)*(sp_s0_0) + (1944281046001/1000000000000 : ℝ)*(sp_s0_1) + (200399977043/100000000000 : ℝ)*(sp_s0_2) + (940281720303/1000000000000 : ℝ)*(sp_s0_6) + (1944281605377/1000000000000 : ℝ)*(f.sum) + (49908139/312500000000000000000 : ℝ)*base63 + (830513921/2500000000000000000000 : ℝ)*base64 + (1665956411/10000000000000000000000 : ℝ)*base66 + (5556801/156250000000000000000 : ℝ)*base68 + (2356817004695271/2500000000000000000000000000 : ℝ)*base70 + (763537867289023/2500000000000000000000000000 : ℝ)*base72 + (266377007/1000000000000000000000 : ℝ)*base74 + (1420707622695271/2500000000000000000000000000 : ℝ)*base76 + (916150568789023/2500000000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p001_b023 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 41 ≤ c.val) (hhi : c.val < 43)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=41 ∨ c=42 := by omega
  rcases hc with rfl|rfl
  · exact collision_c301041 p hpa (by linarith only [hpb]) X hX
  · exact collision_c301042 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 41 ≤ c.val) (hhi : c.val < 43)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b023 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

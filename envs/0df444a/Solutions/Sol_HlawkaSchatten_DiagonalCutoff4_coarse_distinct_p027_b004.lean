-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b004
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:14:21.942853+00:00
-- url     : https://prove2.me/submissions/1f70ec42-7c13-4376-beb1-b38bf1d231d5

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
theorem collision_support_c327012_s0_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2420080119/10000000000 : ℝ)*x 0 + (-5820214821/10000000000 : ℝ)*x 1 + (-3734176681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2420080119/10000000000 : ℝ)^91 ≤ (17880517717049/100000000000000 : ℝ)^75 := by
    have hnat : (2420080119 : ℕ)^91*100000000000000^75 ≤ 17880517717049^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2420080119 10000000000 17880517717049 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5820214821/10000000000 : ℝ)^91 ≤ (25927621332421/50000000000000 : ℝ)^75 := by
    have hnat : (5820214821 : ℕ)^91*50000000000000^75 ≤ 25927621332421^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5820214821 10000000000 25927621332421 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3734176681/10000000000 : ℝ)^91 ≤ (30264239599557/100000000000000 : ℝ)^75 := by
    have hnat : (3734176681 : ℕ)^91*100000000000000^75 ≤ 30264239599557^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3734176681 10000000000 30264239599557 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2420080119/10000000000 : ℝ), (-5820214821/10000000000 : ℝ), (-3734176681/10000000000 : ℝ)] ![(17880517717049/100000000000000 : ℝ), (25927621332421/50000000000000 : ℝ), (30264239599557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2420080119/10000000000 : ℝ)|^91 ≤ (17880517717049/100000000000000 : ℝ)^75
        have hw : |(-2420080119/10000000000 : ℝ)|=(2420080119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5820214821/10000000000 : ℝ)|^91 ≤ (25927621332421/50000000000000 : ℝ)^75
        have hw : |(-5820214821/10000000000 : ℝ)|=(5820214821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3734176681/10000000000 : ℝ)|^91 ≤ (30264239599557/100000000000000 : ℝ)^75
        have hw : |(-3734176681/10000000000 : ℝ)|=(3734176681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327012_s0_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2998401973/5000000000 : ℝ)*x 0 + (2457671687/10000000000 : ℝ)*x 1 + (-43794467/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2998401973/5000000000 : ℝ)^91 ≤ (53770336224293/100000000000000 : ℝ)^75 := by
    have hnat : (2998401973 : ℕ)^91*100000000000000^75 ≤ 53770336224293^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2998401973 5000000000 53770336224293 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2457671687/10000000000 : ℝ)^91 ≤ (18218066840989/100000000000000 : ℝ)^75 := by
    have hnat : (2457671687 : ℕ)^91*100000000000000^75 ≤ 18218066840989^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2457671687 10000000000 18218066840989 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43794467/125000000 : ℝ)^91 ≤ (28011596918989/100000000000000 : ℝ)^75 := by
    have hnat : (43794467 : ℕ)^91*100000000000000^75 ≤ 28011596918989^75*125000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43794467 125000000 28011596918989 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2998401973/5000000000 : ℝ), (2457671687/10000000000 : ℝ), (-43794467/125000000 : ℝ)] ![(53770336224293/100000000000000 : ℝ), (18218066840989/100000000000000 : ℝ), (28011596918989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2998401973/5000000000 : ℝ)|^91 ≤ (53770336224293/100000000000000 : ℝ)^75
        have hw : |(2998401973/5000000000 : ℝ)|=(2998401973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2457671687/10000000000 : ℝ)|^91 ≤ (18218066840989/100000000000000 : ℝ)^75
        have hw : |(2457671687/10000000000 : ℝ)|=(2457671687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43794467/125000000 : ℝ)|^91 ≤ (28011596918989/100000000000000 : ℝ)^75
        have hw : |(-43794467/125000000 : ℝ)|=(43794467/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327012_s0_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1666283727/5000000000 : ℝ)*x 0 + (-360710431/1000000000 : ℝ)*x 1 + (5142142021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1666283727/5000000000 : ℝ)^91 ≤ (5272320304787/20000000000000 : ℝ)^75 := by
    have hnat : (1666283727 : ℕ)^91*20000000000000^75 ≤ 5272320304787^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1666283727 5000000000 5272320304787 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (360710431/1000000000 : ℝ)^91 ≤ (3627403803469/12500000000000 : ℝ)^75 := by
    have hnat : (360710431 : ℕ)^91*12500000000000^75 ≤ 3627403803469^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360710431 1000000000 3627403803469 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5142142021/10000000000 : ℝ)^91 ≤ (44619168042859/100000000000000 : ℝ)^75 := by
    have hnat : (5142142021 : ℕ)^91*100000000000000^75 ≤ 44619168042859^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142142021 10000000000 44619168042859 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1666283727/5000000000 : ℝ), (-360710431/1000000000 : ℝ), (5142142021/10000000000 : ℝ)] ![(5272320304787/20000000000000 : ℝ), (3627403803469/12500000000000 : ℝ), (44619168042859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1666283727/5000000000 : ℝ)|^91 ≤ (5272320304787/20000000000000 : ℝ)^75
        have hw : |(1666283727/5000000000 : ℝ)|=(1666283727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-360710431/1000000000 : ℝ)|^91 ≤ (3627403803469/12500000000000 : ℝ)^75
        have hw : |(-360710431/1000000000 : ℝ)|=(360710431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5142142021/10000000000 : ℝ)|^91 ≤ (44619168042859/100000000000000 : ℝ)^75
        have hw : |(5142142021/10000000000 : ℝ)|=(5142142021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327012_s0_6 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2418765417/5000000000 : ℝ)*x 0 + (-2202557647/5000000000 : ℝ)*x 1 + (-282626661/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2418765417/5000000000 : ℝ)^91 ≤ (2071636160531/5000000000000 : ℝ)^75 := by
    have hnat : (2418765417 : ℕ)^91*5000000000000^75 ≤ 2071636160531^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418765417 5000000000 2071636160531 5000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2202557647/5000000000 : ℝ)^91 ≤ (18491472823113/50000000000000 : ℝ)^75 := by
    have hnat : (2202557647 : ℕ)^91*50000000000000^75 ≤ 18491472823113^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202557647 5000000000 18491472823113 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282626661/1000000000 : ℝ)^91 ≤ (21584331128679/100000000000000 : ℝ)^75 := by
    have hnat : (282626661 : ℕ)^91*100000000000000^75 ≤ 21584331128679^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282626661 1000000000 21584331128679 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2418765417/5000000000 : ℝ), (-2202557647/5000000000 : ℝ), (-282626661/1000000000 : ℝ)] ![(2071636160531/5000000000000 : ℝ), (18491472823113/50000000000000 : ℝ), (21584331128679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2418765417/5000000000 : ℝ)|^91 ≤ (2071636160531/5000000000000 : ℝ)^75
        have hw : |(2418765417/5000000000 : ℝ)|=(2418765417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2202557647/5000000000 : ℝ)|^91 ≤ (18491472823113/50000000000000 : ℝ)^75
        have hw : |(-2202557647/5000000000 : ℝ)|=(2202557647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-282626661/1000000000 : ℝ)|^91 ≤ (21584331128679/100000000000000 : ℝ)^75
        have hw : |(-282626661/1000000000 : ℝ)|=(282626661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c327012 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (20519/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (20519/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (20519/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (20519/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2420080119/10000000000 : ℝ)*X 0 0+(-5820214821/10000000000 : ℝ)*X 0 1+(-3734176681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327012_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2998401973/5000000000 : ℝ)*X 1 0+(2457671687/10000000000 : ℝ)*X 1 1+(-43794467/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327012_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1666283727/5000000000 : ℝ)*X 2 0+(-360710431/1000000000 : ℝ)*X 2 1+(5142142021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327012_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((2418765417/5000000000 : ℝ)*X 0 0+(-2202557647/5000000000 : ℝ)*X 0 1+(-282626661/1000000000 : ℝ)*X 0 2+(2418765417/5000000000 : ℝ)*X 1 0+(-2202557647/5000000000 : ℝ)*X 1 1+(-282626661/1000000000 : ℝ)*X 1 2+(2418765417/5000000000 : ℝ)*X 2 0+(-2202557647/5000000000 : ℝ)*X 2 1+(-282626661/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327012_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-484833/50000 : ℝ) < ((-211611/100000 : ℝ)*P 0+(-211611/100000 : ℝ)*P 1+(-211611/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-484833/50000 : ℝ) < (-19142001148714029943209/2000000000000000000000 : ℝ) := by norm_num
    linear_combination (12239/500000000000 : ℝ)*(base21) + (2853/125000000000 : ℝ)*(base22) + (389237938043/500000000000 : ℝ)*(base39) + (243988349191/1000000000000 : ℝ)*(base40) + (749245477557/1000000000000 : ℝ)*(base49) + (288333205787/1000000000000 : ℝ)*(base50) + (14749/500000000000 : ℝ)*(base59) + (3889/250000000000 : ℝ)*(base60) + (211611/100000 : ℝ)*(major_s0_0) + (211611/100000 : ℝ)*(major_s0_1) + (211611/100000 : ℝ)*(major_s0_2) + (3190333524781/1000000000000 : ℝ)*(sp_s0_0) + (3190333524781/1000000000000 : ℝ)*(sp_s0_1) + (3190333477479/1000000000000 : ℝ)*(sp_s0_2) + (1 : ℝ)*(sp_s0_6) + (3190333524781/1000000000000 : ℝ)*(f.sum) + (8308071061/10000000000000000000000 : ℝ)*base62 + (146859541/10000000000000000000000 : ℝ)*base65 + (6854048479/10000000000000000000000 : ℝ)*base66 + (934605053/5000000000000000000000 : ℝ)*base68 + (6343680513/10000000000000000000000 : ℝ)*base71 + (269247109/500000000000000000000 : ℝ)*base72 + (2038872093/5000000000000000000000 : ℝ)*base74 + (270921021/1000000000000000000000 : ℝ)*base77 + (11022805739/10000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c327013_s0_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2184915741/10000000000 : ℝ)*x 0 + (-6852157133/10000000000 : ℝ)*x 1 + (2762250229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184915741/10000000000 : ℝ)^91 ≤ (7897399340461/50000000000000 : ℝ)^75 := by
    have hnat : (2184915741 : ℕ)^91*50000000000000^75 ≤ 7897399340461^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184915741 10000000000 7897399340461 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6852157133/10000000000 : ℝ)^91 ≤ (63212622341833/100000000000000 : ℝ)^75 := by
    have hnat : (6852157133 : ℕ)^91*100000000000000^75 ≤ 63212622341833^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6852157133 10000000000 63212622341833 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2762250229/10000000000 : ℝ)^91 ≤ (839703158579/4000000000000 : ℝ)^75 := by
    have hnat : (2762250229 : ℕ)^91*4000000000000^75 ≤ 839703158579^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762250229 10000000000 839703158579 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2184915741/10000000000 : ℝ), (-6852157133/10000000000 : ℝ), (2762250229/10000000000 : ℝ)] ![(7897399340461/50000000000000 : ℝ), (63212622341833/100000000000000 : ℝ), (839703158579/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2184915741/10000000000 : ℝ)|^91 ≤ (7897399340461/50000000000000 : ℝ)^75
        have hw : |(-2184915741/10000000000 : ℝ)|=(2184915741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6852157133/10000000000 : ℝ)|^91 ≤ (63212622341833/100000000000000 : ℝ)^75
        have hw : |(-6852157133/10000000000 : ℝ)|=(6852157133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2762250229/10000000000 : ℝ)|^91 ≤ (839703158579/4000000000000 : ℝ)^75
        have hw : |(2762250229/10000000000 : ℝ)|=(2762250229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s0_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (685351593/1000000000 : ℝ)*x 0 + (281870559/1250000000 : ℝ)*x 1 + (2693560323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (685351593/1000000000 : ℝ)^91 ≤ (7903479004089/12500000000000 : ℝ)^75 := by
    have hnat : (685351593 : ℕ)^91*12500000000000^75 ≤ 7903479004089^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685351593 1000000000 7903479004089 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281870559/1250000000 : ℝ)^91 ≤ (8205647280501/50000000000000 : ℝ)^75 := by
    have hnat : (281870559 : ℕ)^91*50000000000000^75 ≤ 8205647280501^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281870559 1250000000 8205647280501 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693560323/10000000000 : ℝ)^91 ≤ (1272554587147/6250000000000 : ℝ)^75 := by
    have hnat : (2693560323 : ℕ)^91*6250000000000^75 ≤ 1272554587147^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693560323 10000000000 1272554587147 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(685351593/1000000000 : ℝ), (281870559/1250000000 : ℝ), (2693560323/10000000000 : ℝ)] ![(7903479004089/12500000000000 : ℝ), (8205647280501/50000000000000 : ℝ), (1272554587147/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(685351593/1000000000 : ℝ)|^91 ≤ (7903479004089/12500000000000 : ℝ)^75
        have hw : |(685351593/1000000000 : ℝ)|=(685351593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281870559/1250000000 : ℝ)|^91 ≤ (8205647280501/50000000000000 : ℝ)^75
        have hw : |(281870559/1250000000 : ℝ)|=(281870559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693560323/10000000000 : ℝ)|^91 ≤ (1272554587147/6250000000000 : ℝ)^75
        have hw : |(2693560323/10000000000 : ℝ)|=(2693560323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s0_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1735442389/5000000000 : ℝ)*x 0 + (-741541949/2000000000 : ℝ)*x 1 + (-2460458897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1735442389/5000000000 : ℝ)^91 ≤ (13847480951333/50000000000000 : ℝ)^75 := by
    have hnat : (1735442389 : ℕ)^91*50000000000000^75 ≤ 13847480951333^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735442389 5000000000 13847480951333 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (741541949/2000000000 : ℝ)^91 ≤ (30004169978539/100000000000000 : ℝ)^75 := by
    have hnat : (741541949 : ℕ)^91*100000000000000^75 ≤ 30004169978539^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741541949 2000000000 30004169978539 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2460458897/5000000000 : ℝ)^91 ≤ (8460173621693/20000000000000 : ℝ)^75 := by
    have hnat : (2460458897 : ℕ)^91*20000000000000^75 ≤ 8460173621693^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2460458897 5000000000 8460173621693 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1735442389/5000000000 : ℝ), (-741541949/2000000000 : ℝ), (-2460458897/5000000000 : ℝ)] ![(13847480951333/50000000000000 : ℝ), (30004169978539/100000000000000 : ℝ), (8460173621693/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1735442389/5000000000 : ℝ)|^91 ≤ (13847480951333/50000000000000 : ℝ)^75
        have hw : |(1735442389/5000000000 : ℝ)|=(1735442389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-741541949/2000000000 : ℝ)|^91 ≤ (30004169978539/100000000000000 : ℝ)^75
        have hw : |(-741541949/2000000000 : ℝ)|=(741541949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2460458897/5000000000 : ℝ)|^91 ≤ (8460173621693/20000000000000 : ℝ)^75
        have hw : |(-2460458897/5000000000 : ℝ)|=(2460458897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s0_7 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1995040163/10000000000 : ℝ)*x 0 + (-7287301533/10000000000 : ℝ)*x 1 + (12021453/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1995040163/10000000000 : ℝ)^91 ≤ (7072582106477/50000000000000 : ℝ)^75 := by
    have hnat : (1995040163 : ℕ)^91*50000000000000^75 ≤ 7072582106477^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995040163 10000000000 7072582106477 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7287301533/10000000000 : ℝ)^91 ≤ (851447074523/1250000000000 : ℝ)^75 := by
    have hnat : (7287301533 : ℕ)^91*1250000000000^75 ≤ 851447074523^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7287301533 10000000000 851447074523 1250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12021453/50000000 : ℝ)^91 ≤ (17739069815083/100000000000000 : ℝ)^75 := by
    have hnat : (12021453 : ℕ)^91*100000000000000^75 ≤ 17739069815083^75*50000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12021453 50000000 17739069815083 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1995040163/10000000000 : ℝ), (-7287301533/10000000000 : ℝ), (12021453/50000000 : ℝ)] ![(7072582106477/50000000000000 : ℝ), (851447074523/1250000000000 : ℝ), (17739069815083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1995040163/10000000000 : ℝ)|^91 ≤ (7072582106477/50000000000000 : ℝ)^75
        have hw : |(-1995040163/10000000000 : ℝ)|=(1995040163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7287301533/10000000000 : ℝ)|^91 ≤ (851447074523/1250000000000 : ℝ)^75
        have hw : |(-7287301533/10000000000 : ℝ)|=(7287301533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12021453/50000000 : ℝ)|^91 ≤ (17739069815083/100000000000000 : ℝ)^75
        have hw : |(12021453/50000000 : ℝ)|=(12021453/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s0_8 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1382309489/2000000000 : ℝ)*x 0 + (1138181819/5000000000 : ℝ)*x 1 + (2601710171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1382309489/2000000000 : ℝ)^91 ≤ (159695016991/250000000000 : ℝ)^75 := by
    have hnat : (1382309489 : ℕ)^91*250000000000^75 ≤ 159695016991^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382309489 2000000000 159695016991 250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1138181819/5000000000 : ℝ)^91 ≤ (16600449817917/100000000000000 : ℝ)^75 := by
    have hnat : (1138181819 : ℕ)^91*100000000000000^75 ≤ 16600449817917^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138181819 5000000000 16600449817917 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2601710171/10000000000 : ℝ)^91 ≤ (9760771684543/50000000000000 : ℝ)^75 := by
    have hnat : (2601710171 : ℕ)^91*50000000000000^75 ≤ 9760771684543^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601710171 10000000000 9760771684543 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1382309489/2000000000 : ℝ), (1138181819/5000000000 : ℝ), (2601710171/10000000000 : ℝ)] ![(159695016991/250000000000 : ℝ), (16600449817917/100000000000000 : ℝ), (9760771684543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1382309489/2000000000 : ℝ)|^91 ≤ (159695016991/250000000000 : ℝ)^75
        have hw : |(1382309489/2000000000 : ℝ)|=(1382309489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1138181819/5000000000 : ℝ)|^91 ≤ (16600449817917/100000000000000 : ℝ)^75
        have hw : |(1138181819/5000000000 : ℝ)|=(1138181819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2601710171/10000000000 : ℝ)|^91 ≤ (9760771684543/50000000000000 : ℝ)^75
        have hw : |(2601710171/10000000000 : ℝ)|=(2601710171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s0_9 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1718750673/5000000000 : ℝ)*x 0 + (-881581561/2500000000 : ℝ)*x 1 + (-1280216787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1718750673/5000000000 : ℝ)^91 ≤ (13686047037859/50000000000000 : ℝ)^75 := by
    have hnat : (1718750673 : ℕ)^91*50000000000000^75 ≤ 13686047037859^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1718750673 5000000000 13686047037859 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (881581561/2500000000 : ℝ)^91 ≤ (14116313389577/50000000000000 : ℝ)^75 := by
    have hnat : (881581561 : ℕ)^91*50000000000000^75 ≤ 14116313389577^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881581561 2500000000 14116313389577 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1280216787/2500000000 : ℝ)^91 ≤ (22197639563459/50000000000000 : ℝ)^75 := by
    have hnat : (1280216787 : ℕ)^91*50000000000000^75 ≤ 22197639563459^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280216787 2500000000 22197639563459 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1718750673/5000000000 : ℝ), (-881581561/2500000000 : ℝ), (-1280216787/2500000000 : ℝ)] ![(13686047037859/50000000000000 : ℝ), (14116313389577/50000000000000 : ℝ), (22197639563459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1718750673/5000000000 : ℝ)|^91 ≤ (13686047037859/50000000000000 : ℝ)^75
        have hw : |(1718750673/5000000000 : ℝ)|=(1718750673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-881581561/2500000000 : ℝ)|^91 ≤ (14116313389577/50000000000000 : ℝ)^75
        have hw : |(-881581561/2500000000 : ℝ)|=(881581561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1280216787/2500000000 : ℝ)|^91 ≤ (22197639563459/50000000000000 : ℝ)^75
        have hw : |(-1280216787/2500000000 : ℝ)|=(1280216787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s0_13 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (835997651/10000000000 : ℝ)*x 0 + (-6234263/5000000000 : ℝ)*x 1 + (1917986943/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835997651/10000000000 : ℝ)^91 ≤ (4923517312311/100000000000000 : ℝ)^75 := by
    have hnat : (835997651 : ℕ)^91*100000000000000^75 ≤ 4923517312311^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835997651 10000000000 4923517312311 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6234263/5000000000 : ℝ)^91 ≤ (2994026729/10000000000000 : ℝ)^75 := by
    have hnat : (6234263 : ℕ)^91*10000000000000^75 ≤ 2994026729^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6234263 5000000000 2994026729 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1917986943/2000000000 : ℝ)^91 ≤ (11880817801449/12500000000000 : ℝ)^75 := by
    have hnat : (1917986943 : ℕ)^91*12500000000000^75 ≤ 11880817801449^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917986943 2000000000 11880817801449 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(835997651/10000000000 : ℝ), (-6234263/5000000000 : ℝ), (1917986943/2000000000 : ℝ)] ![(4923517312311/100000000000000 : ℝ), (2994026729/10000000000000 : ℝ), (11880817801449/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(835997651/10000000000 : ℝ)|^91 ≤ (4923517312311/100000000000000 : ℝ)^75
        have hw : |(835997651/10000000000 : ℝ)|=(835997651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6234263/5000000000 : ℝ)|^91 ≤ (2994026729/10000000000000 : ℝ)^75
        have hw : |(-6234263/5000000000 : ℝ)|=(6234263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1917986943/2000000000 : ℝ)|^91 ≤ (11880817801449/12500000000000 : ℝ)^75
        have hw : |(1917986943/2000000000 : ℝ)|=(1917986943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s0_14 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2272819811/10000000000 : ℝ)*x 0 + (-6832458757/10000000000 : ℝ)*x 1 + (2702043073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2272819811/10000000000 : ℝ)^91 ≤ (16569098290467/100000000000000 : ℝ)^75 := by
    have hnat : (2272819811 : ℕ)^91*100000000000000^75 ≤ 16569098290467^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272819811 10000000000 16569098290467 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6832458757/10000000000 : ℝ)^91 ≤ (62992200944363/100000000000000 : ℝ)^75 := by
    have hnat : (6832458757 : ℕ)^91*100000000000000^75 ≤ 62992200944363^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6832458757 10000000000 62992200944363 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702043073/10000000000 : ℝ)^91 ≤ (20438700743523/100000000000000 : ℝ)^75 := by
    have hnat : (2702043073 : ℕ)^91*100000000000000^75 ≤ 20438700743523^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702043073 10000000000 20438700743523 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2272819811/10000000000 : ℝ), (-6832458757/10000000000 : ℝ), (2702043073/10000000000 : ℝ)] ![(16569098290467/100000000000000 : ℝ), (62992200944363/100000000000000 : ℝ), (20438700743523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2272819811/10000000000 : ℝ)|^91 ≤ (16569098290467/100000000000000 : ℝ)^75
        have hw : |(-2272819811/10000000000 : ℝ)|=(2272819811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6832458757/10000000000 : ℝ)|^91 ≤ (62992200944363/100000000000000 : ℝ)^75
        have hw : |(-6832458757/10000000000 : ℝ)|=(6832458757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702043073/10000000000 : ℝ)|^91 ≤ (20438700743523/100000000000000 : ℝ)^75
        have hw : |(2702043073/10000000000 : ℝ)|=(2702043073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s0_15 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7278709921/10000000000 : ℝ)*x 0 + (412961897/2000000000 : ℝ)*x 1 + (1173868277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7278709921/10000000000 : ℝ)^91 ≤ (6801833857529/10000000000000 : ℝ)^75 := by
    have hnat : (7278709921 : ℕ)^91*10000000000000^75 ≤ 6801833857529^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7278709921 10000000000 6801833857529 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412961897/2000000000 : ℝ)^91 ≤ (3686897458521/25000000000000 : ℝ)^75 := by
    have hnat : (412961897 : ℕ)^91*25000000000000^75 ≤ 3686897458521^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412961897 2000000000 3686897458521 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1173868277/5000000000 : ℝ)^91 ≤ (8617035791173/50000000000000 : ℝ)^75 := by
    have hnat : (1173868277 : ℕ)^91*50000000000000^75 ≤ 8617035791173^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173868277 5000000000 8617035791173 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7278709921/10000000000 : ℝ), (412961897/2000000000 : ℝ), (1173868277/5000000000 : ℝ)] ![(6801833857529/10000000000000 : ℝ), (3686897458521/25000000000000 : ℝ), (8617035791173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7278709921/10000000000 : ℝ)|^91 ≤ (6801833857529/10000000000000 : ℝ)^75
        have hw : |(7278709921/10000000000 : ℝ)|=(7278709921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(412961897/2000000000 : ℝ)|^91 ≤ (3686897458521/25000000000000 : ℝ)^75
        have hw : |(412961897/2000000000 : ℝ)|=(412961897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1173868277/5000000000 : ℝ)|^91 ≤ (8617035791173/50000000000000 : ℝ)^75
        have hw : |(1173868277/5000000000 : ℝ)|=(1173868277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s0_16 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3405280793/10000000000 : ℝ)*x 0 + (-3671190957/10000000000 : ℝ)*x 1 + (-5015838383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3405280793/10000000000 : ℝ)^91 ≤ (2706110669783/10000000000000 : ℝ)^75 := by
    have hnat : (3405280793 : ℕ)^91*10000000000000^75 ≤ 2706110669783^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3405280793 10000000000 2706110669783 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3671190957/10000000000 : ℝ)^91 ≤ (5929195794521/20000000000000 : ℝ)^75 := by
    have hnat : (3671190957 : ℕ)^91*20000000000000^75 ≤ 5929195794521^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3671190957 10000000000 5929195794521 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5015838383/10000000000 : ℝ)^91 ≤ (21646457157721/50000000000000 : ℝ)^75 := by
    have hnat : (5015838383 : ℕ)^91*50000000000000^75 ≤ 21646457157721^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015838383 10000000000 21646457157721 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3405280793/10000000000 : ℝ), (-3671190957/10000000000 : ℝ), (-5015838383/10000000000 : ℝ)] ![(2706110669783/10000000000000 : ℝ), (5929195794521/20000000000000 : ℝ), (21646457157721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3405280793/10000000000 : ℝ)|^91 ≤ (2706110669783/10000000000000 : ℝ)^75
        have hw : |(3405280793/10000000000 : ℝ)|=(3405280793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3671190957/10000000000 : ℝ)|^91 ≤ (5929195794521/20000000000000 : ℝ)^75
        have hw : |(-3671190957/10000000000 : ℝ)|=(3671190957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5015838383/10000000000 : ℝ)|^91 ≤ (21646457157721/50000000000000 : ℝ)^75
        have hw : |(-5015838383/10000000000 : ℝ)|=(5015838383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s0_20 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (442939931/10000000000 : ℝ)*x 0 + (-80888757/10000000000 : ℝ)*x 1 + (9787909709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442939931/10000000000 : ℝ)^91 ≤ (284757438639/12500000000000 : ℝ)^75 := by
    have hnat : (442939931 : ℕ)^91*12500000000000^75 ≤ 284757438639^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442939931 10000000000 284757438639 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80888757/10000000000 : ℝ)^91 ≤ (289448277611/100000000000000 : ℝ)^75 := by
    have hnat : (80888757 : ℕ)^91*100000000000000^75 ≤ 289448277611^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80888757 10000000000 289448277611 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9787909709/10000000000 : ℝ)^91 ≤ (3044765381199/3125000000000 : ℝ)^75 := by
    have hnat : (9787909709 : ℕ)^91*3125000000000^75 ≤ 3044765381199^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9787909709 10000000000 3044765381199 3125000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(442939931/10000000000 : ℝ), (-80888757/10000000000 : ℝ), (9787909709/10000000000 : ℝ)] ![(284757438639/12500000000000 : ℝ), (289448277611/100000000000000 : ℝ), (3044765381199/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(442939931/10000000000 : ℝ)|^91 ≤ (284757438639/12500000000000 : ℝ)^75
        have hw : |(442939931/10000000000 : ℝ)|=(442939931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-80888757/10000000000 : ℝ)|^91 ≤ (289448277611/100000000000000 : ℝ)^75
        have hw : |(-80888757/10000000000 : ℝ)|=(80888757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9787909709/10000000000 : ℝ)|^91 ≤ (3044765381199/3125000000000 : ℝ)^75
        have hw : |(9787909709/10000000000 : ℝ)|=(9787909709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s0_21 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1714453861/10000000000 : ℝ)*x 0 + (-3772611837/5000000000 : ℝ)*x 1 + (2341567217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1714453861/10000000000 : ℝ)^91 ≤ (2353798610051/20000000000000 : ℝ)^75 := by
    have hnat : (1714453861 : ℕ)^91*20000000000000^75 ≤ 2353798610051^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714453861 10000000000 2353798610051 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3772611837/5000000000 : ℝ)^91 ≤ (17762967153447/25000000000000 : ℝ)^75 := by
    have hnat : (3772611837 : ℕ)^91*25000000000000^75 ≤ 17762967153447^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3772611837 5000000000 17762967153447 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2341567217/10000000000 : ℝ)^91 ≤ (8589569164431/50000000000000 : ℝ)^75 := by
    have hnat : (2341567217 : ℕ)^91*50000000000000^75 ≤ 8589569164431^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2341567217 10000000000 8589569164431 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1714453861/10000000000 : ℝ), (-3772611837/5000000000 : ℝ), (2341567217/10000000000 : ℝ)] ![(2353798610051/20000000000000 : ℝ), (17762967153447/25000000000000 : ℝ), (8589569164431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1714453861/10000000000 : ℝ)|^91 ≤ (2353798610051/20000000000000 : ℝ)^75
        have hw : |(-1714453861/10000000000 : ℝ)|=(1714453861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3772611837/5000000000 : ℝ)|^91 ≤ (17762967153447/25000000000000 : ℝ)^75
        have hw : |(-3772611837/5000000000 : ℝ)|=(3772611837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2341567217/10000000000 : ℝ)|^91 ≤ (8589569164431/50000000000000 : ℝ)^75
        have hw : |(2341567217/10000000000 : ℝ)|=(2341567217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s0_22 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (933281403/1250000000 : ℝ)*x 0 + (1902217639/10000000000 : ℝ)*x 1 + (2264868103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (933281403/1250000000 : ℝ)^91 ≤ (70150561795909/100000000000000 : ℝ)^75 := by
    have hnat : (933281403 : ℕ)^91*100000000000000^75 ≤ 70150561795909^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933281403 1250000000 70150561795909 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1902217639/10000000000 : ℝ)^91 ≤ (13350649104257/100000000000000 : ℝ)^75 := by
    have hnat : (1902217639 : ℕ)^91*100000000000000^75 ≤ 13350649104257^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902217639 10000000000 13350649104257 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2264868103/10000000000 : ℝ)^91 ≤ (16498789088399/100000000000000 : ℝ)^75 := by
    have hnat : (2264868103 : ℕ)^91*100000000000000^75 ≤ 16498789088399^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264868103 10000000000 16498789088399 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(933281403/1250000000 : ℝ), (1902217639/10000000000 : ℝ), (2264868103/10000000000 : ℝ)] ![(70150561795909/100000000000000 : ℝ), (13350649104257/100000000000000 : ℝ), (16498789088399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(933281403/1250000000 : ℝ)|^91 ≤ (70150561795909/100000000000000 : ℝ)^75
        have hw : |(933281403/1250000000 : ℝ)|=(933281403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1902217639/10000000000 : ℝ)|^91 ≤ (13350649104257/100000000000000 : ℝ)^75
        have hw : |(1902217639/10000000000 : ℝ)|=(1902217639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2264868103/10000000000 : ℝ)|^91 ≤ (16498789088399/100000000000000 : ℝ)^75
        have hw : |(2264868103/10000000000 : ℝ)|=(2264868103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s0_23 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3038580141/10000000000 : ℝ)*x 0 + (-441408219/1250000000 : ℝ)*x 1 + (-2737726871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3038580141/10000000000 : ℝ)^91 ≤ (23567152391749/100000000000000 : ℝ)^75 := by
    have hnat : (3038580141 : ℕ)^91*100000000000000^75 ≤ 23567152391749^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3038580141 10000000000 23567152391749 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441408219/1250000000 : ℝ)^91 ≤ (14140308761453/50000000000000 : ℝ)^75 := by
    have hnat : (441408219 : ℕ)^91*50000000000000^75 ≤ 14140308761453^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441408219 1250000000 14140308761453 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2737726871/5000000000 : ℝ)^91 ≤ (48152230066013/100000000000000 : ℝ)^75 := by
    have hnat : (2737726871 : ℕ)^91*100000000000000^75 ≤ 48152230066013^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737726871 5000000000 48152230066013 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3038580141/10000000000 : ℝ), (-441408219/1250000000 : ℝ), (-2737726871/5000000000 : ℝ)] ![(23567152391749/100000000000000 : ℝ), (14140308761453/50000000000000 : ℝ), (48152230066013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3038580141/10000000000 : ℝ)|^91 ≤ (23567152391749/100000000000000 : ℝ)^75
        have hw : |(3038580141/10000000000 : ℝ)|=(3038580141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441408219/1250000000 : ℝ)|^91 ≤ (14140308761453/50000000000000 : ℝ)^75
        have hw : |(-441408219/1250000000 : ℝ)|=(441408219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2737726871/5000000000 : ℝ)|^91 ≤ (48152230066013/100000000000000 : ℝ)^75
        have hw : |(-2737726871/5000000000 : ℝ)|=(2737726871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s0_27 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1765388113/10000000000 : ℝ)*x 0 + (-4424853/2000000000 : ℝ)*x 1 + (1122320523/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1765388113/10000000000 : ℝ)^91 ≤ (2438911842979/20000000000000 : ℝ)^75 := by
    have hnat : (1765388113 : ℕ)^91*20000000000000^75 ≤ 2438911842979^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765388113 10000000000 2438911842979 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4424853/2000000000 : ℝ)^91 ≤ (60040026247/100000000000000 : ℝ)^75 := by
    have hnat : (4424853 : ℕ)^91*100000000000000^75 ≤ 60040026247^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4424853 2000000000 60040026247 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122320523/1250000000 : ℝ)^91 ≤ (87745400744589/100000000000000 : ℝ)^75 := by
    have hnat : (1122320523 : ℕ)^91*100000000000000^75 ≤ 87745400744589^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122320523 1250000000 87745400744589 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1765388113/10000000000 : ℝ), (-4424853/2000000000 : ℝ), (1122320523/1250000000 : ℝ)] ![(2438911842979/20000000000000 : ℝ), (60040026247/100000000000000 : ℝ), (87745400744589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1765388113/10000000000 : ℝ)|^91 ≤ (2438911842979/20000000000000 : ℝ)^75
        have hw : |(1765388113/10000000000 : ℝ)|=(1765388113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4424853/2000000000 : ℝ)|^91 ≤ (60040026247/100000000000000 : ℝ)^75
        have hw : |(-4424853/2000000000 : ℝ)|=(4424853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122320523/1250000000 : ℝ)|^91 ≤ (87745400744589/100000000000000 : ℝ)^75
        have hw : |(1122320523/1250000000 : ℝ)|=(1122320523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s1_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-589015039/2000000000 : ℝ)*x 0 + (-2717682669/5000000000 : ℝ)*x 1 + (1832486287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (589015039/2000000000 : ℝ)^91 ≤ (11345064124657/50000000000000 : ℝ)^75 := by
    have hnat : (589015039 : ℕ)^91*50000000000000^75 ≤ 11345064124657^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589015039 2000000000 11345064124657 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717682669/5000000000 : ℝ)^91 ≤ (47724809677619/100000000000000 : ℝ)^75 := by
    have hnat : (2717682669 : ℕ)^91*100000000000000^75 ≤ 47724809677619^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717682669 5000000000 47724809677619 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1832486287/5000000000 : ℝ)^91 ≤ (3698132757061/12500000000000 : ℝ)^75 := by
    have hnat : (1832486287 : ℕ)^91*12500000000000^75 ≤ 3698132757061^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1832486287 5000000000 3698132757061 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-589015039/2000000000 : ℝ), (-2717682669/5000000000 : ℝ), (1832486287/5000000000 : ℝ)] ![(11345064124657/50000000000000 : ℝ), (47724809677619/100000000000000 : ℝ), (3698132757061/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-589015039/2000000000 : ℝ)|^91 ≤ (11345064124657/50000000000000 : ℝ)^75
        have hw : |(-589015039/2000000000 : ℝ)|=(589015039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2717682669/5000000000 : ℝ)|^91 ≤ (47724809677619/100000000000000 : ℝ)^75
        have hw : |(-2717682669/5000000000 : ℝ)|=(2717682669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1832486287/5000000000 : ℝ)|^91 ≤ (3698132757061/12500000000000 : ℝ)^75
        have hw : |(1832486287/5000000000 : ℝ)|=(1832486287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s1_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (339037281/625000000 : ℝ)*x 0 + (1474587381/5000000000 : ℝ)*x 1 + (91819211/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (339037281/625000000 : ℝ)^91 ≤ (23805053605131/50000000000000 : ℝ)^75 := by
    have hnat : (339037281 : ℕ)^91*50000000000000^75 ≤ 23805053605131^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339037281 625000000 23805053605131 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1474587381/5000000000 : ℝ)^91 ≤ (11364228432597/50000000000000 : ℝ)^75 := by
    have hnat : (1474587381 : ℕ)^91*50000000000000^75 ≤ 11364228432597^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1474587381 5000000000 11364228432597 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91819211/250000000 : ℝ)^91 ≤ (296614359133/1000000000000 : ℝ)^75 := by
    have hnat : (91819211 : ℕ)^91*1000000000000^75 ≤ 296614359133^75*250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91819211 250000000 296614359133 1000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(339037281/625000000 : ℝ), (1474587381/5000000000 : ℝ), (91819211/250000000 : ℝ)] ![(23805053605131/50000000000000 : ℝ), (11364228432597/50000000000000 : ℝ), (296614359133/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(339037281/625000000 : ℝ)|^91 ≤ (23805053605131/50000000000000 : ℝ)^75
        have hw : |(339037281/625000000 : ℝ)|=(339037281/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1474587381/5000000000 : ℝ)|^91 ≤ (11364228432597/50000000000000 : ℝ)^75
        have hw : |(1474587381/5000000000 : ℝ)|=(1474587381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(91819211/250000000 : ℝ)|^91 ≤ (296614359133/1000000000000 : ℝ)^75
        have hw : |(91819211/250000000 : ℝ)|=(91819211/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s1_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3718542809/10000000000 : ℝ)*x 0 + (-1857229361/5000000000 : ℝ)*x 1 + (-2340852033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3718542809/10000000000 : ℝ)^91 ≤ (3763821275617/12500000000000 : ℝ)^75 := by
    have hnat : (3718542809 : ℕ)^91*12500000000000^75 ≤ 3763821275617^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3718542809 10000000000 3763821275617 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1857229361/5000000000 : ℝ)^91 ≤ (3758806166059/12500000000000 : ℝ)^75 := by
    have hnat : (1857229361 : ℕ)^91*12500000000000^75 ≤ 3758806166059^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1857229361 5000000000 3758806166059 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2340852033/5000000000 : ℝ)^91 ≤ (4977372556277/12500000000000 : ℝ)^75 := by
    have hnat : (2340852033 : ℕ)^91*12500000000000^75 ≤ 4977372556277^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2340852033 5000000000 4977372556277 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3718542809/10000000000 : ℝ), (-1857229361/5000000000 : ℝ), (-2340852033/5000000000 : ℝ)] ![(3763821275617/12500000000000 : ℝ), (3758806166059/12500000000000 : ℝ), (4977372556277/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3718542809/10000000000 : ℝ)|^91 ≤ (3763821275617/12500000000000 : ℝ)^75
        have hw : |(3718542809/10000000000 : ℝ)|=(3718542809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1857229361/5000000000 : ℝ)|^91 ≤ (3758806166059/12500000000000 : ℝ)^75
        have hw : |(-1857229361/5000000000 : ℝ)|=(1857229361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2340852033/5000000000 : ℝ)|^91 ≤ (4977372556277/12500000000000 : ℝ)^75
        have hw : |(-2340852033/5000000000 : ℝ)|=(2340852033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327013_s1_6 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1990984131/5000000000 : ℝ)*x 0 + (-3947763591/10000000000 : ℝ)*x 1 + (525010559/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1990984131/5000000000 : ℝ)^91 ≤ (16358946343859/50000000000000 : ℝ)^75 := by
    have hnat : (1990984131 : ℕ)^91*50000000000000^75 ≤ 16358946343859^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990984131 5000000000 16358946343859 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3947763591/10000000000 : ℝ)^91 ≤ (32377206859409/100000000000000 : ℝ)^75 := by
    have hnat : (3947763591 : ℕ)^91*100000000000000^75 ≤ 32377206859409^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3947763591 10000000000 32377206859409 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525010559/1250000000 : ℝ)^91 ≤ (2181556277889/6250000000000 : ℝ)^75 := by
    have hnat : (525010559 : ℕ)^91*6250000000000^75 ≤ 2181556277889^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525010559 1250000000 2181556277889 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1990984131/5000000000 : ℝ), (-3947763591/10000000000 : ℝ), (525010559/1250000000 : ℝ)] ![(16358946343859/50000000000000 : ℝ), (32377206859409/100000000000000 : ℝ), (2181556277889/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1990984131/5000000000 : ℝ)|^91 ≤ (16358946343859/50000000000000 : ℝ)^75
        have hw : |(1990984131/5000000000 : ℝ)|=(1990984131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3947763591/10000000000 : ℝ)|^91 ≤ (32377206859409/100000000000000 : ℝ)^75
        have hw : |(-3947763591/10000000000 : ℝ)|=(3947763591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525010559/1250000000 : ℝ)|^91 ≤ (2181556277889/6250000000000 : ℝ)^75
        have hw : |(525010559/1250000000 : ℝ)|=(525010559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c327013 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (20519/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (20519/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2184915741/10000000000 : ℝ)*X 0 0+(-6852157133/10000000000 : ℝ)*X 0 1+(2762250229/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((685351593/1000000000 : ℝ)*X 1 0+(281870559/1250000000 : ℝ)*X 1 1+(2693560323/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1735442389/5000000000 : ℝ)*X 2 0+(-741541949/2000000000 : ℝ)*X 2 1+(-2460458897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1995040163/10000000000 : ℝ)*X 0 0+(-7287301533/10000000000 : ℝ)*X 0 1+(12021453/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1382309489/2000000000 : ℝ)*X 1 0+(1138181819/5000000000 : ℝ)*X 1 1+(2601710171/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1718750673/5000000000 : ℝ)*X 2 0+(-881581561/2500000000 : ℝ)*X 2 1+(-1280216787/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((835997651/10000000000 : ℝ)*X 0 0+(-6234263/5000000000 : ℝ)*X 0 1+(1917986943/2000000000 : ℝ)*X 0 2+(835997651/10000000000 : ℝ)*X 1 0+(-6234263/5000000000 : ℝ)*X 1 1+(1917986943/2000000000 : ℝ)*X 1 2+(835997651/10000000000 : ℝ)*X 2 0+(-6234263/5000000000 : ℝ)*X 2 1+(1917986943/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-2272819811/10000000000 : ℝ)*X 0 0+(-6832458757/10000000000 : ℝ)*X 0 1+(2702043073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((7278709921/10000000000 : ℝ)*X 1 0+(412961897/2000000000 : ℝ)*X 1 1+(1173868277/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3405280793/10000000000 : ℝ)*X 2 0+(-3671190957/10000000000 : ℝ)*X 2 1+(-5015838383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((442939931/10000000000 : ℝ)*X 0 0+(-80888757/10000000000 : ℝ)*X 0 1+(9787909709/10000000000 : ℝ)*X 0 2+(442939931/10000000000 : ℝ)*X 1 0+(-80888757/10000000000 : ℝ)*X 1 1+(9787909709/10000000000 : ℝ)*X 1 2+(442939931/10000000000 : ℝ)*X 2 0+(-80888757/10000000000 : ℝ)*X 2 1+(9787909709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1714453861/10000000000 : ℝ)*X 0 0+(-3772611837/5000000000 : ℝ)*X 0 1+(2341567217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((933281403/1250000000 : ℝ)*X 1 0+(1902217639/10000000000 : ℝ)*X 1 1+(2264868103/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3038580141/10000000000 : ℝ)*X 2 0+(-441408219/1250000000 : ℝ)*X 2 1+(-2737726871/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1765388113/10000000000 : ℝ)*X 0 0+(-4424853/2000000000 : ℝ)*X 0 1+(1122320523/1250000000 : ℝ)*X 0 2+(1765388113/10000000000 : ℝ)*X 1 0+(-4424853/2000000000 : ℝ)*X 1 1+(1122320523/1250000000 : ℝ)*X 1 2+(1765388113/10000000000 : ℝ)*X 2 0+(-4424853/2000000000 : ℝ)*X 2 1+(1122320523/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((20163/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20163/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (49855033851490881/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (157956460351/62500000000 : ℝ)*(base40) + (2851509731687/1000000000000 : ℝ)*(base50) + (150664200703/500000000000 : ℝ)*(base59) + (2687841571139/250000000000 : ℝ)*(major_s0_0) + (2687841571139/250000000000 : ℝ)*(major_s0_1) + (2687841571139/250000000000 : ℝ)*(major_s0_2) + (5922917/250000000000 : ℝ)*(sp_s0_0) + (3953761/7812500000 : ℝ)*(sp_s0_1) + (2052747964711/125000000000 : ℝ)*(sp_s0_7) + (4105375331987/250000000000 : ℝ)*(sp_s0_8) + (1642151464687/100000000000 : ℝ)*(sp_s0_9) + (1270180459021/250000000000 : ℝ)*(sp_s0_13) + (211821331/500000000000 : ℝ)*(sp_s0_16) + (4319989/62500000000 : ℝ)*(sp_s0_23) + (1270180459021/250000000000 : ℝ)*(f.failure) + (4105501852339/250000000000 : ℝ)*(f.sum) + (167111847/625000000000000000000 : ℝ)*base62 + (139285423629767/1250000000000000000000000000 : ℝ)*base64 + (298240213870233/1250000000000000000000000000 : ℝ)*base66 + (67830400721143/625000000000000000000000000 : ℝ)*base68 + (257222970572053/1250000000000000000000000000 : ℝ)*base70 + (21208646129767/1250000000000000000000000000 : ℝ)*base73 + (236725401653857/625000000000000000000000000 : ℝ)*base74 + (82556138653857/625000000000000000000000000 : ℝ)*base77 + (114527131495233/625000000000000000000000000 : ℝ)*base78 + (7169/25000000000000000 : ℝ)*base86 + (7169/25000000000000000 : ℝ)*base88 + (7169/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-32989/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-32989/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (741425447038704581313/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (570849925253/250000000000 : ℝ)*(base40) + (1816214499491/1000000000000 : ℝ)*(base50) + (17929/12500000000 : ℝ)*(base59) + (8632699252859/1000000000000 : ℝ)*(major_s0_0) + (8632699252859/1000000000000 : ℝ)*(major_s0_1) + (8632699252859/1000000000000 : ℝ)*(major_s0_2) + (16810633/200000000000 : ℝ)*(sp_s0_9) + (15043967/500000000000 : ℝ)*(sp_s0_13) + (13185883056757/1000000000000 : ℝ)*(sp_s0_14) + (2637158053203/200000000000 : ℝ)*(sp_s0_15) + (659287950403/50000000000 : ℝ)*(sp_s0_16) + (4079483383889/1000000000000 : ℝ)*(sp_s0_20) + (46395371/500000000000 : ℝ)*(sp_s0_22) + (9998883/250000000000 : ℝ)*(sp_s0_23) + (4079513471823/1000000000000 : ℝ)*(f.failure) + (13185883056757/1000000000000 : ℝ)*(f.sum) + (520300883/5000000000000000000000 : ℝ)*base62 + (3657522947772927/5000000000000000000000000000 : ℝ)*base64 + (337041585227073/5000000000000000000000000000 : ℝ)*base66 + (786931189835217/2500000000000000000000000000 : ℝ)*base69 + (578587558897507/5000000000000000000000000000 : ℝ)*base71 + (2482651822727073/5000000000000000000000000000 : ℝ)*base72 + (374215287414783/2500000000000000000000000000 : ℝ)*base75 + (669559869085217/2500000000000000000000000000 : ℝ)*base77 + (2146324890977073/2500000000000000000000000000 : ℝ)*base78 + (36853/100000000000000000 : ℝ)*base87 + (36853/100000000000000000 : ℝ)*base89 + (36853/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16779/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16779/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11210930714935403123997/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (311344102159/500000000000 : ℝ)*(base3) + (1157355880403/500000000000 : ℝ)*(base40) + (767933/200000000000 : ℝ)*(base43) + (474566301089/200000000000 : ℝ)*(base50) + (119754826607/250000000000 : ℝ)*(base59) + (7077251883967/1000000000000 : ℝ)*(major_s0_0) + (3538624022151/500000000000 : ℝ)*(major_s0_1) + (7077251883967/1000000000000 : ℝ)*(major_s0_2) + (20366537/250000000000 : ℝ)*(sp_s0_2) + (3120859/50000000000 : ℝ)*(sp_s0_15) + (5405015407201/500000000000 : ℝ)*(sp_s0_21) + (5716330220603/500000000000 : ℝ)*(sp_s0_22) + (5404974674127/500000000000 : ℝ)*(sp_s0_23) + (136088746519/50000000000 : ℝ)*(sp_s0_27) + (3344463134699/1000000000000 : ℝ)*(f.failure) + (10810034654067/1000000000000 : ℝ)*(f.sum) + (137674264896521/500000000000000000000000000 : ℝ)*base62 + (1859920660041549/5000000000000000000000000000 : ℝ)*base65 + (441675274851397/2500000000000000000000000000 : ℝ)*base66 + (1430593937023779/2500000000000000000000000000 : ℝ)*base68 + (50360223006009/5000000000000000000000000000 : ℝ)*base70 + (206511234958451/5000000000000000000000000000 : ℝ)*base73 + (408285811729413/1250000000000000000000000000 : ℝ)*base74 + (374664020976221/2500000000000000000000000000 : ℝ)*base77 + (635177778744343/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (90089/100000000000000000 : ℝ)*base87 + (90089/100000000000000000 : ℝ)*base89 + (90089/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (20163/50000 : ℝ) ^ (89/16 : ℝ) ≤ (639834087194740313/100000000000000000000 : ℝ) := by
    have hpowers : (20163/50000 : ℝ)^89 ≤ (639834087194740313/100000000000000000000 : ℝ)^16 := by
      have hnat : (20163 : ℕ)^89*100000000000000000000^16 ≤ 639834087194740313^16*50000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20163 50000 639834087194740313 100000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20163/50000 : ℝ)) (X := (639834087194740313/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100639834087194740313/100000000000000000000 : ℝ) ≤ (2002294513713119/2000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (100639834087194740313/100000000000000000000 : ℝ)^16 ≤ (2002294513713119/2000000000000000 : ℝ)^89 := by
      have hnat : (100639834087194740313 : ℕ)^16*2000000000000000^89 ≤ 2002294513713119^89*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100639834087194740313 100000000000000000000 2002294513713119 2000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002294513713119/2000000000000000 : ℝ)) (X := (100639834087194740313/100000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50639834087194740313/50000000000000000000 : ℝ) ≤ (5011442733071963/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (50639834087194740313/50000000000000000000 : ℝ)^16 ≤ (5011442733071963/5000000000000000 : ℝ)^89 := by
      have hnat : (50639834087194740313 : ℕ)^16*5000000000000000^89 ≤ 5011442733071963^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50639834087194740313 50000000000000000000 5011442733071963 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011442733071963/5000000000000000 : ℝ)) (X := (50639834087194740313/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(764837904373/268840000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3804299192777/1344200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (20163/50000 : ℝ)) (alpha := (764837904373/268840000000000 : ℝ)) (beta := (3804299192777/1344200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (20163/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(764837904373/268840000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3804299192777/1344200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (32989/100000 : ℝ) ^ (89/16 : ℝ) ≤ (209376724781048433/100000000000000000000 : ℝ) := by
    have hpowers : (32989/100000 : ℝ)^89 ≤ (209376724781048433/100000000000000000000 : ℝ)^16 := by
      have hnat : (32989 : ℕ)^89*100000000000000000000^16 ≤ 209376724781048433^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32989 100000 209376724781048433 100000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (32989/100000 : ℝ)) (X := (209376724781048433/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100209376724781048433/100000000000000000000 : ℝ) ≤ (2500940211978753/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (100209376724781048433/100000000000000000000 : ℝ)^16 ≤ (2500940211978753/2500000000000000 : ℝ)^89 := by
      have hnat : (100209376724781048433 : ℕ)^16*2500000000000000^89 ≤ 2500940211978753^89*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100209376724781048433 100000000000000000000 2500940211978753 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500940211978753/2500000000000000 : ℝ)) (X := (100209376724781048433/100000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50209376724781048433/50000000000000000000 : ℝ) ≤ (5003757628054723/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (50209376724781048433/50000000000000000000 : ℝ)^16 ≤ (5003757628054723/5000000000000000 : ℝ)^89 := by
      have hnat : (50209376724781048433 : ℕ)^16*5000000000000000^89 ≤ 5003757628054723^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50209376724781048433 50000000000000000000 5003757628054723 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003757628054723/5000000000000000 : ℝ)) (X := (50209376724781048433/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(940211978753/824725000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1877204097217/1649450000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (32989/100000 : ℝ)) (alpha := (940211978753/824725000000000 : ℝ)) (beta := (1877204097217/1649450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (32989/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(940211978753/824725000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1877204097217/1649450000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (16779/50000 : ℝ) ^ (89/16 : ℝ) ≤ (115135868711813357/50000000000000000000 : ℝ) := by
    have hpowers : (16779/50000 : ℝ)^89 ≤ (115135868711813357/50000000000000000000 : ℝ)^16 := by
      have hnat : (16779 : ℕ)^89*50000000000000000000^16 ≤ 115135868711813357^16*50000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16779 50000 115135868711813357 50000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16779/50000 : ℝ)) (X := (115135868711813357/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50115135868711813357/50000000000000000000 : ℝ) ≤ (500206790632253/500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (50115135868711813357/50000000000000000000 : ℝ)^16 ≤ (500206790632253/500000000000000 : ℝ)^89 := by
      have hnat : (50115135868711813357 : ℕ)^16*500000000000000^89 ≤ 500206790632253^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50115135868711813357 50000000000000000000 500206790632253 500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500206790632253/500000000000000 : ℝ)) (X := (50115135868711813357/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25115135868711813357/25000000000000000000 : ℝ) ≤ (5004131919533461/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (25115135868711813357/25000000000000000000 : ℝ)^16 ≤ (5004131919533461/5000000000000000 : ℝ)^89 := by
      have hnat : (25115135868711813357 : ℕ)^16*5000000000000000^89 ≤ 5004131919533461^89*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25115135868711813357 25000000000000000000 5004131919533461 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004131919533461/5000000000000000 : ℝ)) (X := (25115135868711813357/25000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(68930210751/55930000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(294859030133/239700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (16779/50000 : ℝ)) (alpha := (68930210751/55930000000000 : ℝ)) (beta := (294859030133/239700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (16779/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(68930210751/55930000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(294859030133/239700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-589015039/2000000000 : ℝ)*X 0 0+(-2717682669/5000000000 : ℝ)*X 0 1+(1832486287/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((339037281/625000000 : ℝ)*X 1 0+(1474587381/5000000000 : ℝ)*X 1 1+(91819211/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3718542809/10000000000 : ℝ)*X 2 0+(-1857229361/5000000000 : ℝ)*X 2 1+(-2340852033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1990984131/5000000000 : ℝ)*X 0 0+(-3947763591/10000000000 : ℝ)*X 0 1+(525010559/1250000000 : ℝ)*X 0 2+(1990984131/5000000000 : ℝ)*X 1 0+(-3947763591/10000000000 : ℝ)*X 1 1+(525010559/1250000000 : ℝ)*X 1 2+(1990984131/5000000000 : ℝ)*X 2 0+(-3947763591/10000000000 : ℝ)*X 2 1+(525010559/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327013_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-484833/50000 : ℝ) < ((-211611/100000 : ℝ)*P 0+(-211611/100000 : ℝ)*P 1+(-211611/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-484833/50000 : ℝ) < (-57057292785222507077253941177217/5996493002500000000000000000000 : ℝ) := by norm_num
    linear_combination (287/200000000000 : ℝ)*(base1) + (821/500000000000 : ℝ)*(base3) + (19/1000000000000 : ℝ)*(base21) + (19/1000000000000 : ℝ)*(base22) + (153/125000000000 : ℝ)*(base39) + (537197245281/1000000000000 : ℝ)*(base40) + (761/1000000000000 : ℝ)*(base49) + (536089235447/1000000000000 : ℝ)*(base50) + (211611/100000 : ℝ)*(major_s1_0) + (211611/100000 : ℝ)*(major_s1_1) + (211611/100000 : ℝ)*(major_s1_2) + (1585851729981/500000000000 : ℝ)*(sp_s1_0) + (3171703460169/1000000000000 : ℝ)*(sp_s1_1) + (3171703458489/1000000000000 : ℝ)*(sp_s1_2) + (999999996923/1000000000000 : ℝ)*(sp_s1_6) + (3171703458527/1000000000000 : ℝ)*(f.sum) + (177429977339870107/461268692500000000000000000000 : ℝ)*base63 + (150655908449/7990000000000000000000000 : ℝ)*base64 + (3566145482071/82472500000000000000000000 : ℝ)*base67 + (396894454791/1118600000000000000000000 : ℝ)*base69 + (74603962113751/228514000000000000000000000 : ℝ)*base71 + (163032688649/1050156250000000000000000 : ℝ)*base72 + (149077455656697/329890000000000000000000000 : ℝ)*base75 + (7874507255729/67210000000000000000000000 : ℝ)*base76 + (14402795949137789/100781395000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p027_b004 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (c : Fin 88) (hlo : 12 ≤ c.val) (hhi : c.val < 14)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=12 ∨ c=13 := by omega
  rcases hc with rfl|rfl
  · exact collision_c327012 p hpa (by linarith only [hpb]) X hX
  · exact collision_c327013 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (c : Fin 88) (hlo : 12 ≤ c.val) (hhi : c.val < 14)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b004 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

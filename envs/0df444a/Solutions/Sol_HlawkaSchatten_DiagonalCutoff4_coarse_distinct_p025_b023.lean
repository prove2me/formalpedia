-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b023
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:02:47.479428+00:00
-- url     : https://prove2.me/submissions/669c79eb-6a2f-4820-b9e8-66054b024a78

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
theorem collision_support_c325047_s0_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-52041121/2000000000 : ℝ)*x 0 + (-3038814619/5000000000 : ℝ)*x 1 + (80742537/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52041121/2000000000 : ℝ)^87 ≤ (1143417687091/100000000000000 : ℝ)^71 := by
    have hnat : (52041121 : ℕ)^87*100000000000000^71 ≤ 1143417687091^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52041121 2000000000 1143417687091 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3038814619/5000000000 : ℝ)^87 ≤ (54324814040837/100000000000000 : ℝ)^71 := by
    have hnat : (3038814619 : ℕ)^87*100000000000000^71 ≤ 54324814040837^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3038814619 5000000000 54324814040837 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80742537/156250000 : ℝ)^87 ≤ (22265884133299/50000000000000 : ℝ)^71 := by
    have hnat : (80742537 : ℕ)^87*50000000000000^71 ≤ 22265884133299^71*156250000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80742537 156250000 22265884133299 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52041121/2000000000 : ℝ), (-3038814619/5000000000 : ℝ), (80742537/156250000 : ℝ)] ![(1143417687091/100000000000000 : ℝ), (54324814040837/100000000000000 : ℝ), (22265884133299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52041121/2000000000 : ℝ)|^87 ≤ (1143417687091/100000000000000 : ℝ)^71
        have hw : |(-52041121/2000000000 : ℝ)|=(52041121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3038814619/5000000000 : ℝ)|^87 ≤ (54324814040837/100000000000000 : ℝ)^71
        have hw : |(-3038814619/5000000000 : ℝ)|=(3038814619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80742537/156250000 : ℝ)|^87 ≤ (22265884133299/50000000000000 : ℝ)^71
        have hw : |(80742537/156250000 : ℝ)|=(80742537/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s0_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (16015757/31250000 : ℝ)*x 0 + (3666436323/10000000000 : ℝ)*x 1 + (106281051/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16015757/31250000 : ℝ)^87 ≤ (22041805222761/50000000000000 : ℝ)^71 := by
    have hnat : (16015757 : ℕ)^87*50000000000000^71 ≤ 22041805222761^71*31250000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16015757 31250000 22041805222761 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3666436323/10000000000 : ℝ)^87 ≤ (5848919448603/20000000000000 : ℝ)^71 := by
    have hnat : (3666436323 : ℕ)^87*20000000000000^71 ≤ 5848919448603^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3666436323 10000000000 5848919448603 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106281051/312500000 : ℝ)^87 ≤ (266717922951/1000000000000 : ℝ)^71 := by
    have hnat : (106281051 : ℕ)^87*1000000000000^71 ≤ 266717922951^71*312500000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106281051 312500000 266717922951 1000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16015757/31250000 : ℝ), (3666436323/10000000000 : ℝ), (106281051/312500000 : ℝ)] ![(22041805222761/50000000000000 : ℝ), (5848919448603/20000000000000 : ℝ), (266717922951/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16015757/31250000 : ℝ)|^87 ≤ (22041805222761/50000000000000 : ℝ)^71
        have hw : |(16015757/31250000 : ℝ)|=(16015757/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3666436323/10000000000 : ℝ)|^87 ≤ (5848919448603/20000000000000 : ℝ)^71
        have hw : |(3666436323/10000000000 : ℝ)|=(3666436323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(106281051/312500000 : ℝ)|^87 ≤ (266717922951/1000000000000 : ℝ)^71
        have hw : |(106281051/312500000 : ℝ)|=(106281051/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s0_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5490006501/10000000000 : ℝ)*x 0 + (-904679113/2500000000 : ℝ)*x 1 + (-760400619/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5490006501/10000000000 : ℝ)^87 ≤ (2997540568903/6250000000000 : ℝ)^71 := by
    have hnat : (5490006501 : ℕ)^87*6250000000000^71 ≤ 2997540568903^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490006501 10000000000 2997540568903 6250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904679113/2500000000 : ℝ)^87 ≤ (7194720047819/25000000000000 : ℝ)^71 := by
    have hnat : (904679113 : ℕ)^87*25000000000000^71 ≤ 7194720047819^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904679113 2500000000 7194720047819 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (760400619/2500000000 : ℝ)^87 ≤ (11630235348139/50000000000000 : ℝ)^71 := by
    have hnat : (760400619 : ℕ)^87*50000000000000^71 ≤ 11630235348139^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760400619 2500000000 11630235348139 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5490006501/10000000000 : ℝ), (-904679113/2500000000 : ℝ), (-760400619/2500000000 : ℝ)] ![(2997540568903/6250000000000 : ℝ), (7194720047819/25000000000000 : ℝ), (11630235348139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5490006501/10000000000 : ℝ)|^87 ≤ (2997540568903/6250000000000 : ℝ)^71
        have hw : |(5490006501/10000000000 : ℝ)|=(5490006501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-904679113/2500000000 : ℝ)|^87 ≤ (7194720047819/25000000000000 : ℝ)^71
        have hw : |(-904679113/2500000000 : ℝ)|=(904679113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-760400619/2500000000 : ℝ)|^87 ≤ (11630235348139/50000000000000 : ℝ)^71
        have hw : |(-760400619/2500000000 : ℝ)|=(760400619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s0_7 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-258788279/10000000000 : ℝ)*x 0 + (-379991701/500000000 : ℝ)*x 1 + (1739531677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258788279/10000000000 : ℝ)^87 ≤ (1135790719261/100000000000000 : ℝ)^71 := by
    have hnat : (258788279 : ℕ)^87*100000000000000^71 ≤ 1135790719261^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258788279 10000000000 1135790719261 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (379991701/500000000 : ℝ)^87 ≤ (7144026571483/10000000000000 : ℝ)^71 := by
    have hnat : (379991701 : ℕ)^87*10000000000000^71 ≤ 7144026571483^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379991701 500000000 7144026571483 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1739531677/5000000000 : ℝ)^87 ≤ (13711971776637/50000000000000 : ℝ)^71 := by
    have hnat : (1739531677 : ℕ)^87*50000000000000^71 ≤ 13711971776637^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1739531677 5000000000 13711971776637 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-258788279/10000000000 : ℝ), (-379991701/500000000 : ℝ), (1739531677/5000000000 : ℝ)] ![(1135790719261/100000000000000 : ℝ), (7144026571483/10000000000000 : ℝ), (13711971776637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-258788279/10000000000 : ℝ)|^87 ≤ (1135790719261/100000000000000 : ℝ)^71
        have hw : |(-258788279/10000000000 : ℝ)|=(258788279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-379991701/500000000 : ℝ)|^87 ≤ (7144026571483/10000000000000 : ℝ)^71
        have hw : |(-379991701/500000000 : ℝ)|=(379991701/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1739531677/5000000000 : ℝ)|^87 ≤ (13711971776637/50000000000000 : ℝ)^71
        have hw : |(1739531677/5000000000 : ℝ)|=(1739531677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s0_8 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3184518707/10000000000 : ℝ)*x 0 + (5030154217/10000000000 : ℝ)*x 1 + (795387127/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3184518707/10000000000 : ℝ)^87 ≤ (24606717076799/100000000000000 : ℝ)^71 := by
    have hnat : (3184518707 : ℕ)^87*100000000000000^71 ≤ 24606717076799^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3184518707 10000000000 24606717076799 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5030154217/10000000000 : ℝ)^87 ≤ (43085587140867/100000000000000 : ℝ)^71 := by
    have hnat : (5030154217 : ℕ)^87*100000000000000^71 ≤ 43085587140867^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030154217 10000000000 43085587140867 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (795387127/2000000000 : ℝ)^87 ≤ (32307695770087/100000000000000 : ℝ)^71 := by
    have hnat : (795387127 : ℕ)^87*100000000000000^71 ≤ 32307695770087^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795387127 2000000000 32307695770087 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3184518707/10000000000 : ℝ), (5030154217/10000000000 : ℝ), (795387127/2000000000 : ℝ)] ![(24606717076799/100000000000000 : ℝ), (43085587140867/100000000000000 : ℝ), (32307695770087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3184518707/10000000000 : ℝ)|^87 ≤ (24606717076799/100000000000000 : ℝ)^71
        have hw : |(3184518707/10000000000 : ℝ)|=(3184518707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5030154217/10000000000 : ℝ)|^87 ≤ (43085587140867/100000000000000 : ℝ)^71
        have hw : |(5030154217/10000000000 : ℝ)|=(5030154217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(795387127/2000000000 : ℝ)|^87 ≤ (32307695770087/100000000000000 : ℝ)^71
        have hw : |(795387127/2000000000 : ℝ)|=(795387127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s0_9 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4786341743/10000000000 : ℝ)*x 0 + (-1651251123/5000000000 : ℝ)*x 1 + (-2059664099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4786341743/10000000000 : ℝ)^87 ≤ (40540757806069/100000000000000 : ℝ)^71 := by
    have hnat : (4786341743 : ℕ)^87*100000000000000^71 ≤ 40540757806069^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4786341743 10000000000 40540757806069 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1651251123/5000000000 : ℝ)^87 ≤ (25728436935757/100000000000000 : ℝ)^71 := by
    have hnat : (1651251123 : ℕ)^87*100000000000000^71 ≤ 25728436935757^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1651251123 5000000000 25728436935757 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2059664099/5000000000 : ℝ)^87 ≤ (8432701310643/25000000000000 : ℝ)^71 := by
    have hnat : (2059664099 : ℕ)^87*25000000000000^71 ≤ 8432701310643^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059664099 5000000000 8432701310643 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4786341743/10000000000 : ℝ), (-1651251123/5000000000 : ℝ), (-2059664099/5000000000 : ℝ)] ![(40540757806069/100000000000000 : ℝ), (25728436935757/100000000000000 : ℝ), (8432701310643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4786341743/10000000000 : ℝ)|^87 ≤ (40540757806069/100000000000000 : ℝ)^71
        have hw : |(4786341743/10000000000 : ℝ)|=(4786341743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1651251123/5000000000 : ℝ)|^87 ≤ (25728436935757/100000000000000 : ℝ)^71
        have hw : |(-1651251123/5000000000 : ℝ)|=(1651251123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2059664099/5000000000 : ℝ)|^87 ≤ (8432701310643/25000000000000 : ℝ)^71
        have hw : |(-2059664099/5000000000 : ℝ)|=(2059664099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s0_13 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8171307/16000000 : ℝ)*x 0 + (398871/2000000000 : ℝ)*x 1 + (3119741623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8171307/16000000 : ℝ)^87 ≤ (8778845008051/20000000000000 : ℝ)^71 := by
    have hnat : (8171307 : ℕ)^87*20000000000000^71 ≤ 8778845008051^71*16000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8171307 16000000 8778845008051 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (398871/2000000000 : ℝ)^87 ≤ (365481289/12500000000000 : ℝ)^71 := by
    have hnat : (398871 : ℕ)^87*12500000000000^71 ≤ 365481289^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398871 2000000000 365481289 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3119741623/5000000000 : ℝ)^87 ≤ (14025712774677/25000000000000 : ℝ)^71 := by
    have hnat : (3119741623 : ℕ)^87*25000000000000^71 ≤ 14025712774677^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3119741623 5000000000 14025712774677 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8171307/16000000 : ℝ), (398871/2000000000 : ℝ), (3119741623/5000000000 : ℝ)] ![(8778845008051/20000000000000 : ℝ), (365481289/12500000000000 : ℝ), (14025712774677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8171307/16000000 : ℝ)|^87 ≤ (8778845008051/20000000000000 : ℝ)^71
        have hw : |(8171307/16000000 : ℝ)|=(8171307/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(398871/2000000000 : ℝ)|^87 ≤ (365481289/12500000000000 : ℝ)^71
        have hw : |(398871/2000000000 : ℝ)|=(398871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3119741623/5000000000 : ℝ)|^87 ≤ (14025712774677/25000000000000 : ℝ)^71
        have hw : |(3119741623/5000000000 : ℝ)|=(3119741623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s0_14 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1853/10000000000 : ℝ)*x 0 + (-1186033519/2500000000 : ℝ)*x 1 + (6581748957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1853/10000000000 : ℝ)^87 ≤ (563349/100000000000000 : ℝ)^71 := by
    have hnat : (1853 : ℕ)^87*100000000000000^71 ≤ 563349^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853 10000000000 563349 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1186033519/2500000000 : ℝ)^87 ≤ (40103127201769/100000000000000 : ℝ)^71 := by
    have hnat : (1186033519 : ℕ)^87*100000000000000^71 ≤ 40103127201769^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1186033519 2500000000 40103127201769 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6581748957/10000000000 : ℝ)^87 ≤ (29948436115169/50000000000000 : ℝ)^71 := by
    have hnat : (6581748957 : ℕ)^87*50000000000000^71 ≤ 29948436115169^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6581748957 10000000000 29948436115169 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1853/10000000000 : ℝ), (-1186033519/2500000000 : ℝ), (6581748957/10000000000 : ℝ)] ![(563349/100000000000000 : ℝ), (40103127201769/100000000000000 : ℝ), (29948436115169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1853/10000000000 : ℝ)|^87 ≤ (563349/100000000000000 : ℝ)^71
        have hw : |(-1853/10000000000 : ℝ)|=(1853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1186033519/2500000000 : ℝ)|^87 ≤ (40103127201769/100000000000000 : ℝ)^71
        have hw : |(-1186033519/2500000000 : ℝ)|=(1186033519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6581748957/10000000000 : ℝ)|^87 ≤ (29948436115169/50000000000000 : ℝ)^71
        have hw : |(6581748957/10000000000 : ℝ)|=(6581748957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s0_15 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1618520749/5000000000 : ℝ)*x 0 + (1139184529/2500000000 : ℝ)*x 1 + (4415317081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1618520749/5000000000 : ℝ)^87 ≤ (12552468736353/50000000000000 : ℝ)^71 := by
    have hnat : (1618520749 : ℕ)^87*50000000000000^71 ≤ 12552468736353^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1618520749 5000000000 12552468736353 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1139184529/2500000000 : ℝ)^87 ≤ (19085390370031/50000000000000 : ℝ)^71 := by
    have hnat : (1139184529 : ℕ)^87*50000000000000^71 ≤ 19085390370031^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139184529 2500000000 19085390370031 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4415317081/10000000000 : ℝ)^87 ≤ (18362140885303/50000000000000 : ℝ)^71 := by
    have hnat : (4415317081 : ℕ)^87*50000000000000^71 ≤ 18362140885303^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4415317081 10000000000 18362140885303 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1618520749/5000000000 : ℝ), (1139184529/2500000000 : ℝ), (4415317081/10000000000 : ℝ)] ![(12552468736353/50000000000000 : ℝ), (19085390370031/50000000000000 : ℝ), (18362140885303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1618520749/5000000000 : ℝ)|^87 ≤ (12552468736353/50000000000000 : ℝ)^71
        have hw : |(1618520749/5000000000 : ℝ)|=(1618520749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1139184529/2500000000 : ℝ)|^87 ≤ (19085390370031/50000000000000 : ℝ)^71
        have hw : |(1139184529/2500000000 : ℝ)|=(1139184529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4415317081/10000000000 : ℝ)|^87 ≤ (18362140885303/50000000000000 : ℝ)^71
        have hw : |(4415317081/10000000000 : ℝ)|=(4415317081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s0_16 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3319016603/5000000000 : ℝ)*x 0 + (-2719146067/10000000000 : ℝ)*x 1 + (-2600690401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3319016603/5000000000 : ℝ)^87 ≤ (60525115662261/100000000000000 : ℝ)^71 := by
    have hnat : (3319016603 : ℕ)^87*100000000000000^71 ≤ 60525115662261^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3319016603 5000000000 60525115662261 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719146067/10000000000 : ℝ)^87 ≤ (10137963410687/50000000000000 : ℝ)^71 := by
    have hnat : (2719146067 : ℕ)^87*50000000000000^71 ≤ 10137963410687^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719146067 10000000000 10137963410687 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2600690401/10000000000 : ℝ)^87 ≤ (1199934844027/6250000000000 : ℝ)^71 := by
    have hnat : (2600690401 : ℕ)^87*6250000000000^71 ≤ 1199934844027^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600690401 10000000000 1199934844027 6250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3319016603/5000000000 : ℝ), (-2719146067/10000000000 : ℝ), (-2600690401/10000000000 : ℝ)] ![(60525115662261/100000000000000 : ℝ), (10137963410687/50000000000000 : ℝ), (1199934844027/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3319016603/5000000000 : ℝ)|^87 ≤ (60525115662261/100000000000000 : ℝ)^71
        have hw : |(3319016603/5000000000 : ℝ)|=(3319016603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2719146067/10000000000 : ℝ)|^87 ≤ (10137963410687/50000000000000 : ℝ)^71
        have hw : |(-2719146067/10000000000 : ℝ)|=(2719146067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2600690401/10000000000 : ℝ)|^87 ≤ (1199934844027/6250000000000 : ℝ)^71
        have hw : |(-2600690401/10000000000 : ℝ)|=(2600690401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s0_20 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1652343741/2000000000 : ℝ)*x 0 + (-147283519/10000000000 : ℝ)*x 1 + (2721041607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1652343741/2000000000 : ℝ)^87 ≤ (19784362146593/25000000000000 : ℝ)^71 := by
    have hnat : (1652343741 : ℕ)^87*25000000000000^71 ≤ 19784362146593^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1652343741 2000000000 19784362146593 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147283519/10000000000 : ℝ)^87 ≤ (5693034559/1000000000000 : ℝ)^71 := by
    have hnat : (147283519 : ℕ)^87*1000000000000^71 ≤ 5693034559^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147283519 10000000000 5693034559 1000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721041607/10000000000 : ℝ)^87 ≤ (20293247948137/100000000000000 : ℝ)^71 := by
    have hnat : (2721041607 : ℕ)^87*100000000000000^71 ≤ 20293247948137^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721041607 10000000000 20293247948137 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1652343741/2000000000 : ℝ), (-147283519/10000000000 : ℝ), (2721041607/10000000000 : ℝ)] ![(19784362146593/25000000000000 : ℝ), (5693034559/1000000000000 : ℝ), (20293247948137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1652343741/2000000000 : ℝ)|^87 ≤ (19784362146593/25000000000000 : ℝ)^71
        have hw : |(1652343741/2000000000 : ℝ)|=(1652343741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-147283519/10000000000 : ℝ)|^87 ≤ (5693034559/1000000000000 : ℝ)^71
        have hw : |(-147283519/10000000000 : ℝ)|=(147283519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721041607/10000000000 : ℝ)|^87 ≤ (20293247948137/100000000000000 : ℝ)^71
        have hw : |(2721041607/10000000000 : ℝ)|=(2721041607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s0_21 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-59470261/1250000000 : ℝ)*x 0 + (-3998355943/5000000000 : ℝ)*x 1 + (2859588677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59470261/1250000000 : ℝ)^87 ≤ (598793178883/25000000000000 : ℝ)^71 := by
    have hnat : (59470261 : ℕ)^87*25000000000000^71 ≤ 598793178883^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59470261 1250000000 598793178883 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3998355943/5000000000 : ℝ)^87 ≤ (38019144773519/50000000000000 : ℝ)^71 := by
    have hnat : (3998355943 : ℕ)^87*50000000000000^71 ≤ 38019144773519^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3998355943 5000000000 38019144773519 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2859588677/10000000000 : ℝ)^87 ≤ (10783268859911/50000000000000 : ℝ)^71 := by
    have hnat : (2859588677 : ℕ)^87*50000000000000^71 ≤ 10783268859911^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2859588677 10000000000 10783268859911 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-59470261/1250000000 : ℝ), (-3998355943/5000000000 : ℝ), (2859588677/10000000000 : ℝ)] ![(598793178883/25000000000000 : ℝ), (38019144773519/50000000000000 : ℝ), (10783268859911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-59470261/1250000000 : ℝ)|^87 ≤ (598793178883/25000000000000 : ℝ)^71
        have hw : |(-59470261/1250000000 : ℝ)|=(59470261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3998355943/5000000000 : ℝ)|^87 ≤ (38019144773519/50000000000000 : ℝ)^71
        have hw : |(-3998355943/5000000000 : ℝ)|=(3998355943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2859588677/10000000000 : ℝ)|^87 ≤ (10783268859911/50000000000000 : ℝ)^71
        have hw : |(2859588677/10000000000 : ℝ)|=(2859588677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s0_22 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3263464431/5000000000 : ℝ)*x 0 + (1562985933/5000000000 : ℝ)*x 1 + (2316446611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3263464431/5000000000 : ℝ)^87 ≤ (14821533584721/25000000000000 : ℝ)^71 := by
    have hnat : (3263464431 : ℕ)^87*25000000000000^71 ≤ 14821533584721^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3263464431 5000000000 14821533584721 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1562985933/5000000000 : ℝ)^87 ≤ (12026766710649/50000000000000 : ℝ)^71 := by
    have hnat : (1562985933 : ℕ)^87*50000000000000^71 ≤ 12026766710649^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562985933 5000000000 12026766710649 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2316446611/10000000000 : ℝ)^87 ≤ (1041270763931/6250000000000 : ℝ)^71 := by
    have hnat : (2316446611 : ℕ)^87*6250000000000^71 ≤ 1041270763931^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2316446611 10000000000 1041270763931 6250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3263464431/5000000000 : ℝ), (1562985933/5000000000 : ℝ), (2316446611/10000000000 : ℝ)] ![(14821533584721/25000000000000 : ℝ), (12026766710649/50000000000000 : ℝ), (1041270763931/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3263464431/5000000000 : ℝ)|^87 ≤ (14821533584721/25000000000000 : ℝ)^71
        have hw : |(3263464431/5000000000 : ℝ)|=(3263464431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1562985933/5000000000 : ℝ)|^87 ≤ (12026766710649/50000000000000 : ℝ)^71
        have hw : |(1562985933/5000000000 : ℝ)|=(1562985933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2316446611/10000000000 : ℝ)|^87 ≤ (1041270763931/6250000000000 : ℝ)^71
        have hw : |(2316446611/10000000000 : ℝ)|=(2316446611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s0_23 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1177930271/5000000000 : ℝ)*x 0 + (-129191003/200000000 : ℝ)*x 1 + (-396055239/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1177930271/5000000000 : ℝ)^87 ≤ (17008349023911/100000000000000 : ℝ)^71 := by
    have hnat : (1177930271 : ℕ)^87*100000000000000^71 ≤ 17008349023911^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177930271 5000000000 17008349023911 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129191003/200000000 : ℝ)^87 ≤ (29268533333837/50000000000000 : ℝ)^71 := by
    have hnat : (129191003 : ℕ)^87*50000000000000^71 ≤ 29268533333837^71*200000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129191003 200000000 29268533333837 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396055239/1250000000 : ℝ)^87 ≤ (24454584292537/100000000000000 : ℝ)^71 := by
    have hnat : (396055239 : ℕ)^87*100000000000000^71 ≤ 24454584292537^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396055239 1250000000 24454584292537 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1177930271/5000000000 : ℝ), (-129191003/200000000 : ℝ), (-396055239/1250000000 : ℝ)] ![(17008349023911/100000000000000 : ℝ), (29268533333837/50000000000000 : ℝ), (24454584292537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1177930271/5000000000 : ℝ)|^87 ≤ (17008349023911/100000000000000 : ℝ)^71
        have hw : |(1177930271/5000000000 : ℝ)|=(1177930271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129191003/200000000 : ℝ)|^87 ≤ (29268533333837/50000000000000 : ℝ)^71
        have hw : |(-129191003/200000000 : ℝ)|=(129191003/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-396055239/1250000000 : ℝ)|^87 ≤ (24454584292537/100000000000000 : ℝ)^71
        have hw : |(-396055239/1250000000 : ℝ)|=(396055239/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s0_27 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8067058349/10000000000 : ℝ)*x 0 + (1/2000000000 : ℝ)*x 1 + (302887477/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8067058349/10000000000 : ℝ)^87 ≤ (76858741867261/100000000000000 : ℝ)^71 := by
    have hnat : (8067058349 : ℕ)^87*100000000000000^71 ≤ 76858741867261^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8067058349 10000000000 76858741867261 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1/2000000000 : ℝ)^87 ≤ (401/100000000000000 : ℝ)^71 := by
    have hnat : (1 : ℕ)^87*100000000000000^71 ≤ 401^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 2000000000 401 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (302887477/1000000000 : ℝ)^87 ≤ (23141258127621/100000000000000 : ℝ)^71 := by
    have hnat : (302887477 : ℕ)^87*100000000000000^71 ≤ 23141258127621^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302887477 1000000000 23141258127621 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8067058349/10000000000 : ℝ), (1/2000000000 : ℝ), (302887477/1000000000 : ℝ)] ![(76858741867261/100000000000000 : ℝ), (401/100000000000000 : ℝ), (23141258127621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8067058349/10000000000 : ℝ)|^87 ≤ (76858741867261/100000000000000 : ℝ)^71
        have hw : |(8067058349/10000000000 : ℝ)|=(8067058349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1/2000000000 : ℝ)|^87 ≤ (401/100000000000000 : ℝ)^71
        have hw : |(1/2000000000 : ℝ)|=(1/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(302887477/1000000000 : ℝ)|^87 ≤ (23141258127621/100000000000000 : ℝ)^71
        have hw : |(302887477/1000000000 : ℝ)|=(302887477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s1_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-432860061/2500000000 : ℝ)*x 0 + (-2469673651/5000000000 : ℝ)*x 1 + (266264083/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432860061/2500000000 : ℝ)^87 ≤ (11388881491/97656250000 : ℝ)^71 := by
    have hnat : (432860061 : ℕ)^87*97656250000^71 ≤ 11388881491^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432860061 2500000000 11388881491 97656250000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2469673651/5000000000 : ℝ)^87 ≤ (42134452302491/100000000000000 : ℝ)^71 := by
    have hnat : (2469673651 : ℕ)^87*100000000000000^71 ≤ 42134452302491^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2469673651 5000000000 42134452302491 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266264083/500000000 : ℝ)^87 ≤ (2310166651577/5000000000000 : ℝ)^71 := by
    have hnat : (266264083 : ℕ)^87*5000000000000^71 ≤ 2310166651577^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266264083 500000000 2310166651577 5000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432860061/2500000000 : ℝ), (-2469673651/5000000000 : ℝ), (266264083/500000000 : ℝ)] ![(11388881491/97656250000 : ℝ), (42134452302491/100000000000000 : ℝ), (2310166651577/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432860061/2500000000 : ℝ)|^87 ≤ (11388881491/97656250000 : ℝ)^71
        have hw : |(-432860061/2500000000 : ℝ)|=(432860061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2469673651/5000000000 : ℝ)|^87 ≤ (42134452302491/100000000000000 : ℝ)^71
        have hw : |(-2469673651/5000000000 : ℝ)|=(2469673651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(266264083/500000000 : ℝ)|^87 ≤ (2310166651577/5000000000000 : ℝ)^71
        have hw : |(266264083/500000000 : ℝ)|=(266264083/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s1_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2459333631/5000000000 : ℝ)*x 0 + (196928989/500000000 : ℝ)*x 1 + (836787699/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2459333631/5000000000 : ℝ)^87 ≤ (8383678406157/20000000000000 : ℝ)^71 := by
    have hnat : (2459333631 : ℕ)^87*20000000000000^71 ≤ 8383678406157^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2459333631 5000000000 8383678406157 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196928989/500000000 : ℝ)^87 ≤ (15963149679137/50000000000000 : ℝ)^71 := by
    have hnat : (196928989 : ℕ)^87*50000000000000^71 ≤ 15963149679137^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196928989 500000000 15963149679137 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (836787699/2500000000 : ℝ)^87 ≤ (26155308597933/100000000000000 : ℝ)^71 := by
    have hnat : (836787699 : ℕ)^87*100000000000000^71 ≤ 26155308597933^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836787699 2500000000 26155308597933 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2459333631/5000000000 : ℝ), (196928989/500000000 : ℝ), (836787699/2500000000 : ℝ)] ![(8383678406157/20000000000000 : ℝ), (15963149679137/50000000000000 : ℝ), (26155308597933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2459333631/5000000000 : ℝ)|^87 ≤ (8383678406157/20000000000000 : ℝ)^71
        have hw : |(2459333631/5000000000 : ℝ)|=(2459333631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(196928989/500000000 : ℝ)|^87 ≤ (15963149679137/50000000000000 : ℝ)^71
        have hw : |(196928989/500000000 : ℝ)|=(196928989/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(836787699/2500000000 : ℝ)|^87 ≤ (26155308597933/100000000000000 : ℝ)^71
        have hw : |(836787699/2500000000 : ℝ)|=(836787699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s1_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4815338709/10000000000 : ℝ)*x 0 + (-100753733/250000000 : ℝ)*x 1 + (-1682163909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4815338709/10000000000 : ℝ)^87 ≤ (4084191796497/10000000000000 : ℝ)^71 := by
    have hnat : (4815338709 : ℕ)^87*10000000000000^71 ≤ 4084191796497^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4815338709 10000000000 4084191796497 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100753733/250000000 : ℝ)^87 ≤ (16419102958593/50000000000000 : ℝ)^71 := by
    have hnat : (100753733 : ℕ)^87*50000000000000^71 ≤ 16419102958593^71*250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100753733 250000000 16419102958593 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1682163909/5000000000 : ℝ)^87 ≤ (657996902389/2500000000000 : ℝ)^71 := by
    have hnat : (1682163909 : ℕ)^87*2500000000000^71 ≤ 657996902389^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1682163909 5000000000 657996902389 2500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4815338709/10000000000 : ℝ), (-100753733/250000000 : ℝ), (-1682163909/5000000000 : ℝ)] ![(4084191796497/10000000000000 : ℝ), (16419102958593/50000000000000 : ℝ), (657996902389/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4815338709/10000000000 : ℝ)|^87 ≤ (4084191796497/10000000000000 : ℝ)^71
        have hw : |(4815338709/10000000000 : ℝ)|=(4815338709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100753733/250000000 : ℝ)|^87 ≤ (16419102958593/50000000000000 : ℝ)^71
        have hw : |(-100753733/250000000 : ℝ)|=(100753733/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1682163909/5000000000 : ℝ)|^87 ≤ (657996902389/2500000000000 : ℝ)^71
        have hw : |(-1682163909/5000000000 : ℝ)|=(1682163909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325047_s1_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5987592931/10000000000 : ℝ)*x 0 + (-84219161/500000000 : ℝ)*x 1 + (2141714113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5987592931/10000000000 : ℝ)^87 ≤ (53340317293891/100000000000000 : ℝ)^71 := by
    have hnat : (5987592931 : ℕ)^87*100000000000000^71 ≤ 53340317293891^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5987592931 10000000000 53340317293891 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84219161/500000000 : ℝ)^87 ≤ (1127503062659/10000000000000 : ℝ)^71 := by
    have hnat : (84219161 : ℕ)^87*10000000000000^71 ≤ 1127503062659^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84219161 500000000 1127503062659 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2141714113/5000000000 : ℝ)^87 ≤ (35384652057179/100000000000000 : ℝ)^71 := by
    have hnat : (2141714113 : ℕ)^87*100000000000000^71 ≤ 35384652057179^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141714113 5000000000 35384652057179 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5987592931/10000000000 : ℝ), (-84219161/500000000 : ℝ), (2141714113/5000000000 : ℝ)] ![(53340317293891/100000000000000 : ℝ), (1127503062659/10000000000000 : ℝ), (35384652057179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5987592931/10000000000 : ℝ)|^87 ≤ (53340317293891/100000000000000 : ℝ)^71
        have hw : |(5987592931/10000000000 : ℝ)|=(5987592931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84219161/500000000 : ℝ)|^87 ≤ (1127503062659/10000000000000 : ℝ)^71
        have hw : |(-84219161/500000000 : ℝ)|=(84219161/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2141714113/5000000000 : ℝ)|^87 ≤ (35384652057179/100000000000000 : ℝ)^71
        have hw : |(2141714113/5000000000 : ℝ)|=(2141714113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325047 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]]) : False := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (33069/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-52041121/2000000000 : ℝ)*X 0 0+(-3038814619/5000000000 : ℝ)*X 0 1+(80742537/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((16015757/31250000 : ℝ)*X 1 0+(3666436323/10000000000 : ℝ)*X 1 1+(106281051/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5490006501/10000000000 : ℝ)*X 2 0+(-904679113/2500000000 : ℝ)*X 2 1+(-760400619/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-258788279/10000000000 : ℝ)*X 0 0+(-379991701/500000000 : ℝ)*X 0 1+(1739531677/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3184518707/10000000000 : ℝ)*X 1 0+(5030154217/10000000000 : ℝ)*X 1 1+(795387127/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4786341743/10000000000 : ℝ)*X 2 0+(-1651251123/5000000000 : ℝ)*X 2 1+(-2059664099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((8171307/16000000 : ℝ)*X 0 0+(398871/2000000000 : ℝ)*X 0 1+(3119741623/5000000000 : ℝ)*X 0 2+(8171307/16000000 : ℝ)*X 1 0+(398871/2000000000 : ℝ)*X 1 1+(3119741623/5000000000 : ℝ)*X 1 2+(8171307/16000000 : ℝ)*X 2 0+(398871/2000000000 : ℝ)*X 2 1+(3119741623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1853/10000000000 : ℝ)*X 0 0+(-1186033519/2500000000 : ℝ)*X 0 1+(6581748957/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1618520749/5000000000 : ℝ)*X 1 0+(1139184529/2500000000 : ℝ)*X 1 1+(4415317081/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3319016603/5000000000 : ℝ)*X 2 0+(-2719146067/10000000000 : ℝ)*X 2 1+(-2600690401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1652343741/2000000000 : ℝ)*X 0 0+(-147283519/10000000000 : ℝ)*X 0 1+(2721041607/10000000000 : ℝ)*X 0 2+(1652343741/2000000000 : ℝ)*X 1 0+(-147283519/10000000000 : ℝ)*X 1 1+(2721041607/10000000000 : ℝ)*X 1 2+(1652343741/2000000000 : ℝ)*X 2 0+(-147283519/10000000000 : ℝ)*X 2 1+(2721041607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-59470261/1250000000 : ℝ)*X 0 0+(-3998355943/5000000000 : ℝ)*X 0 1+(2859588677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3263464431/5000000000 : ℝ)*X 1 0+(1562985933/5000000000 : ℝ)*X 1 1+(2316446611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1177930271/5000000000 : ℝ)*X 2 0+(-129191003/200000000 : ℝ)*X 2 1+(-396055239/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((8067058349/10000000000 : ℝ)*X 0 0+(1/2000000000 : ℝ)*X 0 1+(302887477/1000000000 : ℝ)*X 0 2+(8067058349/10000000000 : ℝ)*X 1 0+(1/2000000000 : ℝ)*X 1 1+(302887477/1000000000 : ℝ)*X 1 2+(8067058349/10000000000 : ℝ)*X 2 0+(1/2000000000 : ℝ)*X 2 1+(302887477/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((55143/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(55143/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (85880328569267811091143/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (396473445989/1000000000000 : ℝ)*(base3) + (9294477181/7812500000 : ℝ)*(base7) + (2633433/1000000000000 : ℝ)*(base40) + (285734388159/1000000000000 : ℝ)*(base50) + (2148494598951/1000000000000 : ℝ)*(major_s0_0) + (2148494598951/1000000000000 : ℝ)*(major_s0_1) + (2148494598951/1000000000000 : ℝ)*(major_s0_2) + (1353901/100000000000 : ℝ)*(sp_s0_0) + (128602165777/50000000000 : ℝ)*(sp_s0_7) + (371056245339/125000000000 : ℝ)*(sp_s0_8) + (2572034343461/1000000000000 : ℝ)*(sp_s0_9) + (1862446910587/1000000000000 : ℝ)*(sp_s0_13) + (80337827/1000000000000 : ℝ)*(sp_s0_15) + (1406943/62500000000 : ℝ)*(sp_s0_23) + (33413352419/31250000000 : ℝ)*(f.failure) + (2572056854549/1000000000000 : ℝ)*(f.sum) + (2655097048469619/5000000000000000000000000000 : ℝ)*base62 + (5314944010429281/10000000000000000000000000000 : ℝ)*base65 + (1227612973429281/10000000000000000000000000000 : ℝ)*base67 + (3976301445969619/10000000000000000000000000000 : ℝ)*base68 + (372215401729831/5000000000000000000000000000 : ℝ)*base71 + (9461655293570719/10000000000000000000000000000 : ℝ)*base72 + (5261785434969619/10000000000000000000000000000 : ℝ)*base74 + (3244042630030381/10000000000000000000000000000 : ℝ)*base77 + (851760718570719/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (217/1562500000000000 : ℝ)*base86 + (217/1562500000000000 : ℝ)*base88 + (217/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-48619/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-48619/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (49503003249589553248263/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (423457919721/500000000000 : ℝ)*(base7) + (19906420349/31250000000 : ℝ)*(base40) + (5036697/1000000000000 : ℝ)*(base49) + (152725822817/1000000000000 : ℝ)*(base59) + (2267885053209/1000000000000 : ℝ)*(major_s0_0) + (2267885053209/1000000000000 : ℝ)*(major_s0_1) + (2267885053209/1000000000000 : ℝ)*(major_s0_2) + (214961/125000000000 : ℝ)*(sp_s0_0) + (12048609/250000000000 : ℝ)*(sp_s0_1) + (1470171938227/500000000000 : ℝ)*(sp_s0_14) + (588059480341/200000000000 : ℝ)*(sp_s0_15) + (1470172798071/500000000000 : ℝ)*(sp_s0_16) + (1975332522983/1000000000000 : ℝ)*(sp_s0_20) + (113430809/500000000000 : ℝ)*(sp_s0_27) + (28216088629/25000000000 : ℝ)*(f.failure) + (1470172798071/500000000000 : ℝ)*(f.sum) + (2658616174750579/5000000000000000000000000000 : ℝ)*base63 + (4924698977324321/10000000000000000000000000000 : ℝ)*base64 + (25163515324321/10000000000000000000000000000 : ℝ)*base66 + (10410902345250579/10000000000000000000000000000 : ℝ)*base69 + (2825045530536871/5000000000000000000000000000 : ℝ)*base70 + (10693321489675679/10000000000000000000000000000 : ℝ)*base73 + (4843341823250579/10000000000000000000000000000 : ℝ)*base75 + (6407138626749421/10000000000000000000000000000 : ℝ)*base76 + (2227358388175679/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (131/2500000000000000 : ℝ)*base87 + (131/2500000000000000 : ℝ)*base89 + (131/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64953/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(64953/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32296112888198864209041/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (614572901849/500000000000 : ℝ)*(base7) + (5788279/500000000000 : ℝ)*(base22) + (117541/1000000000000 : ℝ)*(base34) + (58423097843/250000000000 : ℝ)*(base40) + (14870521893/125000000000 : ℝ)*(base50) + (464228759183/250000000000 : ℝ)*(major_s0_0) + (1856915154273/1000000000000 : ℝ)*(major_s0_1) + (1856915154273/1000000000000 : ℝ)*(major_s0_2) + (96627/10000000000 : ℝ)*(sp_s0_0) + (2334471/100000000000 : ℝ)*(sp_s0_2) + (2112255823103/1000000000000 : ℝ)*(sp_s0_21) + (132016600209/62500000000 : ℝ)*(sp_s0_22) + (528057670519/250000000000 : ℝ)*(sp_s0_23) + (2153264525343/1000000000000 : ℝ)*(sp_s0_27) + (924118839187/1000000000000 : ℝ)*(f.failure) + (132016600209/62500000000 : ℝ)*(f.sum) + (1420394546289163/5000000000000000000000000000 : ℝ)*base63 + (10764145875900276137/10000000000000000000000000000 : ℝ)*base64 + (4812148484276137/10000000000000000000000000000 : ℝ)*base66 + (432715617210837/10000000000000000000000000000 : ℝ)*base68 + (2152463335399790929/2000000000000000000000000000 : ℝ)*base70 + (1788961958685927/2500000000000000000000000000 : ℝ)*base72 + (1105594008789163/10000000000000000000000000000 : ℝ)*base75 + (2689587525682919627/2500000000000000000000000000 : ℝ)*base76 + (1145696684403969/2000000000000000000000000000 : ℝ)*base78 + (96593/100000000000000000 : ℝ)*base87 + (96593/100000000000000000 : ℝ)*base89 + (96593/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (55143/100000 : ℝ) ^ (85/16 : ℝ) ≤ (846637871592069263/20000000000000000000 : ℝ) := by
    have hpowers : (55143/100000 : ℝ)^85 ≤ (846637871592069263/20000000000000000000 : ℝ)^16 := by
      have hnat : (55143 : ℕ)^85*20000000000000000000^16 ≤ 846637871592069263^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55143 100000 846637871592069263 20000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (55143/100000 : ℝ)) (X := (846637871592069263/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (20846637871592069263/20000000000000000000 : ℝ) ≤ (5039174226078999/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (20846637871592069263/20000000000000000000 : ℝ)^16 ≤ (5039174226078999/5000000000000000 : ℝ)^85 := by
      have hnat : (20846637871592069263 : ℕ)^16*5000000000000000^85 ≤ 5039174226078999^85*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20846637871592069263 20000000000000000000 5039174226078999 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5039174226078999/5000000000000000 : ℝ)) (X := (20846637871592069263/20000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (10846637871592069263/10000000000000000000 : ℝ) ≤ (1269269383029347/1250000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (10846637871592069263/10000000000000000000 : ℝ)^16 ≤ (1269269383029347/1250000000000000 : ℝ)^85 := by
      have hnat : (10846637871592069263 : ℕ)^16*1250000000000000^85 ≤ 1269269383029347^85*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10846637871592069263 10000000000000000000 1269269383029347 1250000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1269269383029347/1250000000000000 : ℝ)) (X := (10846637871592069263/10000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3561293279909/250650000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3445755094399/250650000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (55143/100000 : ℝ)) (alpha := (3561293279909/250650000000000 : ℝ)) (beta := (3445755094399/250650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (55143/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3561293279909/250650000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3445755094399/250650000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (48619/100000 : ℝ) ^ (85/16 : ℝ) ≤ (67765245106462833/3125000000000000000 : ℝ) := by
    have hpowers : (48619/100000 : ℝ)^85 ≤ (67765245106462833/3125000000000000000 : ℝ)^16 := by
      have hnat : (48619 : ℕ)^85*3125000000000000000^16 ≤ 67765245106462833^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48619 100000 67765245106462833 3125000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48619/100000 : ℝ)) (X := (67765245106462833/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (3192765245106462833/3125000000000000000 : ℝ) ≤ (10040463963823801/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3192765245106462833/3125000000000000000 : ℝ)^16 ≤ (10040463963823801/10000000000000000 : ℝ)^85 := by
      have hnat : (3192765245106462833 : ℕ)^16*10000000000000000^85 ≤ 10040463963823801^85*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3192765245106462833 3125000000000000000 10040463963823801 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10040463963823801/10000000000000000 : ℝ)) (X := (3192765245106462833/3125000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (1630265245106462833/1562500000000000000 : ℝ) ≤ (5040118328492619/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (1630265245106462833/1562500000000000000 : ℝ)^16 ≤ (5040118328492619/5000000000000000 : ℝ)^85 := by
      have hnat : (1630265245106462833 : ℕ)^16*5000000000000000^85 ≤ 5040118328492619^85*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1630265245106462833 1562500000000000000 5040118328492619 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5040118328492619/5000000000000000 : ℝ)) (X := (1630265245106462833/1562500000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(40463963823801/4861900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(39772693161437/4861900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (48619/100000 : ℝ)) (alpha := (40463963823801/4861900000000000 : ℝ)) (beta := (39772693161437/4861900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (48619/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(40463963823801/4861900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(39772693161437/4861900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (64953/100000 : ℝ) ^ (85/16 : ℝ) ≤ (10102603961911183153/100000000000000000000 : ℝ) := by
    have hpowers : (64953/100000 : ℝ)^85 ≤ (10102603961911183153/100000000000000000000 : ℝ)^16 := by
      have hnat : (64953 : ℕ)^85*100000000000000000000^16 ≤ 10102603961911183153^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64953 100000 10102603961911183153 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64953/100000 : ℝ)) (X := (10102603961911183153/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (110102603961911183153/100000000000000000000 : ℝ) ≤ (10182813313398873/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (110102603961911183153/100000000000000000000 : ℝ)^16 ≤ (10182813313398873/10000000000000000 : ℝ)^85 := by
      have hnat : (110102603961911183153 : ℕ)^16*10000000000000000^85 ≤ 10182813313398873^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110102603961911183153 100000000000000000000 10182813313398873 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10182813313398873/10000000000000000 : ℝ)) (X := (110102603961911183153/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (60102603961911183153/50000000000000000000 : ℝ) ≤ (10352479587879209/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (60102603961911183153/50000000000000000000 : ℝ)^16 ≤ (10352479587879209/10000000000000000 : ℝ)^85 := by
      have hnat : (60102603961911183153 : ℕ)^16*10000000000000000^85 ≤ 10352479587879209^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60102603961911183153 50000000000000000000 10352479587879209 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10352479587879209/10000000000000000 : ℝ)) (X := (60102603961911183153/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(182813313398873/6495300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(10604142155021/405956250000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (64953/100000 : ℝ)) (alpha := (182813313398873/6495300000000000 : ℝ)) (beta := (10604142155021/405956250000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (64953/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(182813313398873/6495300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(10604142155021/405956250000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-432860061/2500000000 : ℝ)*X 0 0+(-2469673651/5000000000 : ℝ)*X 0 1+(266264083/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2459333631/5000000000 : ℝ)*X 1 0+(196928989/500000000 : ℝ)*X 1 1+(836787699/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4815338709/10000000000 : ℝ)*X 2 0+(-100753733/250000000 : ℝ)*X 2 1+(-1682163909/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5987592931/10000000000 : ℝ)*X 0 0+(-84219161/500000000 : ℝ)*X 0 1+(2141714113/5000000000 : ℝ)*X 0 2+(5987592931/10000000000 : ℝ)*X 1 0+(-84219161/500000000 : ℝ)*X 1 1+(2141714113/5000000000 : ℝ)*X 1 2+(5987592931/10000000000 : ℝ)*X 2 0+(-84219161/500000000 : ℝ)*X 2 1+(2141714113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325047_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-452817/50000 : ℝ) < ((-200939/100000 : ℝ)*P 0+(-200939/100000 : ℝ)*P 1+(-200939/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-452817/50000 : ℝ) < (-52468443786817218146976310647538561/5863260327330000000000000000000000 : ℝ) := by norm_num
    linear_combination (33247/500000000000 : ℝ)*(base3) + (98619/500000000000 : ℝ)*(base10) + (18237/40000000000 : ℝ)*(base21) + (25267/1000000000000 : ℝ)*(base31) + (152562841893/250000000000 : ℝ)*(base40) + (9010260471/1000000000000 : ℝ)*(base50) + (39388615853/125000000000 : ℝ)*(base59) + (52161/500000000000 : ℝ)*(base60) + (200939/100000 : ℝ)*(major_s1_0) + (200939/100000 : ℝ)*(major_s1_1) + (200939/100000 : ℝ)*(major_s1_2) + (74572333179/25000000000 : ℝ)*(sp_s1_0) + (745723397723/250000000000 : ℝ)*(sp_s1_1) + (2982893068473/1000000000000 : ℝ)*(sp_s1_2) + (499999954119/500000000000 : ℝ)*(sp_s1_6) + (1491446762199/500000000000 : ℝ)*(f.sum) + (1955574442499957983/15789749535000000000000000000000 : ℝ)*base62 + (4069175434199/16238250000000000000000000 : ℝ)*base64 + (45483609081707/121547500000000000000000000 : ℝ)*base67 + (51165549052127/324765000000000000000000000 : ℝ)*base69 + (72907937529109/602980350000000000000000000 : ℝ)*base70 + (1458762215717/2506500000000000000000000 : ℝ)*base73 + (8558263621447/97238000000000000000000000 : ℝ)*base75 + (47910667429/313312500000000000000000 : ℝ)*base76 + (694354519637869961/1218635235000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p025_b023 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 48)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=47 := by omega
  rcases hc with rfl
  · exact collision_c325047 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 48)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b023 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

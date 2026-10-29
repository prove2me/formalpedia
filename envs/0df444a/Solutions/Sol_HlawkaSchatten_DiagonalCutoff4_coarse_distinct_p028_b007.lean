-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b007
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:20:41.316998+00:00
-- url     : https://prove2.me/submissions/796c7860-109e-4fca-a5cd-68587328c653

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
theorem collision_support_c328018_s0_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4592036657/10000000000 : ℝ)*x 0 + (-2081094471/10000000000 : ℝ)*x 1 + (-5249672509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4592036657/10000000000 : ℝ)^93 ≤ (9765909594889/25000000000000 : ℝ)^77 := by
    have hnat : (4592036657 : ℕ)^93*25000000000000^77 ≤ 9765909594889^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4592036657 10000000000 9765909594889 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2081094471/10000000000 : ℝ)^93 ≤ (15018900582519/100000000000000 : ℝ)^77 := by
    have hnat : (2081094471 : ℕ)^93*100000000000000^77 ≤ 15018900582519^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081094471 10000000000 15018900582519 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5249672509/10000000000 : ℝ)^93 ≤ (11479365254327/25000000000000 : ℝ)^77 := by
    have hnat : (5249672509 : ℕ)^93*25000000000000^77 ≤ 11479365254327^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5249672509 10000000000 11479365254327 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4592036657/10000000000 : ℝ), (-2081094471/10000000000 : ℝ), (-5249672509/10000000000 : ℝ)] ![(9765909594889/25000000000000 : ℝ), (15018900582519/100000000000000 : ℝ), (11479365254327/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4592036657/10000000000 : ℝ)|^93 ≤ (9765909594889/25000000000000 : ℝ)^77
        have hw : |(4592036657/10000000000 : ℝ)|=(4592036657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2081094471/10000000000 : ℝ)|^93 ≤ (15018900582519/100000000000000 : ℝ)^77
        have hw : |(-2081094471/10000000000 : ℝ)|=(2081094471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5249672509/10000000000 : ℝ)|^93 ≤ (11479365254327/25000000000000 : ℝ)^77
        have hw : |(-5249672509/10000000000 : ℝ)|=(5249672509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s0_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1913978283/5000000000 : ℝ)*x 0 + (1322669299/2500000000 : ℝ)*x 1 + (2886178153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1913978283/5000000000 : ℝ)^93 ≤ (31355287982029/100000000000000 : ℝ)^77 := by
    have hnat : (1913978283 : ℕ)^93*100000000000000^77 ≤ 31355287982029^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913978283 5000000000 31355287982029 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1322669299/2500000000 : ℝ)^93 ≤ (46350994806759/100000000000000 : ℝ)^77 := by
    have hnat : (1322669299 : ℕ)^93*100000000000000^77 ≤ 46350994806759^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322669299 2500000000 46350994806759 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2886178153/10000000000 : ℝ)^93 ≤ (2229371719799/10000000000000 : ℝ)^77 := by
    have hnat : (2886178153 : ℕ)^93*10000000000000^77 ≤ 2229371719799^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2886178153 10000000000 2229371719799 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1913978283/5000000000 : ℝ), (1322669299/2500000000 : ℝ), (2886178153/10000000000 : ℝ)] ![(31355287982029/100000000000000 : ℝ), (46350994806759/100000000000000 : ℝ), (2229371719799/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1913978283/5000000000 : ℝ)|^93 ≤ (31355287982029/100000000000000 : ℝ)^77
        have hw : |(1913978283/5000000000 : ℝ)|=(1913978283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1322669299/2500000000 : ℝ)|^93 ≤ (46350994806759/100000000000000 : ℝ)^77
        have hw : |(1322669299/2500000000 : ℝ)|=(1322669299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2886178153/10000000000 : ℝ)|^93 ≤ (2229371719799/10000000000000 : ℝ)^77
        have hw : |(2886178153/10000000000 : ℝ)|=(2886178153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s0_6 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-652567/10000000000 : ℝ)*x 0 + (1588383493/2000000000 : ℝ)*x 1 + (-774721691/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (652567/10000000000 : ℝ)^93 ≤ (220230177/25000000000000 : ℝ)^77 := by
    have hnat : (652567 : ℕ)^93*25000000000000^77 ≤ 220230177^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652567 10000000000 220230177 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1588383493/2000000000 : ℝ)^93 ≤ (75706059367911/100000000000000 : ℝ)^77 := by
    have hnat : (1588383493 : ℕ)^93*100000000000000^77 ≤ 75706059367911^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588383493 2000000000 75706059367911 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (774721691/2500000000 : ℝ)^93 ≤ (12146529853923/50000000000000 : ℝ)^77 := by
    have hnat : (774721691 : ℕ)^93*50000000000000^77 ≤ 12146529853923^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774721691 2500000000 12146529853923 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-652567/10000000000 : ℝ), (1588383493/2000000000 : ℝ), (-774721691/2500000000 : ℝ)] ![(220230177/25000000000000 : ℝ), (75706059367911/100000000000000 : ℝ), (12146529853923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-652567/10000000000 : ℝ)|^93 ≤ (220230177/25000000000000 : ℝ)^77
        have hw : |(-652567/10000000000 : ℝ)|=(652567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1588383493/2000000000 : ℝ)|^93 ≤ (75706059367911/100000000000000 : ℝ)^77
        have hw : |(1588383493/2000000000 : ℝ)|=(1588383493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-774721691/2500000000 : ℝ)|^93 ≤ (12146529853923/50000000000000 : ℝ)^77
        have hw : |(-774721691/2500000000 : ℝ)|=(774721691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s0_7 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-923584299/2000000000 : ℝ)*x 0 + (3032796543/10000000000 : ℝ)*x 1 + (-2195203199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (923584299/2000000000 : ℝ)^93 ≤ (9832436745289/25000000000000 : ℝ)^77 := by
    have hnat : (923584299 : ℕ)^93*25000000000000^77 ≤ 9832436745289^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923584299 2000000000 9832436745289 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3032796543/10000000000 : ℝ)^93 ≤ (11834348413357/50000000000000 : ℝ)^77 := by
    have hnat : (3032796543 : ℕ)^93*50000000000000^77 ≤ 11834348413357^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3032796543 10000000000 11834348413357 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2195203199/5000000000 : ℝ)^93 ≤ (9250389044231/25000000000000 : ℝ)^77 := by
    have hnat : (2195203199 : ℕ)^93*25000000000000^77 ≤ 9250389044231^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195203199 5000000000 9250389044231 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-923584299/2000000000 : ℝ), (3032796543/10000000000 : ℝ), (-2195203199/5000000000 : ℝ)] ![(9832436745289/25000000000000 : ℝ), (11834348413357/50000000000000 : ℝ), (9250389044231/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-923584299/2000000000 : ℝ)|^93 ≤ (9832436745289/25000000000000 : ℝ)^77
        have hw : |(-923584299/2000000000 : ℝ)|=(923584299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3032796543/10000000000 : ℝ)|^93 ≤ (11834348413357/50000000000000 : ℝ)^77
        have hw : |(3032796543/10000000000 : ℝ)|=(3032796543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2195203199/5000000000 : ℝ)|^93 ≤ (9250389044231/25000000000000 : ℝ)^77
        have hw : |(-2195203199/5000000000 : ℝ)|=(2195203199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s0_8 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4909785233/10000000000 : ℝ)*x 0 + (-3758537/25000000 : ℝ)*x 1 + (-5399748717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4909785233/10000000000 : ℝ)^93 ≤ (42351391995287/100000000000000 : ℝ)^77 := by
    have hnat : (4909785233 : ℕ)^93*100000000000000^77 ≤ 42351391995287^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4909785233 10000000000 42351391995287 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3758537/25000000 : ℝ)^93 ≤ (10141033390053/100000000000000 : ℝ)^77 := by
    have hnat : (3758537 : ℕ)^93*100000000000000^77 ≤ 10141033390053^77*25000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3758537 25000000 10141033390053 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399748717/10000000000 : ℝ)^93 ≤ (23753787301801/50000000000000 : ℝ)^77 := by
    have hnat : (5399748717 : ℕ)^93*50000000000000^77 ≤ 23753787301801^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399748717 10000000000 23753787301801 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4909785233/10000000000 : ℝ), (-3758537/25000000 : ℝ), (-5399748717/10000000000 : ℝ)] ![(42351391995287/100000000000000 : ℝ), (10141033390053/100000000000000 : ℝ), (23753787301801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4909785233/10000000000 : ℝ)|^93 ≤ (42351391995287/100000000000000 : ℝ)^77
        have hw : |(4909785233/10000000000 : ℝ)|=(4909785233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3758537/25000000 : ℝ)|^93 ≤ (10141033390053/100000000000000 : ℝ)^77
        have hw : |(-3758537/25000000 : ℝ)|=(3758537/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5399748717/10000000000 : ℝ)|^93 ≤ (23753787301801/50000000000000 : ℝ)^77
        have hw : |(-5399748717/10000000000 : ℝ)|=(5399748717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s0_9 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3413903329/10000000000 : ℝ)*x 0 + (5491026827/10000000000 : ℝ)*x 1 + (3090574719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3413903329/10000000000 : ℝ)^93 ≤ (27306400735499/100000000000000 : ℝ)^77 := by
    have hnat : (3413903329 : ℕ)^93*100000000000000^77 ≤ 27306400735499^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3413903329 10000000000 27306400735499 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5491026827/10000000000 : ℝ)^93 ≤ (12119804480983/25000000000000 : ℝ)^77 := by
    have hnat : (5491026827 : ℕ)^93*25000000000000^77 ≤ 12119804480983^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491026827 10000000000 12119804480983 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3090574719/10000000000 : ℝ)^93 ≤ (1210719065669/5000000000000 : ℝ)^77 := by
    have hnat : (3090574719 : ℕ)^93*5000000000000^77 ≤ 1210719065669^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3090574719 10000000000 1210719065669 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3413903329/10000000000 : ℝ), (5491026827/10000000000 : ℝ), (3090574719/10000000000 : ℝ)] ![(27306400735499/100000000000000 : ℝ), (12119804480983/25000000000000 : ℝ), (1210719065669/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3413903329/10000000000 : ℝ)|^93 ≤ (27306400735499/100000000000000 : ℝ)^77
        have hw : |(3413903329/10000000000 : ℝ)|=(3413903329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5491026827/10000000000 : ℝ)|^93 ≤ (12119804480983/25000000000000 : ℝ)^77
        have hw : |(5491026827/10000000000 : ℝ)|=(5491026827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3090574719/10000000000 : ℝ)|^93 ≤ (1210719065669/5000000000000 : ℝ)^77
        have hw : |(3090574719/10000000000 : ℝ)|=(3090574719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s0_13 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-19937/2500000000 : ℝ)*x 0 + (8698743897/10000000000 : ℝ)*x 1 + (-427140129/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19937/2500000000 : ℝ)^93 ≤ (69556369/100000000000000 : ℝ)^77 := by
    have hnat : (19937 : ℕ)^93*100000000000000^77 ≤ 69556369^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19937 2500000000 69556369 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8698743897/10000000000 : ℝ)^93 ≤ (5281485647483/6250000000000 : ℝ)^77 := by
    have hnat : (8698743897 : ℕ)^93*6250000000000^77 ≤ 5281485647483^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8698743897 10000000000 5281485647483 6250000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427140129/2000000000 : ℝ)^93 ≤ (1937020008971/12500000000000 : ℝ)^77 := by
    have hnat : (427140129 : ℕ)^93*12500000000000^77 ≤ 1937020008971^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427140129 2000000000 1937020008971 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19937/2500000000 : ℝ), (8698743897/10000000000 : ℝ), (-427140129/2000000000 : ℝ)] ![(69556369/100000000000000 : ℝ), (5281485647483/6250000000000 : ℝ), (1937020008971/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19937/2500000000 : ℝ)|^93 ≤ (69556369/100000000000000 : ℝ)^77
        have hw : |(-19937/2500000000 : ℝ)|=(19937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8698743897/10000000000 : ℝ)|^93 ≤ (5281485647483/6250000000000 : ℝ)^77
        have hw : |(8698743897/10000000000 : ℝ)|=(8698743897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427140129/2000000000 : ℝ)|^93 ≤ (1937020008971/12500000000000 : ℝ)^77
        have hw : |(-427140129/2000000000 : ℝ)|=(427140129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s0_14 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1187628771/2500000000 : ℝ)*x 0 + (2844538681/10000000000 : ℝ)*x 1 + (-4429166739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1187628771/2500000000 : ℝ)^93 ≤ (40697706745517/100000000000000 : ℝ)^77 := by
    have hnat : (1187628771 : ℕ)^93*100000000000000^77 ≤ 40697706745517^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187628771 2500000000 40697706745517 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2844538681/10000000000 : ℝ)^93 ≤ (1095291617071/5000000000000 : ℝ)^77 := by
    have hnat : (2844538681 : ℕ)^93*5000000000000^77 ≤ 1095291617071^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2844538681 10000000000 1095291617071 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4429166739/10000000000 : ℝ)^93 ≤ (18698230448343/50000000000000 : ℝ)^77 := by
    have hnat : (4429166739 : ℕ)^93*50000000000000^77 ≤ 18698230448343^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4429166739 10000000000 18698230448343 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1187628771/2500000000 : ℝ), (2844538681/10000000000 : ℝ), (-4429166739/10000000000 : ℝ)] ![(40697706745517/100000000000000 : ℝ), (1095291617071/5000000000000 : ℝ), (18698230448343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1187628771/2500000000 : ℝ)|^93 ≤ (40697706745517/100000000000000 : ℝ)^77
        have hw : |(-1187628771/2500000000 : ℝ)|=(1187628771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2844538681/10000000000 : ℝ)|^93 ≤ (1095291617071/5000000000000 : ℝ)^77
        have hw : |(2844538681/10000000000 : ℝ)|=(2844538681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4429166739/10000000000 : ℝ)|^93 ≤ (18698230448343/50000000000000 : ℝ)^77
        have hw : |(-4429166739/10000000000 : ℝ)|=(4429166739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s0_15 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1305179521/2500000000 : ℝ)*x 0 + (-661145609/5000000000 : ℝ)*x 1 + (-2614716237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1305179521/2500000000 : ℝ)^93 ≤ (22805877663999/50000000000000 : ℝ)^77 := by
    have hnat : (1305179521 : ℕ)^93*50000000000000^77 ≤ 22805877663999^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305179521 2500000000 22805877663999 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (661145609/5000000000 : ℝ)^93 ≤ (1085564787333/12500000000000 : ℝ)^77 := by
    have hnat : (661145609 : ℕ)^93*12500000000000^77 ≤ 1085564787333^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661145609 5000000000 1085564787333 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614716237/5000000000 : ℝ)^93 ≤ (11425931588761/25000000000000 : ℝ)^77 := by
    have hnat : (2614716237 : ℕ)^93*25000000000000^77 ≤ 11425931588761^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614716237 5000000000 11425931588761 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1305179521/2500000000 : ℝ), (-661145609/5000000000 : ℝ), (-2614716237/5000000000 : ℝ)] ![(22805877663999/50000000000000 : ℝ), (1085564787333/12500000000000 : ℝ), (11425931588761/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1305179521/2500000000 : ℝ)|^93 ≤ (22805877663999/50000000000000 : ℝ)^77
        have hw : |(1305179521/2500000000 : ℝ)|=(1305179521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-661145609/5000000000 : ℝ)|^93 ≤ (1085564787333/12500000000000 : ℝ)^77
        have hw : |(-661145609/5000000000 : ℝ)|=(661145609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2614716237/5000000000 : ℝ)|^93 ≤ (11425931588761/25000000000000 : ℝ)^77
        have hw : |(-2614716237/5000000000 : ℝ)|=(2614716237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s0_16 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3144667943/10000000000 : ℝ)*x 0 + (3051604631/5000000000 : ℝ)*x 1 + (2659019411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3144667943/10000000000 : ℝ)^93 ≤ (12363594562651/50000000000000 : ℝ)^77 := by
    have hnat : (3144667943 : ℕ)^93*50000000000000^77 ≤ 12363594562651^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3144667943 10000000000 12363594562651 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3051604631/5000000000 : ℝ)^93 ≤ (27540317509993/50000000000000 : ℝ)^77 := by
    have hnat : (3051604631 : ℕ)^93*50000000000000^77 ≤ 27540317509993^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3051604631 5000000000 27540317509993 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2659019411/10000000000 : ℝ)^93 ≤ (25240219809/125000000000 : ℝ)^77 := by
    have hnat : (2659019411 : ℕ)^93*125000000000^77 ≤ 25240219809^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2659019411 10000000000 25240219809 125000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3144667943/10000000000 : ℝ), (3051604631/5000000000 : ℝ), (2659019411/10000000000 : ℝ)] ![(12363594562651/50000000000000 : ℝ), (27540317509993/50000000000000 : ℝ), (25240219809/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3144667943/10000000000 : ℝ)|^93 ≤ (12363594562651/50000000000000 : ℝ)^77
        have hw : |(3144667943/10000000000 : ℝ)|=(3144667943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3051604631/5000000000 : ℝ)|^93 ≤ (27540317509993/50000000000000 : ℝ)^77
        have hw : |(3051604631/5000000000 : ℝ)|=(3051604631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2659019411/10000000000 : ℝ)|^93 ≤ (25240219809/125000000000 : ℝ)^77
        have hw : |(2659019411/10000000000 : ℝ)|=(2659019411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s0_20 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-968277/10000000000 : ℝ)*x 0 + (6785540957/10000000000 : ℝ)*x 1 + (-4429166739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (968277/10000000000 : ℝ)^93 ≤ (1418801419/100000000000000 : ℝ)^77 := by
    have hnat : (968277 : ℕ)^93*100000000000000^77 ≤ 1418801419^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968277 10000000000 1418801419 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6785540957/10000000000 : ℝ)^93 ≤ (15650530071859/25000000000000 : ℝ)^77 := by
    have hnat : (6785540957 : ℕ)^93*25000000000000^77 ≤ 15650530071859^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6785540957 10000000000 15650530071859 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4429166739/10000000000 : ℝ)^93 ≤ (18698230448343/50000000000000 : ℝ)^77 := by
    have hnat : (4429166739 : ℕ)^93*50000000000000^77 ≤ 18698230448343^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4429166739 10000000000 18698230448343 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-968277/10000000000 : ℝ), (6785540957/10000000000 : ℝ), (-4429166739/10000000000 : ℝ)] ![(1418801419/100000000000000 : ℝ), (15650530071859/25000000000000 : ℝ), (18698230448343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-968277/10000000000 : ℝ)|^93 ≤ (1418801419/100000000000000 : ℝ)^77
        have hw : |(-968277/10000000000 : ℝ)|=(968277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6785540957/10000000000 : ℝ)|^93 ≤ (15650530071859/25000000000000 : ℝ)^77
        have hw : |(6785540957/10000000000 : ℝ)|=(6785540957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4429166739/10000000000 : ℝ)|^93 ≤ (18698230448343/50000000000000 : ℝ)^77
        have hw : |(-4429166739/10000000000 : ℝ)|=(4429166739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s0_21 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-604559957/1250000000 : ℝ)*x 0 + (174613089/500000000 : ℝ)*x 1 + (-1862823523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (604559957/1250000000 : ℝ)^93 ≤ (41588860922717/100000000000000 : ℝ)^77 := by
    have hnat : (604559957 : ℕ)^93*100000000000000^77 ≤ 41588860922717^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604559957 1250000000 41588860922717 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174613089/500000000 : ℝ)^93 ≤ (1122607485303/4000000000000 : ℝ)^77 := by
    have hnat : (174613089 : ℕ)^93*4000000000000^77 ≤ 1122607485303^77*500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174613089 500000000 1122607485303 4000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1862823523/5000000000 : ℝ)^93 ≤ (3793243990817/12500000000000 : ℝ)^77 := by
    have hnat : (1862823523 : ℕ)^93*12500000000000^77 ≤ 3793243990817^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862823523 5000000000 3793243990817 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-604559957/1250000000 : ℝ), (174613089/500000000 : ℝ), (-1862823523/5000000000 : ℝ)] ![(41588860922717/100000000000000 : ℝ), (1122607485303/4000000000000 : ℝ), (3793243990817/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-604559957/1250000000 : ℝ)|^93 ≤ (41588860922717/100000000000000 : ℝ)^77
        have hw : |(-604559957/1250000000 : ℝ)|=(604559957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(174613089/500000000 : ℝ)|^93 ≤ (1122607485303/4000000000000 : ℝ)^77
        have hw : |(174613089/500000000 : ℝ)|=(174613089/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1862823523/5000000000 : ℝ)|^93 ≤ (3793243990817/12500000000000 : ℝ)^77
        have hw : |(-1862823523/5000000000 : ℝ)|=(1862823523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s0_22 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2306765781/5000000000 : ℝ)*x 0 + (-306040757/1250000000 : ℝ)*x 1 + (-153694753/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2306765781/5000000000 : ℝ)^93 ≤ (1571383779187/4000000000000 : ℝ)^77 := by
    have hnat : (2306765781 : ℕ)^93*4000000000000^77 ≤ 1571383779187^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306765781 5000000000 1571383779187 4000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (306040757/1250000000 : ℝ)^93 ≤ (1827599571977/10000000000000 : ℝ)^77 := by
    have hnat : (306040757 : ℕ)^93*10000000000000^77 ≤ 1827599571977^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306040757 1250000000 1827599571977 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153694753/312500000 : ℝ)^93 ≤ (42439409783921/100000000000000 : ℝ)^77 := by
    have hnat : (153694753 : ℕ)^93*100000000000000^77 ≤ 42439409783921^77*312500000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153694753 312500000 42439409783921 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2306765781/5000000000 : ℝ), (-306040757/1250000000 : ℝ), (-153694753/312500000 : ℝ)] ![(1571383779187/4000000000000 : ℝ), (1827599571977/10000000000000 : ℝ), (42439409783921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2306765781/5000000000 : ℝ)|^93 ≤ (1571383779187/4000000000000 : ℝ)^77
        have hw : |(2306765781/5000000000 : ℝ)|=(2306765781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-306040757/1250000000 : ℝ)|^93 ≤ (1827599571977/10000000000000 : ℝ)^77
        have hw : |(-306040757/1250000000 : ℝ)|=(306040757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-153694753/312500000 : ℝ)|^93 ≤ (42439409783921/100000000000000 : ℝ)^77
        have hw : |(-153694753/312500000 : ℝ)|=(153694753/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s0_23 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4762120413/10000000000 : ℝ)*x 0 + (4454862153/10000000000 : ℝ)*x 1 + (1401687023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4762120413/10000000000 : ℝ)^93 ≤ (1275556858817/3125000000000 : ℝ)^77 := by
    have hnat : (4762120413 : ℕ)^93*3125000000000^77 ≤ 1275556858817^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4762120413 10000000000 1275556858817 3125000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4454862153/10000000000 : ℝ)^93 ≤ (3765865179181/10000000000000 : ℝ)^77 := by
    have hnat : (4454862153 : ℕ)^93*10000000000000^77 ≤ 3765865179181^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4454862153 10000000000 3765865179181 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1401687023/5000000000 : ℝ)^93 ≤ (10761764353389/50000000000000 : ℝ)^77 := by
    have hnat : (1401687023 : ℕ)^93*50000000000000^77 ≤ 10761764353389^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401687023 5000000000 10761764353389 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4762120413/10000000000 : ℝ), (4454862153/10000000000 : ℝ), (1401687023/5000000000 : ℝ)] ![(1275556858817/3125000000000 : ℝ), (3765865179181/10000000000000 : ℝ), (10761764353389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4762120413/10000000000 : ℝ)|^93 ≤ (1275556858817/3125000000000 : ℝ)^77
        have hw : |(4762120413/10000000000 : ℝ)|=(4762120413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4454862153/10000000000 : ℝ)|^93 ≤ (3765865179181/10000000000000 : ℝ)^77
        have hw : |(4454862153/10000000000 : ℝ)|=(4454862153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1401687023/5000000000 : ℝ)|^93 ≤ (10761764353389/50000000000000 : ℝ)^77
        have hw : |(1401687023/5000000000 : ℝ)|=(1401687023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s0_27 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-464067/10000000000 : ℝ)*x 0 + (8679135417/10000000000 : ℝ)*x 1 + (-2161855711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464067/10000000000 : ℝ)^93 ≤ (58361967/10000000000000 : ℝ)^77 := by
    have hnat : (464067 : ℕ)^93*10000000000000^77 ≤ 58361967^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464067 10000000000 58361967 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8679135417/10000000000 : ℝ)^93 ≤ (84273756550423/100000000000000 : ℝ)^77 := by
    have hnat : (8679135417 : ℕ)^93*100000000000000^77 ≤ 84273756550423^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8679135417 10000000000 84273756550423 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2161855711/10000000000 : ℝ)^93 ≤ (15725659822063/100000000000000 : ℝ)^77 := by
    have hnat : (2161855711 : ℕ)^93*100000000000000^77 ≤ 15725659822063^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161855711 10000000000 15725659822063 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-464067/10000000000 : ℝ), (8679135417/10000000000 : ℝ), (-2161855711/10000000000 : ℝ)] ![(58361967/10000000000000 : ℝ), (84273756550423/100000000000000 : ℝ), (15725659822063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-464067/10000000000 : ℝ)|^93 ≤ (58361967/10000000000000 : ℝ)^77
        have hw : |(-464067/10000000000 : ℝ)|=(464067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8679135417/10000000000 : ℝ)|^93 ≤ (84273756550423/100000000000000 : ℝ)^77
        have hw : |(8679135417/10000000000 : ℝ)|=(8679135417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2161855711/10000000000 : ℝ)|^93 ≤ (15725659822063/100000000000000 : ℝ)^77
        have hw : |(-2161855711/10000000000 : ℝ)|=(2161855711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s1_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2238025359/5000000000 : ℝ)*x 0 + (3448218693/10000000000 : ℝ)*x 1 + (-2070927827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2238025359/5000000000 : ℝ)^93 ≤ (37875092304851/100000000000000 : ℝ)^77 := by
    have hnat : (2238025359 : ℕ)^93*100000000000000^77 ≤ 37875092304851^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238025359 5000000000 37875092304851 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3448218693/10000000000 : ℝ)^93 ≤ (27638254069713/100000000000000 : ℝ)^77 := by
    have hnat : (3448218693 : ℕ)^93*100000000000000^77 ≤ 27638254069713^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3448218693 10000000000 27638254069713 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070927827/5000000000 : ℝ)^93 ≤ (34486653605831/100000000000000 : ℝ)^77 := by
    have hnat : (2070927827 : ℕ)^93*100000000000000^77 ≤ 34486653605831^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070927827 5000000000 34486653605831 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2238025359/5000000000 : ℝ), (3448218693/10000000000 : ℝ), (-2070927827/5000000000 : ℝ)] ![(37875092304851/100000000000000 : ℝ), (27638254069713/100000000000000 : ℝ), (34486653605831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2238025359/5000000000 : ℝ)|^93 ≤ (37875092304851/100000000000000 : ℝ)^77
        have hw : |(-2238025359/5000000000 : ℝ)|=(2238025359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3448218693/10000000000 : ℝ)|^93 ≤ (27638254069713/100000000000000 : ℝ)^77
        have hw : |(3448218693/10000000000 : ℝ)|=(3448218693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2070927827/5000000000 : ℝ)|^93 ≤ (34486653605831/100000000000000 : ℝ)^77
        have hw : |(-2070927827/5000000000 : ℝ)|=(2070927827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s1_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4180963649/10000000000 : ℝ)*x 0 + (-15930453/50000000 : ℝ)*x 1 + (-585355571/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180963649/10000000000 : ℝ)^93 ≤ (1395213173667/4000000000000 : ℝ)^77 := by
    have hnat : (4180963649 : ℕ)^93*4000000000000^77 ≤ 1395213173667^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180963649 10000000000 1395213173667 4000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15930453/50000000 : ℝ)^93 ≤ (5024224364647/20000000000000 : ℝ)^77 := by
    have hnat : (15930453 : ℕ)^93*20000000000000^77 ≤ 5024224364647^77*50000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15930453 50000000 5024224364647 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (585355571/1250000000 : ℝ)^93 ≤ (39998548820727/100000000000000 : ℝ)^77 := by
    have hnat : (585355571 : ℕ)^93*100000000000000^77 ≤ 39998548820727^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585355571 1250000000 39998548820727 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180963649/10000000000 : ℝ), (-15930453/50000000 : ℝ), (-585355571/1250000000 : ℝ)] ![(1395213173667/4000000000000 : ℝ), (5024224364647/20000000000000 : ℝ), (39998548820727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180963649/10000000000 : ℝ)|^93 ≤ (1395213173667/4000000000000 : ℝ)^77
        have hw : |(4180963649/10000000000 : ℝ)|=(4180963649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15930453/50000000 : ℝ)|^93 ≤ (5024224364647/20000000000000 : ℝ)^77
        have hw : |(-15930453/50000000 : ℝ)|=(15930453/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-585355571/1250000000 : ℝ)|^93 ≤ (39998548820727/100000000000000 : ℝ)^77
        have hw : |(-585355571/1250000000 : ℝ)|=(585355571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s1_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3709098969/10000000000 : ℝ)*x 0 + (2454049839/5000000000 : ℝ)*x 1 + (3432166771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3709098969/10000000000 : ℝ)^93 ≤ (15091616491419/50000000000000 : ℝ)^77 := by
    have hnat : (3709098969 : ℕ)^93*50000000000000^77 ≤ 15091616491419^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3709098969 10000000000 15091616491419 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2454049839/5000000000 : ℝ)^93 ≤ (4233383198147/10000000000000 : ℝ)^77 := by
    have hnat : (2454049839 : ℕ)^93*10000000000000^77 ≤ 4233383198147^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2454049839 5000000000 4233383198147 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3432166771/10000000000 : ℝ)^93 ≤ (27482935025009/100000000000000 : ℝ)^77 := by
    have hnat : (3432166771 : ℕ)^93*100000000000000^77 ≤ 27482935025009^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3432166771 10000000000 27482935025009 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3709098969/10000000000 : ℝ), (2454049839/5000000000 : ℝ), (3432166771/10000000000 : ℝ)] ![(15091616491419/50000000000000 : ℝ), (4233383198147/10000000000000 : ℝ), (27482935025009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3709098969/10000000000 : ℝ)|^93 ≤ (15091616491419/50000000000000 : ℝ)^77
        have hw : |(3709098969/10000000000 : ℝ)|=(3709098969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2454049839/5000000000 : ℝ)|^93 ≤ (4233383198147/10000000000000 : ℝ)^77
        have hw : |(2454049839/5000000000 : ℝ)|=(2454049839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3432166771/10000000000 : ℝ)|^93 ≤ (27482935025009/100000000000000 : ℝ)^77
        have hw : |(3432166771/10000000000 : ℝ)|=(3432166771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328018_s1_6 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2974700427/10000000000 : ℝ)*x 0 + (70838529/125000000 : ℝ)*x 1 + (-3331782073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2974700427/10000000000 : ℝ)^93 ≤ (1156109174371/5000000000000 : ℝ)^77 := by
    have hnat : (2974700427 : ℕ)^93*5000000000000^77 ≤ 1156109174371^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2974700427 10000000000 1156109174371 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70838529/125000000 : ℝ)^93 ≤ (50362763382449/100000000000000 : ℝ)^77 := by
    have hnat : (70838529 : ℕ)^93*100000000000000^77 ≤ 50362763382449^77*125000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70838529 125000000 50362763382449 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3331782073/10000000000 : ℝ)^93 ≤ (13257526553309/50000000000000 : ℝ)^77 := by
    have hnat : (3331782073 : ℕ)^93*50000000000000^77 ≤ 13257526553309^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3331782073 10000000000 13257526553309 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2974700427/10000000000 : ℝ), (70838529/125000000 : ℝ), (-3331782073/10000000000 : ℝ)] ![(1156109174371/5000000000000 : ℝ), (50362763382449/100000000000000 : ℝ), (13257526553309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2974700427/10000000000 : ℝ)|^93 ≤ (1156109174371/5000000000000 : ℝ)^77
        have hw : |(2974700427/10000000000 : ℝ)|=(2974700427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70838529/125000000 : ℝ)|^93 ≤ (50362763382449/100000000000000 : ℝ)^77
        have hw : |(70838529/125000000 : ℝ)|=(70838529/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3331782073/10000000000 : ℝ)|^93 ≤ (13257526553309/50000000000000 : ℝ)^77
        have hw : |(-3331782073/10000000000 : ℝ)|=(3331782073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328018 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (80697/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((4592036657/10000000000 : ℝ)*X 1 0+(-2081094471/10000000000 : ℝ)*X 1 1+(-5249672509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1913978283/5000000000 : ℝ)*X 2 0+(1322669299/2500000000 : ℝ)*X 2 1+(2886178153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((-652567/10000000000 : ℝ)*X 0 0+(1588383493/2000000000 : ℝ)*X 0 1+(-774721691/2500000000 : ℝ)*X 0 2+(-652567/10000000000 : ℝ)*X 1 0+(1588383493/2000000000 : ℝ)*X 1 1+(-774721691/2500000000 : ℝ)*X 1 2+(-652567/10000000000 : ℝ)*X 2 0+(1588383493/2000000000 : ℝ)*X 2 1+(-774721691/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-923584299/2000000000 : ℝ)*X 0 0+(3032796543/10000000000 : ℝ)*X 0 1+(-2195203199/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4909785233/10000000000 : ℝ)*X 1 0+(-3758537/25000000 : ℝ)*X 1 1+(-5399748717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3413903329/10000000000 : ℝ)*X 2 0+(5491026827/10000000000 : ℝ)*X 2 1+(3090574719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-19937/2500000000 : ℝ)*X 0 0+(8698743897/10000000000 : ℝ)*X 0 1+(-427140129/2000000000 : ℝ)*X 0 2+(-19937/2500000000 : ℝ)*X 1 0+(8698743897/10000000000 : ℝ)*X 1 1+(-427140129/2000000000 : ℝ)*X 1 2+(-19937/2500000000 : ℝ)*X 2 0+(8698743897/10000000000 : ℝ)*X 2 1+(-427140129/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1187628771/2500000000 : ℝ)*X 0 0+(2844538681/10000000000 : ℝ)*X 0 1+(-4429166739/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1305179521/2500000000 : ℝ)*X 1 0+(-661145609/5000000000 : ℝ)*X 1 1+(-2614716237/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3144667943/10000000000 : ℝ)*X 2 0+(3051604631/5000000000 : ℝ)*X 2 1+(2659019411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-968277/10000000000 : ℝ)*X 0 0+(6785540957/10000000000 : ℝ)*X 0 1+(-4429166739/10000000000 : ℝ)*X 0 2+(-968277/10000000000 : ℝ)*X 1 0+(6785540957/10000000000 : ℝ)*X 1 1+(-4429166739/10000000000 : ℝ)*X 1 2+(-968277/10000000000 : ℝ)*X 2 0+(6785540957/10000000000 : ℝ)*X 2 1+(-4429166739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-604559957/1250000000 : ℝ)*X 0 0+(174613089/500000000 : ℝ)*X 0 1+(-1862823523/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2306765781/5000000000 : ℝ)*X 1 0+(-306040757/1250000000 : ℝ)*X 1 1+(-153694753/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((4762120413/10000000000 : ℝ)*X 2 0+(4454862153/10000000000 : ℝ)*X 2 1+(1401687023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((-464067/10000000000 : ℝ)*X 0 0+(8679135417/10000000000 : ℝ)*X 0 1+(-2161855711/10000000000 : ℝ)*X 0 2+(-464067/10000000000 : ℝ)*X 1 0+(8679135417/10000000000 : ℝ)*X 1 1+(-2161855711/10000000000 : ℝ)*X 1 2+(-464067/10000000000 : ℝ)*X 2 0+(8679135417/10000000000 : ℝ)*X 2 1+(-2161855711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((7361/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7361/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (896097103861966433073/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2025153/1000000000000 : ℝ)*(base1) + (791022202553/1000000000000 : ℝ)*(base7) + (1467235795407/1000000000000 : ℝ)*(base50) + (276559/125000000000 : ℝ)*(base53) + (113016681851/250000000000 : ℝ)*(base60) + (585725681437/125000000000 : ℝ)*(major_s0_0) + (585725681437/125000000000 : ℝ)*(major_s0_1) + (187432129561/40000000000 : ℝ)*(major_s0_2) + (34678131/500000000000 : ℝ)*(sp_s0_1) + (1696612236043/250000000000 : ℝ)*(sp_s0_7) + (6786377562757/1000000000000 : ℝ)*(sp_s0_8) + (6786449131491/1000000000000 : ℝ)*(sp_s0_9) + (2950029677841/1000000000000 : ℝ)*(sp_s0_13) + (596653031/1000000000000 : ℝ)*(sp_s0_27) + (8435961537/3906250000 : ℝ)*(f.failure) + (6786449131491/1000000000000 : ℝ)*(f.sum) + (3661414923964549/10000000000000000000000000000 : ℝ)*base63 + (294614990763/8000000000000000000000000 : ℝ)*base64 + (5621333993329/25000000000000000000000000 : ℝ)*base66 + (4324230322309/400000000000000000000000000 : ℝ)*base69 + (1689845574319713/5000000000000000000000000000 : ℝ)*base71 + (11435712119171/25000000000000000000000000 : ℝ)*base72 + (659920485386647/1250000000000000000000000000 : ℝ)*base74 + (811570358988353/1250000000000000000000000000 : ℝ)*base76 + (1127341457/10000000000000000000000 : ℝ)*base79 + (1/7812500000000 : ℝ)*base86 + (1/7812500000000 : ℝ)*base88 + (141/125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4181/10000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(4181/10000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1180038386177624128281/100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1773487179543/1000000000000 : ℝ)*(base1) + (1267715591169/1000000000000 : ℝ)*(base7) + (322947472151/1000000000000 : ℝ)*(base39) + (58276628267/200000000000 : ℝ)*(base50) + (542469740929/1000000000000 : ℝ)*(base60) + (2786936250369/1000000000000 : ℝ)*(major_s0_0) + (2786936250369/1000000000000 : ℝ)*(major_s0_1) + (2786936250369/1000000000000 : ℝ)*(major_s0_2) + (18500863/500000000000 : ℝ)*(sp_s0_2) + (3720457/100000000000 : ℝ)*(sp_s0_9) + (1076179943079/200000000000 : ℝ)*(sp_s0_14) + (901853133963/250000000000 : ℝ)*(sp_s0_15) + (901834582389/250000000000 : ℝ)*(sp_s0_16) + (778678809307/1000000000000 : ℝ)*(sp_s0_20) + (1284450397681/1000000000000 : ℝ)*(f.failure) + (901853133963/250000000000 : ℝ)*(f.sum) + (1745967370530861/5000000000000000000000000000 : ℝ)*base63 + (145488054980573/200000000000000000000000000 : ℝ)*base65 + (41921935300573/200000000000000000000000000 : ℝ)*base66 + (4003637732030861/10000000000000000000000000000 : ℝ)*base69 + (7053813218997789/10000000000000000000000000000 : ℝ)*base71 + (65790374719427/200000000000000000000000000 : ℝ)*base72 + (456284453969139/10000000000000000000000000000 : ℝ)*base74 + (2254294581969139/10000000000000000000000000000 : ℝ)*base77 + (3708729551/10000000000000000000000 : ℝ)*base78 + (2601/4000000000000000 : ℝ)*base86 + (2601/4000000000000000 : ℝ)*base88 + (2601/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-6277/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-6277/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (21945735576283009851159/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (906786605453/1000000000000 : ℝ)*(base1) + (1523948319879/1000000000000 : ℝ)*(base7) + (923532428089/1000000000000 : ℝ)*(base50) + (9546393/500000000000 : ℝ)*(base60) + (969449050813/250000000000 : ℝ)*(major_s0_0) + (969449050813/250000000000 : ℝ)*(major_s0_1) + (969449050813/250000000000 : ℝ)*(major_s0_2) + (37019/50000000000 : ℝ)*(sp_s0_6) + (12187381/500000000000 : ℝ)*(sp_s0_15) + (10188107/125000000000 : ℝ)*(sp_s0_16) + (3027655342179/500000000000 : ℝ)*(sp_s0_21) + (2574249852071/500000000000 : ℝ)*(sp_s0_22) + (160888830439/31250000000 : ℝ)*(sp_s0_23) + (2404369732313/1000000000000 : ℝ)*(sp_s0_27) + (446802189567/250000000000 : ℝ)*(f.failure) + (643565509863/125000000000 : ℝ)*(f.sum) + (827401915386897/1250000000000000000000000000 : ℝ)*base63 + (43785703369921/50000000000000000000000000 : ℝ)*base65 + (22305089019921/50000000000000000000000000 : ℝ)*base66 + (2042024410261897/2500000000000000000000000000 : ℝ)*base69 + (1681642739984153/2500000000000000000000000000 : ℝ)*base71 + (24576365910079/50000000000000000000000000 : ℝ)*base72 + (1401737605261897/2500000000000000000000000000 : ℝ)*base75 + (1551570285238103/2500000000000000000000000000 : ℝ)*base77 + (1608498161/10000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (7/1000000000000000 : ℝ)*base86 + (7/1000000000000000 : ℝ)*base88 + (7/1000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (7361/25000 : ℝ) ^ (91/16 : ℝ) ≤ (19096305207785907/20000000000000000000 : ℝ) := by
    have hpowers : (7361/25000 : ℝ)^91 ≤ (19096305207785907/20000000000000000000 : ℝ)^16 := by
      have hnat : (7361 : ℕ)^91*20000000000000000000^16 ≤ 19096305207785907^16*25000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7361 25000 19096305207785907 20000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7361/25000 : ℝ)) (X := (19096305207785907/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (20019096305207785907/20000000000000000000 : ℝ) ≤ (625104883493327/625000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (20019096305207785907/20000000000000000000 : ℝ)^16 ≤ (625104883493327/625000000000000 : ℝ)^91 := by
      have hnat : (20019096305207785907 : ℕ)^16*625000000000000^91 ≤ 625104883493327^91*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20019096305207785907 20000000000000000000 625104883493327 625000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625104883493327/625000000000000 : ℝ)) (X := (20019096305207785907/20000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (10019096305207785907/10000000000000000000 : ℝ) ≤ (625209684561213/625000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (10019096305207785907/10000000000000000000 : ℝ)^16 ≤ (625209684561213/625000000000000 : ℝ)^91 := by
      have hnat : (10019096305207785907 : ℕ)^16*625000000000000^91 ≤ 625209684561213^91*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10019096305207785907 10000000000000000000 625209684561213 625000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625209684561213/625000000000000 : ℝ)) (X := (10019096305207785907/10000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(104883493327/184025000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(52400533943/92012500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (7361/25000 : ℝ)) (alpha := (104883493327/184025000000000 : ℝ)) (beta := (52400533943/92012500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (7361/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(104883493327/184025000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(52400533943/92012500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (4181/10000 : ℝ) ^ (91/16 : ℝ) ≤ (70150529417287863/10000000000000000000 : ℝ) := by
    have hpowers : (4181/10000 : ℝ)^91 ≤ (70150529417287863/10000000000000000000 : ℝ)^16 := by
      have hnat : (4181 : ℕ)^91*10000000000000000000^16 ≤ 70150529417287863^16*10000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4181 10000 70150529417287863 10000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4181/10000 : ℝ)) (X := (70150529417287863/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (10070150529417287863/10000000000000000000 : ℝ) ≤ (10012298654545961/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (10070150529417287863/10000000000000000000 : ℝ)^16 ≤ (10012298654545961/10000000000000000 : ℝ)^91 := by
      have hnat : (10070150529417287863 : ℕ)^16*10000000000000000^91 ≤ 10012298654545961^91*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10070150529417287863 10000000000000000000 10012298654545961 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012298654545961/10000000000000000 : ℝ)) (X := (10070150529417287863/10000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5070150529417287863/5000000000000000000 : ℝ) ≤ (10024526899587733/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (5070150529417287863/5000000000000000000 : ℝ)^16 ≤ (10024526899587733/10000000000000000 : ℝ)^91 := by
      have hnat : (5070150529417287863 : ℕ)^16*10000000000000000^91 ≤ 10024526899587733^91*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5070150529417287863 5000000000000000000 10024526899587733 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024526899587733/10000000000000000 : ℝ)) (X := (5070150529417287863/5000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(12298654545961/4181000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(3057061260443/1045250000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (4181/10000 : ℝ)) (alpha := (12298654545961/4181000000000000 : ℝ)) (beta := (3057061260443/1045250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (4181/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(12298654545961/4181000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(3057061260443/1045250000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (6277/12500 : ℝ) ^ (91/16 : ℝ) ≤ (994281908022105331/50000000000000000000 : ℝ) := by
    have hpowers : (6277/12500 : ℝ)^91 ≤ (994281908022105331/50000000000000000000 : ℝ)^16 := by
      have hnat : (6277 : ℕ)^91*50000000000000000000^16 ≤ 994281908022105331^16*12500^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6277 12500 994281908022105331 50000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6277/12500 : ℝ)) (X := (994281908022105331/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50994281908022105331/50000000000000000000 : ℝ) ≤ (10034680660815159/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (50994281908022105331/50000000000000000000 : ℝ)^16 ≤ (10034680660815159/10000000000000000 : ℝ)^91 := by
      have hnat : (50994281908022105331 : ℕ)^16*10000000000000000^91 ≤ 10034680660815159^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50994281908022105331 50000000000000000000 10034680660815159 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10034680660815159/10000000000000000 : ℝ)) (X := (50994281908022105331/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25994281908022105331/25000000000000000000 : ℝ) ≤ (10068808418531761/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (25994281908022105331/25000000000000000000 : ℝ)^16 ≤ (10068808418531761/10000000000000000 : ℝ)^91 := by
      have hnat : (25994281908022105331 : ℕ)^16*10000000000000000^91 ≤ 10068808418531761^91*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25994281908022105331 25000000000000000000 10068808418531761 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10068808418531761/10000000000000000 : ℝ)) (X := (25994281908022105331/25000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(34680660815159/5021600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(17063878858301/2510800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (6277/12500 : ℝ)) (alpha := (34680660815159/5021600000000000 : ℝ)) (beta := (17063878858301/2510800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (6277/12500 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(34680660815159/5021600000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(17063878858301/2510800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2238025359/5000000000 : ℝ)*X 0 0+(3448218693/10000000000 : ℝ)*X 0 1+(-2070927827/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4180963649/10000000000 : ℝ)*X 1 0+(-15930453/50000000 : ℝ)*X 1 1+(-585355571/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3709098969/10000000000 : ℝ)*X 2 0+(2454049839/5000000000 : ℝ)*X 2 1+(3432166771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2974700427/10000000000 : ℝ)*X 0 0+(70838529/125000000 : ℝ)*X 0 1+(-3331782073/10000000000 : ℝ)*X 0 2+(2974700427/10000000000 : ℝ)*X 1 0+(70838529/125000000 : ℝ)*X 1 1+(-3331782073/10000000000 : ℝ)*X 1 2+(2974700427/10000000000 : ℝ)*X 2 0+(70838529/125000000 : ℝ)*X 2 1+(-3331782073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328018_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-20037/2000 : ℝ) < ((-8679/4000 : ℝ)*P 0+(-8679/4000 : ℝ)*P 1+(-8679/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-20037/2000 : ℝ) < (-757733892882048753902133115780182639/77273236982800000000000000000000000 : ℝ) := by norm_num
    linear_combination (89177/200000000000 : ℝ)*(base11) + (63581/1000000000000 : ℝ)*(base12) + (152342661609/500000000000 : ℝ)*(base39) + (6011/100000000000 : ℝ)*(base43) + (82216058959/500000000000 : ℝ)*(base49) + (326764333993/500000000000 : ℝ)*(base50) + (195197/1000000000000 : ℝ)*(base53) + (3925527373/8000000000 : ℝ)*(base60) + (8679/4000 : ℝ)*(major_s1_0) + (216974993989/100000000000 : ℝ)*(major_s1_1) + (2169749804803/1000000000000 : ℝ)*(major_s1_2) + (3268633683009/1000000000000 : ℝ)*(sp_s1_0) + (653726850517/200000000000 : ℝ)*(sp_s1_1) + (3268634387673/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1634317223891/500000000000 : ℝ)*(f.sum) + (18156716458162834319/20995309600000000000000000000000 : ℝ)*base63 + (190305526753743/2510800000000000000000000000 : ℝ)*base65 + (16913752840303/26131250000000000000000000 : ℝ)*base66 + (1787261903534923/5021600000000000000000000000 : ℝ)*base69 + (6468662286319113783/18481998800000000000000000000000 : ℝ)*base71 + (1313428496273/1840250000000000000000000 : ℝ)*base72 + (151774332753601/418100000000000000000000000 : ℝ)*base75 + (18405906236567/36805000000000000000000000 : ℝ)*base76 + (752489071532974209/1538817050000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c328019_s0_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1286674367/2500000000 : ℝ)*x 0 + (1735008879/5000000000 : ℝ)*x 1 + (3415180469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1286674367/2500000000 : ℝ)^93 ≤ (11207959381833/25000000000000 : ℝ)^77 := by
    have hnat : (1286674367 : ℕ)^93*25000000000000^77 ≤ 11207959381833^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286674367 2500000000 11207959381833 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1735008879/5000000000 : ℝ)^93 ≤ (27849423269983/100000000000000 : ℝ)^77 := by
    have hnat : (1735008879 : ℕ)^93*100000000000000^77 ≤ 27849423269983^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735008879 5000000000 27849423269983 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3415180469/10000000000 : ℝ)^93 ≤ (27318739192413/100000000000000 : ℝ)^77 := by
    have hnat : (3415180469 : ℕ)^93*100000000000000^77 ≤ 27318739192413^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3415180469 10000000000 27318739192413 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1286674367/2500000000 : ℝ), (1735008879/5000000000 : ℝ), (3415180469/10000000000 : ℝ)] ![(11207959381833/25000000000000 : ℝ), (27849423269983/100000000000000 : ℝ), (27318739192413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1286674367/2500000000 : ℝ)|^93 ≤ (11207959381833/25000000000000 : ℝ)^77
        have hw : |(-1286674367/2500000000 : ℝ)|=(1286674367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1735008879/5000000000 : ℝ)|^93 ≤ (27849423269983/100000000000000 : ℝ)^77
        have hw : |(1735008879/5000000000 : ℝ)|=(1735008879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3415180469/10000000000 : ℝ)|^93 ≤ (27318739192413/100000000000000 : ℝ)^77
        have hw : |(3415180469/10000000000 : ℝ)|=(3415180469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328019_s0_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (874723013/2500000000 : ℝ)*x 0 + (-2253744613/10000000000 : ℝ)*x 1 + (306322003/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874723013/2500000000 : ℝ)^93 ≤ (28129555179907/100000000000000 : ℝ)^77 := by
    have hnat : (874723013 : ℕ)^93*100000000000000^77 ≤ 28129555179907^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874723013 2500000000 28129555179907 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253744613/10000000000 : ℝ)^93 ≤ (1033530644961/6250000000000 : ℝ)^77 := by
    have hnat : (2253744613 : ℕ)^93*6250000000000^77 ≤ 1033530644961^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253744613 10000000000 1033530644961 6250000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (306322003/500000000 : ℝ)^93 ≤ (55333954489779/100000000000000 : ℝ)^77 := by
    have hnat : (306322003 : ℕ)^93*100000000000000^77 ≤ 55333954489779^77*500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306322003 500000000 55333954489779 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874723013/2500000000 : ℝ), (-2253744613/10000000000 : ℝ), (306322003/500000000 : ℝ)] ![(28129555179907/100000000000000 : ℝ), (1033530644961/6250000000000 : ℝ), (55333954489779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874723013/2500000000 : ℝ)|^93 ≤ (28129555179907/100000000000000 : ℝ)^77
        have hw : |(874723013/2500000000 : ℝ)|=(874723013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2253744613/10000000000 : ℝ)|^93 ≤ (1033530644961/6250000000000 : ℝ)^77
        have hw : |(-2253744613/10000000000 : ℝ)|=(2253744613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(306322003/500000000 : ℝ)|^93 ≤ (55333954489779/100000000000000 : ℝ)^77
        have hw : |(306322003/500000000 : ℝ)|=(306322003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328019_s0_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3936293961/10000000000 : ℝ)*x 0 + (2714007191/5000000000 : ℝ)*x 1 + (-1305998103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3936293961/10000000000 : ℝ)^93 ≤ (4053777235933/12500000000000 : ℝ)^77 := by
    have hnat : (3936293961 : ℕ)^93*12500000000000^77 ≤ 4053777235933^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3936293961 10000000000 4053777235933 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714007191/5000000000 : ℝ)^93 ≤ (747001512393/1562500000000 : ℝ)^77 := by
    have hnat : (2714007191 : ℕ)^93*1562500000000^77 ≤ 747001512393^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714007191 5000000000 747001512393 1562500000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305998103/5000000000 : ℝ)^93 ≤ (19761685302297/100000000000000 : ℝ)^77 := by
    have hnat : (1305998103 : ℕ)^93*100000000000000^77 ≤ 19761685302297^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305998103 5000000000 19761685302297 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3936293961/10000000000 : ℝ), (2714007191/5000000000 : ℝ), (-1305998103/5000000000 : ℝ)] ![(4053777235933/12500000000000 : ℝ), (747001512393/1562500000000 : ℝ), (19761685302297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3936293961/10000000000 : ℝ)|^93 ≤ (4053777235933/12500000000000 : ℝ)^77
        have hw : |(3936293961/10000000000 : ℝ)|=(3936293961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714007191/5000000000 : ℝ)|^93 ≤ (747001512393/1562500000000 : ℝ)^77
        have hw : |(2714007191/5000000000 : ℝ)|=(2714007191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1305998103/5000000000 : ℝ)|^93 ≤ (19761685302297/100000000000000 : ℝ)^77
        have hw : |(-1305998103/5000000000 : ℝ)|=(1305998103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328019_s0_6 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (188163999/1000000000 : ℝ)*x 0 + (6600213619/10000000000 : ℝ)*x 1 + (329468713/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (188163999/1000000000 : ℝ)^93 ≤ (6649069670217/50000000000000 : ℝ)^77 := by
    have hnat : (188163999 : ℕ)^93*50000000000000^77 ≤ 6649069670217^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188163999 1000000000 6649069670217 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6600213619/10000000000 : ℝ)^93 ≤ (60542945848329/100000000000000 : ℝ)^77 := by
    have hnat : (6600213619 : ℕ)^93*100000000000000^77 ≤ 60542945848329^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6600213619 10000000000 60542945848329 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329468713/1000000000 : ℝ)^93 ≤ (13079457395199/50000000000000 : ℝ)^77 := by
    have hnat : (329468713 : ℕ)^93*50000000000000^77 ≤ 13079457395199^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329468713 1000000000 13079457395199 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(188163999/1000000000 : ℝ), (6600213619/10000000000 : ℝ), (329468713/1000000000 : ℝ)] ![(6649069670217/50000000000000 : ℝ), (60542945848329/100000000000000 : ℝ), (13079457395199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(188163999/1000000000 : ℝ)|^93 ≤ (6649069670217/50000000000000 : ℝ)^77
        have hw : |(188163999/1000000000 : ℝ)|=(188163999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6600213619/10000000000 : ℝ)|^93 ≤ (60542945848329/100000000000000 : ℝ)^77
        have hw : |(6600213619/10000000000 : ℝ)|=(6600213619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329468713/1000000000 : ℝ)|^93 ≤ (13079457395199/50000000000000 : ℝ)^77
        have hw : |(329468713/1000000000 : ℝ)|=(329468713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328019 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1286674367/2500000000 : ℝ)*X 0 0+(1735008879/5000000000 : ℝ)*X 0 1+(3415180469/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328019_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((874723013/2500000000 : ℝ)*X 1 0+(-2253744613/10000000000 : ℝ)*X 1 1+(306322003/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328019_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3936293961/10000000000 : ℝ)*X 2 0+(2714007191/5000000000 : ℝ)*X 2 1+(-1305998103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328019_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((188163999/1000000000 : ℝ)*X 0 0+(6600213619/10000000000 : ℝ)*X 0 1+(329468713/1000000000 : ℝ)*X 0 2+(188163999/1000000000 : ℝ)*X 1 0+(6600213619/10000000000 : ℝ)*X 1 1+(329468713/1000000000 : ℝ)*X 1 2+(188163999/1000000000 : ℝ)*X 2 0+(6600213619/10000000000 : ℝ)*X 2 1+(329468713/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328019_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-20037/2000 : ℝ) < ((-8679/4000 : ℝ)*P 0+(-8679/4000 : ℝ)*P 1+(-8679/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-20037/2000 : ℝ) < (-4949182663270659728349/500000000000000000000 : ℝ) := by norm_num
    linear_combination (28997/1000000000000 : ℝ)*(base1) + (93/12500000000 : ℝ)*(base3) + (39797/500000000000 : ℝ)*(base5) + (32391/1000000000000 : ℝ)*(base19) + (20257/1000000000000 : ℝ)*(base21) + (93395092473/100000000000 : ℝ)*(base49) + (80320632277/200000000000 : ℝ)*(base50) + (68240251257/125000000000 : ℝ)*(base60) + (8679/4000 : ℝ)*(major_s0_0) + (8679/4000 : ℝ)*(major_s0_1) + (8679/4000 : ℝ)*(major_s0_2) + (41243189223/12500000000 : ℝ)*(sp_s0_0) + (824863770973/250000000000 : ℝ)*(sp_s0_1) + (164972758409/50000000000 : ℝ)*(sp_s0_2) + (15624998187/15625000000 : ℝ)*(sp_s0_6) + (3299455108843/1000000000000 : ℝ)*(f.sum) + (28295657/100000000000000000000 : ℝ)*base62 + (447646353/2500000000000000000000 : ℝ)*base64 + (50943163/100000000000000000000 : ℝ)*base66 + (1130321977/5000000000000000000000 : ℝ)*base68 + (1797405823/5000000000000000000000 : ℝ)*base70 + (194404607/500000000000000000000 : ℝ)*base73 + (25560429/200000000000000000000 : ℝ)*base75 + (1358906149/5000000000000000000000 : ℝ)*base77 + (190275169/250000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p028_b007 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (c : Fin 88) (hlo : 18 ≤ c.val) (hhi : c.val < 20)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=18 ∨ c=19 := by omega
  rcases hc with rfl|rfl
  · exact collision_c328018 p hpa (by linarith only [hpb]) X hX
  · exact collision_c328019 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (c : Fin 88) (hlo : 18 ≤ c.val) (hhi : c.val < 20)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b007 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

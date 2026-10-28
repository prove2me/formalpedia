-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b030
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:54:56.988988+00:00
-- url     : https://prove2.me/submissions/91e3388f-d842-4620-a63b-3b966a164377

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
theorem collision_support_c303070_s0_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130921273/10000000000 : ℝ)*x 0 + (-276934483/625000000 : ℝ)*x 1 + (-3084653823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130921273/10000000000 : ℝ)^33 ≤ (12992986121919/100000000000000 : ℝ)^25 := by
    have hnat : (2130921273 : ℕ)^33*100000000000000^25 ≤ 12992986121919^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130921273 10000000000 12992986121919 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276934483/625000000 : ℝ)^33 ≤ (17074424284817/50000000000000 : ℝ)^25 := by
    have hnat : (276934483 : ℕ)^33*50000000000000^25 ≤ 17074424284817^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276934483 625000000 17074424284817 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3084653823/5000000000 : ℝ)^33 ≤ (26429082648709/50000000000000 : ℝ)^25 := by
    have hnat : (3084653823 : ℕ)^33*50000000000000^25 ≤ 26429082648709^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3084653823 5000000000 26429082648709 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130921273/10000000000 : ℝ), (-276934483/625000000 : ℝ), (-3084653823/5000000000 : ℝ)] ![(12992986121919/100000000000000 : ℝ), (17074424284817/50000000000000 : ℝ), (26429082648709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130921273/10000000000 : ℝ)|^33 ≤ (12992986121919/100000000000000 : ℝ)^25
        have hw : |(-2130921273/10000000000 : ℝ)|=(2130921273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-276934483/625000000 : ℝ)|^33 ≤ (17074424284817/50000000000000 : ℝ)^25
        have hw : |(-276934483/625000000 : ℝ)|=(276934483/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3084653823/5000000000 : ℝ)|^33 ≤ (26429082648709/50000000000000 : ℝ)^25
        have hw : |(-3084653823/5000000000 : ℝ)|=(3084653823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s0_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (625794533/1000000000 : ℝ)*x 0 + (4414742349/10000000000 : ℝ)*x 1 + (-2025719067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (625794533/1000000000 : ℝ)^33 ≤ (53862924461099/100000000000000 : ℝ)^25 := by
    have hnat : (625794533 : ℕ)^33*100000000000000^25 ≤ 53862924461099^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625794533 1000000000 53862924461099 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4414742349/10000000000 : ℝ)^33 ≤ (16992022831043/50000000000000 : ℝ)^25 := by
    have hnat : (4414742349 : ℕ)^33*50000000000000^25 ≤ 16992022831043^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4414742349 10000000000 16992022831043 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2025719067/10000000000 : ℝ)^33 ≤ (1215302986043/10000000000000 : ℝ)^25 := by
    have hnat : (2025719067 : ℕ)^33*10000000000000^25 ≤ 1215302986043^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025719067 10000000000 1215302986043 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(625794533/1000000000 : ℝ), (4414742349/10000000000 : ℝ), (-2025719067/10000000000 : ℝ)] ![(53862924461099/100000000000000 : ℝ), (16992022831043/50000000000000 : ℝ), (1215302986043/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(625794533/1000000000 : ℝ)|^33 ≤ (53862924461099/100000000000000 : ℝ)^25
        have hw : |(625794533/1000000000 : ℝ)|=(625794533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4414742349/10000000000 : ℝ)|^33 ≤ (16992022831043/50000000000000 : ℝ)^25
        have hw : |(4414742349/10000000000 : ℝ)|=(4414742349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2025719067/10000000000 : ℝ)|^33 ≤ (1215302986043/10000000000000 : ℝ)^25
        have hw : |(-2025719067/10000000000 : ℝ)|=(2025719067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s0_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1042461011/2000000000 : ℝ)*x 0 + (-546846571/2500000000 : ℝ)*x 1 + (-2695420611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042461011/2000000000 : ℝ)^33 ≤ (10578385217441/25000000000000 : ℝ)^25 := by
    have hnat : (1042461011 : ℕ)^33*25000000000000^25 ≤ 10578385217441^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042461011 2000000000 10578385217441 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546846571/2500000000 : ℝ)^33 ≤ (13449360652373/100000000000000 : ℝ)^25 := by
    have hnat : (546846571 : ℕ)^33*100000000000000^25 ≤ 13449360652373^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546846571 2500000000 13449360652373 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695420611/5000000000 : ℝ)^33 ≤ (8847419692813/20000000000000 : ℝ)^25 := by
    have hnat : (2695420611 : ℕ)^33*20000000000000^25 ≤ 8847419692813^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695420611 5000000000 8847419692813 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042461011/2000000000 : ℝ), (-546846571/2500000000 : ℝ), (-2695420611/5000000000 : ℝ)] ![(10578385217441/25000000000000 : ℝ), (13449360652373/100000000000000 : ℝ), (8847419692813/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042461011/2000000000 : ℝ)|^33 ≤ (10578385217441/25000000000000 : ℝ)^25
        have hw : |(1042461011/2000000000 : ℝ)|=(1042461011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-546846571/2500000000 : ℝ)|^33 ≤ (13449360652373/100000000000000 : ℝ)^25
        have hw : |(-546846571/2500000000 : ℝ)|=(546846571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2695420611/5000000000 : ℝ)|^33 ≤ (8847419692813/20000000000000 : ℝ)^25
        have hw : |(-2695420611/5000000000 : ℝ)|=(2695420611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s0_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1720238459/10000000000 : ℝ)*x 0 + (-2439857923/5000000000 : ℝ)*x 1 + (-3020820461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1720238459/10000000000 : ℝ)^33 ≤ (4897190813263/50000000000000 : ℝ)^25 := by
    have hnat : (1720238459 : ℕ)^33*50000000000000^25 ≤ 4897190813263^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720238459 10000000000 4897190813263 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2439857923/5000000000 : ℝ)^33 ≤ (7757303428353/20000000000000 : ℝ)^25 := by
    have hnat : (2439857923 : ℕ)^33*20000000000000^25 ≤ 7757303428353^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439857923 5000000000 7757303428353 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3020820461/5000000000 : ℝ)^33 ≤ (51419101214861/100000000000000 : ℝ)^25 := by
    have hnat : (3020820461 : ℕ)^33*100000000000000^25 ≤ 51419101214861^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3020820461 5000000000 51419101214861 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1720238459/10000000000 : ℝ), (-2439857923/5000000000 : ℝ), (-3020820461/5000000000 : ℝ)] ![(4897190813263/50000000000000 : ℝ), (7757303428353/20000000000000 : ℝ), (51419101214861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1720238459/10000000000 : ℝ)|^33 ≤ (4897190813263/50000000000000 : ℝ)^25
        have hw : |(-1720238459/10000000000 : ℝ)|=(1720238459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2439857923/5000000000 : ℝ)|^33 ≤ (7757303428353/20000000000000 : ℝ)^25
        have hw : |(-2439857923/5000000000 : ℝ)|=(2439857923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3020820461/5000000000 : ℝ)|^33 ≤ (51419101214861/100000000000000 : ℝ)^25
        have hw : |(-3020820461/5000000000 : ℝ)|=(3020820461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s0_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3110364817/5000000000 : ℝ)*x 0 + (2439857923/5000000000 : ℝ)*x 1 + (-1443896107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3110364817/5000000000 : ℝ)^33 ≤ (53440504677987/100000000000000 : ℝ)^25 := by
    have hnat : (3110364817 : ℕ)^33*100000000000000^25 ≤ 53440504677987^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3110364817 5000000000 53440504677987 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2439857923/5000000000 : ℝ)^33 ≤ (7757303428353/20000000000000 : ℝ)^25 := by
    have hnat : (2439857923 : ℕ)^33*20000000000000^25 ≤ 7757303428353^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439857923 5000000000 7757303428353 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1443896107/10000000000 : ℝ)^33 ≤ (1554595633993/20000000000000 : ℝ)^25 := by
    have hnat : (1443896107 : ℕ)^33*20000000000000^25 ≤ 1554595633993^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1443896107 10000000000 1554595633993 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3110364817/5000000000 : ℝ), (2439857923/5000000000 : ℝ), (-1443896107/10000000000 : ℝ)] ![(53440504677987/100000000000000 : ℝ), (7757303428353/20000000000000 : ℝ), (1554595633993/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3110364817/5000000000 : ℝ)|^33 ≤ (53440504677987/100000000000000 : ℝ)^25
        have hw : |(3110364817/5000000000 : ℝ)|=(3110364817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2439857923/5000000000 : ℝ)|^33 ≤ (7757303428353/20000000000000 : ℝ)^25
        have hw : |(2439857923/5000000000 : ℝ)|=(2439857923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1443896107/10000000000 : ℝ)|^33 ≤ (1554595633993/20000000000000 : ℝ)^25
        have hw : |(-1443896107/10000000000 : ℝ)|=(1443896107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s0_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (256190957/625000000 : ℝ)*x 0 + (-4326376989/10000000000 : ℝ)*x 1 + (2310596117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256190957/625000000 : ℝ)^33 ≤ (30813610448047/100000000000000 : ℝ)^25 := by
    have hnat : (256190957 : ℕ)^33*100000000000000^25 ≤ 30813610448047^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256190957 625000000 30813610448047 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4326376989/10000000000 : ℝ)^33 ≤ (16544519539331/50000000000000 : ℝ)^25 := by
    have hnat : (4326376989 : ℕ)^33*50000000000000^25 ≤ 16544519539331^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326376989 10000000000 16544519539331 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2310596117/5000000000 : ℝ)^33 ≤ (9024337616037/25000000000000 : ℝ)^25 := by
    have hnat : (2310596117 : ℕ)^33*25000000000000^25 ≤ 9024337616037^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2310596117 5000000000 9024337616037 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(256190957/625000000 : ℝ), (-4326376989/10000000000 : ℝ), (2310596117/5000000000 : ℝ)] ![(30813610448047/100000000000000 : ℝ), (16544519539331/50000000000000 : ℝ), (9024337616037/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(256190957/625000000 : ℝ)|^33 ≤ (30813610448047/100000000000000 : ℝ)^25
        have hw : |(256190957/625000000 : ℝ)|=(256190957/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4326376989/10000000000 : ℝ)|^33 ≤ (16544519539331/50000000000000 : ℝ)^25
        have hw : |(-4326376989/10000000000 : ℝ)|=(4326376989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2310596117/5000000000 : ℝ)|^33 ≤ (9024337616037/25000000000000 : ℝ)^25
        have hw : |(2310596117/5000000000 : ℝ)|=(2310596117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s0_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1283013427/2500000000 : ℝ)*x 0 + (-135178079/1000000000 : ℝ)*x 1 + (-3020820461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1283013427/2500000000 : ℝ)^33 ≤ (8291142320603/20000000000000 : ℝ)^25 := by
    have hnat : (1283013427 : ℕ)^33*20000000000000^25 ≤ 8291142320603^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283013427 2500000000 8291142320603 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135178079/1000000000 : ℝ)^33 ≤ (7125187166167/100000000000000 : ℝ)^25 := by
    have hnat : (135178079 : ℕ)^33*100000000000000^25 ≤ 7125187166167^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135178079 1000000000 7125187166167 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3020820461/5000000000 : ℝ)^33 ≤ (51419101214861/100000000000000 : ℝ)^25 := by
    have hnat : (3020820461 : ℕ)^33*100000000000000^25 ≤ 51419101214861^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3020820461 5000000000 51419101214861 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1283013427/2500000000 : ℝ), (-135178079/1000000000 : ℝ), (-3020820461/5000000000 : ℝ)] ![(8291142320603/20000000000000 : ℝ), (7125187166167/100000000000000 : ℝ), (51419101214861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1283013427/2500000000 : ℝ)|^33 ≤ (8291142320603/20000000000000 : ℝ)^25
        have hw : |(1283013427/2500000000 : ℝ)|=(1283013427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-135178079/1000000000 : ℝ)|^33 ≤ (7125187166167/100000000000000 : ℝ)^25
        have hw : |(-135178079/1000000000 : ℝ)|=(135178079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3020820461/5000000000 : ℝ)|^33 ≤ (51419101214861/100000000000000 : ℝ)^25
        have hw : |(-3020820461/5000000000 : ℝ)|=(3020820461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s0_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-456860723/2500000000 : ℝ)*x 0 + (-1006064241/2500000000 : ℝ)*x 1 + (-1683115367/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (456860723/2500000000 : ℝ)^33 ≤ (5304003950571/50000000000000 : ℝ)^25 := by
    have hnat : (456860723 : ℕ)^33*50000000000000^25 ≤ 5304003950571^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456860723 2500000000 5304003950571 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006064241/2500000000 : ℝ)^33 ≤ (30073579962473/100000000000000 : ℝ)^25 := by
    have hnat : (1006064241 : ℕ)^33*100000000000000^25 ≤ 30073579962473^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006064241 2500000000 30073579962473 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1683115367/2500000000 : ℝ)^33 ≤ (14829603029057/25000000000000 : ℝ)^25 := by
    have hnat : (1683115367 : ℕ)^33*25000000000000^25 ≤ 14829603029057^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683115367 2500000000 14829603029057 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-456860723/2500000000 : ℝ), (-1006064241/2500000000 : ℝ), (-1683115367/2500000000 : ℝ)] ![(5304003950571/50000000000000 : ℝ), (30073579962473/100000000000000 : ℝ), (14829603029057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-456860723/2500000000 : ℝ)|^33 ≤ (5304003950571/50000000000000 : ℝ)^25
        have hw : |(-456860723/2500000000 : ℝ)|=(456860723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1006064241/2500000000 : ℝ)|^33 ≤ (30073579962473/100000000000000 : ℝ)^25
        have hw : |(-1006064241/2500000000 : ℝ)|=(1006064241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1683115367/2500000000 : ℝ)|^33 ≤ (14829603029057/25000000000000 : ℝ)^25
        have hw : |(-1683115367/2500000000 : ℝ)|=(1683115367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s0_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (823218793/1250000000 : ℝ)*x 0 + (2271726851/5000000000 : ℝ)*x 1 + (-336461851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823218793/1250000000 : ℝ)^33 ≤ (57618101919611/100000000000000 : ℝ)^25 := by
    have hnat : (823218793 : ℕ)^33*100000000000000^25 ≤ 57618101919611^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823218793 1250000000 57618101919611 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2271726851/5000000000 : ℝ)^33 ≤ (35297964431507/100000000000000 : ℝ)^25 := by
    have hnat : (2271726851 : ℕ)^33*100000000000000^25 ≤ 35297964431507^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271726851 5000000000 35297964431507 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336461851/2500000000 : ℝ)^33 ≤ (1770983408757/25000000000000 : ℝ)^25 := by
    have hnat : (336461851 : ℕ)^33*25000000000000^25 ≤ 1770983408757^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336461851 2500000000 1770983408757 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(823218793/1250000000 : ℝ), (2271726851/5000000000 : ℝ), (-336461851/2500000000 : ℝ)] ![(57618101919611/100000000000000 : ℝ), (35297964431507/100000000000000 : ℝ), (1770983408757/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(823218793/1250000000 : ℝ)|^33 ≤ (57618101919611/100000000000000 : ℝ)^25
        have hw : |(823218793/1250000000 : ℝ)|=(823218793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2271726851/5000000000 : ℝ)|^33 ≤ (35297964431507/100000000000000 : ℝ)^25
        have hw : |(2271726851/5000000000 : ℝ)|=(2271726851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-336461851/2500000000 : ℝ)|^33 ≤ (1770983408757/25000000000000 : ℝ)^25
        have hw : |(-336461851/2500000000 : ℝ)|=(336461851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s0_16 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4280301941/10000000000 : ℝ)*x 0 + (-1258674677/2500000000 : ℝ)*x 1 + (1851954189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4280301941/10000000000 : ℝ)^33 ≤ (509760572719/1562500000000 : ℝ)^25 := by
    have hnat : (4280301941 : ℕ)^33*1562500000000^25 ≤ 509760572719^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4280301941 10000000000 509760572719 1562500000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1258674677/2500000000 : ℝ)^33 ≤ (8084161805073/20000000000000 : ℝ)^25 := by
    have hnat : (1258674677 : ℕ)^33*20000000000000^25 ≤ 8084161805073^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1258674677 2500000000 8084161805073 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1851954189/5000000000 : ℝ)^33 ≤ (26954514291843/100000000000000 : ℝ)^25 := by
    have hnat : (1851954189 : ℕ)^33*100000000000000^25 ≤ 26954514291843^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851954189 5000000000 26954514291843 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4280301941/10000000000 : ℝ), (-1258674677/2500000000 : ℝ), (1851954189/5000000000 : ℝ)] ![(509760572719/1562500000000 : ℝ), (8084161805073/20000000000000 : ℝ), (26954514291843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4280301941/10000000000 : ℝ)|^33 ≤ (509760572719/1562500000000 : ℝ)^25
        have hw : |(4280301941/10000000000 : ℝ)|=(4280301941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1258674677/2500000000 : ℝ)|^33 ≤ (8084161805073/20000000000000 : ℝ)^25
        have hw : |(-1258674677/2500000000 : ℝ)|=(1258674677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1851954189/5000000000 : ℝ)|^33 ≤ (26954514291843/100000000000000 : ℝ)^25
        have hw : |(1851954189/5000000000 : ℝ)|=(1851954189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s0_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2295194143/5000000000 : ℝ)*x 0 + (-772644921/5000000000 : ℝ)*x 1 + (-6420593237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2295194143/5000000000 : ℝ)^33 ≤ (17890037142469/50000000000000 : ℝ)^25 := by
    have hnat : (2295194143 : ℕ)^33*50000000000000^25 ≤ 17890037142469^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295194143 5000000000 17890037142469 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (772644921/5000000000 : ℝ)^33 ≤ (531340782537/6250000000000 : ℝ)^25 := by
    have hnat : (772644921 : ℕ)^33*6250000000000^25 ≤ 531340782537^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772644921 5000000000 531340782537 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6420593237/10000000000 : ℝ)^33 ≤ (55718473182499/100000000000000 : ℝ)^25 := by
    have hnat : (6420593237 : ℕ)^33*100000000000000^25 ≤ 55718473182499^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6420593237 10000000000 55718473182499 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2295194143/5000000000 : ℝ), (-772644921/5000000000 : ℝ), (-6420593237/10000000000 : ℝ)] ![(17890037142469/50000000000000 : ℝ), (531340782537/6250000000000 : ℝ), (55718473182499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2295194143/5000000000 : ℝ)|^33 ≤ (17890037142469/50000000000000 : ℝ)^25
        have hw : |(2295194143/5000000000 : ℝ)|=(2295194143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-772644921/5000000000 : ℝ)|^33 ≤ (531340782537/6250000000000 : ℝ)^25
        have hw : |(-772644921/5000000000 : ℝ)|=(772644921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6420593237/10000000000 : ℝ)|^33 ≤ (55718473182499/100000000000000 : ℝ)^25
        have hw : |(-6420593237/10000000000 : ℝ)|=(6420593237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s0_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-760786577/5000000000 : ℝ)*x 0 + (-4823651883/10000000000 : ℝ)*x 1 + (-388963549/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (760786577/5000000000 : ℝ)^33 ≤ (4164823002269/50000000000000 : ℝ)^25 := by
    have hnat : (760786577 : ℕ)^33*50000000000000^25 ≤ 4164823002269^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760786577 5000000000 4164823002269 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4823651883/10000000000 : ℝ)^33 ≤ (763987512317/2000000000000 : ℝ)^25 := by
    have hnat : (4823651883 : ℕ)^33*2000000000000^25 ≤ 763987512317^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4823651883 10000000000 763987512317 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (388963549/625000000 : ℝ)^33 ≤ (53470978370267/100000000000000 : ℝ)^25 := by
    have hnat : (388963549 : ℕ)^33*100000000000000^25 ≤ 53470978370267^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388963549 625000000 53470978370267 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-760786577/5000000000 : ℝ), (-4823651883/10000000000 : ℝ), (-388963549/625000000 : ℝ)] ![(4164823002269/50000000000000 : ℝ), (763987512317/2000000000000 : ℝ), (53470978370267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-760786577/5000000000 : ℝ)|^33 ≤ (4164823002269/50000000000000 : ℝ)^25
        have hw : |(-760786577/5000000000 : ℝ)|=(760786577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4823651883/10000000000 : ℝ)|^33 ≤ (763987512317/2000000000000 : ℝ)^25
        have hw : |(-4823651883/10000000000 : ℝ)|=(4823651883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-388963549/625000000 : ℝ)|^33 ≤ (53470978370267/100000000000000 : ℝ)^25
        have hw : |(-388963549/625000000 : ℝ)|=(388963549/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s0_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6891617727/10000000000 : ℝ)*x 0 + (4047691549/10000000000 : ℝ)*x 1 + (-386913653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6891617727/10000000000 : ℝ)^33 ≤ (244705622571/400000000000 : ℝ)^25 := by
    have hnat : (6891617727 : ℕ)^33*400000000000^25 ≤ 244705622571^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6891617727 10000000000 244705622571 400000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4047691549/10000000000 : ℝ)^33 ≤ (6060992923017/20000000000000 : ℝ)^25 := by
    have hnat : (4047691549 : ℕ)^33*20000000000000^25 ≤ 6060992923017^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4047691549 10000000000 6060992923017 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (386913653/2500000000 : ℝ)^33 ≤ (4259314859047/50000000000000 : ℝ)^25 := by
    have hnat : (386913653 : ℕ)^33*50000000000000^25 ≤ 4259314859047^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386913653 2500000000 4259314859047 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6891617727/10000000000 : ℝ), (4047691549/10000000000 : ℝ), (-386913653/2500000000 : ℝ)] ![(244705622571/400000000000 : ℝ), (6060992923017/20000000000000 : ℝ), (4259314859047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6891617727/10000000000 : ℝ)|^33 ≤ (244705622571/400000000000 : ℝ)^25
        have hw : |(6891617727/10000000000 : ℝ)|=(6891617727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4047691549/10000000000 : ℝ)|^33 ≤ (6060992923017/20000000000000 : ℝ)^25
        have hw : |(4047691549/10000000000 : ℝ)|=(4047691549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-386913653/2500000000 : ℝ)|^33 ≤ (4259314859047/50000000000000 : ℝ)^25
        have hw : |(-386913653/2500000000 : ℝ)|=(386913653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s0_23 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3483197959/10000000000 : ℝ)*x 0 + (-5250143281/10000000000 : ℝ)*x 1 + (532563459/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3483197959/10000000000 : ℝ)^33 ≤ (24854851203639/100000000000000 : ℝ)^25 := by
    have hnat : (3483197959 : ℕ)^33*100000000000000^25 ≤ 24854851203639^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3483197959 10000000000 24854851203639 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5250143281/10000000000 : ℝ)^33 ≤ (42719476860331/100000000000000 : ℝ)^25 := by
    have hnat : (5250143281 : ℕ)^33*100000000000000^25 ≤ 42719476860331^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250143281 10000000000 42719476860331 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (532563459/1250000000 : ℝ)^33 ≤ (6485134383881/20000000000000 : ℝ)^25 := by
    have hnat : (532563459 : ℕ)^33*20000000000000^25 ≤ 6485134383881^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532563459 1250000000 6485134383881 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3483197959/10000000000 : ℝ), (-5250143281/10000000000 : ℝ), (532563459/1250000000 : ℝ)] ![(24854851203639/100000000000000 : ℝ), (42719476860331/100000000000000 : ℝ), (6485134383881/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3483197959/10000000000 : ℝ)|^33 ≤ (24854851203639/100000000000000 : ℝ)^25
        have hw : |(3483197959/10000000000 : ℝ)|=(3483197959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5250143281/10000000000 : ℝ)|^33 ≤ (42719476860331/100000000000000 : ℝ)^25
        have hw : |(-5250143281/10000000000 : ℝ)|=(5250143281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(532563459/1250000000 : ℝ)|^33 ≤ (6485134383881/20000000000000 : ℝ)^25
        have hw : |(532563459/1250000000 : ℝ)|=(532563459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s0_27 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6191288461/10000000000 : ℝ)*x 0 + (-1722406549/10000000000 : ℝ)*x 1 + (-4716416573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6191288461/10000000000 : ℝ)^33 ≤ (53106902466291/100000000000000 : ℝ)^25 := by
    have hnat : (6191288461 : ℕ)^33*100000000000000^25 ≤ 53106902466291^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6191288461 10000000000 53106902466291 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1722406549/10000000000 : ℝ)^33 ≤ (2452669839427/25000000000000 : ℝ)^25 := by
    have hnat : (1722406549 : ℕ)^33*25000000000000^25 ≤ 2452669839427^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722406549 10000000000 2452669839427 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4716416573/10000000000 : ℝ)^33 ≤ (18541209080301/50000000000000 : ℝ)^25 := by
    have hnat : (4716416573 : ℕ)^33*50000000000000^25 ≤ 18541209080301^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4716416573 10000000000 18541209080301 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6191288461/10000000000 : ℝ), (-1722406549/10000000000 : ℝ), (-4716416573/10000000000 : ℝ)] ![(53106902466291/100000000000000 : ℝ), (2452669839427/25000000000000 : ℝ), (18541209080301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6191288461/10000000000 : ℝ)|^33 ≤ (53106902466291/100000000000000 : ℝ)^25
        have hw : |(6191288461/10000000000 : ℝ)|=(6191288461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1722406549/10000000000 : ℝ)|^33 ≤ (2452669839427/25000000000000 : ℝ)^25
        have hw : |(-1722406549/10000000000 : ℝ)|=(1722406549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4716416573/10000000000 : ℝ)|^33 ≤ (18541209080301/50000000000000 : ℝ)^25
        have hw : |(-4716416573/10000000000 : ℝ)|=(4716416573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s1_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3497542647/10000000000 : ℝ)*x 0 + (-84208491/200000000 : ℝ)*x 1 + (-2642138319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3497542647/10000000000 : ℝ)^33 ≤ (24990053433053/100000000000000 : ℝ)^25 := by
    have hnat : (3497542647 : ℕ)^33*100000000000000^25 ≤ 24990053433053^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3497542647 10000000000 24990053433053 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84208491/200000000 : ℝ)^33 ≤ (31923476020731/100000000000000 : ℝ)^25 := by
    have hnat : (84208491 : ℕ)^33*100000000000000^25 ≤ 31923476020731^25*200000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84208491 200000000 31923476020731 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2642138319/5000000000 : ℝ)^33 ≤ (43086470527893/100000000000000 : ℝ)^25 := by
    have hnat : (2642138319 : ℕ)^33*100000000000000^25 ≤ 43086470527893^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642138319 5000000000 43086470527893 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3497542647/10000000000 : ℝ), (-84208491/200000000 : ℝ), (-2642138319/5000000000 : ℝ)] ![(24990053433053/100000000000000 : ℝ), (31923476020731/100000000000000 : ℝ), (43086470527893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3497542647/10000000000 : ℝ)|^33 ≤ (24990053433053/100000000000000 : ℝ)^25
        have hw : |(-3497542647/10000000000 : ℝ)|=(3497542647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84208491/200000000 : ℝ)|^33 ≤ (31923476020731/100000000000000 : ℝ)^25
        have hw : |(-84208491/200000000 : ℝ)|=(84208491/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2642138319/5000000000 : ℝ)|^33 ≤ (43086470527893/100000000000000 : ℝ)^25
        have hw : |(-2642138319/5000000000 : ℝ)|=(2642138319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s1_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5281580681/10000000000 : ℝ)*x 0 + (421433279/1000000000 : ℝ)*x 1 + (-1748235509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281580681/10000000000 : ℝ)^33 ≤ (344459652649/800000000000 : ℝ)^25 := by
    have hnat : (5281580681 : ℕ)^33*800000000000^25 ≤ 344459652649^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281580681 10000000000 344459652649 800000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421433279/1000000000 : ℝ)^33 ≤ (15981298239011/50000000000000 : ℝ)^25 := by
    have hnat : (421433279 : ℕ)^33*50000000000000^25 ≤ 15981298239011^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421433279 1000000000 15981298239011 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1748235509/5000000000 : ℝ)^33 ≤ (3122493365229/12500000000000 : ℝ)^25 := by
    have hnat : (1748235509 : ℕ)^33*12500000000000^25 ≤ 3122493365229^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748235509 5000000000 3122493365229 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281580681/10000000000 : ℝ), (421433279/1000000000 : ℝ), (-1748235509/5000000000 : ℝ)] ![(344459652649/800000000000 : ℝ), (15981298239011/50000000000000 : ℝ), (3122493365229/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281580681/10000000000 : ℝ)|^33 ≤ (344459652649/800000000000 : ℝ)^25
        have hw : |(5281580681/10000000000 : ℝ)|=(5281580681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(421433279/1000000000 : ℝ)|^33 ≤ (15981298239011/50000000000000 : ℝ)^25
        have hw : |(421433279/1000000000 : ℝ)|=(421433279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1748235509/5000000000 : ℝ)|^33 ≤ (3122493365229/12500000000000 : ℝ)^25
        have hw : |(-1748235509/5000000000 : ℝ)|=(1748235509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s1_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2035054763/5000000000 : ℝ)*x 0 + (-4899694099/10000000000 : ℝ)*x 1 + (406508913/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2035054763/5000000000 : ℝ)^33 ≤ (1907919577049/6250000000000 : ℝ)^25 := by
    have hnat : (2035054763 : ℕ)^33*6250000000000^25 ≤ 1907919577049^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035054763 5000000000 1907919577049 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4899694099/10000000000 : ℝ)^33 ≤ (1559850682861/4000000000000 : ℝ)^25 := by
    have hnat : (4899694099 : ℕ)^33*4000000000000^25 ≤ 1559850682861^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4899694099 10000000000 1559850682861 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (406508913/1000000000 : ℝ)^33 ≤ (30477019672419/100000000000000 : ℝ)^25 := by
    have hnat : (406508913 : ℕ)^33*100000000000000^25 ≤ 30477019672419^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406508913 1000000000 30477019672419 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2035054763/5000000000 : ℝ), (-4899694099/10000000000 : ℝ), (406508913/1000000000 : ℝ)] ![(1907919577049/6250000000000 : ℝ), (1559850682861/4000000000000 : ℝ), (30477019672419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2035054763/5000000000 : ℝ)|^33 ≤ (1907919577049/6250000000000 : ℝ)^25
        have hw : |(2035054763/5000000000 : ℝ)|=(2035054763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4899694099/10000000000 : ℝ)|^33 ≤ (1559850682861/4000000000000 : ℝ)^25
        have hw : |(-4899694099/10000000000 : ℝ)|=(4899694099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(406508913/1000000000 : ℝ)|^33 ≤ (30477019672419/100000000000000 : ℝ)^25
        have hw : |(406508913/1000000000 : ℝ)|=(406508913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303070_s1_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4654402327/10000000000 : ℝ)*x 0 + (-3713888233/10000000000 : ℝ)*x 1 + (-4661100703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4654402327/10000000000 : ℝ)^33 ≤ (7288033687757/20000000000000 : ℝ)^25 := by
    have hnat : (4654402327 : ℕ)^33*20000000000000^25 ≤ 7288033687757^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4654402327 10000000000 7288033687757 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3713888233/10000000000 : ℝ)^33 ≤ (27050422661881/100000000000000 : ℝ)^25 := by
    have hnat : (3713888233 : ℕ)^33*100000000000000^25 ≤ 27050422661881^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3713888233 10000000000 27050422661881 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4661100703/10000000000 : ℝ)^33 ≤ (36509408886317/100000000000000 : ℝ)^25 := by
    have hnat : (4661100703 : ℕ)^33*100000000000000^25 ≤ 36509408886317^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4661100703 10000000000 36509408886317 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4654402327/10000000000 : ℝ), (-3713888233/10000000000 : ℝ), (-4661100703/10000000000 : ℝ)] ![(7288033687757/20000000000000 : ℝ), (27050422661881/100000000000000 : ℝ), (36509408886317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4654402327/10000000000 : ℝ)|^33 ≤ (7288033687757/20000000000000 : ℝ)^25
        have hw : |(4654402327/10000000000 : ℝ)|=(4654402327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3713888233/10000000000 : ℝ)|^33 ≤ (27050422661881/100000000000000 : ℝ)^25
        have hw : |(-3713888233/10000000000 : ℝ)|=(3713888233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4661100703/10000000000 : ℝ)|^33 ≤ (36509408886317/100000000000000 : ℝ)^25
        have hw : |(-4661100703/10000000000 : ℝ)|=(4661100703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303070 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2130921273/10000000000 : ℝ)*X 0 0+(-276934483/625000000 : ℝ)*X 0 1+(-3084653823/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((625794533/1000000000 : ℝ)*X 1 0+(4414742349/10000000000 : ℝ)*X 1 1+(-2025719067/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1042461011/2000000000 : ℝ)*X 0 0+(-546846571/2500000000 : ℝ)*X 0 1+(-2695420611/5000000000 : ℝ)*X 0 2+(1042461011/2000000000 : ℝ)*X 1 0+(-546846571/2500000000 : ℝ)*X 1 1+(-2695420611/5000000000 : ℝ)*X 1 2+(1042461011/2000000000 : ℝ)*X 2 0+(-546846571/2500000000 : ℝ)*X 2 1+(-2695420611/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1720238459/10000000000 : ℝ)*X 0 0+(-2439857923/5000000000 : ℝ)*X 0 1+(-3020820461/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3110364817/5000000000 : ℝ)*X 1 0+(2439857923/5000000000 : ℝ)*X 1 1+(-1443896107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((256190957/625000000 : ℝ)*X 2 0+(-4326376989/10000000000 : ℝ)*X 2 1+(2310596117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1283013427/2500000000 : ℝ)*X 0 0+(-135178079/1000000000 : ℝ)*X 0 1+(-3020820461/5000000000 : ℝ)*X 0 2+(1283013427/2500000000 : ℝ)*X 1 0+(-135178079/1000000000 : ℝ)*X 1 1+(-3020820461/5000000000 : ℝ)*X 1 2+(1283013427/2500000000 : ℝ)*X 2 0+(-135178079/1000000000 : ℝ)*X 2 1+(-3020820461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-456860723/2500000000 : ℝ)*X 0 0+(-1006064241/2500000000 : ℝ)*X 0 1+(-1683115367/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((823218793/1250000000 : ℝ)*X 1 0+(2271726851/5000000000 : ℝ)*X 1 1+(-336461851/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4280301941/10000000000 : ℝ)*X 2 0+(-1258674677/2500000000 : ℝ)*X 2 1+(1851954189/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2295194143/5000000000 : ℝ)*X 0 0+(-772644921/5000000000 : ℝ)*X 0 1+(-6420593237/10000000000 : ℝ)*X 0 2+(2295194143/5000000000 : ℝ)*X 1 0+(-772644921/5000000000 : ℝ)*X 1 1+(-6420593237/10000000000 : ℝ)*X 1 2+(2295194143/5000000000 : ℝ)*X 2 0+(-772644921/5000000000 : ℝ)*X 2 1+(-6420593237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-760786577/5000000000 : ℝ)*X 0 0+(-4823651883/10000000000 : ℝ)*X 0 1+(-388963549/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((6891617727/10000000000 : ℝ)*X 1 0+(4047691549/10000000000 : ℝ)*X 1 1+(-386913653/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3483197959/10000000000 : ℝ)*X 2 0+(-5250143281/10000000000 : ℝ)*X 2 1+(532563459/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((6191288461/10000000000 : ℝ)*X 0 0+(-1722406549/10000000000 : ℝ)*X 0 1+(-4716416573/10000000000 : ℝ)*X 0 2+(6191288461/10000000000 : ℝ)*X 1 0+(-1722406549/10000000000 : ℝ)*X 1 1+(-4716416573/10000000000 : ℝ)*X 1 2+(6191288461/10000000000 : ℝ)*X 2 0+(-1722406549/10000000000 : ℝ)*X 2 1+(-4716416573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((4861/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4861/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (169767574109794629/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (275687005751/1000000000000 : ℝ)*(base1) + (24770770617/100000000000 : ℝ)*(base3) + (2052755977689/1000000000000 : ℝ)*(base39) + (251187/31250000000 : ℝ)*(base49) + (157133659317/200000000000 : ℝ)*(base59) + (6279534331663/1000000000000 : ℝ)*(major_s0_0) + (6279534331663/1000000000000 : ℝ)*(major_s0_1) + (6279534331663/1000000000000 : ℝ)*(major_s0_2) + (19775847/1000000000000 : ℝ)*(sp_s0_1) + (4329707403687/500000000000 : ℝ)*(sp_s0_7) + (539505236353/62500000000 : ℝ)*(sp_s0_8) + (335375834053/40000000000 : ℝ)*(sp_s0_9) + (3651272441159/1000000000000 : ℝ)*(sp_s0_13) + (334024851/500000000000 : ℝ)*(sp_s0_21) + (104366678827/25000000000 : ℝ)*(f.failure) + (335375834053/40000000000 : ℝ)*(f.sum) + (4756977174666639/10000000000000000000000000000 : ℝ)*base63 + (322120531278447/1250000000000000000000000000 : ℝ)*base65 + (389585290221157/2000000000000000000000000000 : ℝ)*base67 + (89034085778843/2000000000000000000000000000 : ℝ)*base69 + (363872487878209/10000000000000000000000000000 : ℝ)*base70 + (158852381653447/1250000000000000000000000000 : ℝ)*base73 + (342331582221553/1250000000000000000000000000 : ℝ)*base75 + (253807075578843/2000000000000000000000000000 : ℝ)*base77 + (60650575333361/10000000000000000000000000000 : ℝ)*base79 + (1/15625000000000 : ℝ)*base86 + (1/15625000000000 : ℝ)*base88 + (1/15625000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-287/1000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-287/1000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2152836884992495819287/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (382460778563/200000000000 : ℝ)*(base39) + (277621524797/200000000000 : ℝ)*(base59) + (1769780319591/250000000000 : ℝ)*(major_s0_0) + (1769780319591/250000000000 : ℝ)*(major_s0_1) + (1769780319591/250000000000 : ℝ)*(major_s0_2) + (47954131/500000000000 : ℝ)*(sp_s0_0) + (96354279/1000000000000 : ℝ)*(sp_s0_1) + (13551407/250000000000 : ℝ)*(sp_s0_9) + (45578101/1000000000000 : ℝ)*(sp_s0_13) + (9451905332991/1000000000000 : ℝ)*(sp_s0_14) + (590738519741/62500000000 : ℝ)*(sp_s0_15) + (15123115257/1600000000 : ℝ)*(sp_s0_16) + (4706191144651/1000000000000 : ℝ)*(sp_s0_20) + (44285559/500000000000 : ℝ)*(sp_s0_22) + (73534948793/15625000000 : ℝ)*(f.failure) + (9452001241253/1000000000000 : ℝ)*(f.sum) + (597422708582823/2500000000000000000000000000 : ℝ)*base63 + (42685706512679/312500000000000000000000000 : ℝ)*base65 + (71719740113149/500000000000000000000000000 : ℝ)*base67 + (94419768363149/500000000000000000000000000 : ℝ)*base68 + (877233467464313/2500000000000000000000000000 : ℝ)*base70 + (57903195049821/312500000000000000000000000 : ℝ)*base72 + (26168824106429/312500000000000000000000000 : ℝ)*base74 + (104591158536851/500000000000000000000000000 : ℝ)*base77 + (1417668705832823/2500000000000000000000000000 : ℝ)*base78 + (69/156250000000000 : ℝ)*base86 + (69/156250000000000 : ℝ)*base88 + (69/156250000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13581/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-13581/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10473589171337863444227/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85961411439/40000000000 : ℝ)*(base39) + (211843/100000000000 : ℝ)*(base49) + (802057785063/1000000000000 : ℝ)*(base59) + (3395191354621/500000000000 : ℝ)*(major_s0_0) + (3395191354621/500000000000 : ℝ)*(major_s0_1) + (3395191354621/500000000000 : ℝ)*(major_s0_2) + (39818599/1000000000000 : ℝ)*(sp_s0_6) + (302791349/1000000000000 : ℝ)*(sp_s0_7) + (6192369/250000000000 : ℝ)*(sp_s0_15) + (48371571/1000000000000 : ℝ)*(sp_s0_16) + (90661780171/10000000000 : ℝ)*(sp_s0_21) + (9066456038973/1000000000000 : ℝ)*(sp_s0_22) + (4533216218439/500000000000 : ℝ)*(sp_s0_23) + (180569679939/40000000000 : ℝ)*(sp_s0_27) + (2257140908537/500000000000 : ℝ)*(f.failure) + (9066480808449/1000000000000 : ℝ)*(f.sum) + (1087125144375587/5000000000000000000000000000 : ℝ)*base62 + (193128737660751/625000000000000000000000000 : ℝ)*base64 + (328584853832319/1000000000000000000000000000 : ℝ)*base67 + (365383324232319/1000000000000000000000000000 : ℝ)*base68 + (2126229446447603/5000000000000000000000000000 : ℝ)*base70 + (366466480339249/625000000000000000000000000 : ℝ)*base73 + (177330124089249/625000000000000000000000000 : ℝ)*base74 + (165601166967681/1000000000000000000000000000 : ℝ)*base77 + (2477612129375587/5000000000000000000000000000 : ℝ)*base79 + (1777/2500000000000000 : ℝ)*base87 + (1777/2500000000000000 : ℝ)*base89 + (1777/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (4861/25000 : ℝ) ^ (131/32 : ℝ) ≤ (122593120783420597/100000000000000000000 : ℝ) := by
    have hpowers : (4861/25000 : ℝ)^131 ≤ (122593120783420597/100000000000000000000 : ℝ)^32 := by
      have hnat : (4861 : ℕ)^131*100000000000000000000^32 ≤ 122593120783420597^32*25000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4861 25000 122593120783420597 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4861/25000 : ℝ)) (X := (122593120783420597/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100122593120783420597/100000000000000000000 : ℝ) ≤ (5001496627447293/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (100122593120783420597/100000000000000000000 : ℝ)^32 ≤ (5001496627447293/5000000000000000 : ℝ)^131 := by
      have hnat : (100122593120783420597 : ℕ)^32*5000000000000000^131 ≤ 5001496627447293^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100122593120783420597 100000000000000000000 5001496627447293 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001496627447293/5000000000000000 : ℝ)) (X := (100122593120783420597/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50122593120783420597/50000000000000000000 : ℝ) ≤ (5002991870656329/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50122593120783420597/50000000000000000000 : ℝ)^32 ≤ (5002991870656329/5000000000000000 : ℝ)^131 := by
      have hnat : (50122593120783420597 : ℕ)^32*5000000000000000^131 ≤ 5002991870656329^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50122593120783420597 50000000000000000000 5002991870656329 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002991870656329/5000000000000000 : ℝ)) (X := (50122593120783420597/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1496627447293/972200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(373810802259/243050000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (4861/25000 : ℝ)) (alpha := (1496627447293/972200000000000 : ℝ)) (beta := (373810802259/243050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (4861/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1496627447293/972200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(373810802259/243050000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (287/1000 : ℝ) ^ (131/32 : ℝ) ≤ (9430268121324937/1562500000000000000 : ℝ) := by
    have hpowers : (287/1000 : ℝ)^131 ≤ (9430268121324937/1562500000000000000 : ℝ)^32 := by
      have hnat : (287 : ℕ)^131*1562500000000000000^32 ≤ 9430268121324937^32*1000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        287 1000 9430268121324937 1562500000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (287/1000 : ℝ)) (X := (9430268121324937/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (1571930268121324937/1562500000000000000 : ℝ) ≤ (312959668404519/312500000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (1571930268121324937/1562500000000000000 : ℝ)^32 ≤ (312959668404519/312500000000000 : ℝ)^131 := by
      have hnat : (1571930268121324937 : ℕ)^32*312500000000000^131 ≤ 312959668404519^131*1562500000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1571930268121324937 1562500000000000000 312959668404519 312500000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312959668404519/312500000000000 : ℝ)) (X := (1571930268121324937/1562500000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (790680268121324937/781250000000000000 : ℝ) ≤ (10029352240039251/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (790680268121324937/781250000000000000 : ℝ)^32 ≤ (10029352240039251/10000000000000000 : ℝ)^131 := by
      have hnat : (790680268121324937 : ℕ)^32*10000000000000000^131 ≤ 10029352240039251^131*781250000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        790680268121324937 781250000000000000 10029352240039251 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10029352240039251/10000000000000000 : ℝ)) (X := (790680268121324937/781250000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(459668404519/89687500000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(14642851094643/2870000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (287/1000 : ℝ)) (alpha := (459668404519/89687500000000 : ℝ)) (beta := (14642851094643/2870000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (287/1000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(459668404519/89687500000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(14642851094643/2870000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13581/50000 : ℝ) ^ (131/32 : ℝ) ≤ (240852355182625291/50000000000000000000 : ℝ) := by
    have hpowers : (13581/50000 : ℝ)^131 ≤ (240852355182625291/50000000000000000000 : ℝ)^32 := by
      have hnat : (13581 : ℕ)^131*50000000000000000000^32 ≤ 240852355182625291^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13581 50000 240852355182625291 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13581/50000 : ℝ)) (X := (240852355182625291/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50240852355182625291/50000000000000000000 : ℝ) ≤ (25029363687559/25000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50240852355182625291/50000000000000000000 : ℝ)^32 ≤ (25029363687559/25000000000000 : ℝ)^131 := by
      have hnat : (50240852355182625291 : ℕ)^32*25000000000000^131 ≤ 25029363687559^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50240852355182625291 50000000000000000000 25029363687559 25000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25029363687559/25000000000000 : ℝ)) (X := (50240852355182625291/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25240852355182625291/25000000000000000000 : ℝ) ≤ (10023448473989371/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (25240852355182625291/25000000000000000000 : ℝ)^32 ≤ (10023448473989371/10000000000000000 : ℝ)^131 := by
      have hnat : (25240852355182625291 : ℕ)^32*10000000000000000^131 ≤ 10023448473989371^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25240852355182625291 25000000000000000000 10023448473989371 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10023448473989371/10000000000000000 : ℝ)) (X := (25240852355182625291/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(3262631951/754500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1300333218419/301800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (13581/50000 : ℝ)) (alpha := (3262631951/754500000000 : ℝ)) (beta := (1300333218419/301800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (13581/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(3262631951/754500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1300333218419/301800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3497542647/10000000000 : ℝ)*X 0 0+(-84208491/200000000 : ℝ)*X 0 1+(-2642138319/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5281580681/10000000000 : ℝ)*X 1 0+(421433279/1000000000 : ℝ)*X 1 1+(-1748235509/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2035054763/5000000000 : ℝ)*X 2 0+(-4899694099/10000000000 : ℝ)*X 2 1+(406508913/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4654402327/10000000000 : ℝ)*X 0 0+(-3713888233/10000000000 : ℝ)*X 0 1+(-4661100703/10000000000 : ℝ)*X 0 2+(4654402327/10000000000 : ℝ)*X 1 0+(-3713888233/10000000000 : ℝ)*X 1 1+(-4661100703/10000000000 : ℝ)*X 1 2+(4654402327/10000000000 : ℝ)*X 2 0+(-3713888233/10000000000 : ℝ)*X 2 1+(-4661100703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303070_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15063/2500 : ℝ) < ((-7521/5000 : ℝ)*P 0+(-7521/5000 : ℝ)*P 1+(-7521/5000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15063/2500 : ℝ) < (-416638462872862332934693285584337/70173882100000000000000000000000 : ℝ) := by norm_num
    linear_combination (718687/500000000000 : ℝ)*(base1) + (197957/100000000000 : ℝ)*(base22) + (3719/6250000000 : ℝ)*(base25) + (252303688889/500000000000 : ℝ)*(base39) + (8040450563/50000000000 : ℝ)*(base40) + (225581766153/1000000000000 : ℝ)*(base49) + (709099/1000000000000 : ℝ)*(base54) + (146527559409/500000000000 : ℝ)*(base59) + (7521/5000 : ℝ)*(major_s1_0) + (7521/5000 : ℝ)*(major_s1_1) + (1504199290901/1000000000000 : ℝ)*(major_s1_2) + (494769508021/250000000000 : ℝ)*(sp_s1_0) + (197907659471/100000000000 : ℝ)*(sp_s1_1) + (1979073311/1000000000 : ℝ)*(sp_s1_2) + (999997853527/1000000000000 : ℝ)*(sp_s1_6) + (197907659471/100000000000 : ℝ)*(f.sum) + (1823977298000317/4330830000000000000000000000 : ℝ)*base63 + (5959808166101/301800000000000000000000000 : ℝ)*base64 + (438638341951/2870000000000000000000000 : ℝ)*base67 + (328299495031/15090000000000000000000000 : ℝ)*base68 + (271010239784854961/1467049800000000000000000000000 : ℝ)*base70 + (1001679047279/48610000000000000000000000 : ℝ)*base72 + (1626585464577/2870000000000000000000000 : ℝ)*base75 + (35584460558949/48610000000000000000000000 : ℝ)*base76 + (3877510645439467/13951070000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p003_b030 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 71)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=70 := by omega
  rcases hc with rfl
  · exact collision_c303070 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 71)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b030 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

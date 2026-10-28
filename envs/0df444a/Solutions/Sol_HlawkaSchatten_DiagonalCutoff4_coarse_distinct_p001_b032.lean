-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b032
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:23:06.233504+00:00
-- url     : https://prove2.me/submissions/f2fdd87e-6959-4d5e-b3c2-1fe339ae7d5c

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
theorem collision_support_c301070_s0_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-216670597/1000000000 : ℝ)*x 0 + (-224045069/500000000 : ℝ)*x 1 + (-1228241013/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216670597/1000000000 : ℝ)^65 ≤ (1643721946483/12500000000000 : ℝ)^49 := by
    have hnat : (216670597 : ℕ)^65*12500000000000^49 ≤ 1643721946483^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216670597 1000000000 1643721946483 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224045069/500000000 : ℝ)^65 ≤ (34476685846779/100000000000000 : ℝ)^49 := by
    have hnat : (224045069 : ℕ)^65*100000000000000^49 ≤ 34476685846779^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224045069 500000000 34476685846779 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1228241013/2000000000 : ℝ)^65 ≤ (26186769286117/50000000000000 : ℝ)^49 := by
    have hnat : (1228241013 : ℕ)^65*50000000000000^49 ≤ 26186769286117^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1228241013 2000000000 26186769286117 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-216670597/1000000000 : ℝ), (-224045069/500000000 : ℝ), (-1228241013/2000000000 : ℝ)] ![(1643721946483/12500000000000 : ℝ), (34476685846779/100000000000000 : ℝ), (26186769286117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-216670597/1000000000 : ℝ)|^65 ≤ (1643721946483/12500000000000 : ℝ)^49
        have hw : |(-216670597/1000000000 : ℝ)|=(216670597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-224045069/500000000 : ℝ)|^65 ≤ (34476685846779/100000000000000 : ℝ)^49
        have hw : |(-224045069/500000000 : ℝ)|=(224045069/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1228241013/2000000000 : ℝ)|^65 ≤ (26186769286117/50000000000000 : ℝ)^49
        have hw : |(-1228241013/2000000000 : ℝ)|=(1228241013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s0_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (251943969/400000000 : ℝ)*x 0 + (4450258421/10000000000 : ℝ)*x 1 + (-1980762097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (251943969/400000000 : ℝ)^65 ≤ (54161537934399/100000000000000 : ℝ)^49 := by
    have hnat : (251943969 : ℕ)^65*100000000000000^49 ≤ 54161537934399^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251943969 400000000 54161537934399 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4450258421/10000000000 : ℝ)^65 ≤ (273314222501/800000000000 : ℝ)^49 := by
    have hnat : (4450258421 : ℕ)^65*800000000000^49 ≤ 273314222501^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4450258421 10000000000 273314222501 800000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1980762097/10000000000 : ℝ)^65 ≤ (1167418423737/10000000000000 : ℝ)^49 := by
    have hnat : (1980762097 : ℕ)^65*10000000000000^49 ≤ 1167418423737^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980762097 10000000000 1167418423737 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(251943969/400000000 : ℝ), (4450258421/10000000000 : ℝ), (-1980762097/10000000000 : ℝ)] ![(54161537934399/100000000000000 : ℝ), (273314222501/800000000000 : ℝ), (1167418423737/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(251943969/400000000 : ℝ)|^65 ≤ (54161537934399/100000000000000 : ℝ)^49
        have hw : |(251943969/400000000 : ℝ)|=(251943969/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4450258421/10000000000 : ℝ)|^65 ≤ (273314222501/800000000000 : ℝ)^49
        have hw : |(4450258421/10000000000 : ℝ)|=(4450258421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1980762097/10000000000 : ℝ)|^65 ≤ (1167418423737/10000000000000 : ℝ)^49
        have hw : |(-1980762097/10000000000 : ℝ)|=(1980762097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s0_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5178252971/10000000000 : ℝ)*x 0 + (-108132531/500000000 : ℝ)*x 1 + (-2743923837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5178252971/10000000000 : ℝ)^65 ≤ (10442280561333/25000000000000 : ℝ)^49 := by
    have hnat : (5178252971 : ℕ)^65*25000000000000^49 ≤ 10442280561333^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178252971 10000000000 10442280561333 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108132531/500000000 : ℝ)^65 ≤ (6558568498301/50000000000000 : ℝ)^49 := by
    have hnat : (108132531 : ℕ)^65*50000000000000^49 ≤ 6558568498301^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108132531 500000000 6558568498301 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743923837/5000000000 : ℝ)^65 ≤ (2255687036991/5000000000000 : ℝ)^49 := by
    have hnat : (2743923837 : ℕ)^65*5000000000000^49 ≤ 2255687036991^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743923837 5000000000 2255687036991 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5178252971/10000000000 : ℝ), (-108132531/500000000 : ℝ), (-2743923837/5000000000 : ℝ)] ![(10442280561333/25000000000000 : ℝ), (6558568498301/50000000000000 : ℝ), (2255687036991/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5178252971/10000000000 : ℝ)|^65 ≤ (10442280561333/25000000000000 : ℝ)^49
        have hw : |(5178252971/10000000000 : ℝ)|=(5178252971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-108132531/500000000 : ℝ)|^65 ≤ (6558568498301/50000000000000 : ℝ)^49
        have hw : |(-108132531/500000000 : ℝ)|=(108132531/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2743923837/5000000000 : ℝ)|^65 ≤ (2255687036991/5000000000000 : ℝ)^49
        have hw : |(-2743923837/5000000000 : ℝ)|=(2743923837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s0_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-77327491/500000000 : ℝ)*x 0 + (-1241588747/2500000000 : ℝ)*x 1 + (-1222967173/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77327491/500000000 : ℝ)^65 ≤ (8407491125199/100000000000000 : ℝ)^49 := by
    have hnat : (77327491 : ℕ)^65*100000000000000^49 ≤ 8407491125199^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77327491 500000000 8407491125199 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1241588747/2500000000 : ℝ)^65 ≤ (316136593619/800000000000 : ℝ)^49 := by
    have hnat : (1241588747 : ℕ)^65*800000000000^49 ≤ 316136593619^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1241588747 2500000000 316136593619 800000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1222967173/2000000000 : ℝ)^65 ≤ (52075434647331/100000000000000 : ℝ)^49 := by
    have hnat : (1222967173 : ℕ)^65*100000000000000^49 ≤ 52075434647331^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222967173 2000000000 52075434647331 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-77327491/500000000 : ℝ), (-1241588747/2500000000 : ℝ), (-1222967173/2000000000 : ℝ)] ![(8407491125199/100000000000000 : ℝ), (316136593619/800000000000 : ℝ), (52075434647331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-77327491/500000000 : ℝ)|^65 ≤ (8407491125199/100000000000000 : ℝ)^49
        have hw : |(-77327491/500000000 : ℝ)|=(77327491/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1241588747/2500000000 : ℝ)|^65 ≤ (316136593619/800000000000 : ℝ)^49
        have hw : |(-1241588747/2500000000 : ℝ)|=(1241588747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1222967173/2000000000 : ℝ)|^65 ≤ (52075434647331/100000000000000 : ℝ)^49
        have hw : |(-1222967173/2000000000 : ℝ)|=(1222967173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s0_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (625479227/1000000000 : ℝ)*x 0 + (1241588747/2500000000 : ℝ)*x 1 + (-1320923497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (625479227/1000000000 : ℝ)^65 ≤ (26831204265699/50000000000000 : ℝ)^49 := by
    have hnat : (625479227 : ℕ)^65*50000000000000^49 ≤ 26831204265699^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625479227 1000000000 26831204265699 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1241588747/2500000000 : ℝ)^65 ≤ (316136593619/800000000000 : ℝ)^49 := by
    have hnat : (1241588747 : ℕ)^65*800000000000^49 ≤ 316136593619^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1241588747 2500000000 316136593619 800000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320923497/10000000000 : ℝ)^65 ≤ (6820517248079/100000000000000 : ℝ)^49 := by
    have hnat : (1320923497 : ℕ)^65*100000000000000^49 ≤ 6820517248079^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320923497 10000000000 6820517248079 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(625479227/1000000000 : ℝ), (1241588747/2500000000 : ℝ), (-1320923497/10000000000 : ℝ)] ![(26831204265699/50000000000000 : ℝ), (316136593619/800000000000 : ℝ), (6820517248079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(625479227/1000000000 : ℝ)|^65 ≤ (26831204265699/50000000000000 : ℝ)^49
        have hw : |(625479227/1000000000 : ℝ)|=(625479227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1241588747/2500000000 : ℝ)|^65 ≤ (316136593619/800000000000 : ℝ)^49
        have hw : |(1241588747/2500000000 : ℝ)|=(1241588747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1320923497/10000000000 : ℝ)|^65 ≤ (6820517248079/100000000000000 : ℝ)^49
        have hw : |(-1320923497/10000000000 : ℝ)|=(1320923497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s0_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (520223279/1250000000 : ℝ)*x 0 + (-835512651/2000000000 : ℝ)*x 1 + (11893413/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520223279/1250000000 : ℝ)^65 ≤ (31258127554389/100000000000000 : ℝ)^49 := by
    have hnat : (520223279 : ℕ)^65*100000000000000^49 ≤ 31258127554389^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520223279 1250000000 31258127554389 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (835512651/2000000000 : ℝ)^65 ≤ (1570770749109/5000000000000 : ℝ)^49 := by
    have hnat : (835512651 : ℕ)^65*5000000000000^49 ≤ 1570770749109^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835512651 2000000000 1570770749109 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11893413/25000000 : ℝ)^65 ≤ (37326457458119/100000000000000 : ℝ)^49 := by
    have hnat : (11893413 : ℕ)^65*100000000000000^49 ≤ 37326457458119^49*25000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11893413 25000000 37326457458119 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520223279/1250000000 : ℝ), (-835512651/2000000000 : ℝ), (11893413/25000000 : ℝ)] ![(31258127554389/100000000000000 : ℝ), (1570770749109/5000000000000 : ℝ), (37326457458119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520223279/1250000000 : ℝ)|^65 ≤ (31258127554389/100000000000000 : ℝ)^49
        have hw : |(520223279/1250000000 : ℝ)|=(520223279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-835512651/2000000000 : ℝ)|^65 ≤ (1570770749109/5000000000000 : ℝ)^49
        have hw : |(-835512651/2000000000 : ℝ)|=(835512651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11893413/25000000 : ℝ)|^65 ≤ (37326457458119/100000000000000 : ℝ)^49
        have hw : |(11893413/25000000 : ℝ)|=(11893413/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s0_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2608496423/5000000000 : ℝ)*x 0 + (-289984121/2500000000 : ℝ)*x 1 + (-1222967173/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2608496423/5000000000 : ℝ)^65 ≤ (42184149700587/100000000000000 : ℝ)^49 := by
    have hnat : (2608496423 : ℕ)^65*100000000000000^49 ≤ 42184149700587^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608496423 5000000000 42184149700587 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (289984121/2500000000 : ℝ)^65 ≤ (5740415627549/100000000000000 : ℝ)^49 := by
    have hnat : (289984121 : ℕ)^65*100000000000000^49 ≤ 5740415627549^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289984121 2500000000 5740415627549 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1222967173/2000000000 : ℝ)^65 ≤ (52075434647331/100000000000000 : ℝ)^49 := by
    have hnat : (1222967173 : ℕ)^65*100000000000000^49 ≤ 52075434647331^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222967173 2000000000 52075434647331 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2608496423/5000000000 : ℝ), (-289984121/2500000000 : ℝ), (-1222967173/2000000000 : ℝ)] ![(42184149700587/100000000000000 : ℝ), (5740415627549/100000000000000 : ℝ), (52075434647331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2608496423/5000000000 : ℝ)|^65 ≤ (42184149700587/100000000000000 : ℝ)^49
        have hw : |(2608496423/5000000000 : ℝ)|=(2608496423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-289984121/2500000000 : ℝ)|^65 ≤ (5740415627549/100000000000000 : ℝ)^49
        have hw : |(-289984121/2500000000 : ℝ)|=(289984121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1222967173/2000000000 : ℝ)|^65 ≤ (52075434647331/100000000000000 : ℝ)^49
        have hw : |(-1222967173/2000000000 : ℝ)|=(1222967173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s0_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1797792863/10000000000 : ℝ)*x 0 + (-4002986307/10000000000 : ℝ)*x 1 + (-6808070087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1797792863/10000000000 : ℝ)^65 ≤ (10265718101681/100000000000000 : ℝ)^49 := by
    have hnat : (1797792863 : ℕ)^65*100000000000000^49 ≤ 10265718101681^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797792863 10000000000 10265718101681 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4002986307/10000000000 : ℝ)^65 ≤ (5937181675731/20000000000000 : ℝ)^49 := by
    have hnat : (4002986307 : ℕ)^65*20000000000000^49 ≤ 5937181675731^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4002986307 10000000000 5937181675731 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6808070087/10000000000 : ℝ)^65 ≤ (7506046687887/12500000000000 : ℝ)^49 := by
    have hnat : (6808070087 : ℕ)^65*12500000000000^49 ≤ 7506046687887^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6808070087 10000000000 7506046687887 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1797792863/10000000000 : ℝ), (-4002986307/10000000000 : ℝ), (-6808070087/10000000000 : ℝ)] ![(10265718101681/100000000000000 : ℝ), (5937181675731/20000000000000 : ℝ), (7506046687887/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1797792863/10000000000 : ℝ)|^65 ≤ (10265718101681/100000000000000 : ℝ)^49
        have hw : |(-1797792863/10000000000 : ℝ)|=(1797792863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4002986307/10000000000 : ℝ)|^65 ≤ (5937181675731/20000000000000 : ℝ)^49
        have hw : |(-4002986307/10000000000 : ℝ)|=(4002986307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6808070087/10000000000 : ℝ)|^65 ≤ (7506046687887/12500000000000 : ℝ)^49
        have hw : |(-6808070087/10000000000 : ℝ)|=(6808070087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s0_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6704348533/10000000000 : ℝ)*x 0 + (1141023067/2500000000 : ℝ)*x 1 + (-1174136999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6704348533/10000000000 : ℝ)^65 ≤ (58837836132197/100000000000000 : ℝ)^49 := by
    have hnat : (6704348533 : ℕ)^65*100000000000000^49 ≤ 58837836132197^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6704348533 10000000000 58837836132197 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141023067/2500000000 : ℝ)^65 ≤ (35328337798163/100000000000000 : ℝ)^49 := by
    have hnat : (1141023067 : ℕ)^65*100000000000000^49 ≤ 35328337798163^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141023067 2500000000 35328337798163 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1174136999/10000000000 : ℝ)^65 ≤ (5833826047041/100000000000000 : ℝ)^49 := by
    have hnat : (1174136999 : ℕ)^65*100000000000000^49 ≤ 5833826047041^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174136999 10000000000 5833826047041 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6704348533/10000000000 : ℝ), (1141023067/2500000000 : ℝ), (-1174136999/10000000000 : ℝ)] ![(58837836132197/100000000000000 : ℝ), (35328337798163/100000000000000 : ℝ), (5833826047041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6704348533/10000000000 : ℝ)|^65 ≤ (58837836132197/100000000000000 : ℝ)^49
        have hw : |(6704348533/10000000000 : ℝ)|=(6704348533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1141023067/2500000000 : ℝ)|^65 ≤ (35328337798163/100000000000000 : ℝ)^49
        have hw : |(1141023067/2500000000 : ℝ)|=(1141023067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1174136999/10000000000 : ℝ)|^65 ≤ (5833826047041/100000000000000 : ℝ)^49
        have hw : |(-1174136999/10000000000 : ℝ)|=(1174136999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s0_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (433818169/1000000000 : ℝ)*x 0 + (-5030386617/10000000000 : ℝ)*x 1 + (46295923/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433818169/1000000000 : ℝ)^65 ≤ (3302764518349/10000000000000 : ℝ)^49 := by
    have hnat : (433818169 : ℕ)^65*10000000000000^49 ≤ 3302764518349^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433818169 1000000000 3302764518349 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5030386617/10000000000 : ℝ)^65 ≤ (40194356072713/100000000000000 : ℝ)^49 := by
    have hnat : (5030386617 : ℕ)^65*100000000000000^49 ≤ 40194356072713^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030386617 10000000000 40194356072713 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46295923/125000000 : ℝ)^65 ≤ (26777998725997/100000000000000 : ℝ)^49 := by
    have hnat : (46295923 : ℕ)^65*100000000000000^49 ≤ 26777998725997^49*125000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46295923 125000000 26777998725997 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433818169/1000000000 : ℝ), (-5030386617/10000000000 : ℝ), (46295923/125000000 : ℝ)] ![(3302764518349/10000000000000 : ℝ), (40194356072713/100000000000000 : ℝ), (26777998725997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433818169/1000000000 : ℝ)|^65 ≤ (3302764518349/10000000000000 : ℝ)^49
        have hw : |(433818169/1000000000 : ℝ)|=(433818169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5030386617/10000000000 : ℝ)|^65 ≤ (40194356072713/100000000000000 : ℝ)^49
        have hw : |(-5030386617/10000000000 : ℝ)|=(5030386617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(46295923/125000000 : ℝ)|^65 ≤ (26777998725997/100000000000000 : ℝ)^49
        have hw : |(46295923/125000000 : ℝ)|=(46295923/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s0_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (554660091/1250000000 : ℝ)*x 0 + (-1376112039/10000000000 : ℝ)*x 1 + (-669824023/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (554660091/1250000000 : ℝ)^65 ≤ (34032180241979/100000000000000 : ℝ)^49 := by
    have hnat : (554660091 : ℕ)^65*100000000000000^49 ≤ 34032180241979^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554660091 1250000000 34032180241979 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376112039/10000000000 : ℝ)^65 ≤ (7201084223311/100000000000000 : ℝ)^49 := by
    have hnat : (1376112039 : ℕ)^65*100000000000000^49 ≤ 7201084223311^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376112039 10000000000 7201084223311 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (669824023/1000000000 : ℝ)^65 ≤ (58766735520357/100000000000000 : ℝ)^49 := by
    have hnat : (669824023 : ℕ)^65*100000000000000^49 ≤ 58766735520357^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669824023 1000000000 58766735520357 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(554660091/1250000000 : ℝ), (-1376112039/10000000000 : ℝ), (-669824023/1000000000 : ℝ)] ![(34032180241979/100000000000000 : ℝ), (7201084223311/100000000000000 : ℝ), (58766735520357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(554660091/1250000000 : ℝ)|^65 ≤ (34032180241979/100000000000000 : ℝ)^49
        have hw : |(554660091/1250000000 : ℝ)|=(554660091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1376112039/10000000000 : ℝ)|^65 ≤ (7201084223311/100000000000000 : ℝ)^49
        have hw : |(-1376112039/10000000000 : ℝ)|=(1376112039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-669824023/1000000000 : ℝ)|^65 ≤ (58766735520357/100000000000000 : ℝ)^49
        have hw : |(-669824023/1000000000 : ℝ)|=(669824023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s0_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1445842279/10000000000 : ℝ)*x 0 + (-4963503227/10000000000 : ℝ)*x 1 + (-6180975851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1445842279/10000000000 : ℝ)^65 ≤ (240283921789/3125000000000 : ℝ)^49 := by
    have hnat : (1445842279 : ℕ)^65*3125000000000^49 ≤ 240283921789^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445842279 10000000000 240283921789 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4963503227/10000000000 : ℝ)^65 ≤ (39486976267141/100000000000000 : ℝ)^49 := by
    have hnat : (4963503227 : ℕ)^65*100000000000000^49 ≤ 39486976267141^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4963503227 10000000000 39486976267141 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6180975851/10000000000 : ℝ)^65 ≤ (6602992278181/12500000000000 : ℝ)^49 := by
    have hnat : (6180975851 : ℕ)^65*12500000000000^49 ≤ 6602992278181^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6180975851 10000000000 6602992278181 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1445842279/10000000000 : ℝ), (-4963503227/10000000000 : ℝ), (-6180975851/10000000000 : ℝ)] ![(240283921789/3125000000000 : ℝ), (39486976267141/100000000000000 : ℝ), (6602992278181/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1445842279/10000000000 : ℝ)|^65 ≤ (240283921789/3125000000000 : ℝ)^49
        have hw : |(-1445842279/10000000000 : ℝ)|=(1445842279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4963503227/10000000000 : ℝ)|^65 ≤ (39486976267141/100000000000000 : ℝ)^49
        have hw : |(-4963503227/10000000000 : ℝ)|=(4963503227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6180975851/10000000000 : ℝ)|^65 ≤ (6602992278181/12500000000000 : ℝ)^49
        have hw : |(-6180975851/10000000000 : ℝ)|=(6180975851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s0_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7056299989/10000000000 : ℝ)*x 0 + (4006520857/10000000000 : ℝ)*x 1 + (-695846771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7056299989/10000000000 : ℝ)^65 ≤ (62969870882627/100000000000000 : ℝ)^49 := by
    have hnat : (7056299989 : ℕ)^65*100000000000000^49 ≤ 62969870882627^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7056299989 10000000000 62969870882627 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4006520857/10000000000 : ℝ)^65 ≤ (7430171106837/25000000000000 : ℝ)^49 := by
    have hnat : (4006520857 : ℕ)^65*25000000000000^49 ≤ 7430171106837^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4006520857 10000000000 7430171106837 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (695846771/5000000000 : ℝ)^65 ≤ (7309444673489/100000000000000 : ℝ)^49 := by
    have hnat : (695846771 : ℕ)^65*100000000000000^49 ≤ 7309444673489^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695846771 5000000000 7309444673489 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7056299989/10000000000 : ℝ), (4006520857/10000000000 : ℝ), (-695846771/5000000000 : ℝ)] ![(62969870882627/100000000000000 : ℝ), (7430171106837/25000000000000 : ℝ), (7309444673489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7056299989/10000000000 : ℝ)|^65 ≤ (62969870882627/100000000000000 : ℝ)^49
        have hw : |(7056299989/10000000000 : ℝ)|=(7056299989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4006520857/10000000000 : ℝ)|^65 ≤ (7430171106837/25000000000000 : ℝ)^49
        have hw : |(4006520857/10000000000 : ℝ)|=(4006520857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-695846771/5000000000 : ℝ)|^65 ≤ (7309444673489/100000000000000 : ℝ)^49
        have hw : |(-695846771/5000000000 : ℝ)|=(695846771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s0_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3366452697/10000000000 : ℝ)*x 0 + (-2659759537/5000000000 : ℝ)*x 1 + (543412921/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3366452697/10000000000 : ℝ)^65 ≤ (11796410392989/50000000000000 : ℝ)^49 := by
    have hnat : (3366452697 : ℕ)^65*50000000000000^49 ≤ 11796410392989^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3366452697 10000000000 11796410392989 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2659759537/5000000000 : ℝ)^65 ≤ (43287380711223/100000000000000 : ℝ)^49 := by
    have hnat : (2659759537 : ℕ)^65*100000000000000^49 ≤ 43287380711223^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2659759537 5000000000 43287380711223 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543412921/1250000000 : ℝ)^65 ≤ (8279949620257/25000000000000 : ℝ)^49 := by
    have hnat : (543412921 : ℕ)^65*25000000000000^49 ≤ 8279949620257^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543412921 1250000000 8279949620257 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3366452697/10000000000 : ℝ), (-2659759537/5000000000 : ℝ), (543412921/1250000000 : ℝ)] ![(11796410392989/50000000000000 : ℝ), (43287380711223/100000000000000 : ℝ), (8279949620257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3366452697/10000000000 : ℝ)|^65 ≤ (11796410392989/50000000000000 : ℝ)^49
        have hw : |(3366452697/10000000000 : ℝ)|=(3366452697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2659759537/5000000000 : ℝ)|^65 ≤ (43287380711223/100000000000000 : ℝ)^49
        have hw : |(-2659759537/5000000000 : ℝ)|=(2659759537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543412921/1250000000 : ℝ)|^65 ≤ (8279949620257/25000000000000 : ℝ)^49
        have hw : |(543412921/1250000000 : ℝ)|=(543412921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s0_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6340394371/10000000000 : ℝ)*x 0 + (-159901539/1000000000 : ℝ)*x 1 + (-4684818339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6340394371/10000000000 : ℝ)^65 ≤ (54638803040491/100000000000000 : ℝ)^49 := by
    have hnat : (6340394371 : ℕ)^65*100000000000000^49 ≤ 54638803040491^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6340394371 10000000000 54638803040491 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (159901539/1000000000 : ℝ)^65 ≤ (4393960660813/50000000000000 : ℝ)^49 := by
    have hnat : (159901539 : ℕ)^65*50000000000000^49 ≤ 4393960660813^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159901539 1000000000 4393960660813 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4684818339/10000000000 : ℝ)^65 ≤ (36573275614999/100000000000000 : ℝ)^49 := by
    have hnat : (4684818339 : ℕ)^65*100000000000000^49 ≤ 36573275614999^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4684818339 10000000000 36573275614999 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6340394371/10000000000 : ℝ), (-159901539/1000000000 : ℝ), (-4684818339/10000000000 : ℝ)] ![(54638803040491/100000000000000 : ℝ), (4393960660813/50000000000000 : ℝ), (36573275614999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6340394371/10000000000 : ℝ)|^65 ≤ (54638803040491/100000000000000 : ℝ)^49
        have hw : |(6340394371/10000000000 : ℝ)|=(6340394371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-159901539/1000000000 : ℝ)|^65 ≤ (4393960660813/50000000000000 : ℝ)^49
        have hw : |(-159901539/1000000000 : ℝ)|=(159901539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4684818339/10000000000 : ℝ)|^65 ≤ (36573275614999/100000000000000 : ℝ)^49
        have hw : |(-4684818339/10000000000 : ℝ)|=(4684818339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1759643727/5000000000 : ℝ)*x 0 + (-4229905169/10000000000 : ℝ)*x 1 + (-33102089/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1759643727/5000000000 : ℝ)^65 ≤ (5004818425673/20000000000000 : ℝ)^49 := by
    have hnat : (1759643727 : ℕ)^65*20000000000000^49 ≤ 5004818425673^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759643727 5000000000 5004818425673 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229905169/10000000000 : ℝ)^65 ≤ (15969309847163/50000000000000 : ℝ)^49 := by
    have hnat : (4229905169 : ℕ)^65*50000000000000^49 ≤ 15969309847163^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229905169 10000000000 15969309847163 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33102089/62500000 : ℝ)^65 ≤ (43037288161083/100000000000000 : ℝ)^49 := by
    have hnat : (33102089 : ℕ)^65*100000000000000^49 ≤ 43037288161083^49*62500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33102089 62500000 43037288161083 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1759643727/5000000000 : ℝ), (-4229905169/10000000000 : ℝ), (-33102089/62500000 : ℝ)] ![(5004818425673/20000000000000 : ℝ), (15969309847163/50000000000000 : ℝ), (43037288161083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1759643727/5000000000 : ℝ)|^65 ≤ (5004818425673/20000000000000 : ℝ)^49
        have hw : |(-1759643727/5000000000 : ℝ)|=(1759643727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4229905169/10000000000 : ℝ)|^65 ≤ (15969309847163/50000000000000 : ℝ)^49
        have hw : |(-4229905169/10000000000 : ℝ)|=(4229905169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33102089/62500000 : ℝ)|^65 ≤ (43037288161083/100000000000000 : ℝ)^49
        have hw : |(-33102089/62500000 : ℝ)|=(33102089/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s1_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5291627347/10000000000 : ℝ)*x 0 + (4236778997/10000000000 : ℝ)*x 1 + (-3517364261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291627347/10000000000 : ℝ)^65 ≤ (8597311790557/20000000000000 : ℝ)^49 := by
    have hnat : (5291627347 : ℕ)^65*20000000000000^49 ≤ 8597311790557^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291627347 10000000000 8597311790557 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4236778997/10000000000 : ℝ)^65 ≤ (16003743779483/50000000000000 : ℝ)^49 := by
    have hnat : (4236778997 : ℕ)^65*50000000000000^49 ≤ 16003743779483^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236778997 10000000000 16003743779483 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3517364261/10000000000 : ℝ)^65 ≤ (25005953477523/100000000000000 : ℝ)^49 := by
    have hnat : (3517364261 : ℕ)^65*100000000000000^49 ≤ 25005953477523^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3517364261 10000000000 25005953477523 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291627347/10000000000 : ℝ), (4236778997/10000000000 : ℝ), (-3517364261/10000000000 : ℝ)] ![(8597311790557/20000000000000 : ℝ), (16003743779483/50000000000000 : ℝ), (25005953477523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291627347/10000000000 : ℝ)|^65 ≤ (8597311790557/20000000000000 : ℝ)^49
        have hw : |(5291627347/10000000000 : ℝ)|=(5291627347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4236778997/10000000000 : ℝ)|^65 ≤ (16003743779483/50000000000000 : ℝ)^49
        have hw : |(4236778997/10000000000 : ℝ)|=(4236778997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3517364261/10000000000 : ℝ)|^65 ≤ (25005953477523/100000000000000 : ℝ)^49
        have hw : |(-3517364261/10000000000 : ℝ)|=(3517364261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4090401447/10000000000 : ℝ)*x 0 + (-2458169509/5000000000 : ℝ)*x 1 + (4081533441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4090401447/10000000000 : ℝ)^65 ≤ (30548903448353/100000000000000 : ℝ)^49 := by
    have hnat : (4090401447 : ℕ)^65*100000000000000^49 ≤ 30548903448353^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4090401447 10000000000 30548903448353 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2458169509/5000000000 : ℝ)^65 ≤ (9747504569181/25000000000000 : ℝ)^49 := by
    have hnat : (2458169509 : ℕ)^65*25000000000000^49 ≤ 9747504569181^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2458169509 5000000000 9747504569181 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4081533441/10000000000 : ℝ)^65 ≤ (152305391267/500000000000 : ℝ)^49 := by
    have hnat : (4081533441 : ℕ)^65*500000000000^49 ≤ 152305391267^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4081533441 10000000000 152305391267 500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4090401447/10000000000 : ℝ), (-2458169509/5000000000 : ℝ), (4081533441/10000000000 : ℝ)] ![(30548903448353/100000000000000 : ℝ), (9747504569181/25000000000000 : ℝ), (152305391267/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4090401447/10000000000 : ℝ)|^65 ≤ (30548903448353/100000000000000 : ℝ)^49
        have hw : |(4090401447/10000000000 : ℝ)|=(4090401447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2458169509/5000000000 : ℝ)|^65 ≤ (9747504569181/25000000000000 : ℝ)^49
        have hw : |(-2458169509/5000000000 : ℝ)|=(2458169509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4081533441/10000000000 : ℝ)|^65 ≤ (152305391267/500000000000 : ℝ)^49
        have hw : |(4081533441/10000000000 : ℝ)|=(4081533441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301070_s1_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4667206839/10000000000 : ℝ)*x 0 + (-747366457/2000000000 : ℝ)*x 1 + (-1169737381/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4667206839/10000000000 : ℝ)^65 ≤ (36391004492459/100000000000000 : ℝ)^49 := by
    have hnat : (4667206839 : ℕ)^65*100000000000000^49 ≤ 36391004492459^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4667206839 10000000000 36391004492459 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (747366457/2000000000 : ℝ)^65 ≤ (13548242194213/50000000000000 : ℝ)^49 := by
    have hnat : (747366457 : ℕ)^65*50000000000000^49 ≤ 13548242194213^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747366457 2000000000 13548242194213 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1169737381/2500000000 : ℝ)^65 ≤ (18256255556653/50000000000000 : ℝ)^49 := by
    have hnat : (1169737381 : ℕ)^65*50000000000000^49 ≤ 18256255556653^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1169737381 2500000000 18256255556653 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4667206839/10000000000 : ℝ), (-747366457/2000000000 : ℝ), (-1169737381/2500000000 : ℝ)] ![(36391004492459/100000000000000 : ℝ), (13548242194213/50000000000000 : ℝ), (18256255556653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4667206839/10000000000 : ℝ)|^65 ≤ (36391004492459/100000000000000 : ℝ)^49
        have hw : |(4667206839/10000000000 : ℝ)|=(4667206839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-747366457/2000000000 : ℝ)|^65 ≤ (13548242194213/50000000000000 : ℝ)^49
        have hw : |(-747366457/2000000000 : ℝ)|=(747366457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1169737381/2500000000 : ℝ)|^65 ≤ (18256255556653/50000000000000 : ℝ)^49
        have hw : |(-1169737381/2500000000 : ℝ)|=(1169737381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301070 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-216670597/1000000000 : ℝ)*X 0 0+(-224045069/500000000 : ℝ)*X 0 1+(-1228241013/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((251943969/400000000 : ℝ)*X 1 0+(4450258421/10000000000 : ℝ)*X 1 1+(-1980762097/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((5178252971/10000000000 : ℝ)*X 0 0+(-108132531/500000000 : ℝ)*X 0 1+(-2743923837/5000000000 : ℝ)*X 0 2+(5178252971/10000000000 : ℝ)*X 1 0+(-108132531/500000000 : ℝ)*X 1 1+(-2743923837/5000000000 : ℝ)*X 1 2+(5178252971/10000000000 : ℝ)*X 2 0+(-108132531/500000000 : ℝ)*X 2 1+(-2743923837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-77327491/500000000 : ℝ)*X 0 0+(-1241588747/2500000000 : ℝ)*X 0 1+(-1222967173/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((625479227/1000000000 : ℝ)*X 1 0+(1241588747/2500000000 : ℝ)*X 1 1+(-1320923497/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((520223279/1250000000 : ℝ)*X 2 0+(-835512651/2000000000 : ℝ)*X 2 1+(11893413/25000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2608496423/5000000000 : ℝ)*X 0 0+(-289984121/2500000000 : ℝ)*X 0 1+(-1222967173/2000000000 : ℝ)*X 0 2+(2608496423/5000000000 : ℝ)*X 1 0+(-289984121/2500000000 : ℝ)*X 1 1+(-1222967173/2000000000 : ℝ)*X 1 2+(2608496423/5000000000 : ℝ)*X 2 0+(-289984121/2500000000 : ℝ)*X 2 1+(-1222967173/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1797792863/10000000000 : ℝ)*X 0 0+(-4002986307/10000000000 : ℝ)*X 0 1+(-6808070087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((6704348533/10000000000 : ℝ)*X 1 0+(1141023067/2500000000 : ℝ)*X 1 1+(-1174136999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((433818169/1000000000 : ℝ)*X 2 0+(-5030386617/10000000000 : ℝ)*X 2 1+(46295923/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((554660091/1250000000 : ℝ)*X 0 0+(-1376112039/10000000000 : ℝ)*X 0 1+(-669824023/1000000000 : ℝ)*X 0 2+(554660091/1250000000 : ℝ)*X 1 0+(-1376112039/10000000000 : ℝ)*X 1 1+(-669824023/1000000000 : ℝ)*X 1 2+(554660091/1250000000 : ℝ)*X 2 0+(-1376112039/10000000000 : ℝ)*X 2 1+(-669824023/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1445842279/10000000000 : ℝ)*X 0 0+(-4963503227/10000000000 : ℝ)*X 0 1+(-6180975851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((7056299989/10000000000 : ℝ)*X 1 0+(4006520857/10000000000 : ℝ)*X 1 1+(-695846771/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3366452697/10000000000 : ℝ)*X 2 0+(-2659759537/5000000000 : ℝ)*X 2 1+(543412921/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((6340394371/10000000000 : ℝ)*X 0 0+(-159901539/1000000000 : ℝ)*X 0 1+(-4684818339/10000000000 : ℝ)*X 0 2+(6340394371/10000000000 : ℝ)*X 1 0+(-159901539/1000000000 : ℝ)*X 1 1+(-4684818339/10000000000 : ℝ)*X 1 2+(6340394371/10000000000 : ℝ)*X 2 0+(-159901539/1000000000 : ℝ)*X 2 1+(-4684818339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((11123/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11123/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (26601838359100678208133/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (418543474349/1000000000000 : ℝ)*(base1) + (293282422247/1000000000000 : ℝ)*(base3) + (73901417917/40000000000 : ℝ)*(base39) + (1159629/500000000000 : ℝ)*(base49) + (288315711519/500000000000 : ℝ)*(base59) + (5072181217523/1000000000000 : ℝ)*(major_s0_0) + (5072181217523/1000000000000 : ℝ)*(major_s0_1) + (5072181217523/1000000000000 : ℝ)*(major_s0_2) + (26654759/1000000000000 : ℝ)*(sp_s0_1) + (3566603213849/500000000000 : ℝ)*(sp_s0_7) + (3504352196281/500000000000 : ℝ)*(sp_s0_8) + (3357724312537/500000000000 : ℝ)*(sp_s0_9) + (135854218323/50000000000 : ℝ)*(sp_s0_13) + (31426869/40000000000 : ℝ)*(sp_s0_21) + (214306891441/62500000000 : ℝ)*(f.failure) + (3357724312537/500000000000 : ℝ)*(f.sum) + (465709936358067/1250000000000000000000000000 : ℝ)*base62 + (8323210503597289/10000000000000000000000000000 : ℝ)*base65 + (4458029946267247/10000000000000000000000000000 : ℝ)*base67 + (5234042976267247/10000000000000000000000000000 : ℝ)*base68 + (1026240604165021/5000000000000000000000000000 : ℝ)*base71 + (320256501597289/10000000000000000000000000000 : ℝ)*base73 + (7884995992597289/10000000000000000000000000000 : ℝ)*base74 + (3645342208732753/10000000000000000000000000000 : ℝ)*base77 + (551978366766933/1250000000000000000000000000 : ℝ)*base78 + (133/3125000000000000 : ℝ)*base86 + (133/3125000000000000 : ℝ)*base88 + (133/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-32027/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-32027/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4872647454431069892267/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (798625380769/500000000000 : ℝ)*(base39) + (74279111043/62500000000 : ℝ)*(base59) + (6003227722441/1000000000000 : ℝ)*(major_s0_0) + (6003227722441/1000000000000 : ℝ)*(major_s0_1) + (6003227722441/1000000000000 : ℝ)*(major_s0_2) + (437073/5000000000 : ℝ)*(sp_s0_0) + (775439/10000000000 : ℝ)*(sp_s0_1) + (2380853/500000000000 : ℝ)*(sp_s0_9) + (23798411/1000000000000 : ℝ)*(sp_s0_13) + (1987011620579/250000000000 : ℝ)*(sp_s0_14) + (3973987944813/500000000000 : ℝ)*(sp_s0_15) + (794812913521/100000000000 : ℝ)*(sp_s0_16) + (4058295150807/1000000000000 : ℝ)*(sp_s0_20) + (8046339/100000000000 : ℝ)*(sp_s0_22) + (2029159474609/500000000000 : ℝ)*(f.failure) + (1987033474229/250000000000 : ℝ)*(f.sum) + (239254833089089/1250000000000000000000000000 : ℝ)*base62 + (1252458985560437/10000000000000000000000000000 : ℝ)*base64 + (2738350817726851/10000000000000000000000000000 : ℝ)*base66 + (3078243364726851/10000000000000000000000000000 : ℝ)*base69 + (2227092269583207/5000000000000000000000000000 : ℝ)*base71 + (4995612215560437/10000000000000000000000000000 : ℝ)*base72 + (1787794500560437/10000000000000000000000000000 : ℝ)*base75 + (3177852568273149/10000000000000000000000000000 : ℝ)*base76 + (145995663035911/1250000000000000000000000000 : ℝ)*base78 + (2929/12500000000000000 : ℝ)*base87 + (2929/12500000000000000 : ℝ)*base89 + (2929/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29991/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29991/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3849442913570246640447/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (114412196509/62500000000 : ℝ)*(base39) + (618719/250000000000 : ℝ)*(base49) + (622431769727/1000000000000 : ℝ)*(base59) + (1426521814687/250000000000 : ℝ)*(major_s0_0) + (1426521814687/250000000000 : ℝ)*(major_s0_1) + (1426521814687/250000000000 : ℝ)*(major_s0_2) + (27009379/1000000000000 : ℝ)*(sp_s0_6) + (525353217/1000000000000 : ℝ)*(sp_s0_7) + (30198487/1000000000000 : ℝ)*(sp_s0_15) + (403871/31250000000 : ℝ)*(sp_s0_16) + (472137618561/62500000000 : ℝ)*(sp_s0_21) + (3777348525853/500000000000 : ℝ)*(sp_s0_22) + (7554714326321/1000000000000 : ℝ)*(sp_s0_23) + (771483640977/200000000000 : ℝ)*(sp_s0_27) + (482180651783/125000000000 : ℝ)*(f.failure) + (7554727250193/1000000000000 : ℝ)*(f.sum) + (144260921150977/312500000000000000000000000 : ℝ)*base63 + (563726068286259/2500000000000000000000000000 : ℝ)*base64 + (153528629078443/2500000000000000000000000000 : ℝ)*base67 + (315639480828443/2500000000000000000000000000 : ℝ)*base68 + (551926569182351/1250000000000000000000000000 : ℝ)*base70 + (654734068713741/2500000000000000000000000000 : ℝ)*base73 + (954357147536259/2500000000000000000000000000 : ℝ)*base75 + (215493283421557/2500000000000000000000000000 : ℝ)*base77 + (40644227380273/312500000000000000000000000 : ℝ)*base79 + (377/3125000000000000 : ℝ)*base86 + (377/3125000000000000 : ℝ)*base88 + (377/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (11123/50000 : ℝ) ^ (129/32 : ℝ) ≤ (29209180162522321/12500000000000000000 : ℝ) := by
    have hpowers : (11123/50000 : ℝ)^129 ≤ (29209180162522321/12500000000000000000 : ℝ)^32 := by
      have hnat : (11123 : ℕ)^129*12500000000000000000^32 ≤ 29209180162522321^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11123 50000 29209180162522321 12500000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11123/50000 : ℝ)) (X := (29209180162522321/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (12529209180162522321/12500000000000000000 : ℝ) ≤ (5002895732460171/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (12529209180162522321/12500000000000000000 : ℝ)^32 ≤ (5002895732460171/5000000000000000 : ℝ)^129 := by
      have hnat : (12529209180162522321 : ℕ)^32*5000000000000000^129 ≤ 5002895732460171^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12529209180162522321 12500000000000000000 5002895732460171 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002895732460171/5000000000000000 : ℝ)) (X := (12529209180162522321/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (6279209180162522321/6250000000000000000 : ℝ) ≤ (5005786393190557/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (6279209180162522321/6250000000000000000 : ℝ)^32 ≤ (5005786393190557/5000000000000000 : ℝ)^129 := by
      have hnat : (6279209180162522321 : ℕ)^32*5000000000000000^129 ≤ 5005786393190557^129*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6279209180162522321 6250000000000000000 5005786393190557 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005786393190557/5000000000000000 : ℝ)) (X := (6279209180162522321/6250000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(2895732460171/1112300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1445330365193/556150000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (11123/50000 : ℝ)) (alpha := (2895732460171/1112300000000000 : ℝ)) (beta := (1445330365193/556150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11123/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(2895732460171/1112300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1445330365193/556150000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (32027/100000 : ℝ) ^ (129/32 : ℝ) ≤ (253835541470199763/25000000000000000000 : ℝ) := by
    have hpowers : (32027/100000 : ℝ)^129 ≤ (253835541470199763/25000000000000000000 : ℝ)^32 := by
      have hnat : (32027 : ℕ)^129*25000000000000000000^32 ≤ 253835541470199763^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32027 100000 253835541470199763 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (32027/100000 : ℝ)) (X := (253835541470199763/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25253835541470199763/25000000000000000000 : ℝ) ≤ (39160512504849/39062500000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (25253835541470199763/25000000000000000000 : ℝ)^32 ≤ (39160512504849/39062500000000 : ℝ)^129 := by
      have hnat : (25253835541470199763 : ℕ)^32*39062500000000^129 ≤ 39160512504849^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25253835541470199763 25000000000000000000 39160512504849 39062500000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39160512504849/39062500000000 : ℝ)) (X := (25253835541470199763/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12753835541470199763/12500000000000000000 : ℝ) ≤ (2512498368393143/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (12753835541470199763/12500000000000000000 : ℝ)^32 ≤ (2512498368393143/2500000000000000 : ℝ)^129 := by
      have hnat : (12753835541470199763 : ℕ)^32*2500000000000000^129 ≤ 2512498368393143^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12753835541470199763 12500000000000000000 2512498368393143 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2512498368393143/2500000000000000 : ℝ)) (X := (12753835541470199763/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(98012504849/12510546875000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(6225568082807/800675000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (32027/100000 : ℝ)) (alpha := (98012504849/12510546875000 : ℝ)) (beta := (6225568082807/800675000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (32027/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(98012504849/12510546875000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(6225568082807/800675000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (29991/100000 : ℝ) ^ (129/32 : ℝ) ≤ (155829526152410147/20000000000000000000 : ℝ) := by
    have hpowers : (29991/100000 : ℝ)^129 ≤ (155829526152410147/20000000000000000000 : ℝ)^32 := by
      have hnat : (29991 : ℕ)^129*20000000000000000000^32 ≤ 155829526152410147^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29991 100000 155829526152410147 20000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29991/100000 : ℝ)) (X := (155829526152410147/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (20155829526152410147/20000000000000000000 : ℝ) ≤ (10019271331761509/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (20155829526152410147/20000000000000000000 : ℝ)^32 ≤ (10019271331761509/10000000000000000 : ℝ)^129 := by
      have hnat : (20155829526152410147 : ℕ)^32*10000000000000000^129 ≤ 10019271331761509^129*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20155829526152410147 20000000000000000000 10019271331761509 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10019271331761509/10000000000000000 : ℝ)) (X := (20155829526152410147/20000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (10155829526152410147/10000000000000000000 : ℝ) ≤ (10038430954820753/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (10155829526152410147/10000000000000000000 : ℝ)^32 ≤ (10038430954820753/10000000000000000 : ℝ)^129 := by
      have hnat : (10155829526152410147 : ℕ)^32*10000000000000000^129 ≤ 10038430954820753^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10155829526152410147 10000000000000000000 10038430954820753 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10038430954820753/10000000000000000 : ℝ)) (X := (10155829526152410147/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(19271331761509/2999100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1596635254937/249925000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (29991/100000 : ℝ)) (alpha := (19271331761509/2999100000000000 : ℝ)) (beta := (1596635254937/249925000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (29991/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(19271331761509/2999100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1596635254937/249925000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1759643727/5000000000 : ℝ)*X 0 0+(-4229905169/10000000000 : ℝ)*X 0 1+(-33102089/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5291627347/10000000000 : ℝ)*X 1 0+(4236778997/10000000000 : ℝ)*X 1 1+(-3517364261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4090401447/10000000000 : ℝ)*X 2 0+(-2458169509/5000000000 : ℝ)*X 2 1+(4081533441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4667206839/10000000000 : ℝ)*X 0 0+(-747366457/2000000000 : ℝ)*X 0 1+(-1169737381/2500000000 : ℝ)*X 0 2+(4667206839/10000000000 : ℝ)*X 1 0+(-747366457/2000000000 : ℝ)*X 1 1+(-1169737381/2500000000 : ℝ)*X 1 2+(4667206839/10000000000 : ℝ)*X 2 0+(-747366457/2000000000 : ℝ)*X 2 1+(-1169737381/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301070_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-73443/12500 : ℝ) < ((-36981/25000 : ℝ)*P 0+(-36981/25000 : ℝ)*P 1+(-36981/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-73443/12500 : ℝ) < (-73695893743629799402201788976812543/12718908932275000000000000000000000 : ℝ) := by norm_num
    linear_combination (261831/500000000000 : ℝ)*(base1) + (7343/12500000000 : ℝ)*(base22) + (92129/200000000000 : ℝ)*(base25) + (120080421989/250000000000 : ℝ)*(base39) + (19020550093/125000000000 : ℝ)*(base40) + (6593699783/31250000000 : ℝ)*(base49) + (150127/1000000000000 : ℝ)*(base54) + (279142949471/1000000000000 : ℝ)*(base59) + (36981/25000 : ℝ)*(major_s1_0) + (36981/25000 : ℝ)*(major_s1_1) + (1479239849873/1000000000000 : ℝ)*(major_s1_2) + (1931400303729/1000000000000 : ℝ)*(sp_s1_0) + (1931399780067/1000000000000 : ℝ)*(sp_s1_1) + (386279716371/200000000000 : ℝ)*(sp_s1_2) + (249999831553/250000000000 : ℝ)*(sp_s1_6) + (1931399780067/1000000000000 : ℝ)*(f.sum) + (31967121143429721499/96052175700000000000000000000000 : ℝ)*base63 + (215234673751687/499850000000000000000000000 : ℝ)*base65 + (13221581696581/20016875000000000000000000 : ℝ)*base67 + (597374540111113/2999100000000000000000000000 : ℝ)*base68 + (18992750615310643/794261650000000000000000000000 : ℝ)*base71 + (409672021027/635600000000000000000000 : ℝ)*base73 + (72375555986569/320270000000000000000000000 : ℝ)*base75 + (550311990491/1589000000000000000000000 : ℝ)*base76 + (239485099327829799/508909030000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p001_b032 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 71)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=70 := by omega
  rcases hc with rfl
  · exact collision_c301070 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 71)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b032 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

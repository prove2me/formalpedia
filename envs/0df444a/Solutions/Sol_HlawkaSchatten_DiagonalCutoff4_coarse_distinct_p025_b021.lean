-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b021
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:02:18.126163+00:00
-- url     : https://prove2.me/submissions/04d7b361-855e-4c8c-b8a0-b3a93b0c0638

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
theorem collision_support_c325044_s0_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-704426471/10000000000 : ℝ)*x 0 + (-6483961021/10000000000 : ℝ)*x 1 + (-178937283/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (704426471/10000000000 : ℝ)^87 ≤ (193714890511/5000000000000 : ℝ)^71 := by
    have hnat : (704426471 : ℕ)^87*5000000000000^71 ≤ 193714890511^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704426471 10000000000 193714890511 5000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6483961021/10000000000 : ℝ)^87 ≤ (11761649322401/20000000000000 : ℝ)^71 := by
    have hnat : (6483961021 : ℕ)^87*20000000000000^71 ≤ 11761649322401^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6483961021 10000000000 11761649322401 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (178937283/400000000 : ℝ)^87 ≤ (7463491110763/20000000000000 : ℝ)^71 := by
    have hnat : (178937283 : ℕ)^87*20000000000000^71 ≤ 7463491110763^71*400000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178937283 400000000 7463491110763 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-704426471/10000000000 : ℝ), (-6483961021/10000000000 : ℝ), (-178937283/400000000 : ℝ)] ![(193714890511/5000000000000 : ℝ), (11761649322401/20000000000000 : ℝ), (7463491110763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-704426471/10000000000 : ℝ)|^87 ≤ (193714890511/5000000000000 : ℝ)^71
        have hw : |(-704426471/10000000000 : ℝ)|=(704426471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6483961021/10000000000 : ℝ)|^87 ≤ (11761649322401/20000000000000 : ℝ)^71
        have hw : |(-6483961021/10000000000 : ℝ)|=(6483961021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-178937283/400000000 : ℝ)|^87 ≤ (7463491110763/20000000000000 : ℝ)^71
        have hw : |(-178937283/400000000 : ℝ)|=(178937283/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s0_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (309239279/400000000 : ℝ)*x 0 + (-92140589/400000000 : ℝ)*x 1 + (-1589247163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (309239279/400000000 : ℝ)^87 ≤ (7295383143321/10000000000000 : ℝ)^71 := by
    have hnat : (309239279 : ℕ)^87*10000000000000^71 ≤ 7295383143321^71*400000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309239279 400000000 7295383143321 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92140589/400000000 : ℝ)^87 ≤ (1654643569931/10000000000000 : ℝ)^71 := by
    have hnat : (92140589 : ℕ)^87*10000000000000^71 ≤ 1654643569931^71*400000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92140589 400000000 1654643569931 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1589247163/10000000000 : ℝ)^87 ≤ (10499732851631/100000000000000 : ℝ)^71 := by
    have hnat : (1589247163 : ℕ)^87*100000000000000^71 ≤ 10499732851631^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1589247163 10000000000 10499732851631 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(309239279/400000000 : ℝ), (-92140589/400000000 : ℝ), (-1589247163/10000000000 : ℝ)] ![(7295383143321/10000000000000 : ℝ), (1654643569931/10000000000000 : ℝ), (10499732851631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(309239279/400000000 : ℝ)|^87 ≤ (7295383143321/10000000000000 : ℝ)^71
        have hw : |(309239279/400000000 : ℝ)|=(309239279/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-92140589/400000000 : ℝ)|^87 ≤ (1654643569931/10000000000000 : ℝ)^71
        have hw : |(-92140589/400000000 : ℝ)|=(92140589/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1589247163/10000000000 : ℝ)|^87 ≤ (10499732851631/100000000000000 : ℝ)^71
        have hw : |(-1589247163/10000000000 : ℝ)|=(1589247163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s0_7 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-180012567/2500000000 : ℝ)*x 0 + (-1633985683/2500000000 : ℝ)*x 1 + (-4406424399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (180012567/2500000000 : ℝ)^87 ≤ (3979853749237/100000000000000 : ℝ)^71 := by
    have hnat : (180012567 : ℕ)^87*100000000000000^71 ≤ 3979853749237^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180012567 2500000000 3979853749237 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1633985683/2500000000 : ℝ)^87 ≤ (29693238313419/50000000000000 : ℝ)^71 := by
    have hnat : (1633985683 : ℕ)^87*50000000000000^71 ≤ 29693238313419^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633985683 2500000000 29693238313419 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4406424399/10000000000 : ℝ)^87 ≤ (36633669615361/100000000000000 : ℝ)^71 := by
    have hnat : (4406424399 : ℕ)^87*100000000000000^71 ≤ 36633669615361^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4406424399 10000000000 36633669615361 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-180012567/2500000000 : ℝ), (-1633985683/2500000000 : ℝ), (-4406424399/10000000000 : ℝ)] ![(3979853749237/100000000000000 : ℝ), (29693238313419/50000000000000 : ℝ), (36633669615361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-180012567/2500000000 : ℝ)|^87 ≤ (3979853749237/100000000000000 : ℝ)^71
        have hw : |(-180012567/2500000000 : ℝ)|=(180012567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1633985683/2500000000 : ℝ)|^87 ≤ (29693238313419/50000000000000 : ℝ)^71
        have hw : |(-1633985683/2500000000 : ℝ)|=(1633985683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4406424399/10000000000 : ℝ)|^87 ≤ (36633669615361/100000000000000 : ℝ)^71
        have hw : |(-4406424399/10000000000 : ℝ)|=(4406424399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s0_8 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4978361151/10000000000 : ℝ)*x 0 + (157800063/500000000 : ℝ)*x 1 + (-4058391347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4978361151/10000000000 : ℝ)^87 ≤ (5317826844151/12500000000000 : ℝ)^71 := by
    have hnat : (4978361151 : ℕ)^87*12500000000000^71 ≤ 5317826844151^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4978361151 10000000000 5317826844151 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (157800063/500000000 : ℝ)^87 ≤ (6084244794783/25000000000000 : ℝ)^71 := by
    have hnat : (157800063 : ℕ)^87*25000000000000^71 ≤ 6084244794783^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157800063 500000000 6084244794783 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4058391347/10000000000 : ℝ)^87 ≤ (1324816242087/4000000000000 : ℝ)^71 := by
    have hnat : (4058391347 : ℕ)^87*4000000000000^71 ≤ 1324816242087^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4058391347 10000000000 1324816242087 4000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4978361151/10000000000 : ℝ), (157800063/500000000 : ℝ), (-4058391347/10000000000 : ℝ)] ![(5317826844151/12500000000000 : ℝ), (6084244794783/25000000000000 : ℝ), (1324816242087/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4978361151/10000000000 : ℝ)|^87 ≤ (5317826844151/12500000000000 : ℝ)^71
        have hw : |(4978361151/10000000000 : ℝ)|=(4978361151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(157800063/500000000 : ℝ)|^87 ≤ (6084244794783/25000000000000 : ℝ)^71
        have hw : |(157800063/500000000 : ℝ)|=(157800063/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4058391347/10000000000 : ℝ)|^87 ≤ (1324816242087/4000000000000 : ℝ)^71
        have hw : |(-4058391347/10000000000 : ℝ)|=(4058391347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s0_9 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (311147529/625000000 : ℝ)*x 0 + (-2898801311/10000000000 : ℝ)*x 1 + (429757621/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (311147529/625000000 : ℝ)^87 ≤ (42542607559457/100000000000000 : ℝ)^71 := by
    have hnat : (311147529 : ℕ)^87*100000000000000^71 ≤ 42542607559457^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311147529 625000000 42542607559457 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2898801311/10000000000 : ℝ)^87 ≤ (21929475291319/100000000000000 : ℝ)^71 := by
    have hnat : (2898801311 : ℕ)^87*100000000000000^71 ≤ 21929475291319^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2898801311 10000000000 21929475291319 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429757621/1000000000 : ℝ)^87 ≤ (35527917141733/100000000000000 : ℝ)^71 := by
    have hnat : (429757621 : ℕ)^87*100000000000000^71 ≤ 35527917141733^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429757621 1000000000 35527917141733 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(311147529/625000000 : ℝ), (-2898801311/10000000000 : ℝ), (429757621/1000000000 : ℝ)] ![(42542607559457/100000000000000 : ℝ), (21929475291319/100000000000000 : ℝ), (35527917141733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(311147529/625000000 : ℝ)|^87 ≤ (42542607559457/100000000000000 : ℝ)^71
        have hw : |(311147529/625000000 : ℝ)|=(311147529/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2898801311/10000000000 : ℝ)|^87 ≤ (21929475291319/100000000000000 : ℝ)^71
        have hw : |(-2898801311/10000000000 : ℝ)|=(2898801311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(429757621/1000000000 : ℝ)|^87 ≤ (35527917141733/100000000000000 : ℝ)^71
        have hw : |(429757621/1000000000 : ℝ)|=(429757621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s0_10 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9999999999/10000000000 : ℝ)*x 0 + (13/2000000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9999999999/10000000000 : ℝ)^87 ≤ (99999999987747/100000000000000 : ℝ)^71 := by
    have hnat : (9999999999 : ℕ)^87*100000000000000^71 ≤ 99999999987747^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999999 10000000000 99999999987747 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13/2000000000 : ℝ)^87 ≤ (9289/100000000000000 : ℝ)^71 := by
    have hnat : (13 : ℕ)^87*100000000000000^71 ≤ 9289^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13 2000000000 9289 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^87 ≤ (0 : ℝ)^71 := by
    have hnat : (0 : ℕ)^87*1^71 ≤ 0^71*1^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9999999999/10000000000 : ℝ), (13/2000000000 : ℝ), (0 : ℝ)] ![(99999999987747/100000000000000 : ℝ), (9289/100000000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9999999999/10000000000 : ℝ)|^87 ≤ (99999999987747/100000000000000 : ℝ)^71
        have hw : |(9999999999/10000000000 : ℝ)|=(9999999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13/2000000000 : ℝ)|^87 ≤ (9289/100000000000000 : ℝ)^71
        have hw : |(13/2000000000 : ℝ)|=(13/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^87 ≤ (0 : ℝ)^71
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s0_13 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (971826753/1250000000 : ℝ)*x 0 + (-435820113/2000000000 : ℝ)*x 1 + (-1660959921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (971826753/1250000000 : ℝ)^87 ≤ (18364668406521/25000000000000 : ℝ)^71 := by
    have hnat : (971826753 : ℕ)^87*25000000000000^71 ≤ 18364668406521^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971826753 1250000000 18364668406521 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (435820113/2000000000 : ℝ)^87 ≤ (15458119447223/100000000000000 : ℝ)^71 := by
    have hnat : (435820113 : ℕ)^87*100000000000000^71 ≤ 15458119447223^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435820113 2000000000 15458119447223 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1660959921/10000000000 : ℝ)^87 ≤ (692700431861/6250000000000 : ℝ)^71 := by
    have hnat : (1660959921 : ℕ)^87*6250000000000^71 ≤ 692700431861^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1660959921 10000000000 692700431861 6250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(971826753/1250000000 : ℝ), (-435820113/2000000000 : ℝ), (-1660959921/10000000000 : ℝ)] ![(18364668406521/25000000000000 : ℝ), (15458119447223/100000000000000 : ℝ), (692700431861/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(971826753/1250000000 : ℝ)|^87 ≤ (18364668406521/25000000000000 : ℝ)^71
        have hw : |(971826753/1250000000 : ℝ)|=(971826753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-435820113/2000000000 : ℝ)|^87 ≤ (15458119447223/100000000000000 : ℝ)^71
        have hw : |(-435820113/2000000000 : ℝ)|=(435820113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1660959921/10000000000 : ℝ)|^87 ≤ (692700431861/6250000000000 : ℝ)^71
        have hw : |(-1660959921/10000000000 : ℝ)|=(1660959921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s0_14 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-70780833/2500000000 : ℝ)*x 0 + (-6534669041/10000000000 : ℝ)*x 1 + (-1168059339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (70780833/2500000000 : ℝ)^87 ≤ (317004271431/25000000000000 : ℝ)^71 := by
    have hnat : (70780833 : ℕ)^87*25000000000000^71 ≤ 317004271431^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70780833 2500000000 317004271431 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6534669041/10000000000 : ℝ)^87 ≤ (59372296021557/100000000000000 : ℝ)^71 := by
    have hnat : (6534669041 : ℕ)^87*100000000000000^71 ≤ 59372296021557^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6534669041 10000000000 59372296021557 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1168059339/2500000000 : ℝ)^87 ≤ (39359686884533/100000000000000 : ℝ)^71 := by
    have hnat : (1168059339 : ℕ)^87*100000000000000^71 ≤ 39359686884533^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168059339 2500000000 39359686884533 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-70780833/2500000000 : ℝ), (-6534669041/10000000000 : ℝ), (-1168059339/2500000000 : ℝ)] ![(317004271431/25000000000000 : ℝ), (59372296021557/100000000000000 : ℝ), (39359686884533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-70780833/2500000000 : ℝ)|^87 ≤ (317004271431/25000000000000 : ℝ)^71
        have hw : |(-70780833/2500000000 : ℝ)|=(70780833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6534669041/10000000000 : ℝ)|^87 ≤ (59372296021557/100000000000000 : ℝ)^71
        have hw : |(-6534669041/10000000000 : ℝ)|=(6534669041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1168059339/2500000000 : ℝ)|^87 ≤ (39359686884533/100000000000000 : ℝ)^71
        have hw : |(-1168059339/2500000000 : ℝ)|=(1168059339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s0_15 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1191101611/2500000000 : ℝ)*x 0 + (771959837/2500000000 : ℝ)*x 1 + (-868672813/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1191101611/2500000000 : ℝ)^87 ≤ (5039151552411/12500000000000 : ℝ)^71 := by
    have hnat : (1191101611 : ℕ)^87*12500000000000^71 ≤ 5039151552411^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191101611 2500000000 5039151552411 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (771959837/2500000000 : ℝ)^87 ≤ (23694486698137/100000000000000 : ℝ)^71 := by
    have hnat : (771959837 : ℕ)^87*100000000000000^71 ≤ 23694486698137^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771959837 2500000000 23694486698137 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (868672813/2000000000 : ℝ)^87 ≤ (8998075216593/25000000000000 : ℝ)^71 := by
    have hnat : (868672813 : ℕ)^87*25000000000000^71 ≤ 8998075216593^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868672813 2000000000 8998075216593 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1191101611/2500000000 : ℝ), (771959837/2500000000 : ℝ), (-868672813/2000000000 : ℝ)] ![(5039151552411/12500000000000 : ℝ), (23694486698137/100000000000000 : ℝ), (8998075216593/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1191101611/2500000000 : ℝ)|^87 ≤ (5039151552411/12500000000000 : ℝ)^71
        have hw : |(1191101611/2500000000 : ℝ)|=(1191101611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(771959837/2500000000 : ℝ)|^87 ≤ (23694486698137/100000000000000 : ℝ)^71
        have hw : |(771959837/2500000000 : ℝ)|=(771959837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-868672813/2000000000 : ℝ)|^87 ≤ (8998075216593/25000000000000 : ℝ)^71
        have hw : |(-868672813/2000000000 : ℝ)|=(868672813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s0_16 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2722746021/5000000000 : ℝ)*x 0 + (-1390775673/5000000000 : ℝ)*x 1 + (782507689/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2722746021/5000000000 : ℝ)^87 ≤ (47484572973143/100000000000000 : ℝ)^71 := by
    have hnat : (2722746021 : ℕ)^87*100000000000000^71 ≤ 47484572973143^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722746021 5000000000 47484572973143 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1390775673/5000000000 : ℝ)^87 ≤ (10423798444917/50000000000000 : ℝ)^71 := by
    have hnat : (1390775673 : ℕ)^87*50000000000000^71 ≤ 10423798444917^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390775673 5000000000 10423798444917 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (782507689/2000000000 : ℝ)^87 ≤ (31667830122207/100000000000000 : ℝ)^71 := by
    have hnat : (782507689 : ℕ)^87*100000000000000^71 ≤ 31667830122207^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782507689 2000000000 31667830122207 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2722746021/5000000000 : ℝ), (-1390775673/5000000000 : ℝ), (782507689/2000000000 : ℝ)] ![(47484572973143/100000000000000 : ℝ), (10423798444917/50000000000000 : ℝ), (31667830122207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2722746021/5000000000 : ℝ)|^87 ≤ (47484572973143/100000000000000 : ℝ)^71
        have hw : |(2722746021/5000000000 : ℝ)|=(2722746021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1390775673/5000000000 : ℝ)|^87 ≤ (10423798444917/50000000000000 : ℝ)^71
        have hw : |(-1390775673/5000000000 : ℝ)|=(1390775673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(782507689/2000000000 : ℝ)|^87 ≤ (31667830122207/100000000000000 : ℝ)^71
        have hw : |(782507689/2000000000 : ℝ)|=(782507689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s0_19 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4255837829/5000000000 : ℝ)*x 0 + (-1623220343/10000000000 : ℝ)*x 1 + (-9284719/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4255837829/5000000000 : ℝ)^87 ≤ (8208122201957/10000000000000 : ℝ)^71 := by
    have hnat : (4255837829 : ℕ)^87*10000000000000^71 ≤ 8208122201957^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255837829 5000000000 8208122201957 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1623220343/10000000000 : ℝ)^87 ≤ (2693856030451/25000000000000 : ℝ)^71 := by
    have hnat : (1623220343 : ℕ)^87*25000000000000^71 ≤ 2693856030451^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1623220343 10000000000 2693856030451 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9284719/80000000 : ℝ)^87 ≤ (285734154163/4000000000000 : ℝ)^71 := by
    have hnat : (9284719 : ℕ)^87*4000000000000^71 ≤ 285734154163^71*80000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9284719 80000000 285734154163 4000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4255837829/5000000000 : ℝ), (-1623220343/10000000000 : ℝ), (-9284719/80000000 : ℝ)] ![(8208122201957/10000000000000 : ℝ), (2693856030451/25000000000000 : ℝ), (285734154163/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4255837829/5000000000 : ℝ)|^87 ≤ (8208122201957/10000000000000 : ℝ)^71
        have hw : |(4255837829/5000000000 : ℝ)|=(4255837829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1623220343/10000000000 : ℝ)|^87 ≤ (2693856030451/25000000000000 : ℝ)^71
        have hw : |(-1623220343/10000000000 : ℝ)|=(1623220343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9284719/80000000 : ℝ)|^87 ≤ (285734154163/4000000000000 : ℝ)^71
        have hw : |(-9284719/80000000 : ℝ)|=(9284719/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s0_20 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-277308537/10000000000 : ℝ)*x 0 + (-26174609/39062500 : ℝ)*x 1 + (-4494977153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277308537/10000000000 : ℝ)^87 ≤ (618090004621/50000000000000 : ℝ)^71 := by
    have hnat : (277308537 : ℕ)^87*50000000000000^71 ≤ 618090004621^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277308537 10000000000 618090004621 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26174609/39062500 : ℝ)^87 ≤ (1530650329697/2500000000000 : ℝ)^71 := by
    have hnat : (26174609 : ℕ)^87*2500000000000^71 ≤ 1530650329697^71*39062500^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26174609 39062500 1530650329697 2500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494977153/10000000000 : ℝ)^87 ≤ (37537806781987/100000000000000 : ℝ)^71 := by
    have hnat : (4494977153 : ℕ)^87*100000000000000^71 ≤ 37537806781987^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494977153 10000000000 37537806781987 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-277308537/10000000000 : ℝ), (-26174609/39062500 : ℝ), (-4494977153/10000000000 : ℝ)] ![(618090004621/50000000000000 : ℝ), (1530650329697/2500000000000 : ℝ), (37537806781987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-277308537/10000000000 : ℝ)|^87 ≤ (618090004621/50000000000000 : ℝ)^71
        have hw : |(-277308537/10000000000 : ℝ)|=(277308537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26174609/39062500 : ℝ)|^87 ≤ (1530650329697/2500000000000 : ℝ)^71
        have hw : |(-26174609/39062500 : ℝ)|=(26174609/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4494977153/10000000000 : ℝ)|^87 ≤ (37537806781987/100000000000000 : ℝ)^71
        have hw : |(-4494977153/10000000000 : ℝ)|=(4494977153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s0_21 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1362826699/2500000000 : ℝ)*x 0 + (1434683657/5000000000 : ℝ)*x 1 + (-152977767/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1362826699/2500000000 : ℝ)^87 ≤ (4754671134853/10000000000000 : ℝ)^71 := by
    have hnat : (1362826699 : ℕ)^87*10000000000000^71 ≤ 4754671134853^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362826699 2500000000 4754671134853 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1434683657/5000000000 : ℝ)^87 ≤ (4331388160753/20000000000000 : ℝ)^71 := by
    have hnat : (1434683657 : ℕ)^87*20000000000000^71 ≤ 4331388160753^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1434683657 5000000000 4331388160753 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (152977767/400000000 : ℝ)^87 ≤ (15398173921311/50000000000000 : ℝ)^71 := by
    have hnat : (152977767 : ℕ)^87*50000000000000^71 ≤ 15398173921311^71*400000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152977767 400000000 15398173921311 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1362826699/2500000000 : ℝ), (1434683657/5000000000 : ℝ), (-152977767/400000000 : ℝ)] ![(4754671134853/10000000000000 : ℝ), (4331388160753/20000000000000 : ℝ), (15398173921311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1362826699/2500000000 : ℝ)|^87 ≤ (4754671134853/10000000000000 : ℝ)^71
        have hw : |(1362826699/2500000000 : ℝ)|=(1362826699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1434683657/5000000000 : ℝ)|^87 ≤ (4331388160753/20000000000000 : ℝ)^71
        have hw : |(1434683657/5000000000 : ℝ)|=(1434683657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-152977767/400000000 : ℝ)|^87 ≤ (15398173921311/50000000000000 : ℝ)^71
        have hw : |(-152977767/400000000 : ℝ)|=(152977767/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s0_22 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2385483671/5000000000 : ℝ)*x 0 + (-318543799/1000000000 : ℝ)*x 1 + (4245719851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2385483671/5000000000 : ℝ)^87 ≤ (40381247068579/100000000000000 : ℝ)^71 := by
    have hnat : (2385483671 : ℕ)^87*100000000000000^71 ≤ 40381247068579^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2385483671 5000000000 40381247068579 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (318543799/1000000000 : ℝ)^87 ≤ (12307710691187/50000000000000 : ℝ)^71 := by
    have hnat : (318543799 : ℕ)^87*50000000000000^71 ≤ 12307710691187^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318543799 1000000000 12307710691187 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4245719851/10000000000 : ℝ)^87 ≤ (35003331541179/100000000000000 : ℝ)^71 := by
    have hnat : (4245719851 : ℕ)^87*100000000000000^71 ≤ 35003331541179^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245719851 10000000000 35003331541179 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2385483671/5000000000 : ℝ), (-318543799/1000000000 : ℝ), (4245719851/10000000000 : ℝ)] ![(40381247068579/100000000000000 : ℝ), (12307710691187/50000000000000 : ℝ), (35003331541179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2385483671/5000000000 : ℝ)|^87 ≤ (40381247068579/100000000000000 : ℝ)^71
        have hw : |(2385483671/5000000000 : ℝ)|=(2385483671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-318543799/1000000000 : ℝ)|^87 ≤ (12307710691187/50000000000000 : ℝ)^71
        have hw : |(-318543799/1000000000 : ℝ)|=(318543799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4245719851/10000000000 : ℝ)|^87 ≤ (35003331541179/100000000000000 : ℝ)^71
        have hw : |(4245719851/10000000000 : ℝ)|=(4245719851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s0_25 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1698373989/2000000000 : ℝ)*x 0 + (-336347103/2000000000 : ℝ)*x 1 + (-564072621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1698373989/2000000000 : ℝ)^87 ≤ (1023090609779/1250000000000 : ℝ)^71 := by
    have hnat : (1698373989 : ℕ)^87*1250000000000^71 ≤ 1023090609779^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1698373989 2000000000 1023090609779 1250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336347103/2000000000 : ℝ)^87 ≤ (1406664637503/12500000000000 : ℝ)^71 := by
    have hnat : (336347103 : ℕ)^87*12500000000000^71 ≤ 1406664637503^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336347103 2000000000 1406664637503 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564072621/5000000000 : ℝ)^87 ≤ (6899434093259/100000000000000 : ℝ)^71 := by
    have hnat : (564072621 : ℕ)^87*100000000000000^71 ≤ 6899434093259^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564072621 5000000000 6899434093259 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1698373989/2000000000 : ℝ), (-336347103/2000000000 : ℝ), (-564072621/5000000000 : ℝ)] ![(1023090609779/1250000000000 : ℝ), (1406664637503/12500000000000 : ℝ), (6899434093259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1698373989/2000000000 : ℝ)|^87 ≤ (1023090609779/1250000000000 : ℝ)^71
        have hw : |(1698373989/2000000000 : ℝ)|=(1698373989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-336347103/2000000000 : ℝ)|^87 ≤ (1406664637503/12500000000000 : ℝ)^71
        have hw : |(-336347103/2000000000 : ℝ)|=(336347103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-564072621/5000000000 : ℝ)|^87 ≤ (6899434093259/100000000000000 : ℝ)^71
        have hw : |(-564072621/5000000000 : ℝ)|=(564072621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s1_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2048743047/10000000000 : ℝ)*x 0 + (-563507573/1000000000 : ℝ)*x 1 + (-2179399067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2048743047/10000000000 : ℝ)^87 ≤ (7166378610853/50000000000000 : ℝ)^71 := by
    have hnat : (2048743047 : ℕ)^87*50000000000000^71 ≤ 7166378610853^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048743047 10000000000 7166378610853 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563507573/1000000000 : ℝ)^87 ≤ (49518159100979/100000000000000 : ℝ)^71 := by
    have hnat : (563507573 : ℕ)^87*100000000000000^71 ≤ 49518159100979^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563507573 1000000000 49518159100979 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2179399067/5000000000 : ℝ)^87 ≤ (36149083664899/100000000000000 : ℝ)^71 := by
    have hnat : (2179399067 : ℕ)^87*100000000000000^71 ≤ 36149083664899^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179399067 5000000000 36149083664899 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2048743047/10000000000 : ℝ), (-563507573/1000000000 : ℝ), (-2179399067/5000000000 : ℝ)] ![(7166378610853/50000000000000 : ℝ), (49518159100979/100000000000000 : ℝ), (36149083664899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2048743047/10000000000 : ℝ)|^87 ≤ (7166378610853/50000000000000 : ℝ)^71
        have hw : |(-2048743047/10000000000 : ℝ)|=(2048743047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-563507573/1000000000 : ℝ)|^87 ≤ (49518159100979/100000000000000 : ℝ)^71
        have hw : |(-563507573/1000000000 : ℝ)|=(563507573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2179399067/5000000000 : ℝ)|^87 ≤ (36149083664899/100000000000000 : ℝ)^71
        have hw : |(-2179399067/5000000000 : ℝ)|=(2179399067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s1_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (470022183/1000000000 : ℝ)*x 0 + (3374350377/10000000000 : ℝ)*x 1 + (-4139693701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (470022183/1000000000 : ℝ)^87 ≤ (39648753098153/100000000000000 : ℝ)^71 := by
    have hnat : (470022183 : ℕ)^87*100000000000000^71 ≤ 39648753098153^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470022183 1000000000 39648753098153 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3374350377/10000000000 : ℝ)^87 ≤ (6603996641459/25000000000000 : ℝ)^71 := by
    have hnat : (3374350377 : ℕ)^87*25000000000000^71 ≤ 6603996641459^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3374350377 10000000000 6603996641459 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4139693701/10000000000 : ℝ)^87 ≤ (3393526032509/10000000000000 : ℝ)^71 := by
    have hnat : (4139693701 : ℕ)^87*10000000000000^71 ≤ 3393526032509^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139693701 10000000000 3393526032509 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(470022183/1000000000 : ℝ), (3374350377/10000000000 : ℝ), (-4139693701/10000000000 : ℝ)] ![(39648753098153/100000000000000 : ℝ), (6603996641459/25000000000000 : ℝ), (3393526032509/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(470022183/1000000000 : ℝ)|^87 ≤ (39648753098153/100000000000000 : ℝ)^71
        have hw : |(470022183/1000000000 : ℝ)|=(470022183/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3374350377/10000000000 : ℝ)|^87 ≤ (6603996641459/25000000000000 : ℝ)^71
        have hw : |(3374350377/10000000000 : ℝ)|=(3374350377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4139693701/10000000000 : ℝ)|^87 ≤ (3393526032509/10000000000000 : ℝ)^71
        have hw : |(-4139693701/10000000000 : ℝ)|=(4139693701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s1_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (587504947/1250000000 : ℝ)*x 0 + (-674887267/2000000000 : ℝ)*x 1 + (1034949789/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (587504947/1250000000 : ℝ)^87 ≤ (396468692441/1000000000000 : ℝ)^71 := by
    have hnat : (587504947 : ℕ)^87*1000000000000^71 ≤ 396468692441^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587504947 1250000000 396468692441 1000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674887267/2000000000 : ℝ)^87 ≤ (5283362226249/20000000000000 : ℝ)^71 := by
    have hnat : (674887267 : ℕ)^87*20000000000000^71 ≤ 5283362226249^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674887267 2000000000 5283362226249 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034949789/2500000000 : ℝ)^87 ≤ (33936319608823/100000000000000 : ℝ)^71 := by
    have hnat : (1034949789 : ℕ)^87*100000000000000^71 ≤ 33936319608823^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034949789 2500000000 33936319608823 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(587504947/1250000000 : ℝ), (-674887267/2000000000 : ℝ), (1034949789/2500000000 : ℝ)] ![(396468692441/1000000000000 : ℝ), (5283362226249/20000000000000 : ℝ), (33936319608823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(587504947/1250000000 : ℝ)|^87 ≤ (396468692441/1000000000000 : ℝ)^71
        have hw : |(587504947/1250000000 : ℝ)|=(587504947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-674887267/2000000000 : ℝ)|^87 ≤ (5283362226249/20000000000000 : ℝ)^71
        have hw : |(-674887267/2000000000 : ℝ)|=(674887267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034949789/2500000000 : ℝ)|^87 ≤ (33936319608823/100000000000000 : ℝ)^71
        have hw : |(1034949789/2500000000 : ℝ)|=(1034949789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325044_s1_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6123789327/10000000000 : ℝ)*x 0 + (-3342323689/10000000000 : ℝ)*x 1 + (-1292663573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6123789327/10000000000 : ℝ)^87 ≤ (5483082784483/10000000000000 : ℝ)^71 := by
    have hnat : (6123789327 : ℕ)^87*10000000000000^71 ≤ 5483082784483^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6123789327 10000000000 5483082784483 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3342323689/10000000000 : ℝ)^87 ≤ (26109095849723/100000000000000 : ℝ)^71 := by
    have hnat : (3342323689 : ℕ)^87*100000000000000^71 ≤ 26109095849723^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3342323689 10000000000 26109095849723 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1292663573/5000000000 : ℝ)^87 ≤ (4765019071187/25000000000000 : ℝ)^71 := by
    have hnat : (1292663573 : ℕ)^87*25000000000000^71 ≤ 4765019071187^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292663573 5000000000 4765019071187 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6123789327/10000000000 : ℝ), (-3342323689/10000000000 : ℝ), (-1292663573/5000000000 : ℝ)] ![(5483082784483/10000000000000 : ℝ), (26109095849723/100000000000000 : ℝ), (4765019071187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6123789327/10000000000 : ℝ)|^87 ≤ (5483082784483/10000000000000 : ℝ)^71
        have hw : |(6123789327/10000000000 : ℝ)|=(6123789327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3342323689/10000000000 : ℝ)|^87 ≤ (26109095849723/100000000000000 : ℝ)^71
        have hw : |(-3342323689/10000000000 : ℝ)|=(3342323689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1292663573/5000000000 : ℝ)|^87 ≤ (4765019071187/25000000000000 : ℝ)^71
        have hw : |(-1292663573/5000000000 : ℝ)|=(1292663573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325044 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]]) : False := by
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
  have main2 : (81317/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81317/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 0 (by
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 1 (by
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-704426471/10000000000 : ℝ)*X 0 0+(-6483961021/10000000000 : ℝ)*X 0 1+(-178937283/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((309239279/400000000 : ℝ)*X 0 0+(-92140589/400000000 : ℝ)*X 0 1+(-1589247163/10000000000 : ℝ)*X 0 2+(309239279/400000000 : ℝ)*X 1 0+(-92140589/400000000 : ℝ)*X 1 1+(-1589247163/10000000000 : ℝ)*X 1 2+(309239279/400000000 : ℝ)*X 2 0+(-92140589/400000000 : ℝ)*X 2 1+(-1589247163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-180012567/2500000000 : ℝ)*X 0 0+(-1633985683/2500000000 : ℝ)*X 0 1+(-4406424399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4978361151/10000000000 : ℝ)*X 1 0+(157800063/500000000 : ℝ)*X 1 1+(-4058391347/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((311147529/625000000 : ℝ)*X 2 0+(-2898801311/10000000000 : ℝ)*X 2 1+(429757621/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_10 : ((9999999999/10000000000 : ℝ)*X 1 0+(13/2000000000 : ℝ)*X 1 1+(9999999999/10000000000 : ℝ)*X 2 0+(13/2000000000 : ℝ)*X 2 1+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s0_10 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((971826753/1250000000 : ℝ)*X 0 0+(-435820113/2000000000 : ℝ)*X 0 1+(-1660959921/10000000000 : ℝ)*X 0 2+(971826753/1250000000 : ℝ)*X 1 0+(-435820113/2000000000 : ℝ)*X 1 1+(-1660959921/10000000000 : ℝ)*X 1 2+(971826753/1250000000 : ℝ)*X 2 0+(-435820113/2000000000 : ℝ)*X 2 1+(-1660959921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-70780833/2500000000 : ℝ)*X 0 0+(-6534669041/10000000000 : ℝ)*X 0 1+(-1168059339/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1191101611/2500000000 : ℝ)*X 1 0+(771959837/2500000000 : ℝ)*X 1 1+(-868672813/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((2722746021/5000000000 : ℝ)*X 2 0+(-1390775673/5000000000 : ℝ)*X 2 1+(782507689/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((4255837829/5000000000 : ℝ)*X 0 0+(-1623220343/10000000000 : ℝ)*X 0 1+(-9284719/80000000 : ℝ)*X 0 2+(4255837829/5000000000 : ℝ)*X 1 0+(-1623220343/10000000000 : ℝ)*X 1 1+(-9284719/80000000 : ℝ)*X 1 2+(4255837829/5000000000 : ℝ)*X 2 0+(-1623220343/10000000000 : ℝ)*X 2 1+(-9284719/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-277308537/10000000000 : ℝ)*X 0 0+(-26174609/39062500 : ℝ)*X 0 1+(-4494977153/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((1362826699/2500000000 : ℝ)*X 1 0+(1434683657/5000000000 : ℝ)*X 1 1+(-152977767/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2385483671/5000000000 : ℝ)*X 2 0+(-318543799/1000000000 : ℝ)*X 2 1+(4245719851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((1698373989/2000000000 : ℝ)*X 0 0+(-336347103/2000000000 : ℝ)*X 0 1+(-564072621/5000000000 : ℝ)*X 0 2+(1698373989/2000000000 : ℝ)*X 1 0+(-336347103/2000000000 : ℝ)*X 1 1+(-564072621/5000000000 : ℝ)*X 1 2+(1698373989/2000000000 : ℝ)*X 2 0+(-336347103/2000000000 : ℝ)*X 2 1+(-564072621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((717/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(717/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24682046865597547068621/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (343037456411/500000000000 : ℝ)*(base39) + (52097194951/100000000000 : ℝ)*(base49) + (1578863645003/500000000000 : ℝ)*(major_s0_0) + (1578863645003/500000000000 : ℝ)*(major_s0_1) + (1578863645003/500000000000 : ℝ)*(major_s0_2) + (130582423/200000000000 : ℝ)*(sp_s0_0) + (595473149/1000000000000 : ℝ)*(sp_s0_6) + (4743283611049/1000000000000 : ℝ)*(sp_s0_7) + (2371854638959/500000000000 : ℝ)*(sp_s0_8) + (4743716981697/1000000000000 : ℝ)*(sp_s0_9) + (314178009467/200000000000 : ℝ)*(sp_s0_13) + (63299931/250000000000 : ℝ)*(sp_s0_15) + (12977239/500000000000 : ℝ)*(sp_s0_20) + (49099189/200000000000 : ℝ)*(sp_s0_22) + (392871380121/250000000000 : ℝ)*(f.failure) + (2371981238821/500000000000 : ℝ)*(f.sum) + (501537057268793/2500000000000000000000000000 : ℝ)*base63 + (2877735388250493/5000000000000000000000000000 : ℝ)*base64 + (2027039698249507/5000000000000000000000000000 : ℝ)*base66 + (3203569195768793/5000000000000000000000000000 : ℝ)*base69 + (3618829885183/50000000000000000000000000 : ℝ)*base71 + (849950050249507/5000000000000000000000000000 : ℝ)*base72 + (3170133933768793/5000000000000000000000000000 : ℝ)*base75 + (2012571301231207/5000000000000000000000000000 : ℝ)*base76 + (1146123300000493/2500000000000000000000000000 : ℝ)*base79 + (16381/25000000000000000 : ℝ)*base86 + (16381/25000000000000000 : ℝ)*base88 + (16381/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3403/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-3403/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (101586592238252984391/12500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5213742688479/1000000000000 : ℝ)*(base39) + (1632678882961/500000000000 : ℝ)*(base40) + (1465510779693/1000000000000 : ℝ)*(base49) + (4886647931677/500000000000 : ℝ)*(major_s0_0) + (4886647931677/500000000000 : ℝ)*(major_s0_1) + (4886647931677/500000000000 : ℝ)*(major_s0_2) + (208315033/500000000000 : ℝ)*(sp_s0_0) + (42816567/125000000000 : ℝ)*(sp_s0_9) + (37395577/500000000000 : ℝ)*(sp_s0_13) + (7341180027443/500000000000 : ℝ)*(sp_s0_14) + (91766738007/6250000000 : ℝ)*(sp_s0_15) + (458826067263/31250000000 : ℝ)*(sp_s0_16) + (4863737541621/1000000000000 : ℝ)*(sp_s0_19) + (12325479/125000000000 : ℝ)*(sp_s0_21) + (194552493311/40000000000 : ℝ)*(f.failure) + (1835347085619/125000000000 : ℝ)*(f.sum) + (668515164619713/2500000000000000000000000000 : ℝ)*base62 + (2832784171349413/5000000000000000000000000000 : ℝ)*base65 + (1105592978650587/5000000000000000000000000000 : ℝ)*base67 + (3536300578619713/5000000000000000000000000000 : ℝ)*base68 + (20087233342703/50000000000000000000000000 : ℝ)*base70 + (5832964495650587/5000000000000000000000000000 : ℝ)*base73 + (3547875890619713/5000000000000000000000000000 : ℝ)*base74 + (278094176880287/5000000000000000000000000000 : ℝ)*base77 + (884641823400587/2500000000000000000000000000 : ℝ)*base79 + (3029/4000000000000000 : ℝ)*base87 + (3029/4000000000000000 : ℝ)*base89 + (3029/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6867/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-6867/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1558708776130573514781/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (7984073/1000000000000 : ℝ)*(base10) + (140383944059/250000000000 : ℝ)*(base39) + (1468753409687/1000000000000 : ℝ)*(base49) + (1920632433827/62500000000 : ℝ)*(major_s0_0) + (1222977712679/125000000000 : ℝ)*(major_s0_1) + (1222977712679/125000000000 : ℝ)*(major_s0_2) + (83775827/1000000000000 : ℝ)*(sp_s0_7) + (3267787/62500000000 : ℝ)*(sp_s0_8) + (20946297239799/1000000000000 : ℝ)*(sp_s0_10) + (9938509/1000000000000 : ℝ)*(sp_s0_16) + (14698499322457/1000000000000 : ℝ)*(sp_s0_20) + (2939707759553/200000000000 : ℝ)*(sp_s0_21) + (1837322642981/125000000000 : ℝ)*(sp_s0_22) + (4869050657877/1000000000000 : ℝ)*(sp_s0_25) + (4869050657877/1000000000000 : ℝ)*(f.failure) + (14698591082357/1000000000000 : ℝ)*(f.sum) + (186280579507149/625000000000000000000000000 : ℝ)*base63 + (287568438709751/1250000000000000000000000000 : ℝ)*base65 + (261142095665249/1250000000000000000000000000 : ℝ)*base67 + (1214398899757149/1250000000000000000000000000 : ℝ)*base69 + (469494407589/10000000000000000000000000 : ℝ)*base71 + (327857497899737/625000000000000000000000000 : ℝ)*base73 + (1232116267007149/1250000000000000000000000000 : ℝ)*base75 + (215952488056937/625000000000000000000000000 : ℝ)*base77 + (24169768964723/1250000000000000000000000000 : ℝ)*base79 + (153497/100000000000000000 : ℝ)*base86 + (53497/100000000000000000 : ℝ)*base88 + (53497/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (717/50000 : ℝ) ^ (85/16 : ℝ) ≤ (8047062433/50000000000000000000 : ℝ) := by
    have hpowers : (717/50000 : ℝ)^85 ≤ (8047062433/50000000000000000000 : ℝ)^16 := by
      have hnat : (717 : ℕ)^85*50000000000000000000^16 ≤ 8047062433^16*50000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        717 50000 8047062433 50000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (717/50000 : ℝ)) (X := (8047062433/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50000000008047062433/50000000000000000000 : ℝ) ≤ (10000000000302949/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (50000000008047062433/50000000000000000000 : ℝ)^16 ≤ (10000000000302949/10000000000000000 : ℝ)^85 := by
      have hnat : (50000000008047062433 : ℕ)^16*10000000000000000^85 ≤ 10000000000302949^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000008047062433 50000000000000000000 10000000000302949 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000302949/10000000000000000 : ℝ)) (X := (50000000008047062433/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25000000008047062433/25000000000000000000 : ℝ) ≤ (10000000000605897/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (25000000008047062433/25000000000000000000 : ℝ)^16 ≤ (10000000000605897/10000000000000000 : ℝ)^85 := by
      have hnat : (25000000008047062433 : ℕ)^16*10000000000000000^85 ≤ 10000000000605897^85*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000008047062433 25000000000000000000 10000000000605897 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000605897/10000000000000000 : ℝ)) (X := (25000000008047062433/25000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(100983/47800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(75737/35850000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (717/50000 : ℝ)) (alpha := (100983/47800000000000 : ℝ)) (beta := (75737/35850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (717/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(100983/47800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(75737/35850000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (3403/12500 : ℝ) ^ (85/16 : ℝ) ≤ (24895575443672607/25000000000000000000 : ℝ) := by
    have hpowers : (3403/12500 : ℝ)^85 ≤ (24895575443672607/25000000000000000000 : ℝ)^16 := by
      have hnat : (3403 : ℕ)^85*25000000000000000000^16 ≤ 24895575443672607^16*12500^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3403 12500 24895575443672607 25000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3403/12500 : ℝ)) (X := (24895575443672607/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25024895575443672607/25000000000000000000 : ℝ) ≤ (10001873733197049/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (25024895575443672607/25000000000000000000 : ℝ)^16 ≤ (10001873733197049/10000000000000000 : ℝ)^85 := by
      have hnat : (25024895575443672607 : ℕ)^16*10000000000000000^85 ≤ 10001873733197049^85*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25024895575443672607 25000000000000000000 10001873733197049 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001873733197049/10000000000000000 : ℝ)) (X := (25024895575443672607/25000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12524895575443672607/12500000000000000000 : ℝ) ≤ (2500936488458567/2500000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (12524895575443672607/12500000000000000000 : ℝ)^16 ≤ (2500936488458567/2500000000000000 : ℝ)^85 := by
      have hnat : (12524895575443672607 : ℕ)^16*2500000000000000^85 ≤ 2500936488458567^85*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12524895575443672607 12500000000000000000 2500936488458567 2500000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500936488458567/2500000000000000 : ℝ)) (X := (12524895575443672607/12500000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1873733197049/2722400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1872220637219/2722400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (3403/12500 : ℝ)) (alpha := (1873733197049/2722400000000000 : ℝ)) (beta := (1872220637219/2722400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (3403/12500 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1873733197049/2722400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1872220637219/2722400000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (6867/25000 : ℝ) ^ (85/16 : ℝ) ≤ (104416382544561053/100000000000000000000 : ℝ) := by
    have hpowers : (6867/25000 : ℝ)^85 ≤ (104416382544561053/100000000000000000000 : ℝ)^16 := by
      have hnat : (6867 : ℕ)^85*100000000000000000000^16 ≤ 104416382544561053^16*25000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6867 25000 104416382544561053 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6867/25000 : ℝ)) (X := (104416382544561053/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100104416382544561053/100000000000000000000 : ℝ) ≤ (2000392930477047/2000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (100104416382544561053/100000000000000000000 : ℝ)^16 ≤ (2000392930477047/2000000000000000 : ℝ)^85 := by
      have hnat : (100104416382544561053 : ℕ)^16*2000000000000000^85 ≤ 2000392930477047^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100104416382544561053 100000000000000000000 2000392930477047 2000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000392930477047/2000000000000000 : ℝ)) (X := (100104416382544561053/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50104416382544561053/50000000000000000000 : ℝ) ≤ (2500981910485407/2500000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (50104416382544561053/50000000000000000000 : ℝ)^16 ≤ (2500981910485407/2500000000000000 : ℝ)^85 := by
      have hnat : (50104416382544561053 : ℕ)^16*2500000000000000^85 ≤ 2500981910485407^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50104416382544561053 50000000000000000000 2500981910485407 2500000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500981910485407/2500000000000000 : ℝ)) (X := (50104416382544561053/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(392930477047/549360000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(654329852131/915600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (6867/25000 : ℝ)) (alpha := (392930477047/549360000000000 : ℝ)) (beta := (654329852131/915600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (6867/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(392930477047/549360000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(654329852131/915600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2048743047/10000000000 : ℝ)*X 0 0+(-563507573/1000000000 : ℝ)*X 0 1+(-2179399067/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((470022183/1000000000 : ℝ)*X 1 0+(3374350377/10000000000 : ℝ)*X 1 1+(-4139693701/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((587504947/1250000000 : ℝ)*X 2 0+(-674887267/2000000000 : ℝ)*X 2 1+(1034949789/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6123789327/10000000000 : ℝ)*X 0 0+(-3342323689/10000000000 : ℝ)*X 0 1+(-1292663573/5000000000 : ℝ)*X 0 2+(6123789327/10000000000 : ℝ)*X 1 0+(-3342323689/10000000000 : ℝ)*X 1 1+(-1292663573/5000000000 : ℝ)*X 1 2+(6123789327/10000000000 : ℝ)*X 2 0+(-3342323689/10000000000 : ℝ)*X 2 1+(-1292663573/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325044_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-452817/50000 : ℝ) < ((-200939/100000 : ℝ)*P 0+(-200939/100000 : ℝ)*P 1+(-200939/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-452817/50000 : ℝ) < (-415427232455773860907125253460879/46542065325000000000000000000000 : ℝ) := by norm_num
    linear_combination (1027/1000000000000 : ℝ)*(base8) + (273/500000000000 : ℝ)*(base33) + (59517486517/50000000000 : ℝ)*(base39) + (134233568117/200000000000 : ℝ)*(base40) + (14144071291/31250000000 : ℝ)*(base49) + (107/200000000000 : ℝ)*(base59) + (502347500101/250000000000 : ℝ)*(major_s1_0) + (200939/100000 : ℝ)*(major_s1_1) + (200939/100000 : ℝ)*(major_s1_2) + (1487640729353/500000000000 : ℝ)*(sp_s1_0) + (74382036457/25000000000 : ℝ)*(sp_s1_1) + (743820364559/250000000000 : ℝ)*(sp_s1_2) + (1000000000951/1000000000000 : ℝ)*(sp_s1_6) + (1487640729391/500000000000 : ℝ)*(f.sum) + (15423493447867159/46736802000000000000000000000 : ℝ)*base62 + (2916801103891/22890000000000000000000000 : ℝ)*base65 + (428715011327/680600000000000000000000 : ℝ)*base67 + (3101826751372859/68670000000000000000000000 : ℝ)*base68 + (93089249193427/1709596875000000000000000000 : ℝ)*base71 + (5363345449729/17925000000000000000000000 : ℝ)*base73 + (24977430922939/34030000000000000000000000 : ℝ)*base74 + (767504122897/2987500000000000000000000 : ℝ)*base77 + (39538578965919547/60998775000000000000000000000 : ℝ)*base79 + (951/1000000000000 : ℝ)*base81 + (11/250000000000 : ℝ)*base83 + (19/20000000000 : ℝ)*base86 + (951/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p025_b021 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 44 ≤ c.val) (hhi : c.val < 45)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=44 := by omega
  rcases hc with rfl
  · exact collision_c325044 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 44 ≤ c.val) (hhi : c.val < 45)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b021 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

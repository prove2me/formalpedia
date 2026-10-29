-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p011_b029
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:58:29.220144+00:00
-- url     : https://prove2.me/submissions/f60a96e3-a065-45dc-9afa-5f3ecb4a37cc

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
theorem collision_support_c311068_s0_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7621470467/10000000000 : ℝ)*x 0 + (2832212067/10000000000 : ℝ)*x 1 + (-408083387/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7621470467/10000000000 : ℝ)^9 ≤ (17630944222707/25000000000000 : ℝ)^7 := by
    have hnat : (7621470467 : ℕ)^9*25000000000000^7 ≤ 17630944222707^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7621470467 10000000000 17630944222707 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2832212067/10000000000 : ℝ)^9 ≤ (19751053900897/100000000000000 : ℝ)^7 := by
    have hnat : (2832212067 : ℕ)^9*100000000000000^7 ≤ 19751053900897^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2832212067 10000000000 19751053900897 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (408083387/2500000000 : ℝ)^9 ≤ (9725169186587/100000000000000 : ℝ)^7 := by
    have hnat : (408083387 : ℕ)^9*100000000000000^7 ≤ 9725169186587^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408083387 2500000000 9725169186587 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7621470467/10000000000 : ℝ), (2832212067/10000000000 : ℝ), (-408083387/2500000000 : ℝ)] ![(17630944222707/25000000000000 : ℝ), (19751053900897/100000000000000 : ℝ), (9725169186587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7621470467/10000000000 : ℝ)|^9 ≤ (17630944222707/25000000000000 : ℝ)^7
        have hw : |(7621470467/10000000000 : ℝ)|=(7621470467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2832212067/10000000000 : ℝ)|^9 ≤ (19751053900897/100000000000000 : ℝ)^7
        have hw : |(2832212067/10000000000 : ℝ)|=(2832212067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-408083387/2500000000 : ℝ)|^9 ≤ (9725169186587/100000000000000 : ℝ)^7
        have hw : |(-408083387/2500000000 : ℝ)|=(408083387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s0_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4199622167/10000000000 : ℝ)*x 0 + (-216206581/500000000 : ℝ)*x 1 + (4241156721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199622167/10000000000 : ℝ)^9 ≤ (6555200685767/20000000000000 : ℝ)^7 := by
    have hnat : (4199622167 : ℕ)^9*20000000000000^7 ≤ 6555200685767^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199622167 10000000000 6555200685767 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216206581/500000000 : ℝ)^9 ≤ (850765811199/2500000000000 : ℝ)^7 := by
    have hnat : (216206581 : ℕ)^9*2500000000000^7 ≤ 850765811199^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216206581 500000000 850765811199 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241156721/10000000000 : ℝ)^9 ≤ (33193364105921/100000000000000 : ℝ)^7 := by
    have hnat : (4241156721 : ℕ)^9*100000000000000^7 ≤ 33193364105921^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241156721 10000000000 33193364105921 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199622167/10000000000 : ℝ), (-216206581/500000000 : ℝ), (4241156721/10000000000 : ℝ)] ![(6555200685767/20000000000000 : ℝ), (850765811199/2500000000000 : ℝ), (33193364105921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199622167/10000000000 : ℝ)|^9 ≤ (6555200685767/20000000000000 : ℝ)^7
        have hw : |(4199622167/10000000000 : ℝ)|=(4199622167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216206581/500000000 : ℝ)|^9 ≤ (850765811199/2500000000000 : ℝ)^7
        have hw : |(-216206581/500000000 : ℝ)|=(216206581/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241156721/10000000000 : ℝ)|^9 ≤ (33193364105921/100000000000000 : ℝ)^7
        have hw : |(4241156721/10000000000 : ℝ)|=(4241156721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s0_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-509033023/10000000000 : ℝ)*x 0 + (-5621633167/10000000000 : ℝ)*x 1 + (-5845312787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (509033023/10000000000 : ℝ)^9 ≤ (543481557571/25000000000000 : ℝ)^7 := by
    have hnat : (509033023 : ℕ)^9*25000000000000^7 ≤ 543481557571^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509033023 10000000000 543481557571 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5621633167/10000000000 : ℝ)^9 ≤ (9537282396053/20000000000000 : ℝ)^7 := by
    have hnat : (5621633167 : ℕ)^9*20000000000000^7 ≤ 9537282396053^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5621633167 10000000000 9537282396053 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5845312787/10000000000 : ℝ)^9 ≤ (5013966176889/10000000000000 : ℝ)^7 := by
    have hnat : (5845312787 : ℕ)^9*10000000000000^7 ≤ 5013966176889^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5845312787 10000000000 5013966176889 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-509033023/10000000000 : ℝ), (-5621633167/10000000000 : ℝ), (-5845312787/10000000000 : ℝ)] ![(543481557571/25000000000000 : ℝ), (9537282396053/20000000000000 : ℝ), (5013966176889/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-509033023/10000000000 : ℝ)|^9 ≤ (543481557571/25000000000000 : ℝ)^7
        have hw : |(-509033023/10000000000 : ℝ)|=(509033023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5621633167/10000000000 : ℝ)|^9 ≤ (9537282396053/20000000000000 : ℝ)^7
        have hw : |(-5621633167/10000000000 : ℝ)|=(5621633167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5845312787/10000000000 : ℝ)|^9 ≤ (5013966176889/10000000000000 : ℝ)^7
        have hw : |(-5845312787/10000000000 : ℝ)|=(5845312787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s0_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7633243989/10000000000 : ℝ)*x 0 + (1707061509/5000000000 : ℝ)*x 1 + (-170581291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7633243989/10000000000 : ℝ)^9 ≤ (17665969651863/25000000000000 : ℝ)^7 := by
    have hnat : (7633243989 : ℕ)^9*25000000000000^7 ≤ 17665969651863^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7633243989 10000000000 17665969651863 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1707061509/5000000000 : ℝ)^9 ≤ (12557418266353/50000000000000 : ℝ)^7 := by
    have hnat : (1707061509 : ℕ)^9*50000000000000^7 ≤ 12557418266353^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1707061509 5000000000 12557418266353 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170581291/2000000000 : ℝ)^9 ≤ (422128484683/10000000000000 : ℝ)^7 := by
    have hnat : (170581291 : ℕ)^9*10000000000000^7 ≤ 422128484683^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170581291 2000000000 422128484683 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7633243989/10000000000 : ℝ), (1707061509/5000000000 : ℝ), (-170581291/2000000000 : ℝ)] ![(17665969651863/25000000000000 : ℝ), (12557418266353/50000000000000 : ℝ), (422128484683/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7633243989/10000000000 : ℝ)|^9 ≤ (17665969651863/25000000000000 : ℝ)^7
        have hw : |(7633243989/10000000000 : ℝ)|=(7633243989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1707061509/5000000000 : ℝ)|^9 ≤ (12557418266353/50000000000000 : ℝ)^7
        have hw : |(1707061509/5000000000 : ℝ)|=(1707061509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-170581291/2000000000 : ℝ)|^9 ≤ (422128484683/10000000000000 : ℝ)^7
        have hw : |(-170581291/2000000000 : ℝ)|=(170581291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s0_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1147625771/2500000000 : ℝ)*x 0 + (-23747037/80000000 : ℝ)*x 1 + (2559233219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1147625771/2500000000 : ℝ)^9 ≤ (7349857712907/20000000000000 : ℝ)^7 := by
    have hnat : (1147625771 : ℕ)^9*20000000000000^7 ≤ 7349857712907^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147625771 2500000000 7349857712907 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23747037/80000000 : ℝ)^9 ≤ (2622531564713/12500000000000 : ℝ)^7 := by
    have hnat : (23747037 : ℕ)^9*12500000000000^7 ≤ 2622531564713^7*80000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23747037 80000000 2622531564713 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2559233219/5000000000 : ℝ)^9 ≤ (42270458910569/100000000000000 : ℝ)^7 := by
    have hnat : (2559233219 : ℕ)^9*100000000000000^7 ≤ 42270458910569^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559233219 5000000000 42270458910569 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1147625771/2500000000 : ℝ), (-23747037/80000000 : ℝ), (2559233219/5000000000 : ℝ)] ![(7349857712907/20000000000000 : ℝ), (2622531564713/12500000000000 : ℝ), (42270458910569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1147625771/2500000000 : ℝ)|^9 ≤ (7349857712907/20000000000000 : ℝ)^7
        have hw : |(1147625771/2500000000 : ℝ)|=(1147625771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23747037/80000000 : ℝ)|^9 ≤ (2622531564713/12500000000000 : ℝ)^7
        have hw : |(-23747037/80000000 : ℝ)|=(23747037/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2559233219/5000000000 : ℝ)|^9 ≤ (42270458910569/100000000000000 : ℝ)^7
        have hw : |(2559233219/5000000000 : ℝ)|=(2559233219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s0_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (634955501/1250000000 : ℝ)*x 0 + (-1402546649/10000000000 : ℝ)*x 1 + (-5845312787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (634955501/1250000000 : ℝ)^9 ≤ (1674347636009/4000000000000 : ℝ)^7 := by
    have hnat : (634955501 : ℕ)^9*4000000000000^7 ≤ 1674347636009^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634955501 1250000000 1674347636009 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1402546649/10000000000 : ℝ)^9 ≤ (4000823653839/50000000000000 : ℝ)^7 := by
    have hnat : (1402546649 : ℕ)^9*50000000000000^7 ≤ 4000823653839^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402546649 10000000000 4000823653839 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5845312787/10000000000 : ℝ)^9 ≤ (5013966176889/10000000000000 : ℝ)^7 := by
    have hnat : (5845312787 : ℕ)^9*10000000000000^7 ≤ 5013966176889^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5845312787 10000000000 5013966176889 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(634955501/1250000000 : ℝ), (-1402546649/10000000000 : ℝ), (-5845312787/10000000000 : ℝ)] ![(1674347636009/4000000000000 : ℝ), (4000823653839/50000000000000 : ℝ), (5013966176889/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(634955501/1250000000 : ℝ)|^9 ≤ (1674347636009/4000000000000 : ℝ)^7
        have hw : |(634955501/1250000000 : ℝ)|=(634955501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1402546649/10000000000 : ℝ)|^9 ≤ (4000823653839/50000000000000 : ℝ)^7
        have hw : |(-1402546649/10000000000 : ℝ)|=(1402546649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5845312787/10000000000 : ℝ)|^9 ≤ (5013966176889/10000000000000 : ℝ)^7
        have hw : |(-5845312787/10000000000 : ℝ)|=(5845312787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s0_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-5534657/312500000 : ℝ)*x 0 + (-4252838863/10000000000 : ℝ)*x 1 + (-3624749577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5534657/312500000 : ℝ)^9 ≤ (279710026283/50000000000000 : ℝ)^7 := by
    have hnat : (5534657 : ℕ)^9*50000000000000^7 ≤ 279710026283^7*312500000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5534657 312500000 279710026283 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4252838863/10000000000 : ℝ)^9 ≤ (33310963381577/100000000000000 : ℝ)^7 := by
    have hnat : (4252838863 : ℕ)^9*100000000000000^7 ≤ 33310963381577^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252838863 10000000000 33310963381577 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3624749577/5000000000 : ℝ)^9 ≤ (33064808278467/50000000000000 : ℝ)^7 := by
    have hnat : (3624749577 : ℕ)^9*50000000000000^7 ≤ 33064808278467^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3624749577 5000000000 33064808278467 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5534657/312500000 : ℝ), (-4252838863/10000000000 : ℝ), (-3624749577/5000000000 : ℝ)] ![(279710026283/50000000000000 : ℝ), (33310963381577/100000000000000 : ℝ), (33064808278467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5534657/312500000 : ℝ)|^9 ≤ (279710026283/50000000000000 : ℝ)^7
        have hw : |(-5534657/312500000 : ℝ)|=(5534657/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4252838863/10000000000 : ℝ)|^9 ≤ (33310963381577/100000000000000 : ℝ)^7
        have hw : |(-4252838863/10000000000 : ℝ)|=(4252838863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3624749577/5000000000 : ℝ)|^9 ≤ (33064808278467/50000000000000 : ℝ)^7
        have hw : |(-3624749577/5000000000 : ℝ)|=(3624749577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s0_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (112760459/125000000 : ℝ)*x 0 + (1733066331/10000000000 : ℝ)*x 1 + (-459414397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112760459/125000000 : ℝ)^9 ≤ (5474446514919/6250000000000 : ℝ)^7 := by
    have hnat : (112760459 : ℕ)^9*6250000000000^7 ≤ 5474446514919^7*125000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112760459 125000000 5474446514919 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1733066331/10000000000 : ℝ)^9 ≤ (2625873607353/25000000000000 : ℝ)^7 := by
    have hnat : (1733066331 : ℕ)^9*25000000000000^7 ≤ 2625873607353^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1733066331 10000000000 2625873607353 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (459414397/10000000000 : ℝ)^9 ≤ (476340329397/25000000000000 : ℝ)^7 := by
    have hnat : (459414397 : ℕ)^9*25000000000000^7 ≤ 476340329397^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459414397 10000000000 476340329397 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(112760459/125000000 : ℝ), (1733066331/10000000000 : ℝ), (-459414397/10000000000 : ℝ)] ![(5474446514919/6250000000000 : ℝ), (2625873607353/25000000000000 : ℝ), (476340329397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(112760459/125000000 : ℝ)|^9 ≤ (5474446514919/6250000000000 : ℝ)^7
        have hw : |(112760459/125000000 : ℝ)|=(112760459/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1733066331/10000000000 : ℝ)|^9 ≤ (2625873607353/25000000000000 : ℝ)^7
        have hw : |(1733066331/10000000000 : ℝ)|=(1733066331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-459414397/10000000000 : ℝ)|^9 ≤ (476340329397/25000000000000 : ℝ)^7
        have hw : |(-459414397/10000000000 : ℝ)|=(459414397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s0_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4765679639/10000000000 : ℝ)*x 0 + (-447524447/1000000000 : ℝ)*x 1 + (3493775207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4765679639/10000000000 : ℝ)^9 ≤ (19281042807677/50000000000000 : ℝ)^7 := by
    have hnat : (4765679639 : ℕ)^9*50000000000000^7 ≤ 19281042807677^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4765679639 10000000000 19281042807677 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447524447/1000000000 : ℝ)^9 ≤ (142268947039/400000000000 : ℝ)^7 := by
    have hnat : (447524447 : ℕ)^9*400000000000^7 ≤ 142268947039^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447524447 1000000000 142268947039 400000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3493775207/10000000000 : ℝ)^9 ≤ (12935338802753/50000000000000 : ℝ)^7 := by
    have hnat : (3493775207 : ℕ)^9*50000000000000^7 ≤ 12935338802753^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3493775207 10000000000 12935338802753 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4765679639/10000000000 : ℝ), (-447524447/1000000000 : ℝ), (3493775207/10000000000 : ℝ)] ![(19281042807677/50000000000000 : ℝ), (142268947039/400000000000 : ℝ), (12935338802753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4765679639/10000000000 : ℝ)|^9 ≤ (19281042807677/50000000000000 : ℝ)^7
        have hw : |(4765679639/10000000000 : ℝ)|=(4765679639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447524447/1000000000 : ℝ)|^9 ≤ (142268947039/400000000000 : ℝ)^7
        have hw : |(-447524447/1000000000 : ℝ)|=(447524447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3493775207/10000000000 : ℝ)|^9 ≤ (12935338802753/50000000000000 : ℝ)^7
        have hw : |(3493775207/10000000000 : ℝ)|=(3493775207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s0_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2549488321/10000000000 : ℝ)*x 0 + (-309512423/1250000000 : ℝ)*x 1 + (-3624749577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2549488321/10000000000 : ℝ)^9 ≤ (8626570615107/50000000000000 : ℝ)^7 := by
    have hnat : (2549488321 : ℕ)^9*50000000000000^7 ≤ 8626570615107^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2549488321 10000000000 8626570615107 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (309512423/1250000000 : ℝ)^9 ≤ (2077155275057/12500000000000 : ℝ)^7 := by
    have hnat : (309512423 : ℕ)^9*12500000000000^7 ≤ 2077155275057^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309512423 1250000000 2077155275057 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3624749577/5000000000 : ℝ)^9 ≤ (33064808278467/50000000000000 : ℝ)^7 := by
    have hnat : (3624749577 : ℕ)^9*50000000000000^7 ≤ 33064808278467^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3624749577 5000000000 33064808278467 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2549488321/10000000000 : ℝ), (-309512423/1250000000 : ℝ), (-3624749577/5000000000 : ℝ)] ![(8626570615107/50000000000000 : ℝ), (2077155275057/12500000000000 : ℝ), (33064808278467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2549488321/10000000000 : ℝ)|^9 ≤ (8626570615107/50000000000000 : ℝ)^7
        have hw : |(2549488321/10000000000 : ℝ)|=(2549488321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-309512423/1250000000 : ℝ)|^9 ≤ (2077155275057/12500000000000 : ℝ)^7
        have hw : |(-309512423/1250000000 : ℝ)|=(309512423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3624749577/5000000000 : ℝ)|^9 ≤ (33064808278467/50000000000000 : ℝ)^7
        have hw : |(-3624749577/5000000000 : ℝ)|=(3624749577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s0_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-31399067/2000000000 : ℝ)*x 0 + (-6424223937/10000000000 : ℝ)*x 1 + (-5178448109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31399067/2000000000 : ℝ)^9 ≤ (479099611489/100000000000000 : ℝ)^7 := by
    have hnat : (31399067 : ℕ)^9*100000000000000^7 ≤ 479099611489^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31399067 2000000000 479099611489 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6424223937/10000000000 : ℝ)^9 ≤ (7076561814611/12500000000000 : ℝ)^7 := by
    have hnat : (6424223937 : ℕ)^9*12500000000000^7 ≤ 7076561814611^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6424223937 10000000000 7076561814611 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178448109/10000000000 : ℝ)^9 ≤ (42908405853797/100000000000000 : ℝ)^7 := by
    have hnat : (5178448109 : ℕ)^9*100000000000000^7 ≤ 42908405853797^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178448109 10000000000 42908405853797 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31399067/2000000000 : ℝ), (-6424223937/10000000000 : ℝ), (-5178448109/10000000000 : ℝ)] ![(479099611489/100000000000000 : ℝ), (7076561814611/12500000000000 : ℝ), (42908405853797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31399067/2000000000 : ℝ)|^9 ≤ (479099611489/100000000000000 : ℝ)^7
        have hw : |(-31399067/2000000000 : ℝ)|=(31399067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6424223937/10000000000 : ℝ)|^9 ≤ (7076561814611/12500000000000 : ℝ)^7
        have hw : |(-6424223937/10000000000 : ℝ)|=(6424223937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5178448109/10000000000 : ℝ)|^9 ≤ (42908405853797/100000000000000 : ℝ)^7
        have hw : |(-5178448109/10000000000 : ℝ)|=(5178448109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s0_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (565413611/625000000 : ℝ)*x 0 + (1705640399/10000000000 : ℝ)*x 1 + (-109721391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (565413611/625000000 : ℝ)^9 ≤ (43956564643607/50000000000000 : ℝ)^7 := by
    have hnat : (565413611 : ℕ)^9*50000000000000^7 ≤ 43956564643607^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565413611 625000000 43956564643607 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1705640399/10000000000 : ℝ)^9 ≤ (1029026957693/10000000000000 : ℝ)^7 := by
    have hnat : (1705640399 : ℕ)^9*10000000000000^7 ≤ 1029026957693^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705640399 10000000000 1029026957693 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109721391/2500000000 : ℝ)^9 ≤ (898300560661/50000000000000 : ℝ)^7 := by
    have hnat : (109721391 : ℕ)^9*50000000000000^7 ≤ 898300560661^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109721391 2500000000 898300560661 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(565413611/625000000 : ℝ), (1705640399/10000000000 : ℝ), (-109721391/2500000000 : ℝ)] ![(43956564643607/50000000000000 : ℝ), (1029026957693/10000000000000 : ℝ), (898300560661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(565413611/625000000 : ℝ)|^9 ≤ (43956564643607/50000000000000 : ℝ)^7
        have hw : |(565413611/625000000 : ℝ)|=(565413611/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1705640399/10000000000 : ℝ)|^9 ≤ (1029026957693/10000000000000 : ℝ)^7
        have hw : |(1705640399/10000000000 : ℝ)|=(1705640399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-109721391/2500000000 : ℝ)|^9 ≤ (898300560661/50000000000000 : ℝ)^7
        have hw : |(-109721391/2500000000 : ℝ)|=(109721391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s0_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (871052823/2500000000 : ℝ)*x 0 + (-4676862317/10000000000 : ℝ)*x 1 + (1143506859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871052823/2500000000 : ℝ)^9 ≤ (25779660495127/100000000000000 : ℝ)^7 := by
    have hnat : (871052823 : ℕ)^9*100000000000000^7 ≤ 25779660495127^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871052823 2500000000 25779660495127 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4676862317/10000000000 : ℝ)^9 ≤ (2352534018037/6250000000000 : ℝ)^7 := by
    have hnat : (4676862317 : ℕ)^9*6250000000000^7 ≤ 2352534018037^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4676862317 10000000000 2352534018037 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1143506859/2500000000 : ℝ)^9 ≤ (9144948799553/25000000000000 : ℝ)^7 := by
    have hnat : (1143506859 : ℕ)^9*25000000000000^7 ≤ 9144948799553^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143506859 2500000000 9144948799553 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871052823/2500000000 : ℝ), (-4676862317/10000000000 : ℝ), (1143506859/2500000000 : ℝ)] ![(25779660495127/100000000000000 : ℝ), (2352534018037/6250000000000 : ℝ), (9144948799553/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871052823/2500000000 : ℝ)|^9 ≤ (25779660495127/100000000000000 : ℝ)^7
        have hw : |(871052823/2500000000 : ℝ)|=(871052823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4676862317/10000000000 : ℝ)|^9 ≤ (2352534018037/6250000000000 : ℝ)^7
        have hw : |(-4676862317/10000000000 : ℝ)|=(4676862317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1143506859/2500000000 : ℝ)|^9 ≤ (9144948799553/25000000000000 : ℝ)^7
        have hw : |(1143506859/2500000000 : ℝ)|=(1143506859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s0_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4248307803/10000000000 : ℝ)*x 0 + (-1638542927/5000000000 : ℝ)*x 1 + (-5178448109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4248307803/10000000000 : ℝ)^9 ≤ (33265340109967/100000000000000 : ℝ)^7 := by
    have hnat : (4248307803 : ℕ)^9*100000000000000^7 ≤ 33265340109967^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248307803 10000000000 33265340109967 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1638542927/5000000000 : ℝ)^9 ≤ (4765250804351/20000000000000 : ℝ)^7 := by
    have hnat : (1638542927 : ℕ)^9*20000000000000^7 ≤ 4765250804351^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1638542927 5000000000 4765250804351 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178448109/10000000000 : ℝ)^9 ≤ (42908405853797/100000000000000 : ℝ)^7 := by
    have hnat : (5178448109 : ℕ)^9*100000000000000^7 ≤ 42908405853797^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178448109 10000000000 42908405853797 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4248307803/10000000000 : ℝ), (-1638542927/5000000000 : ℝ), (-5178448109/10000000000 : ℝ)] ![(33265340109967/100000000000000 : ℝ), (4765250804351/20000000000000 : ℝ), (42908405853797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4248307803/10000000000 : ℝ)|^9 ≤ (33265340109967/100000000000000 : ℝ)^7
        have hw : |(4248307803/10000000000 : ℝ)|=(4248307803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1638542927/5000000000 : ℝ)|^9 ≤ (4765250804351/20000000000000 : ℝ)^7
        have hw : |(-1638542927/5000000000 : ℝ)|=(1638542927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5178448109/10000000000 : ℝ)|^9 ≤ (42908405853797/100000000000000 : ℝ)^7
        have hw : |(-5178448109/10000000000 : ℝ)|=(5178448109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s1_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1148841031/5000000000 : ℝ)*x 0 + (-4840711993/10000000000 : ℝ)*x 1 + (-678229053/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1148841031/5000000000 : ℝ)^9 ≤ (15093895654751/100000000000000 : ℝ)^7 := by
    have hnat : (1148841031 : ℕ)^9*100000000000000^7 ≤ 15093895654751^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148841031 5000000000 15093895654751 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4840711993/10000000000 : ℝ)^9 ≤ (19672217544759/50000000000000 : ℝ)^7 := by
    have hnat : (4840711993 : ℕ)^9*50000000000000^7 ≤ 19672217544759^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4840711993 10000000000 19672217544759 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678229053/1250000000 : ℝ)^9 ≤ (5695208655381/12500000000000 : ℝ)^7 := by
    have hnat : (678229053 : ℕ)^9*12500000000000^7 ≤ 5695208655381^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678229053 1250000000 5695208655381 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1148841031/5000000000 : ℝ), (-4840711993/10000000000 : ℝ), (-678229053/1250000000 : ℝ)] ![(15093895654751/100000000000000 : ℝ), (19672217544759/50000000000000 : ℝ), (5695208655381/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1148841031/5000000000 : ℝ)|^9 ≤ (15093895654751/100000000000000 : ℝ)^7
        have hw : |(-1148841031/5000000000 : ℝ)|=(1148841031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4840711993/10000000000 : ℝ)|^9 ≤ (19672217544759/50000000000000 : ℝ)^7
        have hw : |(-4840711993/10000000000 : ℝ)|=(4840711993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-678229053/1250000000 : ℝ)|^9 ≤ (5695208655381/12500000000000 : ℝ)^7
        have hw : |(-678229053/1250000000 : ℝ)|=(678229053/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s1_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1560666363/2500000000 : ℝ)*x 0 + (1664026503/5000000000 : ℝ)*x 1 + (-1492559333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1560666363/2500000000 : ℝ)^9 ≤ (6820471173767/12500000000000 : ℝ)^7 := by
    have hnat : (1560666363 : ℕ)^9*12500000000000^7 ≤ 6820471173767^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560666363 2500000000 6820471173767 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1664026503/5000000000 : ℝ)^9 ≤ (4860748541787/20000000000000 : ℝ)^7 := by
    have hnat : (1664026503 : ℕ)^9*20000000000000^7 ≤ 4860748541787^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1664026503 5000000000 4860748541787 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1492559333/5000000000 : ℝ)^9 ≤ (21132487886999/100000000000000 : ℝ)^7 := by
    have hnat : (1492559333 : ℕ)^9*100000000000000^7 ≤ 21132487886999^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1492559333 5000000000 21132487886999 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1560666363/2500000000 : ℝ), (1664026503/5000000000 : ℝ), (-1492559333/5000000000 : ℝ)] ![(6820471173767/12500000000000 : ℝ), (4860748541787/20000000000000 : ℝ), (21132487886999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1560666363/2500000000 : ℝ)|^9 ≤ (6820471173767/12500000000000 : ℝ)^7
        have hw : |(1560666363/2500000000 : ℝ)|=(1560666363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1664026503/5000000000 : ℝ)|^9 ≤ (4860748541787/20000000000000 : ℝ)^7
        have hw : |(1664026503/5000000000 : ℝ)|=(1664026503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1492559333/5000000000 : ℝ)|^9 ≤ (21132487886999/100000000000000 : ℝ)^7
        have hw : |(-1492559333/5000000000 : ℝ)|=(1492559333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s1_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2111556481/5000000000 : ℝ)*x 0 + (-1125278281/2500000000 : ℝ)*x 1 + (161492101/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2111556481/5000000000 : ℝ)^9 ≤ (6602381387179/20000000000000 : ℝ)^7 := by
    have hnat : (2111556481 : ℕ)^9*20000000000000^7 ≤ 6602381387179^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111556481 5000000000 6602381387179 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125278281/2500000000 : ℝ)^9 ≤ (35831787907559/100000000000000 : ℝ)^7 := by
    have hnat : (1125278281 : ℕ)^9*100000000000000^7 ≤ 35831787907559^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125278281 2500000000 35831787907559 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161492101/400000000 : ℝ)^9 ≤ (15578152571211/50000000000000 : ℝ)^7 := by
    have hnat : (161492101 : ℕ)^9*50000000000000^7 ≤ 15578152571211^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161492101 400000000 15578152571211 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2111556481/5000000000 : ℝ), (-1125278281/2500000000 : ℝ), (161492101/400000000 : ℝ)] ![(6602381387179/20000000000000 : ℝ), (35831787907559/100000000000000 : ℝ), (15578152571211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2111556481/5000000000 : ℝ)|^9 ≤ (6602381387179/20000000000000 : ℝ)^7
        have hw : |(2111556481/5000000000 : ℝ)|=(2111556481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1125278281/2500000000 : ℝ)|^9 ≤ (35831787907559/100000000000000 : ℝ)^7
        have hw : |(-1125278281/2500000000 : ℝ)|=(1125278281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161492101/400000000 : ℝ)|^9 ≤ (15578152571211/50000000000000 : ℝ)^7
        have hw : |(161492101/400000000 : ℝ)|=(161492101/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311068_s1_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (197162381/500000000 : ℝ)*x 0 + (-1038834377/2500000000 : ℝ)*x 1 + (-4657613387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197162381/500000000 : ℝ)^9 ≤ (472284621583/1562500000000 : ℝ)^7 := by
    have hnat : (197162381 : ℕ)^9*1562500000000^7 ≤ 472284621583^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197162381 500000000 472284621583 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038834377/2500000000 : ℝ)^9 ≤ (2020769108073/6250000000000 : ℝ)^7 := by
    have hnat : (1038834377 : ℕ)^9*6250000000000^7 ≤ 2020769108073^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038834377 2500000000 2020769108073 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4657613387/10000000000 : ℝ)^9 ≤ (18720739234753/50000000000000 : ℝ)^7 := by
    have hnat : (4657613387 : ℕ)^9*50000000000000^7 ≤ 18720739234753^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4657613387 10000000000 18720739234753 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(197162381/500000000 : ℝ), (-1038834377/2500000000 : ℝ), (-4657613387/10000000000 : ℝ)] ![(472284621583/1562500000000 : ℝ), (2020769108073/6250000000000 : ℝ), (18720739234753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(197162381/500000000 : ℝ)|^9 ≤ (472284621583/1562500000000 : ℝ)^7
        have hw : |(197162381/500000000 : ℝ)|=(197162381/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1038834377/2500000000 : ℝ)|^9 ≤ (2020769108073/6250000000000 : ℝ)^7
        have hw : |(-1038834377/2500000000 : ℝ)|=(1038834377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4657613387/10000000000 : ℝ)|^9 ≤ (18720739234753/50000000000000 : ℝ)^7
        have hw : |(-4657613387/10000000000 : ℝ)|=(4657613387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311068 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((7621470467/10000000000 : ℝ)*X 1 0+(2832212067/10000000000 : ℝ)*X 1 1+(-408083387/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4199622167/10000000000 : ℝ)*X 2 0+(-216206581/500000000 : ℝ)*X 2 1+(4241156721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-509033023/10000000000 : ℝ)*X 0 0+(-5621633167/10000000000 : ℝ)*X 0 1+(-5845312787/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((7633243989/10000000000 : ℝ)*X 1 0+(1707061509/5000000000 : ℝ)*X 1 1+(-170581291/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1147625771/2500000000 : ℝ)*X 2 0+(-23747037/80000000 : ℝ)*X 2 1+(2559233219/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((634955501/1250000000 : ℝ)*X 0 0+(-1402546649/10000000000 : ℝ)*X 0 1+(-5845312787/10000000000 : ℝ)*X 0 2+(634955501/1250000000 : ℝ)*X 1 0+(-1402546649/10000000000 : ℝ)*X 1 1+(-5845312787/10000000000 : ℝ)*X 1 2+(634955501/1250000000 : ℝ)*X 2 0+(-1402546649/10000000000 : ℝ)*X 2 1+(-5845312787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-5534657/312500000 : ℝ)*X 0 0+(-4252838863/10000000000 : ℝ)*X 0 1+(-3624749577/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((112760459/125000000 : ℝ)*X 1 0+(1733066331/10000000000 : ℝ)*X 1 1+(-459414397/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4765679639/10000000000 : ℝ)*X 2 0+(-447524447/1000000000 : ℝ)*X 2 1+(3493775207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2549488321/10000000000 : ℝ)*X 0 0+(-309512423/1250000000 : ℝ)*X 0 1+(-3624749577/5000000000 : ℝ)*X 0 2+(2549488321/10000000000 : ℝ)*X 1 0+(-309512423/1250000000 : ℝ)*X 1 1+(-3624749577/5000000000 : ℝ)*X 1 2+(2549488321/10000000000 : ℝ)*X 2 0+(-309512423/1250000000 : ℝ)*X 2 1+(-3624749577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-31399067/2000000000 : ℝ)*X 0 0+(-6424223937/10000000000 : ℝ)*X 0 1+(-5178448109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((565413611/625000000 : ℝ)*X 1 0+(1705640399/10000000000 : ℝ)*X 1 1+(-109721391/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((871052823/2500000000 : ℝ)*X 2 0+(-4676862317/10000000000 : ℝ)*X 2 1+(1143506859/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((4248307803/10000000000 : ℝ)*X 0 0+(-1638542927/5000000000 : ℝ)*X 0 1+(-5178448109/10000000000 : ℝ)*X 0 2+(4248307803/10000000000 : ℝ)*X 1 0+(-1638542927/5000000000 : ℝ)*X 1 1+(-5178448109/10000000000 : ℝ)*X 1 2+(4248307803/10000000000 : ℝ)*X 2 0+(-1638542927/5000000000 : ℝ)*X 2 1+(-5178448109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((22201/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22201/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32761183039765977/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (349805689249/250000000000 : ℝ)*(base1) + (909024218151/500000000000 : ℝ)*(base39) + (86103169531/250000000000 : ℝ)*(base49) + (483407510441/200000000000 : ℝ)*(major_s0_0) + (483407510441/200000000000 : ℝ)*(major_s0_1) + (483407510441/200000000000 : ℝ)*(major_s0_2) + (1857331/100000000000 : ℝ)*(sp_s0_1) + (2381304909461/500000000000 : ℝ)*(sp_s0_7) + (3363370464489/1000000000000 : ℝ)*(sp_s0_8) + (210211146913/62500000000 : ℝ)*(sp_s0_9) + (71459911613/1000000000000 : ℝ)*(sp_s0_13) + (428183/100000000000 : ℝ)*(sp_s0_14) + (576489/250000000000 : ℝ)*(sp_s0_15) + (12993147/1000000000000 : ℝ)*(sp_s0_23) + (1470682668609/1000000000000 : ℝ)*(f.failure) + (840847835939/250000000000 : ℝ)*(f.sum) + (140822974145113/2000000000000000000000000000 : ℝ)*base63 + (77381735818073/125000000000000000000000000 : ℝ)*base65 + (310671879228811/400000000000000000000000000 : ℝ)*base67 + (124223429228811/400000000000000000000000000 : ℝ)*base68 + (360202495545113/2000000000000000000000000000 : ℝ)*base71 + (50470819669427/125000000000000000000000000 : ℝ)*base73 + (10066214194427/125000000000000000000000000 : ℝ)*base74 + (88082572811189/400000000000000000000000000 : ℝ)*base77 + (769427077254887/2000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (12983/25000000000000000 : ℝ)*base87 + (12983/25000000000000000 : ℝ)*base89 + (12983/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-56987/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-56987/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (119146624319135427/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (1474122068471/1000000000000 : ℝ)*(base1) + (9186543/1000000000000 : ℝ)*(base21) + (304105652437/125000000000 : ℝ)*(base39) + (624577424509/1000000000000 : ℝ)*(base49) + (24177488063/50000000000 : ℝ)*(base60) + (3560790960697/1000000000000 : ℝ)*(major_s0_0) + (3560790960697/1000000000000 : ℝ)*(major_s0_1) + (3560790960697/1000000000000 : ℝ)*(major_s0_2) + (481797/20000000000 : ℝ)*(sp_s0_8) + (40990831/1000000000000 : ℝ)*(sp_s0_9) + (401817717031/62500000000 : ℝ)*(sp_s0_14) + (198197492567/40000000000 : ℝ)*(sp_s0_15) + (4954911226651/1000000000000 : ℝ)*(sp_s0_16) + (173123619333/250000000000 : ℝ)*(sp_s0_20) + (2166616545803/1000000000000 : ℝ)*(f.failure) + (2477480702013/500000000000 : ℝ)*(f.sum) + (20478352675479/10000000000000000000000000000 : ℝ)*base62 + (530438718105659/625000000000000000000000000 : ℝ)*base64 + (1821901365803013/2000000000000000000000000000 : ℝ)*base66 + (1318359023803013/2000000000000000000000000000 : ℝ)*base69 + (1864188421675479/10000000000000000000000000000 : ℝ)*base70 + (205441788831841/625000000000000000000000000 : ℝ)*base72 + (632880225581841/625000000000000000000000000 : ℝ)*base75 + (845259165196987/2000000000000000000000000000 : ℝ)*base76 + (569851922324521/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (17139/25000000000000000 : ℝ)*base86 + (17139/25000000000000000 : ℝ)*base88 + (17139/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-41251/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-41251/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6455332243432553359323/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (181794304807/1000000000000 : ℝ)*(base1) + (1265134231997/1000000000000 : ℝ)*(base39) + (262555769029/500000000000 : ℝ)*(base49) + (7780093/1000000000000 : ℝ)*(base60) + (618578000137/200000000000 : ℝ)*(major_s0_0) + (618578000137/200000000000 : ℝ)*(major_s0_1) + (618578000137/200000000000 : ℝ)*(major_s0_2) + (21097767/1000000000000 : ℝ)*(sp_s0_2) + (2355630889/500000000000 : ℝ)*(sp_s0_15) + (79945289/1000000000000 : ℝ)*(sp_s0_16) + (1121413699469/250000000000 : ℝ)*(sp_s0_21) + (1074787307823/250000000000 : ℝ)*(sp_s0_22) + (4303759450013/1000000000000 : ℝ)*(sp_s0_23) + (1700120899933/1000000000000 : ℝ)*(sp_s0_27) + (94095760237/50000000000 : ℝ)*(f.failure) + (4303860493069/1000000000000 : ℝ)*(f.sum) + (228577070663559/2000000000000000000000000000 : ℝ)*base62 + (53150335557661/125000000000000000000000000 : ℝ)*base65 + (265617241837227/400000000000000000000000000 : ℝ)*base67 + (626901992637227/400000000000000000000000000 : ℝ)*base68 + (904406171663559/2000000000000000000000000000 : ℝ)*base70 + (48184275004839/125000000000000000000000000 : ℝ)*base73 + (19583431304839/125000000000000000000000000 : ℝ)*base74 + (122226576322773/400000000000000000000000000 : ℝ)*base77 + (10288962663559/2000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1369/1250000000000000 : ℝ)*base87 + (1369/1250000000000000 : ℝ)*base89 + (1369/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (22201/100000 : ℝ) ^ (71/16 : ℝ) ≤ (25151166243880587/20000000000000000000 : ℝ) := by
    have hpowers : (22201/100000 : ℝ)^71 ≤ (25151166243880587/20000000000000000000 : ℝ)^16 := by
      have hnat : (22201 : ℕ)^71*20000000000000000000^16 ≤ 25151166243880587^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22201 100000 25151166243880587 20000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22201/100000 : ℝ)) (X := (25151166243880587/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (20025151166243880587/20000000000000000000 : ℝ) ≤ (5001416277445509/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (20025151166243880587/20000000000000000000 : ℝ)^16 ≤ (5001416277445509/5000000000000000 : ℝ)^71 := by
      have hnat : (20025151166243880587 : ℕ)^16*5000000000000000^71 ≤ 5001416277445509^71*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20025151166243880587 20000000000000000000 5001416277445509 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001416277445509/5000000000000000 : ℝ)) (X := (20025151166243880587/20000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (10025151166243880587/10000000000000000000 : ℝ) ≤ (10005662355211459/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (10025151166243880587/10000000000000000000 : ℝ)^16 ≤ (10005662355211459/10000000000000000 : ℝ)^71 := by
      have hnat : (10025151166243880587 : ℕ)^16*10000000000000000^71 ≤ 10005662355211459^71*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10025151166243880587 10000000000000000000 10005662355211459 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005662355211459/10000000000000000 : ℝ)) (X := (10025151166243880587/10000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1416277445509/1110050000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2829800320441/2220100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (22201/100000 : ℝ)) (alpha := (1416277445509/1110050000000000 : ℝ)) (beta := (2829800320441/2220100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (22201/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1416277445509/1110050000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2829800320441/2220100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (56987/100000 : ℝ) ^ (71/16 : ℝ) ≤ (8246223268135435967/100000000000000000000 : ℝ) := by
    have hpowers : (56987/100000 : ℝ)^71 ≤ (8246223268135435967/100000000000000000000 : ℝ)^16 := by
      have hnat : (56987 : ℕ)^71*100000000000000000000^16 ≤ 8246223268135435967^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56987 100000 8246223268135435967 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (56987/100000 : ℝ)) (X := (8246223268135435967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (108246223268135435967/100000000000000000000 : ℝ) ≤ (81441351770479/80000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (108246223268135435967/100000000000000000000 : ℝ)^16 ≤ (81441351770479/80000000000000 : ℝ)^71 := by
      have hnat : (108246223268135435967 : ℕ)^16*80000000000000^71 ≤ 81441351770479^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108246223268135435967 100000000000000000000 81441351770479 80000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (81441351770479/80000000000000 : ℝ)) (X := (108246223268135435967/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (58246223268135435967/50000000000000000000 : ℝ) ≤ (413999992280613/400000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (58246223268135435967/50000000000000000000 : ℝ)^16 ≤ (413999992280613/400000000000000 : ℝ)^71 := by
      have hnat : (58246223268135435967 : ℕ)^16*400000000000000^71 ≤ 413999992280613^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58246223268135435967 50000000000000000000 413999992280613 400000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (413999992280613/400000000000000 : ℝ)) (X := (58246223268135435967/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1441351770479/45589600000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(3396616714109/113974000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (56987/100000 : ℝ)) (alpha := (1441351770479/45589600000000 : ℝ)) (beta := (3396616714109/113974000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (56987/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1441351770479/45589600000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(3396616714109/113974000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (41251/100000 : ℝ) ^ (71/16 : ℝ) ≤ (61424344651513997/3125000000000000000 : ℝ) := by
    have hpowers : (41251/100000 : ℝ)^71 ≤ (61424344651513997/3125000000000000000 : ℝ)^16 := by
      have hnat : (41251 : ℕ)^71*3125000000000000000^16 ≤ 61424344651513997^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41251 100000 61424344651513997 3125000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41251/100000 : ℝ)) (X := (61424344651513997/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (3186424344651513997/3125000000000000000 : ℝ) ≤ (10043961384159463/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3186424344651513997/3125000000000000000 : ℝ)^16 ≤ (10043961384159463/10000000000000000 : ℝ)^71 := by
      have hnat : (3186424344651513997 : ℕ)^16*10000000000000000^71 ≤ 10043961384159463^71*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3186424344651513997 3125000000000000000 10043961384159463 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10043961384159463/10000000000000000 : ℝ)) (X := (3186424344651513997/3125000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1623924344651513997/1562500000000000000 : ℝ) ≤ (10087271123299567/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (1623924344651513997/1562500000000000000 : ℝ)^16 ≤ (10087271123299567/10000000000000000 : ℝ)^71 := by
      have hnat : (1623924344651513997 : ℕ)^16*10000000000000000^71 ≤ 10087271123299567^71*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1623924344651513997 1562500000000000000 10087271123299567 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10087271123299567/10000000000000000 : ℝ)) (X := (1623924344651513997/1562500000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(43961384159463/4125100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(5413717392513/515637500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (41251/100000 : ℝ)) (alpha := (43961384159463/4125100000000000 : ℝ)) (beta := (5413717392513/515637500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (41251/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(43961384159463/4125100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(5413717392513/515637500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1148841031/5000000000 : ℝ)*X 0 0+(-4840711993/10000000000 : ℝ)*X 0 1+(-678229053/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1560666363/2500000000 : ℝ)*X 1 0+(1664026503/5000000000 : ℝ)*X 1 1+(-1492559333/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2111556481/5000000000 : ℝ)*X 2 0+(-1125278281/2500000000 : ℝ)*X 2 1+(161492101/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((197162381/500000000 : ℝ)*X 0 0+(-1038834377/2500000000 : ℝ)*X 0 1+(-4657613387/10000000000 : ℝ)*X 0 2+(197162381/500000000 : ℝ)*X 1 0+(-1038834377/2500000000 : ℝ)*X 1 1+(-4657613387/10000000000 : ℝ)*X 1 2+(197162381/500000000 : ℝ)*X 2 0+(-1038834377/2500000000 : ℝ)*X 2 1+(-4657613387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311068_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-85761/12500 : ℝ) < ((-41087/25000 : ℝ)*P 0+(-41087/25000 : ℝ)*P 1+(-41087/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-85761/12500 : ℝ) < (-506910472695128599905332269687138821/74556373045910000000000000000000000 : ℝ) := by norm_num
    linear_combination (857/250000000000 : ℝ)*(base3) + (16557/1000000000000 : ℝ)*(base12) + (29583/1000000000000 : ℝ)*(base21) + (7659/125000000000 : ℝ)*(base25) + (70483793593/100000000000 : ℝ)*(base39) + (205743751029/1000000000000 : ℝ)*(base40) + (121537709789/500000000000 : ℝ)*(base49) + (18516365379/125000000000 : ℝ)*(base60) + (41087/25000 : ℝ)*(major_s1_0) + (41087/25000 : ℝ)*(major_s1_1) + (41087/25000 : ℝ)*(major_s1_2) + (566585220777/250000000000 : ℝ)*(sp_s1_0) + (2266340903093/1000000000000 : ℝ)*(sp_s1_1) + (2266340808811/1000000000000 : ℝ)*(sp_s1_2) + (249999999143/250000000000 : ℝ)*(sp_s1_6) + (1133170449833/500000000000 : ℝ)*(f.sum) + (7870235912614487/419780488750000000000000000000 : ℝ)*base63 + (1149896921909/20625500000000000000000000 : ℝ)*base64 + (94546895237257/142467500000000000000000000 : ℝ)*base66 + (58129651665831/103127500000000000000000000 : ℝ)*base69 + (1156120282312466441/4579067255000000000000000000000 : ℝ)*base70 + (7756858976149/111005000000000000000000000 : ℝ)*base72 + (140635711492657/284935000000000000000000000 : ℝ)*base74 + (4414959766693/11100500000000000000000000 : ℝ)*base76 + (785356968661313057/12651683870000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p011_b029 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 69)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=68 := by omega
  rcases hc with rfl
  · exact collision_c311068 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 69)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p011_b029 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

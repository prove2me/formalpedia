-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b021
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:17:19.474967+00:00
-- url     : https://prove2.me/submissions/98957341-caca-447d-9f56-6f3a256e3160

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
theorem collision_support_c301037_s0_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-492646241/5000000000 : ℝ)*x 0 + (-7525915339/10000000000 : ℝ)*x 1 + (3704743913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (492646241/5000000000 : ℝ)^65 ≤ (4623101063989/100000000000000 : ℝ)^49 := by
    have hnat : (492646241 : ℕ)^65*100000000000000^49 ≤ 4623101063989^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492646241 5000000000 4623101063989 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7525915339/10000000000 : ℝ)^65 ≤ (4286789791587/6250000000000 : ℝ)^49 := by
    have hnat : (7525915339 : ℕ)^65*6250000000000^49 ≤ 4286789791587^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7525915339 10000000000 4286789791587 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3704743913/10000000000 : ℝ)^65 ≤ (5357652450223/20000000000000 : ℝ)^49 := by
    have hnat : (3704743913 : ℕ)^65*20000000000000^49 ≤ 5357652450223^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3704743913 10000000000 5357652450223 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-492646241/5000000000 : ℝ), (-7525915339/10000000000 : ℝ), (3704743913/10000000000 : ℝ)] ![(4623101063989/100000000000000 : ℝ), (4286789791587/6250000000000 : ℝ), (5357652450223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-492646241/5000000000 : ℝ)|^65 ≤ (4623101063989/100000000000000 : ℝ)^49
        have hw : |(-492646241/5000000000 : ℝ)|=(492646241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7525915339/10000000000 : ℝ)|^65 ≤ (4286789791587/6250000000000 : ℝ)^49
        have hw : |(-7525915339/10000000000 : ℝ)|=(7525915339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3704743913/10000000000 : ℝ)|^65 ≤ (5357652450223/20000000000000 : ℝ)^49
        have hw : |(3704743913/10000000000 : ℝ)|=(3704743913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s0_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1259866759/2500000000 : ℝ)*x 0 + (-1574420341/5000000000 : ℝ)*x 1 + (-120830333/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1259866759/2500000000 : ℝ)^65 ≤ (20145315677153/50000000000000 : ℝ)^49 := by
    have hnat : (1259866759 : ℕ)^65*50000000000000^49 ≤ 20145315677153^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259866759 2500000000 20145315677153 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1574420341/5000000000 : ℝ)^65 ≤ (21591435863491/100000000000000 : ℝ)^49 := by
    have hnat : (1574420341 : ℕ)^65*100000000000000^49 ≤ 21591435863491^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1574420341 5000000000 21591435863491 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120830333/250000000 : ℝ)^65 ≤ (38117932757993/100000000000000 : ℝ)^49 := by
    have hnat : (120830333 : ℕ)^65*100000000000000^49 ≤ 38117932757993^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120830333 250000000 38117932757993 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1259866759/2500000000 : ℝ), (-1574420341/5000000000 : ℝ), (-120830333/250000000 : ℝ)] ![(20145315677153/50000000000000 : ℝ), (21591435863491/100000000000000 : ℝ), (38117932757993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1259866759/2500000000 : ℝ)|^65 ≤ (20145315677153/50000000000000 : ℝ)^49
        have hw : |(1259866759/2500000000 : ℝ)|=(1259866759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1574420341/5000000000 : ℝ)|^65 ≤ (21591435863491/100000000000000 : ℝ)^49
        have hw : |(-1574420341/5000000000 : ℝ)|=(1574420341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-120830333/250000000 : ℝ)|^65 ≤ (38117932757993/100000000000000 : ℝ)^49
        have hw : |(-120830333/250000000 : ℝ)|=(120830333/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s0_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (939465331/1250000000 : ℝ)*x 0 + (-1639834257/10000000000 : ℝ)*x 1 + (40531733/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (939465331/1250000000 : ℝ)^65 ≤ (17116359719577/25000000000000 : ℝ)^49 := by
    have hnat : (939465331 : ℕ)^65*25000000000000^49 ≤ 17116359719577^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939465331 1250000000 17116359719577 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1639834257/10000000000 : ℝ)^65 ≤ (9086740033721/100000000000000 : ℝ)^49 := by
    have hnat : (1639834257 : ℕ)^65*100000000000000^49 ≤ 9086740033721^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1639834257 10000000000 9086740033721 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40531733/125000000 : ℝ)^65 ≤ (11223910534907/50000000000000 : ℝ)^49 := by
    have hnat : (40531733 : ℕ)^65*50000000000000^49 ≤ 11223910534907^49*125000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40531733 125000000 11223910534907 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(939465331/1250000000 : ℝ), (-1639834257/10000000000 : ℝ), (40531733/125000000 : ℝ)] ![(17116359719577/25000000000000 : ℝ), (9086740033721/100000000000000 : ℝ), (11223910534907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(939465331/1250000000 : ℝ)|^65 ≤ (17116359719577/25000000000000 : ℝ)^49
        have hw : |(939465331/1250000000 : ℝ)|=(939465331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1639834257/10000000000 : ℝ)|^65 ≤ (9086740033721/100000000000000 : ℝ)^49
        have hw : |(-1639834257/10000000000 : ℝ)|=(1639834257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40531733/125000000 : ℝ)|^65 ≤ (11223910534907/50000000000000 : ℝ)^49
        have hw : |(40531733/125000000 : ℝ)|=(40531733/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s0_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-480354813/10000000000 : ℝ)*x 0 + (-4595341847/5000000000 : ℝ)*x 1 + (1601866423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (480354813/10000000000 : ℝ)^65 ≤ (1782591482461/100000000000000 : ℝ)^49 := by
    have hnat : (480354813 : ℕ)^65*100000000000000^49 ≤ 1782591482461^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480354813 10000000000 1782591482461 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4595341847/5000000000 : ℝ)^65 ≤ (44704347997067/50000000000000 : ℝ)^49 := by
    have hnat : (4595341847 : ℕ)^65*50000000000000^49 ≤ 44704347997067^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4595341847 5000000000 44704347997067 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1601866423/10000000000 : ℝ)^65 ≤ (8808712513753/100000000000000 : ℝ)^49 := by
    have hnat : (1601866423 : ℕ)^65*100000000000000^49 ≤ 8808712513753^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1601866423 10000000000 8808712513753 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-480354813/10000000000 : ℝ), (-4595341847/5000000000 : ℝ), (1601866423/10000000000 : ℝ)] ![(1782591482461/100000000000000 : ℝ), (44704347997067/50000000000000 : ℝ), (8808712513753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-480354813/10000000000 : ℝ)|^65 ≤ (1782591482461/100000000000000 : ℝ)^49
        have hw : |(-480354813/10000000000 : ℝ)|=(480354813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4595341847/5000000000 : ℝ)|^65 ≤ (44704347997067/50000000000000 : ℝ)^49
        have hw : |(-4595341847/5000000000 : ℝ)|=(4595341847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1601866423/10000000000 : ℝ)|^65 ≤ (8808712513753/100000000000000 : ℝ)^49
        have hw : |(1601866423/10000000000 : ℝ)|=(1601866423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s0_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (918361409/2000000000 : ℝ)*x 0 + (3371194747/10000000000 : ℝ)*x 1 + (317669359/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (918361409/2000000000 : ℝ)^65 ≤ (17806597504371/50000000000000 : ℝ)^49 := by
    have hnat : (918361409 : ℕ)^65*50000000000000^49 ≤ 17806597504371^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918361409 2000000000 17806597504371 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3371194747/10000000000 : ℝ)^65 ≤ (23636915912513/100000000000000 : ℝ)^49 := by
    have hnat : (3371194747 : ℕ)^65*100000000000000^49 ≤ 23636915912513^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3371194747 10000000000 23636915912513 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317669359/625000000 : ℝ)^65 ≤ (20374944532183/50000000000000 : ℝ)^49 := by
    have hnat : (317669359 : ℕ)^65*50000000000000^49 ≤ 20374944532183^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317669359 625000000 20374944532183 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(918361409/2000000000 : ℝ), (3371194747/10000000000 : ℝ), (317669359/625000000 : ℝ)] ![(17806597504371/50000000000000 : ℝ), (23636915912513/100000000000000 : ℝ), (20374944532183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(918361409/2000000000 : ℝ)|^65 ≤ (17806597504371/50000000000000 : ℝ)^49
        have hw : |(918361409/2000000000 : ℝ)|=(918361409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3371194747/10000000000 : ℝ)|^65 ≤ (23636915912513/100000000000000 : ℝ)^49
        have hw : |(3371194747/10000000000 : ℝ)|=(3371194747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317669359/625000000 : ℝ)|^65 ≤ (20374944532183/50000000000000 : ℝ)^49
        have hw : |(317669359/625000000 : ℝ)|=(317669359/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s0_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2328842489/5000000000 : ℝ)*x 0 + (-594200863/2500000000 : ℝ)*x 1 + (-1165238519/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2328842489/5000000000 : ℝ)^65 ≤ (1451702037877/4000000000000 : ℝ)^49 := by
    have hnat : (2328842489 : ℕ)^65*4000000000000^49 ≤ 1451702037877^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2328842489 5000000000 1451702037877 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (594200863/2500000000 : ℝ)^65 ≤ (14867432307957/100000000000000 : ℝ)^49 := by
    have hnat : (594200863 : ℕ)^65*100000000000000^49 ≤ 14867432307957^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594200863 2500000000 14867432307957 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1165238519/2000000000 : ℝ)^65 ≤ (4884001673039/10000000000000 : ℝ)^49 := by
    have hnat : (1165238519 : ℕ)^65*10000000000000^49 ≤ 4884001673039^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165238519 2000000000 4884001673039 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2328842489/5000000000 : ℝ), (-594200863/2500000000 : ℝ), (-1165238519/2000000000 : ℝ)] ![(1451702037877/4000000000000 : ℝ), (14867432307957/100000000000000 : ℝ), (4884001673039/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2328842489/5000000000 : ℝ)|^65 ≤ (1451702037877/4000000000000 : ℝ)^49
        have hw : |(2328842489/5000000000 : ℝ)|=(2328842489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-594200863/2500000000 : ℝ)|^65 ≤ (14867432307957/100000000000000 : ℝ)^49
        have hw : |(-594200863/2500000000 : ℝ)|=(594200863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1165238519/2000000000 : ℝ)|^65 ≤ (4884001673039/10000000000000 : ℝ)^49
        have hw : |(-1165238519/2000000000 : ℝ)|=(1165238519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s0_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (667885339/1000000000 : ℝ)*x 0 + (-479403/20000000 : ℝ)*x 1 + (317669359/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667885339/1000000000 : ℝ)^65 ≤ (29270606544387/50000000000000 : ℝ)^49 := by
    have hnat : (667885339 : ℕ)^65*50000000000000^49 ≤ 29270606544387^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667885339 1000000000 29270606544387 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (479403/20000000 : ℝ)^65 ≤ (354448917741/50000000000000 : ℝ)^49 := by
    have hnat : (479403 : ℕ)^65*50000000000000^49 ≤ 354448917741^49*20000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479403 20000000 354448917741 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317669359/625000000 : ℝ)^65 ≤ (20374944532183/50000000000000 : ℝ)^49 := by
    have hnat : (317669359 : ℕ)^65*50000000000000^49 ≤ 20374944532183^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317669359 625000000 20374944532183 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(667885339/1000000000 : ℝ), (-479403/20000000 : ℝ), (317669359/625000000 : ℝ)] ![(29270606544387/50000000000000 : ℝ), (354448917741/50000000000000 : ℝ), (20374944532183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(667885339/1000000000 : ℝ)|^65 ≤ (29270606544387/50000000000000 : ℝ)^49
        have hw : |(667885339/1000000000 : ℝ)|=(667885339/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-479403/20000000 : ℝ)|^65 ≤ (354448917741/50000000000000 : ℝ)^49
        have hw : |(-479403/20000000 : ℝ)|=(479403/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317669359/625000000 : ℝ)|^65 ≤ (20374944532183/50000000000000 : ℝ)^49
        have hw : |(317669359/625000000 : ℝ)|=(317669359/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s0_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-643079/1000000000 : ℝ)*x 0 + (-178051101/250000000 : ℝ)*x 1 + (465306873/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (643079/1000000000 : ℝ)^65 ≤ (2917661663/50000000000000 : ℝ)^49 := by
    have hnat : (643079 : ℕ)^65*50000000000000^49 ≤ 2917661663^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643079 1000000000 2917661663 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178051101/250000000 : ℝ)^65 ≤ (31874660437397/50000000000000 : ℝ)^49 := by
    have hnat : (178051101 : ℕ)^65*50000000000000^49 ≤ 31874660437397^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178051101 250000000 31874660437397 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (465306873/1000000000 : ℝ)^65 ≤ (3624484379429/10000000000000 : ℝ)^49 := by
    have hnat : (465306873 : ℕ)^65*10000000000000^49 ≤ 3624484379429^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465306873 1000000000 3624484379429 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-643079/1000000000 : ℝ), (-178051101/250000000 : ℝ), (465306873/1000000000 : ℝ)] ![(2917661663/50000000000000 : ℝ), (31874660437397/50000000000000 : ℝ), (3624484379429/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-643079/1000000000 : ℝ)|^65 ≤ (2917661663/50000000000000 : ℝ)^49
        have hw : |(-643079/1000000000 : ℝ)|=(643079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-178051101/250000000 : ℝ)|^65 ≤ (31874660437397/50000000000000 : ℝ)^49
        have hw : |(-178051101/250000000 : ℝ)|=(178051101/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(465306873/1000000000 : ℝ)|^65 ≤ (3624484379429/10000000000000 : ℝ)^49
        have hw : |(465306873/1000000000 : ℝ)|=(465306873/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s0_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (868938707/2000000000 : ℝ)*x 0 + (3288509041/10000000000 : ℝ)*x 1 + (2694344013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868938707/2000000000 : ℝ)^65 ≤ (8273356436699/25000000000000 : ℝ)^49 := by
    have hnat : (868938707 : ℕ)^65*25000000000000^49 ≤ 8273356436699^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868938707 2000000000 8273356436699 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3288509041/10000000000 : ℝ)^65 ≤ (571774061523/2500000000000 : ℝ)^49 := by
    have hnat : (3288509041 : ℕ)^65*2500000000000^49 ≤ 571774061523^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3288509041 10000000000 571774061523 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2694344013/5000000000 : ℝ)^65 ≤ (2201780588511/5000000000000 : ℝ)^49 := by
    have hnat : (2694344013 : ℕ)^65*5000000000000^49 ≤ 2201780588511^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694344013 5000000000 2201780588511 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868938707/2000000000 : ℝ), (3288509041/10000000000 : ℝ), (2694344013/5000000000 : ℝ)] ![(8273356436699/25000000000000 : ℝ), (571774061523/2500000000000 : ℝ), (2201780588511/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868938707/2000000000 : ℝ)|^65 ≤ (8273356436699/25000000000000 : ℝ)^49
        have hw : |(868938707/2000000000 : ℝ)|=(868938707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3288509041/10000000000 : ℝ)|^65 ≤ (571774061523/2500000000000 : ℝ)^49
        have hw : |(3288509041/10000000000 : ℝ)|=(3288509041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2694344013/5000000000 : ℝ)|^65 ≤ (2201780588511/5000000000000 : ℝ)^49
        have hw : |(2694344013/5000000000 : ℝ)|=(2694344013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s0_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (11971769/19531250 : ℝ)*x 0 + (-2406677019/10000000000 : ℝ)*x 1 + (-4299990417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11971769/19531250 : ℝ)^65 ≤ (26120839030499/50000000000000 : ℝ)^49 := by
    have hnat : (11971769 : ℕ)^65*50000000000000^49 ≤ 26120839030499^49*19531250^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11971769 19531250 26120839030499 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2406677019/10000000000 : ℝ)^65 ≤ (3778955682133/25000000000000 : ℝ)^49 := by
    have hnat : (2406677019 : ℕ)^65*25000000000000^49 ≤ 3778955682133^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406677019 10000000000 3778955682133 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4299990417/10000000000 : ℝ)^65 ≤ (32642499194001/100000000000000 : ℝ)^49 := by
    have hnat : (4299990417 : ℕ)^65*100000000000000^49 ≤ 32642499194001^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299990417 10000000000 32642499194001 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(11971769/19531250 : ℝ), (-2406677019/10000000000 : ℝ), (-4299990417/10000000000 : ℝ)] ![(26120839030499/50000000000000 : ℝ), (3778955682133/25000000000000 : ℝ), (32642499194001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(11971769/19531250 : ℝ)|^65 ≤ (26120839030499/50000000000000 : ℝ)^49
        have hw : |(11971769/19531250 : ℝ)|=(11971769/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2406677019/10000000000 : ℝ)|^65 ≤ (3778955682133/25000000000000 : ℝ)^49
        have hw : |(-2406677019/10000000000 : ℝ)|=(2406677019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4299990417/10000000000 : ℝ)|^65 ≤ (32642499194001/100000000000000 : ℝ)^49
        have hw : |(-4299990417/10000000000 : ℝ)|=(4299990417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s0_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2264654263/2500000000 : ℝ)*x 0 + (-461639227/5000000000 : ℝ)*x 1 + (14967747/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2264654263/2500000000 : ℝ)^65 ≤ (43854210905721/50000000000000 : ℝ)^49 := by
    have hnat : (2264654263 : ℕ)^65*50000000000000^49 ≤ 43854210905721^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264654263 2500000000 43854210905721 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (461639227/5000000000 : ℝ)^65 ≤ (4241135560349/100000000000000 : ℝ)^49 := by
    have hnat : (461639227 : ℕ)^65*100000000000000^49 ≤ 4241135560349^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461639227 5000000000 4241135560349 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14967747/100000000 : ℝ)^65 ≤ (4025221310507/50000000000000 : ℝ)^49 := by
    have hnat : (14967747 : ℕ)^65*50000000000000^49 ≤ 4025221310507^49*100000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14967747 100000000 4025221310507 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2264654263/2500000000 : ℝ), (-461639227/5000000000 : ℝ), (14967747/100000000 : ℝ)] ![(43854210905721/50000000000000 : ℝ), (4241135560349/100000000000000 : ℝ), (4025221310507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2264654263/2500000000 : ℝ)|^65 ≤ (43854210905721/50000000000000 : ℝ)^49
        have hw : |(2264654263/2500000000 : ℝ)|=(2264654263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-461639227/5000000000 : ℝ)|^65 ≤ (4241135560349/100000000000000 : ℝ)^49
        have hw : |(-461639227/5000000000 : ℝ)|=(461639227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(14967747/100000000 : ℝ)|^65 ≤ (4025221310507/50000000000000 : ℝ)^49
        have hw : |(14967747/100000000 : ℝ)|=(14967747/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s0_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-13003291/5000000000 : ℝ)*x 0 + (-8555714929/10000000000 : ℝ)*x 1 + (2820193453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13003291/5000000000 : ℝ)^65 ≤ (7448328681/20000000000000 : ℝ)^49 := by
    have hnat : (13003291 : ℕ)^65*20000000000000^49 ≤ 7448328681^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13003291 5000000000 7448328681 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8555714929/10000000000 : ℝ)^65 ≤ (40654246872781/50000000000000 : ℝ)^49 := by
    have hnat : (8555714929 : ℕ)^65*50000000000000^49 ≤ 40654246872781^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8555714929 10000000000 40654246872781 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2820193453/10000000000 : ℝ)^65 ≤ (9327132300767/50000000000000 : ℝ)^49 := by
    have hnat : (2820193453 : ℕ)^65*50000000000000^49 ≤ 9327132300767^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2820193453 10000000000 9327132300767 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13003291/5000000000 : ℝ), (-8555714929/10000000000 : ℝ), (2820193453/10000000000 : ℝ)] ![(7448328681/20000000000000 : ℝ), (40654246872781/50000000000000 : ℝ), (9327132300767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13003291/5000000000 : ℝ)|^65 ≤ (7448328681/20000000000000 : ℝ)^49
        have hw : |(-13003291/5000000000 : ℝ)|=(13003291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8555714929/10000000000 : ℝ)|^65 ≤ (40654246872781/50000000000000 : ℝ)^49
        have hw : |(-8555714929/10000000000 : ℝ)|=(8555714929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2820193453/10000000000 : ℝ)|^65 ≤ (9327132300767/50000000000000 : ℝ)^49
        have hw : |(2820193453/10000000000 : ℝ)|=(2820193453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s0_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1221993981/2000000000 : ℝ)*x 0 + (1476455077/5000000000 : ℝ)*x 1 + (961509439/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1221993981/2000000000 : ℝ)^65 ≤ (26010235377957/50000000000000 : ℝ)^49 := by
    have hnat : (1221993981 : ℕ)^65*50000000000000^49 ≤ 26010235377957^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221993981 2000000000 26010235377957 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1476455077/5000000000 : ℝ)^65 ≤ (19827625960049/100000000000000 : ℝ)^49 := by
    have hnat : (1476455077 : ℕ)^65*100000000000000^49 ≤ 19827625960049^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1476455077 5000000000 19827625960049 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961509439/2500000000 : ℝ)^65 ≤ (879746977121/3125000000000 : ℝ)^49 := by
    have hnat : (961509439 : ℕ)^65*3125000000000^49 ≤ 879746977121^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961509439 2500000000 879746977121 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1221993981/2000000000 : ℝ), (1476455077/5000000000 : ℝ), (961509439/2500000000 : ℝ)] ![(26010235377957/50000000000000 : ℝ), (19827625960049/100000000000000 : ℝ), (879746977121/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1221993981/2000000000 : ℝ)|^65 ≤ (26010235377957/50000000000000 : ℝ)^49
        have hw : |(1221993981/2000000000 : ℝ)|=(1221993981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1476455077/5000000000 : ℝ)|^65 ≤ (19827625960049/100000000000000 : ℝ)^49
        have hw : |(1476455077/5000000000 : ℝ)|=(1476455077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(961509439/2500000000 : ℝ)|^65 ≤ (879746977121/3125000000000 : ℝ)^49
        have hw : |(961509439/2500000000 : ℝ)|=(961509439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s0_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1094513503/2500000000 : ℝ)*x 0 + (-3426214147/10000000000 : ℝ)*x 1 + (-5238879341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094513503/2500000000 : ℝ)^65 ≤ (16715463454821/50000000000000 : ℝ)^49 := by
    have hnat : (1094513503 : ℕ)^65*50000000000000^49 ≤ 16715463454821^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094513503 2500000000 16715463454821 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3426214147/10000000000 : ℝ)^65 ≤ (12075001781191/50000000000000 : ℝ)^49 := by
    have hnat : (3426214147 : ℕ)^65*50000000000000^49 ≤ 12075001781191^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3426214147 10000000000 12075001781191 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238879341/10000000000 : ℝ)^65 ≤ (21209534753643/50000000000000 : ℝ)^49 := by
    have hnat : (5238879341 : ℕ)^65*50000000000000^49 ≤ 21209534753643^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238879341 10000000000 21209534753643 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094513503/2500000000 : ℝ), (-3426214147/10000000000 : ℝ), (-5238879341/10000000000 : ℝ)] ![(16715463454821/50000000000000 : ℝ), (12075001781191/50000000000000 : ℝ), (21209534753643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094513503/2500000000 : ℝ)|^65 ≤ (16715463454821/50000000000000 : ℝ)^49
        have hw : |(1094513503/2500000000 : ℝ)|=(1094513503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3426214147/10000000000 : ℝ)|^65 ≤ (12075001781191/50000000000000 : ℝ)^49
        have hw : |(-3426214147/10000000000 : ℝ)|=(3426214147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5238879341/10000000000 : ℝ)|^65 ≤ (21209534753643/50000000000000 : ℝ)^49
        have hw : |(-5238879341/10000000000 : ℝ)|=(5238879341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s0_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8993281979/10000000000 : ℝ)*x 0 + (-167607711/5000000000 : ℝ)*x 1 + (2025296439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8993281979/10000000000 : ℝ)^65 ≤ (86870254888169/100000000000000 : ℝ)^49 := by
    have hnat : (8993281979 : ℕ)^65*100000000000000^49 ≤ 86870254888169^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8993281979 10000000000 86870254888169 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (167607711/5000000000 : ℝ)^65 ≤ (69131685863/6250000000000 : ℝ)^49 := by
    have hnat : (167607711 : ℕ)^65*6250000000000^49 ≤ 69131685863^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167607711 5000000000 69131685863 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2025296439/10000000000 : ℝ)^65 ≤ (12023638123423/100000000000000 : ℝ)^49 := by
    have hnat : (2025296439 : ℕ)^65*100000000000000^49 ≤ 12023638123423^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025296439 10000000000 12023638123423 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8993281979/10000000000 : ℝ), (-167607711/5000000000 : ℝ), (2025296439/10000000000 : ℝ)] ![(86870254888169/100000000000000 : ℝ), (69131685863/6250000000000 : ℝ), (12023638123423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8993281979/10000000000 : ℝ)|^65 ≤ (86870254888169/100000000000000 : ℝ)^49
        have hw : |(8993281979/10000000000 : ℝ)|=(8993281979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-167607711/5000000000 : ℝ)|^65 ≤ (69131685863/6250000000000 : ℝ)^49
        have hw : |(-167607711/5000000000 : ℝ)|=(167607711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2025296439/10000000000 : ℝ)|^65 ≤ (12023638123423/100000000000000 : ℝ)^49
        have hw : |(2025296439/10000000000 : ℝ)|=(2025296439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2366705213/10000000000 : ℝ)*x 0 + (-118885973/200000000 : ℝ)*x 1 + (70903103/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2366705213/10000000000 : ℝ)^65 ≤ (7391848947783/50000000000000 : ℝ)^49 := by
    have hnat : (2366705213 : ℕ)^65*50000000000000^49 ≤ 7391848947783^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2366705213 10000000000 7391848947783 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118885973/200000000 : ℝ)^65 ≤ (50157693619639/100000000000000 : ℝ)^49 := by
    have hnat : (118885973 : ℕ)^65*100000000000000^49 ≤ 50157693619639^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118885973 200000000 50157693619639 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70903103/156250000 : ℝ)^65 ≤ (35058608472811/100000000000000 : ℝ)^49 := by
    have hnat : (70903103 : ℕ)^65*100000000000000^49 ≤ 35058608472811^49*156250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70903103 156250000 35058608472811 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2366705213/10000000000 : ℝ), (-118885973/200000000 : ℝ), (70903103/156250000 : ℝ)] ![(7391848947783/50000000000000 : ℝ), (50157693619639/100000000000000 : ℝ), (35058608472811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2366705213/10000000000 : ℝ)|^65 ≤ (7391848947783/50000000000000 : ℝ)^49
        have hw : |(-2366705213/10000000000 : ℝ)|=(2366705213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-118885973/200000000 : ℝ)|^65 ≤ (50157693619639/100000000000000 : ℝ)^49
        have hw : |(-118885973/200000000 : ℝ)|=(118885973/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70903103/156250000 : ℝ)|^65 ≤ (35058608472811/100000000000000 : ℝ)^49
        have hw : |(70903103/156250000 : ℝ)|=(70903103/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s1_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5003443327/10000000000 : ℝ)*x 0 + (1781700677/5000000000 : ℝ)*x 1 + (562233177/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5003443327/10000000000 : ℝ)^65 ≤ (7981804718307/20000000000000 : ℝ)^49 := by
    have hnat : (5003443327 : ℕ)^65*20000000000000^49 ≤ 7981804718307^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5003443327 10000000000 7981804718307 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1781700677/5000000000 : ℝ)^65 ≤ (12720519979411/50000000000000 : ℝ)^49 := by
    have hnat : (1781700677 : ℕ)^65*50000000000000^49 ≤ 12720519979411^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781700677 5000000000 12720519979411 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562233177/1250000000 : ℝ)^65 ≤ (34649936433551/100000000000000 : ℝ)^49 := by
    have hnat : (562233177 : ℕ)^65*100000000000000^49 ≤ 34649936433551^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562233177 1250000000 34649936433551 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5003443327/10000000000 : ℝ), (1781700677/5000000000 : ℝ), (562233177/1250000000 : ℝ)] ![(7981804718307/20000000000000 : ℝ), (12720519979411/50000000000000 : ℝ), (34649936433551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5003443327/10000000000 : ℝ)|^65 ≤ (7981804718307/20000000000000 : ℝ)^49
        have hw : |(5003443327/10000000000 : ℝ)|=(5003443327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1781700677/5000000000 : ℝ)|^65 ≤ (12720519979411/50000000000000 : ℝ)^49
        have hw : |(1781700677/5000000000 : ℝ)|=(1781700677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562233177/1250000000 : ℝ)|^65 ≤ (34649936433551/100000000000000 : ℝ)^49
        have hw : |(562233177/1250000000 : ℝ)|=(562233177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4809983027/10000000000 : ℝ)*x 0 + (-1826975517/5000000000 : ℝ)*x 1 + (-2306080393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4809983027/10000000000 : ℝ)^65 ≤ (591798291009/1562500000000 : ℝ)^49 := by
    have hnat : (4809983027 : ℕ)^65*1562500000000^49 ≤ 591798291009^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4809983027 10000000000 591798291009 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1826975517/5000000000 : ℝ)^65 ≤ (26302157100347/100000000000000 : ℝ)^49 := by
    have hnat : (1826975517 : ℕ)^65*100000000000000^49 ≤ 26302157100347^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826975517 5000000000 26302157100347 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2306080393/5000000000 : ℝ)^65 ≤ (8955688065649/25000000000000 : ℝ)^49 := by
    have hnat : (2306080393 : ℕ)^65*25000000000000^49 ≤ 8955688065649^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306080393 5000000000 8955688065649 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4809983027/10000000000 : ℝ), (-1826975517/5000000000 : ℝ), (-2306080393/5000000000 : ℝ)] ![(591798291009/1562500000000 : ℝ), (26302157100347/100000000000000 : ℝ), (8955688065649/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4809983027/10000000000 : ℝ)|^65 ≤ (591798291009/1562500000000 : ℝ)^49
        have hw : |(4809983027/10000000000 : ℝ)|=(4809983027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1826975517/5000000000 : ℝ)|^65 ≤ (26302157100347/100000000000000 : ℝ)^49
        have hw : |(-1826975517/5000000000 : ℝ)|=(1826975517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2306080393/5000000000 : ℝ)|^65 ≤ (8955688065649/25000000000000 : ℝ)^49
        have hw : |(-2306080393/5000000000 : ℝ)|=(2306080393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301037_s1_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5903280433/10000000000 : ℝ)*x 0 + (-249683569/625000000 : ℝ)*x 1 + (1524840947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5903280433/10000000000 : ℝ)^65 ≤ (49699086619963/100000000000000 : ℝ)^49 := by
    have hnat : (5903280433 : ℕ)^65*100000000000000^49 ≤ 49699086619963^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5903280433 10000000000 49699086619963 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249683569/625000000 : ℝ)^65 ≤ (29606750575803/100000000000000 : ℝ)^49 := by
    have hnat : (249683569 : ℕ)^65*100000000000000^49 ≤ 29606750575803^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249683569 625000000 29606750575803 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1524840947/5000000000 : ℝ)^65 ≤ (82776651131/400000000000 : ℝ)^49 := by
    have hnat : (1524840947 : ℕ)^65*400000000000^49 ≤ 82776651131^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1524840947 5000000000 82776651131 400000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5903280433/10000000000 : ℝ), (-249683569/625000000 : ℝ), (1524840947/5000000000 : ℝ)] ![(49699086619963/100000000000000 : ℝ), (29606750575803/100000000000000 : ℝ), (82776651131/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5903280433/10000000000 : ℝ)|^65 ≤ (49699086619963/100000000000000 : ℝ)^49
        have hw : |(5903280433/10000000000 : ℝ)|=(5903280433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-249683569/625000000 : ℝ)|^65 ≤ (29606750575803/100000000000000 : ℝ)^49
        have hw : |(-249683569/625000000 : ℝ)|=(249683569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1524840947/5000000000 : ℝ)|^65 ≤ (82776651131/400000000000 : ℝ)^49
        have hw : |(1524840947/5000000000 : ℝ)|=(1524840947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301037 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-492646241/5000000000 : ℝ)*X 0 0+(-7525915339/10000000000 : ℝ)*X 0 1+(3704743913/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1259866759/2500000000 : ℝ)*X 2 0+(-1574420341/5000000000 : ℝ)*X 2 1+(-120830333/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((939465331/1250000000 : ℝ)*X 0 0+(-1639834257/10000000000 : ℝ)*X 0 1+(40531733/125000000 : ℝ)*X 0 2+(939465331/1250000000 : ℝ)*X 1 0+(-1639834257/10000000000 : ℝ)*X 1 1+(40531733/125000000 : ℝ)*X 1 2+(939465331/1250000000 : ℝ)*X 2 0+(-1639834257/10000000000 : ℝ)*X 2 1+(40531733/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-480354813/10000000000 : ℝ)*X 0 0+(-4595341847/5000000000 : ℝ)*X 0 1+(1601866423/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((918361409/2000000000 : ℝ)*X 1 0+(3371194747/10000000000 : ℝ)*X 1 1+(317669359/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2328842489/5000000000 : ℝ)*X 2 0+(-594200863/2500000000 : ℝ)*X 2 1+(-1165238519/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((667885339/1000000000 : ℝ)*X 0 0+(-479403/20000000 : ℝ)*X 0 1+(317669359/625000000 : ℝ)*X 0 2+(667885339/1000000000 : ℝ)*X 1 0+(-479403/20000000 : ℝ)*X 1 1+(317669359/625000000 : ℝ)*X 1 2+(667885339/1000000000 : ℝ)*X 2 0+(-479403/20000000 : ℝ)*X 2 1+(317669359/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-643079/1000000000 : ℝ)*X 0 0+(-178051101/250000000 : ℝ)*X 0 1+(465306873/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((868938707/2000000000 : ℝ)*X 1 0+(3288509041/10000000000 : ℝ)*X 1 1+(2694344013/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((11971769/19531250 : ℝ)*X 2 0+(-2406677019/10000000000 : ℝ)*X 2 1+(-4299990417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2264654263/2500000000 : ℝ)*X 0 0+(-461639227/5000000000 : ℝ)*X 0 1+(14967747/100000000 : ℝ)*X 0 2+(2264654263/2500000000 : ℝ)*X 1 0+(-461639227/5000000000 : ℝ)*X 1 1+(14967747/100000000 : ℝ)*X 1 2+(2264654263/2500000000 : ℝ)*X 2 0+(-461639227/5000000000 : ℝ)*X 2 1+(14967747/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-13003291/5000000000 : ℝ)*X 0 0+(-8555714929/10000000000 : ℝ)*X 0 1+(2820193453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1221993981/2000000000 : ℝ)*X 1 0+(1476455077/5000000000 : ℝ)*X 1 1+(961509439/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1094513503/2500000000 : ℝ)*X 2 0+(-3426214147/10000000000 : ℝ)*X 2 1+(-5238879341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((8993281979/10000000000 : ℝ)*X 0 0+(-167607711/5000000000 : ℝ)*X 0 1+(2025296439/10000000000 : ℝ)*X 0 2+(8993281979/10000000000 : ℝ)*X 1 0+(-167607711/5000000000 : ℝ)*X 1 1+(2025296439/10000000000 : ℝ)*X 1 2+(8993281979/10000000000 : ℝ)*X 2 0+(-167607711/5000000000 : ℝ)*X 2 1+(2025296439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((35439/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35439/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (42183905251246146220911/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50952126909/1000000000000 : ℝ)*(base3) + (36585129469/125000000000 : ℝ)*(base40) + (1719852723/1953125000 : ℝ)*(base49) + (286743141249/1000000000000 : ℝ)*(base59) + (2682174065531/1000000000000 : ℝ)*(major_s0_0) + (2682174065531/1000000000000 : ℝ)*(major_s0_1) + (2682174065531/1000000000000 : ℝ)*(major_s0_2) + (1775535864653/500000000000 : ℝ)*(sp_s0_7) + (3601861998031/1000000000000 : ℝ)*(sp_s0_8) + (3551011200859/1000000000000 : ℝ)*(sp_s0_9) + (1762258755389/1000000000000 : ℝ)*(sp_s0_13) + (110876557/500000000000 : ℝ)*(sp_s0_15) + (59894929/1000000000000 : ℝ)*(sp_s0_21) + (7526461/62500000000 : ℝ)*(sp_s0_23) + (1813210882299/1000000000000 : ℝ)*(f.failure) + (887782906059/250000000000 : ℝ)*(f.sum) + (461002430299159/5000000000000000000000000000 : ℝ)*base62 + (4823051324946433/10000000000000000000000000000 : ℝ)*base64 + (3604731079053567/10000000000000000000000000000 : ℝ)*base67 + (2622894398299159/10000000000000000000000000000 : ℝ)*base68 + (37255141969301/1250000000000000000000000000 : ℝ)*base71 + (5643071214053567/10000000000000000000000000000 : ℝ)*base72 + (479428627299159/10000000000000000000000000000 : ℝ)*base74 + (3358019736700841/10000000000000000000000000000 : ℝ)*base77 + (303899219/2000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (24319/25000000000000000 : ℝ)*base87 + (24319/25000000000000000 : ℝ)*base89 + (24319/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-50911/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-50911/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (38908497553969641474639/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (131619146069/100000000000 : ℝ)*(base40) + (83097160011/125000000000 : ℝ)*(base49) + (1552857/500000000000 : ℝ)*(base53) + (1082659/500000000000 : ℝ)*(base60) + (4231736704977/1000000000000 : ℝ)*(major_s0_0) + (4231736704977/1000000000000 : ℝ)*(major_s0_1) + (4231733599263/1000000000000 : ℝ)*(major_s0_2) + (6278843/1000000000000 : ℝ)*(sp_s0_6) + (1400679279707/250000000000 : ℝ)*(sp_s0_14) + (5602684942881/1000000000000 : ℝ)*(sp_s0_15) + (2801360112271/500000000000 : ℝ)*(sp_s0_16) + (715164415323/250000000000 : ℝ)*(sp_s0_20) + (32175947/1000000000000 : ℝ)*(sp_s0_22) + (8665137/100000000000 : ℝ)*(sp_s0_27) + (178796911969/62500000000 : ℝ)*(f.failure) + (2801360112271/500000000000 : ℝ)*(f.sum) + (3152837068167/125000000000000000000000000 : ℝ)*base62 + (6554001045543891/10000000000000000000000000000 : ℝ)*base65 + (2156446675429789/10000000000000000000000000000 : ℝ)*base67 + (1790933903868107/10000000000000000000000000000 : ℝ)*base68 + (4233903207479319/5000000000000000000000000000 : ℝ)*base71 + (7097947653429789/10000000000000000000000000000 : ℝ)*base72 + (5392461805585253/10000000000000000000000000000 : ℝ)*base74 + (6282699105414747/10000000000000000000000000000 : ℝ)*base77 + (310520417/1250000000000000000000 : ℝ)*base78 + (1947/3125000000000000 : ℝ)*base86 + (1947/3125000000000000 : ℝ)*base88 + (1947/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12511/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12511/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2717229359792208222627/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1465776839067/1000000000000 : ℝ)*(base40) + (962038038459/1000000000000 : ℝ)*(base49) + (129763307041/1000000000000 : ℝ)*(base59) + (872214750661/200000000000 : ℝ)*(major_s0_0) + (872214750661/200000000000 : ℝ)*(major_s0_1) + (872214750661/200000000000 : ℝ)*(major_s0_2) + (752779/250000000000 : ℝ)*(sp_s0_0) + (15851153/1000000000000 : ℝ)*(sp_s0_2) + (8543231/200000000000 : ℝ)*(sp_s0_7) + (30930231/500000000000 : ℝ)*(sp_s0_20) + (5773912768391/1000000000000 : ℝ)*(sp_s0_21) + (2886979247831/500000000000 : ℝ)*(sp_s0_22) + (5773942644509/1000000000000 : ℝ)*(sp_s0_23) + (2948123527511/1000000000000 : ℝ)*(sp_s0_27) + (2948185387973/1000000000000 : ℝ)*(f.failure) + (2886979247831/500000000000 : ℝ)*(f.sum) + (66815340762729/1000000000000000000000000000 : ℝ)*base62 + (1401080547814977/2000000000000000000000000000 : ℝ)*base65 + (110051778214977/2000000000000000000000000000 : ℝ)*base67 + (757096340962729/2000000000000000000000000000 : ℝ)*base68 + (29643766093469/250000000000000000000000000 : ℝ)*base70 + (50401483414977/2000000000000000000000000000 : ℝ)*base72 + (687148442162729/2000000000000000000000000000 : ℝ)*base74 + (37874348562729/2000000000000000000000000000 : ℝ)*base76 + (31627009/50000000000000000000 : ℝ)*base79 + (4513/25000000000000000 : ℝ)*base87 + (4513/25000000000000000 : ℝ)*base89 + (4513/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (35439/100000 : ℝ) ^ (129/32 : ℝ) ≤ (763514228275668819/50000000000000000000 : ℝ) := by
    have hpowers : (35439/100000 : ℝ)^129 ≤ (763514228275668819/50000000000000000000 : ℝ)^32 := by
      have hnat : (35439 : ℕ)^129*50000000000000000000^32 ≤ 763514228275668819^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35439 100000 763514228275668819 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35439/100000 : ℝ)) (X := (763514228275668819/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50763514228275668819/50000000000000000000 : ℝ) ≤ (1003766422124393/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (50763514228275668819/50000000000000000000 : ℝ)^32 ≤ (1003766422124393/1000000000000000 : ℝ)^129 := by
      have hnat : (50763514228275668819 : ℕ)^32*1000000000000000^129 ≤ 1003766422124393^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50763514228275668819 50000000000000000000 1003766422124393 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1003766422124393/1000000000000000 : ℝ)) (X := (50763514228275668819/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25763514228275668819/25000000000000000000 : ℝ) ≤ (1007490485283639/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (25763514228275668819/25000000000000000000 : ℝ)^32 ≤ (1007490485283639/1000000000000000 : ℝ)^129 := by
      have hnat : (25763514228275668819 : ℕ)^32*1000000000000000^129 ≤ 1007490485283639^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25763514228275668819 25000000000000000000 1007490485283639 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1007490485283639/1000000000000000 : ℝ)) (X := (25763514228275668819/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3766422124393/354390000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1862031579623/177195000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (35439/100000 : ℝ)) (alpha := (3766422124393/354390000000000 : ℝ)) (beta := (1862031579623/177195000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (35439/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3766422124393/354390000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1862031579623/177195000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (50911/100000 : ℝ) ^ (129/32 : ℝ) ≤ (6577856179767264947/100000000000000000000 : ℝ) := by
    have hpowers : (50911/100000 : ℝ)^129 ≤ (6577856179767264947/100000000000000000000 : ℝ)^32 := by
      have hnat : (50911 : ℕ)^129*100000000000000000000^32 ≤ 6577856179767264947^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50911 100000 6577856179767264947 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (50911/100000 : ℝ)) (X := (6577856179767264947/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (106577856179767264947/100000000000000000000 : ℝ) ≤ (5079642301499163/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (106577856179767264947/100000000000000000000 : ℝ)^32 ≤ (5079642301499163/5000000000000000 : ℝ)^129 := by
      have hnat : (106577856179767264947 : ℕ)^32*5000000000000000^129 ≤ 5079642301499163^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106577856179767264947 100000000000000000000 5079642301499163 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5079642301499163/5000000000000000 : ℝ)) (X := (106577856179767264947/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (56577856179767264947/50000000000000000000 : ℝ) ≤ (5155669873011041/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (56577856179767264947/50000000000000000000 : ℝ)^32 ≤ (5155669873011041/5000000000000000 : ℝ)^129 := by
      have hnat : (56577856179767264947 : ℕ)^32*5000000000000000^129 ≤ 5155669873011041^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56577856179767264947 50000000000000000000 5155669873011041 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5155669873011041/5000000000000000 : ℝ)) (X := (56577856179767264947/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(79642301499163/2545550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(5430540822277/181825000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (50911/100000 : ℝ)) (alpha := (79642301499163/2545550000000000 : ℝ)) (beta := (5430540822277/181825000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (50911/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(79642301499163/2545550000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(5430540822277/181825000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (12511/20000 : ℝ) ^ (129/32 : ℝ) ≤ (3772431049993404849/25000000000000000000 : ℝ) := by
    have hpowers : (12511/20000 : ℝ)^129 ≤ (3772431049993404849/25000000000000000000 : ℝ)^32 := by
      have hnat : (12511 : ℕ)^129*25000000000000000000^32 ≤ 3772431049993404849^32*20000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511 20000 3772431049993404849 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12511/20000 : ℝ)) (X := (3772431049993404849/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (28772431049993404849/25000000000000000000 : ℝ) ≤ (5177389680940621/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (28772431049993404849/25000000000000000000 : ℝ)^32 ≤ (5177389680940621/5000000000000000 : ℝ)^129 := by
      have hnat : (28772431049993404849 : ℕ)^32*5000000000000000^129 ≤ 5177389680940621^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28772431049993404849 25000000000000000000 5177389680940621 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5177389680940621/5000000000000000 : ℝ)) (X := (28772431049993404849/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (16272431049993404849/12500000000000000000 : ℝ) ≤ (5338062196141923/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (16272431049993404849/12500000000000000000 : ℝ)^32 ≤ (5338062196141923/5000000000000000 : ℝ)^129 := by
      have hnat : (16272431049993404849 : ℕ)^32*5000000000000000^129 ≤ 5338062196141923^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16272431049993404849 12500000000000000000 5338062196141923 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5338062196141923/5000000000000000 : ℝ)) (X := (16272431049993404849/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(177389680940621/3127750000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(80336257600651/1563875000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (12511/20000 : ℝ)) (alpha := (177389680940621/3127750000000000 : ℝ)) (beta := (80336257600651/1563875000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (12511/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(177389680940621/3127750000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(80336257600651/1563875000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2366705213/10000000000 : ℝ)*X 0 0+(-118885973/200000000 : ℝ)*X 0 1+(70903103/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5003443327/10000000000 : ℝ)*X 1 0+(1781700677/5000000000 : ℝ)*X 1 1+(562233177/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4809983027/10000000000 : ℝ)*X 2 0+(-1826975517/5000000000 : ℝ)*X 2 1+(-2306080393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5903280433/10000000000 : ℝ)*X 0 0+(-249683569/625000000 : ℝ)*X 0 1+(1524840947/5000000000 : ℝ)*X 0 2+(5903280433/10000000000 : ℝ)*X 1 0+(-249683569/625000000 : ℝ)*X 1 1+(1524840947/5000000000 : ℝ)*X 1 2+(5903280433/10000000000 : ℝ)*X 2 0+(-249683569/625000000 : ℝ)*X 2 1+(1524840947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301037_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-73443/12500 : ℝ) < ((-36981/25000 : ℝ)*P 0+(-36981/25000 : ℝ)*P 1+(-36981/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-73443/12500 : ℝ) < (-1371490253218436266588246920125599893/235133158299156250000000000000000000 : ℝ) := by norm_num
    linear_combination (2541/125000000000 : ℝ)*(base10) + (19144490923/500000000000 : ℝ)*(base39) + (2762474091/7812500000 : ℝ)*(base40) + (123909474707/500000000000 : ℝ)*(base49) + (2547/1000000000000 : ℝ)*(base53) + (5691/1000000000000 : ℝ)*(base59) + (36981/25000 : ℝ)*(major_s1_0) + (1479240006843/1000000000000 : ℝ)*(major_s1_1) + (1479239997453/1000000000000 : ℝ)*(major_s1_2) + (972137259109/500000000000 : ℝ)*(sp_s1_0) + (972137263571/500000000000 : ℝ)*(sp_s1_1) + (486068634133/250000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1944274529689/1000000000000 : ℝ)*(f.sum) + (5065311574998212253/39809220062500000000000000000000 : ℝ)*base62 + (1168514542233153/1563875000000000000000000000 : ℝ)*base64 + (829479861981552231/181825000000000000000000000 : ℝ)*base66 + (145695341281037/3127750000000000000000000000 : ℝ)*base68 + (231725585529609189/18474055375000000000000000000000 : ℝ)*base70 + (9625347826471/7383125000000000000000000 : ℝ)*base72 + (596263432195611/2545550000000000000000000000 : ℝ)*base74 + (9581841562693/14766250000000000000000000 : ℝ)*base77 + (1853620056762043823/2147898725000000000000000000000 : ℝ)*base78 + (2851/250000000000 : ℝ)*base81 + (6843/1000000000000 : ℝ)*base85 + (6843/1000000000000 : ℝ)*base88 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p001_b021 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=37 := by omega
  rcases hc with rfl
  · exact collision_c301037 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b021 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

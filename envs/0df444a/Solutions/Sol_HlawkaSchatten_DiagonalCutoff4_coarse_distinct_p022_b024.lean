-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p022_b024
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:44:59.340823+00:00
-- url     : https://prove2.me/submissions/c3b38df1-90c0-4392-a3ca-55791419e3bf

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
theorem collision_support_c322045_s0_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8763/400000000 : ℝ)*x 0 + (-6501747287/10000000000 : ℝ)*x 1 + (4882488859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8763/400000000 : ℝ)^21 ≤ (175493777/100000000000000 : ℝ)^17 := by
    have hnat : (8763 : ℕ)^21*100000000000000^17 ≤ 175493777^17*400000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8763 400000000 175493777 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6501747287/10000000000 : ℝ)^21 ≤ (58753962803587/100000000000000 : ℝ)^17 := by
    have hnat : (6501747287 : ℕ)^21*100000000000000^17 ≤ 58753962803587^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6501747287 10000000000 58753962803587 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4882488859/10000000000 : ℝ)^21 ≤ (41245861698123/100000000000000 : ℝ)^17 := by
    have hnat : (4882488859 : ℕ)^21*100000000000000^17 ≤ 41245861698123^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4882488859 10000000000 41245861698123 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8763/400000000 : ℝ), (-6501747287/10000000000 : ℝ), (4882488859/10000000000 : ℝ)] ![(175493777/100000000000000 : ℝ), (58753962803587/100000000000000 : ℝ), (41245861698123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8763/400000000 : ℝ)|^21 ≤ (175493777/100000000000000 : ℝ)^17
        have hw : |(8763/400000000 : ℝ)|=(8763/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6501747287/10000000000 : ℝ)|^21 ≤ (58753962803587/100000000000000 : ℝ)^17
        have hw : |(-6501747287/10000000000 : ℝ)|=(6501747287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4882488859/10000000000 : ℝ)|^21 ≤ (41245861698123/100000000000000 : ℝ)^17
        have hw : |(4882488859/10000000000 : ℝ)|=(4882488859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5352195123/10000000000 : ℝ)*x 0 + (3318614287/10000000000 : ℝ)*x 1 + (448593481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352195123/10000000000 : ℝ)^21 ≤ (721900139691/1562500000000 : ℝ)^17 := by
    have hnat : (5352195123 : ℕ)^21*1562500000000^17 ≤ 721900139691^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352195123 10000000000 721900139691 1562500000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3318614287/10000000000 : ℝ)^21 ≤ (12800022432663/50000000000000 : ℝ)^17 := by
    have hnat : (3318614287 : ℕ)^21*50000000000000^17 ≤ 12800022432663^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3318614287 10000000000 12800022432663 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448593481/1250000000 : ℝ)^21 ≤ (28198346189329/100000000000000 : ℝ)^17 := by
    have hnat : (448593481 : ℕ)^21*100000000000000^17 ≤ 28198346189329^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448593481 1250000000 28198346189329 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352195123/10000000000 : ℝ), (3318614287/10000000000 : ℝ), (448593481/1250000000 : ℝ)] ![(721900139691/1562500000000 : ℝ), (12800022432663/50000000000000 : ℝ), (28198346189329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352195123/10000000000 : ℝ)|^21 ≤ (721900139691/1562500000000 : ℝ)^17
        have hw : |(5352195123/10000000000 : ℝ)|=(5352195123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3318614287/10000000000 : ℝ)|^21 ≤ (12800022432663/50000000000000 : ℝ)^17
        have hw : |(3318614287/10000000000 : ℝ)|=(3318614287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448593481/1250000000 : ℝ)|^21 ≤ (28198346189329/100000000000000 : ℝ)^17
        have hw : |(448593481/1250000000 : ℝ)|=(448593481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2967280977/5000000000 : ℝ)*x 0 + (-2966642637/10000000000 : ℝ)*x 1 + (-3278875473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2967280977/5000000000 : ℝ)^21 ≤ (52489006742287/100000000000000 : ℝ)^17 := by
    have hnat : (2967280977 : ℕ)^21*100000000000000^17 ≤ 52489006742287^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2967280977 5000000000 52489006742287 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2966642637/10000000000 : ℝ)^21 ≤ (4457818105327/20000000000000 : ℝ)^17 := by
    have hnat : (2966642637 : ℕ)^21*20000000000000^17 ≤ 4457818105327^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2966642637 10000000000 4457818105327 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3278875473/10000000000 : ℝ)^21 ≤ (25221902713219/100000000000000 : ℝ)^17 := by
    have hnat : (3278875473 : ℕ)^21*100000000000000^17 ≤ 25221902713219^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3278875473 10000000000 25221902713219 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2967280977/5000000000 : ℝ), (-2966642637/10000000000 : ℝ), (-3278875473/10000000000 : ℝ)] ![(52489006742287/100000000000000 : ℝ), (4457818105327/20000000000000 : ℝ), (25221902713219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2967280977/5000000000 : ℝ)|^21 ≤ (52489006742287/100000000000000 : ℝ)^17
        have hw : |(2967280977/5000000000 : ℝ)|=(2967280977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2966642637/10000000000 : ℝ)|^21 ≤ (4457818105327/20000000000000 : ℝ)^17
        have hw : |(-2966642637/10000000000 : ℝ)|=(2966642637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3278875473/10000000000 : ℝ)|^21 ≤ (25221902713219/100000000000000 : ℝ)^17
        have hw : |(-3278875473/10000000000 : ℝ)|=(3278875473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1356794657/2500000000 : ℝ)*x 0 + (-1142773129/5000000000 : ℝ)*x 1 + (445656189/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1356794657/2500000000 : ℝ)^21 ≤ (47002500946451/100000000000000 : ℝ)^17 := by
    have hnat : (1356794657 : ℕ)^21*100000000000000^17 ≤ 47002500946451^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356794657 2500000000 47002500946451 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1142773129/5000000000 : ℝ)^21 ≤ (1614968801357/10000000000000 : ℝ)^17 := by
    have hnat : (1142773129 : ℕ)^21*10000000000000^17 ≤ 1614968801357^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142773129 5000000000 1614968801357 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445656189/1000000000 : ℝ)^21 ≤ (1473912440553/4000000000000 : ℝ)^17 := by
    have hnat : (445656189 : ℕ)^21*4000000000000^17 ≤ 1473912440553^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445656189 1000000000 1473912440553 4000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1356794657/2500000000 : ℝ), (-1142773129/5000000000 : ℝ), (445656189/1000000000 : ℝ)] ![(47002500946451/100000000000000 : ℝ), (1614968801357/10000000000000 : ℝ), (1473912440553/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1356794657/2500000000 : ℝ)|^21 ≤ (47002500946451/100000000000000 : ℝ)^17
        have hw : |(1356794657/2500000000 : ℝ)|=(1356794657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1142773129/5000000000 : ℝ)|^21 ≤ (1614968801357/10000000000000 : ℝ)^17
        have hw : |(-1142773129/5000000000 : ℝ)|=(1142773129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(445656189/1000000000 : ℝ)|^21 ≤ (1473912440553/4000000000000 : ℝ)^17
        have hw : |(445656189/1000000000 : ℝ)|=(445656189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2214687/10000000000 : ℝ)*x 0 + (-4319632503/5000000000 : ℝ)*x 1 + (1164338521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2214687/10000000000 : ℝ)^21 ≤ (1528818243/50000000000000 : ℝ)^17 := by
    have hnat : (2214687 : ℕ)^21*50000000000000^17 ≤ 1528818243^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214687 10000000000 1528818243 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4319632503/5000000000 : ℝ)^21 ≤ (41734975618551/50000000000000 : ℝ)^17 := by
    have hnat : (4319632503 : ℕ)^21*50000000000000^17 ≤ 41734975618551^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319632503 5000000000 41734975618551 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1164338521/5000000000 : ℝ)^21 ≤ (16526991118387/100000000000000 : ℝ)^17 := by
    have hnat : (1164338521 : ℕ)^21*100000000000000^17 ≤ 16526991118387^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164338521 5000000000 16526991118387 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2214687/10000000000 : ℝ), (-4319632503/5000000000 : ℝ), (1164338521/5000000000 : ℝ)] ![(1528818243/50000000000000 : ℝ), (41734975618551/50000000000000 : ℝ), (16526991118387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2214687/10000000000 : ℝ)|^21 ≤ (1528818243/50000000000000 : ℝ)^17
        have hw : |(2214687/10000000000 : ℝ)|=(2214687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4319632503/5000000000 : ℝ)|^21 ≤ (41734975618551/50000000000000 : ℝ)^17
        have hw : |(-4319632503/5000000000 : ℝ)|=(4319632503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1164338521/5000000000 : ℝ)|^21 ≤ (16526991118387/100000000000000 : ℝ)^17
        have hw : |(1164338521/5000000000 : ℝ)|=(1164338521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3084924611/10000000000 : ℝ)*x 0 + (5104825303/10000000000 : ℝ)*x 1 + (1019722337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3084924611/10000000000 : ℝ)^21 ≤ (11695985141749/50000000000000 : ℝ)^17 := by
    have hnat : (3084924611 : ℕ)^21*50000000000000^17 ≤ 11695985141749^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3084924611 10000000000 11695985141749 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5104825303/10000000000 : ℝ)^21 ≤ (10894580513887/25000000000000 : ℝ)^17 := by
    have hnat : (5104825303 : ℕ)^21*25000000000000^17 ≤ 10894580513887^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5104825303 10000000000 10894580513887 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019722337/2500000000 : ℝ)^21 ≤ (33029707639971/100000000000000 : ℝ)^17 := by
    have hnat : (1019722337 : ℕ)^21*100000000000000^17 ≤ 33029707639971^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019722337 2500000000 33029707639971 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3084924611/10000000000 : ℝ), (5104825303/10000000000 : ℝ), (1019722337/2500000000 : ℝ)] ![(11695985141749/50000000000000 : ℝ), (10894580513887/25000000000000 : ℝ), (33029707639971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3084924611/10000000000 : ℝ)|^21 ≤ (11695985141749/50000000000000 : ℝ)^17
        have hw : |(3084924611/10000000000 : ℝ)|=(3084924611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5104825303/10000000000 : ℝ)|^21 ≤ (10894580513887/25000000000000 : ℝ)^17
        have hw : |(5104825303/10000000000 : ℝ)|=(5104825303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1019722337/2500000000 : ℝ)|^21 ≤ (33029707639971/100000000000000 : ℝ)^17
        have hw : |(1019722337/2500000000 : ℝ)|=(1019722337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (967027369/2000000000 : ℝ)*x 0 + (-45683991/200000000 : ℝ)*x 1 + (-101206961/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (967027369/2000000000 : ℝ)^21 ≤ (20376144622733/50000000000000 : ℝ)^17 := by
    have hnat : (967027369 : ℕ)^21*50000000000000^17 ≤ 20376144622733^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967027369 2000000000 20376144622733 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45683991/200000000 : ℝ)^21 ≤ (4034483488933/25000000000000 : ℝ)^17 := by
    have hnat : (45683991 : ℕ)^21*25000000000000^17 ≤ 4034483488933^17*200000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45683991 200000000 4034483488933 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101206961/200000000 : ℝ)^21 ≤ (43109776781851/100000000000000 : ℝ)^17 := by
    have hnat : (101206961 : ℕ)^21*100000000000000^17 ≤ 43109776781851^17*200000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101206961 200000000 43109776781851 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(967027369/2000000000 : ℝ), (-45683991/200000000 : ℝ), (-101206961/200000000 : ℝ)] ![(20376144622733/50000000000000 : ℝ), (4034483488933/25000000000000 : ℝ), (43109776781851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(967027369/2000000000 : ℝ)|^21 ≤ (20376144622733/50000000000000 : ℝ)^17
        have hw : |(967027369/2000000000 : ℝ)|=(967027369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45683991/200000000 : ℝ)|^21 ≤ (4034483488933/25000000000000 : ℝ)^17
        have hw : |(-45683991/200000000 : ℝ)|=(45683991/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-101206961/200000000 : ℝ)|^21 ≤ (43109776781851/100000000000000 : ℝ)^17
        have hw : |(-101206961/200000000 : ℝ)|=(101206961/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2580997501/5000000000 : ℝ)*x 0 + (-90271643/2500000000 : ℝ)*x 1 + (95117463/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2580997501/5000000000 : ℝ)^21 ≤ (44181987202507/100000000000000 : ℝ)^17 := by
    have hnat : (2580997501 : ℕ)^21*100000000000000^17 ≤ 44181987202507^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2580997501 5000000000 44181987202507 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90271643/2500000000 : ℝ)^21 ≤ (1652820804639/100000000000000 : ℝ)^17 := by
    have hnat : (90271643 : ℕ)^21*100000000000000^17 ≤ 1652820804639^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90271643 2500000000 1652820804639 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95117463/156250000 : ℝ)^21 ≤ (6770648996981/12500000000000 : ℝ)^17 := by
    have hnat : (95117463 : ℕ)^21*12500000000000^17 ≤ 6770648996981^17*156250000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95117463 156250000 6770648996981 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2580997501/5000000000 : ℝ), (-90271643/2500000000 : ℝ), (95117463/156250000 : ℝ)] ![(44181987202507/100000000000000 : ℝ), (1652820804639/100000000000000 : ℝ), (6770648996981/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2580997501/5000000000 : ℝ)|^21 ≤ (44181987202507/100000000000000 : ℝ)^17
        have hw : |(2580997501/5000000000 : ℝ)|=(2580997501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90271643/2500000000 : ℝ)|^21 ≤ (1652820804639/100000000000000 : ℝ)^17
        have hw : |(-90271643/2500000000 : ℝ)|=(90271643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95117463/156250000 : ℝ)|^21 ≤ (6770648996981/12500000000000 : ℝ)^17
        have hw : |(95117463/156250000 : ℝ)|=(95117463/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1738073/10000000000 : ℝ)*x 0 + (-221157693/500000000 : ℝ)*x 1 + (6922929587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1738073/10000000000 : ℝ)^21 ≤ (2266616959/100000000000000 : ℝ)^17 := by
    have hnat : (1738073 : ℕ)^21*100000000000000^17 ≤ 2266616959^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1738073 10000000000 2266616959 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221157693/500000000 : ℝ)^21 ≤ (36506893688907/100000000000000 : ℝ)^17 := by
    have hnat : (221157693 : ℕ)^21*100000000000000^17 ≤ 36506893688907^17*500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221157693 500000000 36506893688907 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6922929587/10000000000 : ℝ)^21 ≤ (63490839682751/100000000000000 : ℝ)^17 := by
    have hnat : (6922929587 : ℕ)^21*100000000000000^17 ≤ 63490839682751^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6922929587 10000000000 63490839682751 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1738073/10000000000 : ℝ), (-221157693/500000000 : ℝ), (6922929587/10000000000 : ℝ)] ![(2266616959/100000000000000 : ℝ), (36506893688907/100000000000000 : ℝ), (63490839682751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1738073/10000000000 : ℝ)|^21 ≤ (2266616959/100000000000000 : ℝ)^17
        have hw : |(1738073/10000000000 : ℝ)|=(1738073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-221157693/500000000 : ℝ)|^21 ≤ (36506893688907/100000000000000 : ℝ)^17
        have hw : |(-221157693/500000000 : ℝ)|=(221157693/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6922929587/10000000000 : ℝ)|^21 ≤ (63490839682751/100000000000000 : ℝ)^17
        have hw : |(6922929587/10000000000 : ℝ)|=(6922929587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1056390723/5000000000 : ℝ)*x 0 + (896399719/2500000000 : ℝ)*x 1 + (6360100159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056390723/5000000000 : ℝ)^21 ≤ (14655371339491/100000000000000 : ℝ)^17 := by
    have hnat : (1056390723 : ℕ)^21*100000000000000^17 ≤ 14655371339491^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056390723 5000000000 14655371339491 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896399719/2500000000 : ℝ)^21 ≤ (14083892332193/50000000000000 : ℝ)^17 := by
    have hnat : (896399719 : ℕ)^21*50000000000000^17 ≤ 14083892332193^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896399719 2500000000 14083892332193 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6360100159/10000000000 : ℝ)^21 ≤ (7147105497137/12500000000000 : ℝ)^17 := by
    have hnat : (6360100159 : ℕ)^21*12500000000000^17 ≤ 7147105497137^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6360100159 10000000000 7147105497137 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056390723/5000000000 : ℝ), (896399719/2500000000 : ℝ), (6360100159/10000000000 : ℝ)] ![(14655371339491/100000000000000 : ℝ), (14083892332193/50000000000000 : ℝ), (7147105497137/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056390723/5000000000 : ℝ)|^21 ≤ (14655371339491/100000000000000 : ℝ)^17
        have hw : |(1056390723/5000000000 : ℝ)|=(1056390723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896399719/2500000000 : ℝ)|^21 ≤ (14083892332193/50000000000000 : ℝ)^17
        have hw : |(896399719/2500000000 : ℝ)|=(896399719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6360100159/10000000000 : ℝ)|^21 ≤ (7147105497137/12500000000000 : ℝ)^17
        have hw : |(6360100159/10000000000 : ℝ)|=(6360100159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4044141713/5000000000 : ℝ)*x 0 + (-155361233/1250000000 : ℝ)*x 1 + (-440925173/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4044141713/5000000000 : ℝ)^21 ≤ (4809008252641/6250000000000 : ℝ)^17 := by
    have hnat : (4044141713 : ℕ)^21*6250000000000^17 ≤ 4809008252641^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4044141713 5000000000 4809008252641 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155361233/1250000000 : ℝ)^21 ≤ (1521906495041/20000000000000 : ℝ)^17 := by
    have hnat : (155361233 : ℕ)^21*20000000000000^17 ≤ 1521906495041^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155361233 1250000000 1521906495041 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440925173/2000000000 : ℝ)^21 ≤ (7723167731977/50000000000000 : ℝ)^17 := by
    have hnat : (440925173 : ℕ)^21*50000000000000^17 ≤ 7723167731977^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440925173 2000000000 7723167731977 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4044141713/5000000000 : ℝ), (-155361233/1250000000 : ℝ), (-440925173/2000000000 : ℝ)] ![(4809008252641/6250000000000 : ℝ), (1521906495041/20000000000000 : ℝ), (7723167731977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4044141713/5000000000 : ℝ)|^21 ≤ (4809008252641/6250000000000 : ℝ)^17
        have hw : |(4044141713/5000000000 : ℝ)|=(4044141713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-155361233/1250000000 : ℝ)|^21 ≤ (1521906495041/20000000000000 : ℝ)^17
        have hw : |(-155361233/1250000000 : ℝ)|=(155361233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-440925173/2000000000 : ℝ)|^21 ≤ (7723167731977/50000000000000 : ℝ)^17
        have hw : |(-440925173/2000000000 : ℝ)|=(440925173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_17 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1 : ℝ)*x 0 + (0 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1 : ℝ)^21 ≤ (1 : ℝ)^17 := by
    have hnat : (1 : ℕ)^21*1^17 ≤ 1^17*1^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^21 ≤ (0 : ℝ)^17 := by
    have hnat : (0 : ℕ)^21*1^17 ≤ 0^17*1^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^21 ≤ (0 : ℝ)^17 := by
    have hnat : (0 : ℕ)^21*1^17 ≤ 0^17*1^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1 : ℝ)|^21 ≤ (1 : ℝ)^17
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^21 ≤ (0 : ℝ)^17
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^21 ≤ (0 : ℝ)^17
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1442802851/2000000000 : ℝ)*x 0 + (-1811508379/10000000000 : ℝ)*x 1 + (2835294759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1442802851/2000000000 : ℝ)^21 ≤ (66804678396361/100000000000000 : ℝ)^17 := by
    have hnat : (1442802851 : ℕ)^21*100000000000000^17 ≤ 66804678396361^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1442802851 2000000000 66804678396361 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1811508379/10000000000 : ℝ)^21 ≤ (484754217953/4000000000000 : ℝ)^17 := by
    have hnat : (1811508379 : ℕ)^21*4000000000000^17 ≤ 484754217953^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811508379 10000000000 484754217953 4000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2835294759/10000000000 : ℝ)^21 ≤ (21076466139699/100000000000000 : ℝ)^17 := by
    have hnat : (2835294759 : ℕ)^21*100000000000000^17 ≤ 21076466139699^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835294759 10000000000 21076466139699 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1442802851/2000000000 : ℝ), (-1811508379/10000000000 : ℝ), (2835294759/10000000000 : ℝ)] ![(66804678396361/100000000000000 : ℝ), (484754217953/4000000000000 : ℝ), (21076466139699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1442802851/2000000000 : ℝ)|^21 ≤ (66804678396361/100000000000000 : ℝ)^17
        have hw : |(1442802851/2000000000 : ℝ)|=(1442802851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1811508379/10000000000 : ℝ)|^21 ≤ (484754217953/4000000000000 : ℝ)^17
        have hw : |(-1811508379/10000000000 : ℝ)|=(1811508379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2835294759/10000000000 : ℝ)|^21 ≤ (21076466139699/100000000000000 : ℝ)^17
        have hw : |(2835294759/10000000000 : ℝ)|=(2835294759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (252701/10000000000 : ℝ)*x 0 + (-8841071369/10000000000 : ℝ)*x 1 + (512364219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252701/10000000000 : ℝ)^21 ≤ (817763/390625000000 : ℝ)^17 := by
    have hnat : (252701 : ℕ)^21*390625000000^17 ≤ 817763^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252701 10000000000 817763 390625000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8841071369/10000000000 : ℝ)^21 ≤ (85885097536053/100000000000000 : ℝ)^17 := by
    have hnat : (8841071369 : ℕ)^21*100000000000000^17 ≤ 85885097536053^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8841071369 10000000000 85885097536053 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512364219/2500000000 : ℝ)^21 ≤ (7057346550723/50000000000000 : ℝ)^17 := by
    have hnat : (512364219 : ℕ)^21*50000000000000^17 ≤ 7057346550723^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512364219 2500000000 7057346550723 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(252701/10000000000 : ℝ), (-8841071369/10000000000 : ℝ), (512364219/2500000000 : ℝ)] ![(817763/390625000000 : ℝ), (85885097536053/100000000000000 : ℝ), (7057346550723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(252701/10000000000 : ℝ)|^21 ≤ (817763/390625000000 : ℝ)^17
        have hw : |(252701/10000000000 : ℝ)|=(252701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8841071369/10000000000 : ℝ)|^21 ≤ (85885097536053/100000000000000 : ℝ)^17
        have hw : |(-8841071369/10000000000 : ℝ)|=(8841071369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(512364219/2500000000 : ℝ)|^21 ≤ (7057346550723/50000000000000 : ℝ)^17
        have hw : |(512364219/2500000000 : ℝ)|=(512364219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3915494569/5000000000 : ℝ)*x 0 + (391729097/2000000000 : ℝ)*x 1 + (188413423/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3915494569/5000000000 : ℝ)^21 ≤ (7393197317147/10000000000000 : ℝ)^17 := by
    have hnat : (3915494569 : ℕ)^21*10000000000000^17 ≤ 7393197317147^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3915494569 5000000000 7393197317147 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (391729097/2000000000 : ℝ)^21 ≤ (13346187098969/100000000000000 : ℝ)^17 := by
    have hnat : (391729097 : ℕ)^21*100000000000000^17 ≤ 13346187098969^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391729097 2000000000 13346187098969 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188413423/1000000000 : ℝ)^21 ≤ (2544367943571/20000000000000 : ℝ)^17 := by
    have hnat : (188413423 : ℕ)^21*20000000000000^17 ≤ 2544367943571^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188413423 1000000000 2544367943571 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3915494569/5000000000 : ℝ), (391729097/2000000000 : ℝ), (188413423/1000000000 : ℝ)] ![(7393197317147/10000000000000 : ℝ), (13346187098969/100000000000000 : ℝ), (2544367943571/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3915494569/5000000000 : ℝ)|^21 ≤ (7393197317147/10000000000000 : ℝ)^17
        have hw : |(3915494569/5000000000 : ℝ)|=(3915494569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(391729097/2000000000 : ℝ)|^21 ≤ (13346187098969/100000000000000 : ℝ)^17
        have hw : |(391729097/2000000000 : ℝ)|=(391729097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(188413423/1000000000 : ℝ)|^21 ≤ (2544367943571/20000000000000 : ℝ)^17
        have hw : |(188413423/1000000000 : ℝ)|=(188413423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_23 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (336467527/1250000000 : ℝ)*x 0 + (-4940215069/10000000000 : ℝ)*x 1 + (-143951487/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336467527/1250000000 : ℝ)^21 ≤ (4941551241453/25000000000000 : ℝ)^17 := by
    have hnat : (336467527 : ℕ)^21*25000000000000^17 ≤ 4941551241453^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336467527 1250000000 4941551241453 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4940215069/10000000000 : ℝ)^21 ≤ (20924546864487/50000000000000 : ℝ)^17 := by
    have hnat : (4940215069 : ℕ)^21*50000000000000^17 ≤ 20924546864487^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4940215069 10000000000 20924546864487 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (143951487/312500000 : ℝ)^21 ≤ (19192350643333/50000000000000 : ℝ)^17 := by
    have hnat : (143951487 : ℕ)^21*50000000000000^17 ≤ 19192350643333^17*312500000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143951487 312500000 19192350643333 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336467527/1250000000 : ℝ), (-4940215069/10000000000 : ℝ), (-143951487/312500000 : ℝ)] ![(4941551241453/25000000000000 : ℝ), (20924546864487/50000000000000 : ℝ), (19192350643333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336467527/1250000000 : ℝ)|^21 ≤ (4941551241453/25000000000000 : ℝ)^17
        have hw : |(336467527/1250000000 : ℝ)|=(336467527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4940215069/10000000000 : ℝ)|^21 ≤ (20924546864487/50000000000000 : ℝ)^17
        have hw : |(-4940215069/10000000000 : ℝ)|=(4940215069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-143951487/312500000 : ℝ)|^21 ≤ (19192350643333/50000000000000 : ℝ)^17
        have hw : |(-143951487/312500000 : ℝ)|=(143951487/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s0_27 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7676269383/10000000000 : ℝ)*x 0 + (-441508431/5000000000 : ℝ)*x 1 + (3030130681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7676269383/10000000000 : ℝ)^21 ≤ (72131792767877/100000000000000 : ℝ)^17 := by
    have hnat : (7676269383 : ℕ)^21*100000000000000^17 ≤ 72131792767877^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7676269383 10000000000 72131792767877 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441508431/5000000000 : ℝ)^21 ≤ (4988404956293/100000000000000 : ℝ)^17 := by
    have hnat : (441508431 : ℕ)^21*100000000000000^17 ≤ 4988404956293^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441508431 5000000000 4988404956293 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3030130681/10000000000 : ℝ)^21 ≤ (11439901130929/50000000000000 : ℝ)^17 := by
    have hnat : (3030130681 : ℕ)^21*50000000000000^17 ≤ 11439901130929^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3030130681 10000000000 11439901130929 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7676269383/10000000000 : ℝ), (-441508431/5000000000 : ℝ), (3030130681/10000000000 : ℝ)] ![(72131792767877/100000000000000 : ℝ), (4988404956293/100000000000000 : ℝ), (11439901130929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7676269383/10000000000 : ℝ)|^21 ≤ (72131792767877/100000000000000 : ℝ)^17
        have hw : |(7676269383/10000000000 : ℝ)|=(7676269383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441508431/5000000000 : ℝ)|^21 ≤ (4988404956293/100000000000000 : ℝ)^17
        have hw : |(-441508431/5000000000 : ℝ)|=(441508431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3030130681/10000000000 : ℝ)|^21 ≤ (11439901130929/50000000000000 : ℝ)^17
        have hw : |(3030130681/10000000000 : ℝ)|=(3030130681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-16673237/200000000 : ℝ)*x 0 + (-5606587223/10000000000 : ℝ)*x 1 + (5373082401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16673237/200000000 : ℝ)^21 ≤ (2323139072739/50000000000000 : ℝ)^17 := by
    have hnat : (16673237 : ℕ)^21*50000000000000^17 ≤ 2323139072739^17*200000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16673237 200000000 2323139072739 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5606587223/10000000000 : ℝ)^21 ≤ (24464640713383/50000000000000 : ℝ)^17 := by
    have hnat : (5606587223 : ℕ)^21*50000000000000^17 ≤ 24464640713383^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5606587223 10000000000 24464640713383 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5373082401/10000000000 : ℝ)^21 ≤ (23212220207361/50000000000000 : ℝ)^17 := by
    have hnat : (5373082401 : ℕ)^21*50000000000000^17 ≤ 23212220207361^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373082401 10000000000 23212220207361 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16673237/200000000 : ℝ), (-5606587223/10000000000 : ℝ), (5373082401/10000000000 : ℝ)] ![(2323139072739/50000000000000 : ℝ), (24464640713383/50000000000000 : ℝ), (23212220207361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16673237/200000000 : ℝ)|^21 ≤ (2323139072739/50000000000000 : ℝ)^17
        have hw : |(-16673237/200000000 : ℝ)|=(16673237/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5606587223/10000000000 : ℝ)|^21 ≤ (24464640713383/50000000000000 : ℝ)^17
        have hw : |(-5606587223/10000000000 : ℝ)|=(5606587223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5373082401/10000000000 : ℝ)|^21 ≤ (23212220207361/50000000000000 : ℝ)^17
        have hw : |(5373082401/10000000000 : ℝ)|=(5373082401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (544633401/1000000000 : ℝ)*x 0 + (1675171509/5000000000 : ℝ)*x 1 + (3453320723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544633401/1000000000 : ℝ)^21 ≤ (11801879286413/25000000000000 : ℝ)^17 := by
    have hnat : (544633401 : ℕ)^21*25000000000000^17 ≤ 11801879286413^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544633401 1000000000 11801879286413 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1675171509/5000000000 : ℝ)^21 ≤ (3237841508657/12500000000000 : ℝ)^17 := by
    have hnat : (1675171509 : ℕ)^21*12500000000000^17 ≤ 3237841508657^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1675171509 5000000000 3237841508657 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3453320723/10000000000 : ℝ)^21 ≤ (5377950155971/20000000000000 : ℝ)^17 := by
    have hnat : (3453320723 : ℕ)^21*20000000000000^17 ≤ 5377950155971^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3453320723 10000000000 5377950155971 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544633401/1000000000 : ℝ), (1675171509/5000000000 : ℝ), (3453320723/10000000000 : ℝ)] ![(11801879286413/25000000000000 : ℝ), (3237841508657/12500000000000 : ℝ), (5377950155971/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544633401/1000000000 : ℝ)|^21 ≤ (11801879286413/25000000000000 : ℝ)^17
        have hw : |(544633401/1000000000 : ℝ)|=(544633401/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1675171509/5000000000 : ℝ)|^21 ≤ (3237841508657/12500000000000 : ℝ)^17
        have hw : |(1675171509/5000000000 : ℝ)|=(1675171509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3453320723/10000000000 : ℝ)|^21 ≤ (5377950155971/20000000000000 : ℝ)^17
        have hw : |(3453320723/10000000000 : ℝ)|=(3453320723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5451215499/10000000000 : ℝ)*x 0 + (-1673577367/5000000000 : ℝ)*x 1 + (-1725525701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5451215499/10000000000 : ℝ)^21 ≤ (11814947474189/25000000000000 : ℝ)^17 := by
    have hnat : (5451215499 : ℕ)^21*25000000000000^17 ≤ 11814947474189^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451215499 10000000000 11814947474189 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1673577367/5000000000 : ℝ)^21 ≤ (1617017858327/6250000000000 : ℝ)^17 := by
    have hnat : (1673577367 : ℕ)^21*6250000000000^17 ≤ 1617017858327^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1673577367 5000000000 1617017858327 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1725525701/5000000000 : ℝ)^21 ≤ (3358490544497/12500000000000 : ℝ)^17 := by
    have hnat : (1725525701 : ℕ)^21*12500000000000^17 ≤ 3358490544497^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1725525701 5000000000 3358490544497 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5451215499/10000000000 : ℝ), (-1673577367/5000000000 : ℝ), (-1725525701/5000000000 : ℝ)] ![(11814947474189/25000000000000 : ℝ), (1617017858327/6250000000000 : ℝ), (3358490544497/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5451215499/10000000000 : ℝ)|^21 ≤ (11814947474189/25000000000000 : ℝ)^17
        have hw : |(5451215499/10000000000 : ℝ)|=(5451215499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1673577367/5000000000 : ℝ)|^21 ≤ (1617017858327/6250000000000 : ℝ)^17
        have hw : |(-1673577367/5000000000 : ℝ)|=(1673577367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1725525701/5000000000 : ℝ)|^21 ≤ (3358490544497/12500000000000 : ℝ)^17
        have hw : |(-1725525701/5000000000 : ℝ)|=(1725525701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322045_s1_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2578394429/5000000000 : ℝ)*x 0 + (-440468143/1250000000 : ℝ)*x 1 + (3599658533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2578394429/5000000000 : ℝ)^21 ≤ (8825389839871/20000000000000 : ℝ)^17 := by
    have hnat : (2578394429 : ℕ)^21*20000000000000^17 ≤ 8825389839871^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2578394429 5000000000 8825389839871 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440468143/1250000000 : ℝ)^21 ≤ (27568765014983/100000000000000 : ℝ)^17 := by
    have hnat : (440468143 : ℕ)^21*100000000000000^17 ≤ 27568765014983^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440468143 1250000000 27568765014983 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3599658533/10000000000 : ℝ)^21 ≤ (884508930489/3125000000000 : ℝ)^17 := by
    have hnat : (3599658533 : ℕ)^21*3125000000000^17 ≤ 884508930489^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3599658533 10000000000 884508930489 3125000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2578394429/5000000000 : ℝ), (-440468143/1250000000 : ℝ), (3599658533/10000000000 : ℝ)] ![(8825389839871/20000000000000 : ℝ), (27568765014983/100000000000000 : ℝ), (884508930489/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2578394429/5000000000 : ℝ)|^21 ≤ (8825389839871/20000000000000 : ℝ)^17
        have hw : |(2578394429/5000000000 : ℝ)|=(2578394429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440468143/1250000000 : ℝ)|^21 ≤ (27568765014983/100000000000000 : ℝ)^17
        have hw : |(-440468143/1250000000 : ℝ)|=(440468143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3599658533/10000000000 : ℝ)|^21 ≤ (884508930489/3125000000000 : ℝ)^17
        have hw : |(3599658533/10000000000 : ℝ)|=(3599658533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322045 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (167697/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((8763/400000000 : ℝ)*X 0 0+(-6501747287/10000000000 : ℝ)*X 0 1+(4882488859/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5352195123/10000000000 : ℝ)*X 1 0+(3318614287/10000000000 : ℝ)*X 1 1+(448593481/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2967280977/5000000000 : ℝ)*X 2 0+(-2966642637/10000000000 : ℝ)*X 2 1+(-3278875473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1356794657/2500000000 : ℝ)*X 0 0+(-1142773129/5000000000 : ℝ)*X 0 1+(445656189/1000000000 : ℝ)*X 0 2+(1356794657/2500000000 : ℝ)*X 1 0+(-1142773129/5000000000 : ℝ)*X 1 1+(445656189/1000000000 : ℝ)*X 1 2+(1356794657/2500000000 : ℝ)*X 2 0+(-1142773129/5000000000 : ℝ)*X 2 1+(445656189/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((2214687/10000000000 : ℝ)*X 0 0+(-4319632503/5000000000 : ℝ)*X 0 1+(1164338521/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3084924611/10000000000 : ℝ)*X 1 0+(5104825303/10000000000 : ℝ)*X 1 1+(1019722337/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((967027369/2000000000 : ℝ)*X 2 0+(-45683991/200000000 : ℝ)*X 2 1+(-101206961/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2580997501/5000000000 : ℝ)*X 0 0+(-90271643/2500000000 : ℝ)*X 0 1+(95117463/156250000 : ℝ)*X 0 2+(2580997501/5000000000 : ℝ)*X 1 0+(-90271643/2500000000 : ℝ)*X 1 1+(95117463/156250000 : ℝ)*X 1 2+(2580997501/5000000000 : ℝ)*X 2 0+(-90271643/2500000000 : ℝ)*X 2 1+(95117463/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((1738073/10000000000 : ℝ)*X 0 0+(-221157693/500000000 : ℝ)*X 0 1+(6922929587/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1056390723/5000000000 : ℝ)*X 1 0+(896399719/2500000000 : ℝ)*X 1 1+(6360100159/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4044141713/5000000000 : ℝ)*X 2 0+(-155361233/1250000000 : ℝ)*X 2 1+(-440925173/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_17 : ((1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_17 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1442802851/2000000000 : ℝ)*X 0 0+(-1811508379/10000000000 : ℝ)*X 0 1+(2835294759/10000000000 : ℝ)*X 0 2+(1442802851/2000000000 : ℝ)*X 1 0+(-1811508379/10000000000 : ℝ)*X 1 1+(2835294759/10000000000 : ℝ)*X 1 2+(1442802851/2000000000 : ℝ)*X 2 0+(-1811508379/10000000000 : ℝ)*X 2 1+(2835294759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((252701/10000000000 : ℝ)*X 0 0+(-8841071369/10000000000 : ℝ)*X 0 1+(512364219/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3915494569/5000000000 : ℝ)*X 1 0+(391729097/2000000000 : ℝ)*X 1 1+(188413423/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((336467527/1250000000 : ℝ)*X 2 0+(-4940215069/10000000000 : ℝ)*X 2 1+(-143951487/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((7676269383/10000000000 : ℝ)*X 0 0+(-441508431/5000000000 : ℝ)*X 0 1+(3030130681/10000000000 : ℝ)*X 0 2+(7676269383/10000000000 : ℝ)*X 1 0+(-441508431/5000000000 : ℝ)*X 1 1+(3030130681/10000000000 : ℝ)*X 1 2+(7676269383/10000000000 : ℝ)*X 2 0+(-441508431/5000000000 : ℝ)*X 2 1+(3030130681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((24333/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(24333/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (613101180293892617007/78125000000000000000000000 : ℝ) := by norm_num
    linear_combination (848321322569/1000000000000 : ℝ)*(base7) + (41631/12500000000 : ℝ)*(base43) + (198673006479/500000000000 : ℝ)*(base50) + (7170759/500000000000 : ℝ)*(base54) + (926047785941/500000000000 : ℝ)*(major_s0_0) + (926046120701/500000000000 : ℝ)*(major_s0_1) + (463020307591/250000000000 : ℝ)*(major_s0_2) + (20609637/1000000000000 : ℝ)*(sp_s0_0) + (24348959/500000000000 : ℝ)*(sp_s0_2) + (24046927/1000000000000 : ℝ)*(sp_s0_6) + (454055343141/200000000000 : ℝ)*(sp_s0_7) + (2270300655821/1000000000000 : ℝ)*(sp_s0_8) + (1135117142953/500000000000 : ℝ)*(sp_s0_9) + (90398383503/50000000000 : ℝ)*(sp_s0_13) + (14995073999/15625000000 : ℝ)*(f.failure) + (2270300655821/1000000000000 : ℝ)*(f.sum) + (418405928973661/1250000000000000000000000000 : ℝ)*base63 + (265667331665143/500000000000000000000000000 : ℝ)*base65 + (981263979382173/1000000000000000000000000000 : ℝ)*base66 + (23321585622597/625000000000000000000000000 : ℝ)*base69 + (406922822594809/2500000000000000000000000000 : ℝ)*base71 + (269898864484693/1000000000000000000000000000 : ℝ)*base72 + (213305240353467/1250000000000000000000000000 : ℝ)*base75 + (107432877634547/1250000000000000000000000000 : ℝ)*base77 + (162569823683433/500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (277/312500000000000 : ℝ)*base87 + (277/312500000000000 : ℝ)*base89 + (277/312500000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-62527/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-62527/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20384109958044446147133/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1201167586367/1000000000000 : ℝ)*(base7) + (117730733987/1000000000000 : ℝ)*(base40) + (15883079/1000000000000 : ℝ)*(base53) + (916090949069/500000000000 : ℝ)*(major_s0_0) + (791233513227/500000000000 : ℝ)*(major_s0_1) + (12659609147/8000000000 : ℝ)*(major_s0_2) + (15915731/1000000000000 : ℝ)*(sp_s0_0) + (1908729/62500000000 : ℝ)*(sp_s0_1) + (1673482561761/1000000000000 : ℝ)*(sp_s0_14) + (418366984457/250000000000 : ℝ)*(sp_s0_15) + (1673514360571/1000000000000 : ℝ)*(sp_s0_16) + (62428717921/250000000000 : ℝ)*(sp_s0_17) + (2021110890847/1000000000000 : ℝ)*(sp_s0_20) + (7570747/250000000000 : ℝ)*(sp_s0_27) + (204993396867/250000000000 : ℝ)*(f.failure) + (1673514360571/1000000000000 : ℝ)*(f.sum) + (118019995357043/2500000000000000000000000000 : ℝ)*base63 + (555267713669/16000000000000000000000000 : ℝ)*base64 + (540089481217429/1000000000000000000000000000 : ℝ)*base67 + (2499517690349/20000000000000000000000000 : ℝ)*base69 + (4734841116165859/10000000000000000000000000000 : ℝ)*base71 + (111584057818963/1000000000000000000000000000 : ℝ)*base73 + (488192739906709/1250000000000000000000000000 : ℝ)*base75 + (480045825401123/1250000000000000000000000000 : ℝ)*base77 + (56919357920451/125000000000000000000000000 : ℝ)*base78 + (1233/2500000000000000 : ℝ)*base87 + (1233/2500000000000000 : ℝ)*base89 + (1233/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14123/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14123/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17269183822372240028559/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (225045852651/200000000000 : ℝ)*(base7) + (14486063923/200000000000 : ℝ)*(base40) + (12680448611/25000000000 : ℝ)*(base43) + (6356463657/62500000000 : ℝ)*(base50) + (380304412817/250000000000 : ℝ)*(major_s0_0) + (253499926707/250000000000 : ℝ)*(major_s0_1) + (380304412817/250000000000 : ℝ)*(major_s0_2) + (14560399/500000000000 : ℝ)*(sp_s0_2) + (161419781/1000000000000 : ℝ)*(sp_s0_7) + (4555111/1000000000000 : ℝ)*(sp_s0_20) + (1117822911823/1000000000000 : ℝ)*(sp_s0_21) + (406300569011/250000000000 : ℝ)*(sp_s0_22) + (558977605403/500000000000 : ℝ)*(sp_s0_23) + (1913461223647/1000000000000 : ℝ)*(sp_s0_27) + (394118257751/500000000000 : ℝ)*(f.failure) + (406300569011/250000000000 : ℝ)*(f.sum) + (50934985076473/156250000000000000000000000 : ℝ)*base62 + (61977445557359/500000000000000000000000000 : ℝ)*base64 + (72802749353389/500000000000000000000000000 : ℝ)*base67 + (47120250335761/625000000000000000000000000 : ℝ)*base68 + (1198424112879839/2500000000000000000000000000 : ℝ)*base70 + (245603804557359/500000000000000000000000000 : ℝ)*base73 + (127132383470131/625000000000000000000000000 : ℝ)*base74 + (337656006523261/625000000000000000000000000 : ℝ)*base76 + (70676087027687/125000000000000000000000000 : ℝ)*base79 + (3451/5000000000000000 : ℝ)*base86 + (3451/5000000000000000 : ℝ)*base88 + (3451/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (24333/50000 : ℝ) ^ (41/8 : ℝ) ≤ (2494775471247329807/100000000000000000000 : ℝ) := by
    have hpowers : (24333/50000 : ℝ)^41 ≤ (2494775471247329807/100000000000000000000 : ℝ)^8 := by
      have hnat : (24333 : ℕ)^41*100000000000000000000^8 ≤ 2494775471247329807^8*50000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24333 50000 2494775471247329807 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24333/50000 : ℝ)) (X := (2494775471247329807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (102494775471247329807/100000000000000000000 : ℝ) ≤ (10048197025132353/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (102494775471247329807/100000000000000000000 : ℝ)^8 ≤ (10048197025132353/10000000000000000 : ℝ)^41 := by
      have hnat : (102494775471247329807 : ℕ)^8*10000000000000000^41 ≤ 10048197025132353^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102494775471247329807 100000000000000000000 10048197025132353 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10048197025132353/10000000000000000 : ℝ)) (X := (102494775471247329807/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (52494775471247329807/50000000000000000000 : ℝ) ≤ (2523864719076999/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (52494775471247329807/50000000000000000000 : ℝ)^8 ≤ (2523864719076999/2500000000000000 : ℝ)^41 := by
      have hnat : (52494775471247329807 : ℕ)^8*2500000000000000^41 ≤ 2523864719076999^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52494775471247329807 50000000000000000000 2523864719076999 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2523864719076999/2500000000000000 : ℝ)) (X := (52494775471247329807/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(48197025132353/4866600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(15753950391881/1622200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (24333/50000 : ℝ)) (alpha := (48197025132353/4866600000000000 : ℝ)) (beta := (15753950391881/1622200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (24333/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(48197025132353/4866600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(15753950391881/1622200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (62527/100000 : ℝ) ^ (41/8 : ℝ) ≤ (1126565435156873233/12500000000000000000 : ℝ) := by
    have hpowers : (62527/100000 : ℝ)^41 ≤ (1126565435156873233/12500000000000000000 : ℝ)^8 := by
      have hnat : (62527 : ℕ)^41*12500000000000000000^8 ≤ 1126565435156873233^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62527 100000 1126565435156873233 12500000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62527/100000 : ℝ)) (X := (1126565435156873233/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (13626565435156873233/12500000000000000000 : ℝ) ≤ (2033960256623299/2000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (13626565435156873233/12500000000000000000 : ℝ)^8 ≤ (2033960256623299/2000000000000000 : ℝ)^41 := by
      have hnat : (13626565435156873233 : ℕ)^8*2000000000000000^41 ≤ 2033960256623299^41*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13626565435156873233 12500000000000000000 2033960256623299 2000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2033960256623299/2000000000000000 : ℝ)) (X := (13626565435156873233/12500000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (7376565435156873233/6250000000000000000 : ℝ) ≤ (5164327161629717/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (7376565435156873233/6250000000000000000 : ℝ)^8 ≤ (5164327161629717/5000000000000000 : ℝ)^41 := by
      have hnat : (7376565435156873233 : ℕ)^8*5000000000000000^41 ≤ 5164327161629717^41*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7376565435156873233 6250000000000000000 5164327161629717 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5164327161629717/5000000000000000 : ℝ)) (X := (7376565435156873233/6250000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(33960256623299/1250540000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(158853040142939/6252700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (62527/100000 : ℝ)) (alpha := (33960256623299/1250540000000000 : ℝ)) (beta := (158853040142939/6252700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (62527/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(33960256623299/1250540000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(158853040142939/6252700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (14123/20000 : ℝ) ^ (41/8 : ℝ) ≤ (16811131204793579459/100000000000000000000 : ℝ) := by
    have hpowers : (14123/20000 : ℝ)^41 ≤ (16811131204793579459/100000000000000000000 : ℝ)^8 := by
      have hnat : (14123 : ℕ)^41*100000000000000000000^8 ≤ 16811131204793579459^8*20000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14123 20000 16811131204793579459 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14123/20000 : ℝ)) (X := (16811131204793579459/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (116811131204793579459/100000000000000000000 : ℝ) ≤ (10307839663718537/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (116811131204793579459/100000000000000000000 : ℝ)^8 ≤ (10307839663718537/10000000000000000 : ℝ)^41 := by
      have hnat : (116811131204793579459 : ℕ)^8*10000000000000000^41 ≤ 10307839663718537^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116811131204793579459 100000000000000000000 10307839663718537 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10307839663718537/10000000000000000 : ℝ)) (X := (116811131204793579459/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (66811131204793579459/50000000000000000000 : ℝ) ≤ (10581852926004361/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (66811131204793579459/50000000000000000000 : ℝ)^8 ≤ (10581852926004361/10000000000000000 : ℝ)^41 := by
      have hnat : (66811131204793579459 : ℕ)^8*10000000000000000^41 ≤ 10581852926004361^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66811131204793579459 50000000000000000000 10581852926004361 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10581852926004361/10000000000000000 : ℝ)) (X := (66811131204793579459/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(307839663718537/7061500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(267591076451/6895996093750 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (14123/20000 : ℝ)) (alpha := (307839663718537/7061500000000000 : ℝ)) (beta := (267591076451/6895996093750 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (14123/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(307839663718537/7061500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(267591076451/6895996093750 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-16673237/200000000 : ℝ)*X 0 0+(-5606587223/10000000000 : ℝ)*X 0 1+(5373082401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((544633401/1000000000 : ℝ)*X 1 0+(1675171509/5000000000 : ℝ)*X 1 1+(3453320723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5451215499/10000000000 : ℝ)*X 2 0+(-1673577367/5000000000 : ℝ)*X 2 1+(-1725525701/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2578394429/5000000000 : ℝ)*X 0 0+(-440468143/1250000000 : ℝ)*X 0 1+(3599658533/10000000000 : ℝ)*X 0 2+(2578394429/5000000000 : ℝ)*X 1 0+(-440468143/1250000000 : ℝ)*X 1 1+(3599658533/10000000000 : ℝ)*X 1 2+(2578394429/5000000000 : ℝ)*X 2 0+(-440468143/1250000000 : ℝ)*X 2 1+(3599658533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322045_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-42897/5000 : ℝ) < ((-19299/10000 : ℝ)*P 0+(-19299/10000 : ℝ)*P 1+(-19299/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-42897/5000 : ℝ) < (-306266394233990084657966239361372169/35812856035655000000000000000000000 : ℝ) := by norm_num
    linear_combination (16143/1000000000000 : ℝ)*(base8) + (6717/500000000000 : ℝ)*(base10) + (23787/500000000000 : ℝ)*(base21) + (1841/50000000000 : ℝ)*(base39) + (604266281657/1000000000000 : ℝ)*(base40) + (5456457963/62500000000 : ℝ)*(base50) + (36389/500000000000 : ℝ)*(base59) + (423350191/7812500000 : ℝ)*(base60) + (19299/10000 : ℝ)*(major_s1_0) + (19299/10000 : ℝ)*(major_s1_1) + (19299/10000 : ℝ)*(major_s1_2) + (712654674323/250000000000 : ℝ)*(sp_s1_0) + (2850618726869/1000000000000 : ℝ)*(sp_s1_1) + (570123735859/200000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2850618726869/1000000000000 : ℝ)*(f.sum) + (29025611106133371/44153441050000000000000000000 : ℝ)*base63 + (888406665433/35307500000000000000000000 : ℝ)*base64 + (24531735704621/156317500000000000000000000 : ℝ)*base66 + (4382105203313/14123000000000000000000000 : ℝ)*base69 + (165615195306944387/572758265000000000000000000000 : ℝ)*base71 + (14683756593857/81110000000000000000000000 : ℝ)*base72 + (38546297214193/125054000000000000000000000 : ℝ)*base75 + (1675116585083/8111000000000000000000000 : ℝ)*base77 + (263489004926052977/507156497000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p022_b024 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 45 ≤ c.val) (hhi : c.val < 46)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=45 := by omega
  rcases hc with rfl
  · exact collision_c322045 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 45 ≤ c.val) (hhi : c.val < 46)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p022_b024 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

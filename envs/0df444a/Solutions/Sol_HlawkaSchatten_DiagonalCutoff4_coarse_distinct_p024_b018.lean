-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b018
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:56:09.53998+00:00
-- url     : https://prove2.me/submissions/c4d9ad2c-8c76-4b8b-953e-b7b761272ebf

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
theorem collision_support_c324038_s0_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-710929711/10000000000 : ℝ)*x 0 + (-4476028629/10000000000 : ℝ)*x 1 + (-6496654157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (710929711/10000000000 : ℝ)^43 ≤ (3884964413579/100000000000000 : ℝ)^35 := by
    have hnat : (710929711 : ℕ)^43*100000000000000^35 ≤ 3884964413579^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710929711 10000000000 3884964413579 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476028629/10000000000 : ℝ)^43 ≤ (18623741771157/50000000000000 : ℝ)^35 := by
    have hnat : (4476028629 : ℕ)^43*50000000000000^35 ≤ 18623741771157^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476028629 10000000000 18623741771157 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6496654157/10000000000 : ℝ)^43 ≤ (29433776012389/50000000000000 : ℝ)^35 := by
    have hnat : (6496654157 : ℕ)^43*50000000000000^35 ≤ 29433776012389^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6496654157 10000000000 29433776012389 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-710929711/10000000000 : ℝ), (-4476028629/10000000000 : ℝ), (-6496654157/10000000000 : ℝ)] ![(3884964413579/100000000000000 : ℝ), (18623741771157/50000000000000 : ℝ), (29433776012389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-710929711/10000000000 : ℝ)|^43 ≤ (3884964413579/100000000000000 : ℝ)^35
        have hw : |(-710929711/10000000000 : ℝ)|=(710929711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4476028629/10000000000 : ℝ)|^43 ≤ (18623741771157/50000000000000 : ℝ)^35
        have hw : |(-4476028629/10000000000 : ℝ)|=(4476028629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6496654157/10000000000 : ℝ)|^43 ≤ (29433776012389/50000000000000 : ℝ)^35
        have hw : |(-6496654157/10000000000 : ℝ)|=(6496654157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s0_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5018652069/10000000000 : ℝ)*x 0 + (4162459019/10000000000 : ℝ)*x 1 + (-1514977339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5018652069/10000000000 : ℝ)^43 ≤ (42869641443971/100000000000000 : ℝ)^35 := by
    have hnat : (5018652069 : ℕ)^43*100000000000000^35 ≤ 42869641443971^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5018652069 10000000000 42869641443971 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4162459019/10000000000 : ℝ)^43 ≤ (34067812611829/100000000000000 : ℝ)^35 := by
    have hnat : (4162459019 : ℕ)^43*100000000000000^35 ≤ 34067812611829^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162459019 10000000000 34067812611829 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1514977339/5000000000 : ℝ)^43 ≤ (45044035013/195312500000 : ℝ)^35 := by
    have hnat : (1514977339 : ℕ)^43*195312500000^35 ≤ 45044035013^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514977339 5000000000 45044035013 195312500000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5018652069/10000000000 : ℝ), (4162459019/10000000000 : ℝ), (-1514977339/5000000000 : ℝ)] ![(42869641443971/100000000000000 : ℝ), (34067812611829/100000000000000 : ℝ), (45044035013/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5018652069/10000000000 : ℝ)|^43 ≤ (42869641443971/100000000000000 : ℝ)^35
        have hw : |(5018652069/10000000000 : ℝ)|=(5018652069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4162459019/10000000000 : ℝ)|^43 ≤ (34067812611829/100000000000000 : ℝ)^35
        have hw : |(4162459019/10000000000 : ℝ)|=(4162459019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1514977339/5000000000 : ℝ)|^43 ≤ (45044035013/195312500000 : ℝ)^35
        have hw : |(-1514977339/5000000000 : ℝ)|=(1514977339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s0_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5018652157/10000000000 : ℝ)*x 0 + (-1040614741/2500000000 : ℝ)*x 1 + (1514977319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5018652157/10000000000 : ℝ)^43 ≤ (4286964236749/10000000000000 : ℝ)^35 := by
    have hnat : (5018652157 : ℕ)^43*10000000000000^35 ≤ 4286964236749^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5018652157 10000000000 4286964236749 10000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040614741/2500000000 : ℝ)^43 ≤ (8516953014697/25000000000000 : ℝ)^35 := by
    have hnat : (1040614741 : ℕ)^43*25000000000000^35 ≤ 8516953014697^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040614741 2500000000 8516953014697 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1514977319/5000000000 : ℝ)^43 ≤ (5765636388151/25000000000000 : ℝ)^35 := by
    have hnat : (1514977319 : ℕ)^43*25000000000000^35 ≤ 5765636388151^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514977319 5000000000 5765636388151 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5018652157/10000000000 : ℝ), (-1040614741/2500000000 : ℝ), (1514977319/5000000000 : ℝ)] ![(4286964236749/10000000000000 : ℝ), (8516953014697/25000000000000 : ℝ), (5765636388151/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5018652157/10000000000 : ℝ)|^43 ≤ (4286964236749/10000000000000 : ℝ)^35
        have hw : |(5018652157/10000000000 : ℝ)|=(5018652157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1040614741/2500000000 : ℝ)|^43 ≤ (8516953014697/25000000000000 : ℝ)^35
        have hw : |(-1040614741/2500000000 : ℝ)|=(1040614741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1514977319/5000000000 : ℝ)|^43 ≤ (5765636388151/25000000000000 : ℝ)^35
        have hw : |(1514977319/5000000000 : ℝ)|=(1514977319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s0_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3855121211/5000000000 : ℝ)*x 0 + (-1609042193/10000000000 : ℝ)*x 1 + (-2335416397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3855121211/5000000000 : ℝ)^43 ≤ (18163311069249/25000000000000 : ℝ)^35 := by
    have hnat : (3855121211 : ℕ)^43*25000000000000^35 ≤ 18163311069249^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3855121211 5000000000 18163311069249 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1609042193/10000000000 : ℝ)^43 ≤ (5298847507903/50000000000000 : ℝ)^35 := by
    have hnat : (1609042193 : ℕ)^43*50000000000000^35 ≤ 5298847507903^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1609042193 10000000000 5298847507903 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2335416397/10000000000 : ℝ)^43 ≤ (334981214019/2000000000000 : ℝ)^35 := by
    have hnat : (2335416397 : ℕ)^43*2000000000000^35 ≤ 334981214019^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2335416397 10000000000 334981214019 2000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3855121211/5000000000 : ℝ), (-1609042193/10000000000 : ℝ), (-2335416397/10000000000 : ℝ)] ![(18163311069249/25000000000000 : ℝ), (5298847507903/50000000000000 : ℝ), (334981214019/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3855121211/5000000000 : ℝ)|^43 ≤ (18163311069249/25000000000000 : ℝ)^35
        have hw : |(3855121211/5000000000 : ℝ)|=(3855121211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1609042193/10000000000 : ℝ)|^43 ≤ (5298847507903/50000000000000 : ℝ)^35
        have hw : |(-1609042193/10000000000 : ℝ)|=(1609042193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2335416397/10000000000 : ℝ)|^43 ≤ (334981214019/2000000000000 : ℝ)^35
        have hw : |(-2335416397/10000000000 : ℝ)|=(2335416397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s0_7 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-339525533/5000000000 : ℝ)*x 0 + (-1148423617/2500000000 : ℝ)*x 1 + (-320362771/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (339525533/5000000000 : ℝ)^43 ≤ (3672051016059/100000000000000 : ℝ)^35 := by
    have hnat : (339525533 : ℕ)^43*100000000000000^35 ≤ 3672051016059^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339525533 5000000000 3672051016059 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1148423617/2500000000 : ℝ)^43 ≤ (4806755472529/12500000000000 : ℝ)^35 := by
    have hnat : (1148423617 : ℕ)^43*12500000000000^35 ≤ 4806755472529^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148423617 2500000000 4806755472529 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320362771/500000000 : ℝ)^43 ≤ (57873905188783/100000000000000 : ℝ)^35 := by
    have hnat : (320362771 : ℕ)^43*100000000000000^35 ≤ 57873905188783^35*500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320362771 500000000 57873905188783 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-339525533/5000000000 : ℝ), (-1148423617/2500000000 : ℝ), (-320362771/500000000 : ℝ)] ![(3672051016059/100000000000000 : ℝ), (4806755472529/12500000000000 : ℝ), (57873905188783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-339525533/5000000000 : ℝ)|^43 ≤ (3672051016059/100000000000000 : ℝ)^35
        have hw : |(-339525533/5000000000 : ℝ)|=(339525533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1148423617/2500000000 : ℝ)|^43 ≤ (4806755472529/12500000000000 : ℝ)^35
        have hw : |(-1148423617/2500000000 : ℝ)|=(1148423617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-320362771/500000000 : ℝ)|^43 ≤ (57873905188783/100000000000000 : ℝ)^35
        have hw : |(-320362771/500000000 : ℝ)|=(320362771/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s0_8 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5018833873/10000000000 : ℝ)*x 0 + (4401301471/10000000000 : ℝ)*x 1 + (-173039503/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5018833873/10000000000 : ℝ)^43 ≤ (42871549400197/100000000000000 : ℝ)^35 := by
    have hnat : (5018833873 : ℕ)^43*100000000000000^35 ≤ 42871549400197^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5018833873 10000000000 42871549400197 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4401301471/10000000000 : ℝ)^43 ≤ (36484965817131/100000000000000 : ℝ)^35 := by
    have hnat : (4401301471 : ℕ)^43*100000000000000^35 ≤ 36484965817131^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401301471 10000000000 36484965817131 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173039503/625000000 : ℝ)^43 ≤ (20643484772419/100000000000000 : ℝ)^35 := by
    have hnat : (173039503 : ℕ)^43*100000000000000^35 ≤ 20643484772419^35*625000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173039503 625000000 20643484772419 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5018833873/10000000000 : ℝ), (4401301471/10000000000 : ℝ), (-173039503/625000000 : ℝ)] ![(42871549400197/100000000000000 : ℝ), (36484965817131/100000000000000 : ℝ), (20643484772419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5018833873/10000000000 : ℝ)|^43 ≤ (42871549400197/100000000000000 : ℝ)^35
        have hw : |(5018833873/10000000000 : ℝ)|=(5018833873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4401301471/10000000000 : ℝ)|^43 ≤ (36484965817131/100000000000000 : ℝ)^35
        have hw : |(4401301471/10000000000 : ℝ)|=(4401301471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173039503/625000000 : ℝ)|^43 ≤ (20643484772419/100000000000000 : ℝ)^35
        have hw : |(-173039503/625000000 : ℝ)|=(173039503/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s0_9 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1254708467/2500000000 : ℝ)*x 0 + (-3902258319/10000000000 : ℝ)*x 1 + (1652362273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1254708467/2500000000 : ℝ)^43 ≤ (10717887336931/25000000000000 : ℝ)^35 := by
    have hnat : (1254708467 : ℕ)^43*25000000000000^35 ≤ 10717887336931^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254708467 2500000000 10717887336931 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3902258319/10000000000 : ℝ)^43 ≤ (1258816782301/4000000000000 : ℝ)^35 := by
    have hnat : (3902258319 : ℕ)^43*4000000000000^35 ≤ 1258816782301^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3902258319 10000000000 1258816782301 4000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1652362273/5000000000 : ℝ)^43 ≤ (25658031090573/100000000000000 : ℝ)^35 := by
    have hnat : (1652362273 : ℕ)^43*100000000000000^35 ≤ 25658031090573^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1652362273 5000000000 25658031090573 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1254708467/2500000000 : ℝ), (-3902258319/10000000000 : ℝ), (1652362273/5000000000 : ℝ)] ![(10717887336931/25000000000000 : ℝ), (1258816782301/4000000000000 : ℝ), (25658031090573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1254708467/2500000000 : ℝ)|^43 ≤ (10717887336931/25000000000000 : ℝ)^35
        have hw : |(1254708467/2500000000 : ℝ)|=(1254708467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3902258319/10000000000 : ℝ)|^43 ≤ (1258816782301/4000000000000 : ℝ)^35
        have hw : |(-3902258319/10000000000 : ℝ)|=(3902258319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1652362273/5000000000 : ℝ)|^43 ≤ (25658031090573/100000000000000 : ℝ)^35
        have hw : |(1652362273/5000000000 : ℝ)|=(1652362273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s0_13 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1522204223/2000000000 : ℝ)*x 0 + (-1407670981/10000000000 : ℝ)*x 1 + (-2643298533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1522204223/2000000000 : ℝ)^43 ≤ (71506277044437/100000000000000 : ℝ)^35 := by
    have hnat : (1522204223 : ℕ)^43*100000000000000^35 ≤ 71506277044437^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522204223 2000000000 71506277044437 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1407670981/10000000000 : ℝ)^43 ≤ (8992342728519/100000000000000 : ℝ)^35 := by
    have hnat : (1407670981 : ℕ)^43*100000000000000^35 ≤ 8992342728519^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1407670981 10000000000 8992342728519 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2643298533/10000000000 : ℝ)^43 ≤ (19501380216183/100000000000000 : ℝ)^35 := by
    have hnat : (2643298533 : ℕ)^43*100000000000000^35 ≤ 19501380216183^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643298533 10000000000 19501380216183 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1522204223/2000000000 : ℝ), (-1407670981/10000000000 : ℝ), (-2643298533/10000000000 : ℝ)] ![(71506277044437/100000000000000 : ℝ), (8992342728519/100000000000000 : ℝ), (19501380216183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1522204223/2000000000 : ℝ)|^43 ≤ (71506277044437/100000000000000 : ℝ)^35
        have hw : |(1522204223/2000000000 : ℝ)|=(1522204223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1407670981/10000000000 : ℝ)|^43 ≤ (8992342728519/100000000000000 : ℝ)^35
        have hw : |(-1407670981/10000000000 : ℝ)|=(1407670981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2643298533/10000000000 : ℝ)|^43 ≤ (19501380216183/100000000000000 : ℝ)^35
        have hw : |(-2643298533/10000000000 : ℝ)|=(2643298533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s0_14 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-23300819/1000000000 : ℝ)*x 0 + (-4484395651/10000000000 : ℝ)*x 1 + (-13180097/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23300819/1000000000 : ℝ)^43 ≤ (197346251547/20000000000000 : ℝ)^35 := by
    have hnat : (23300819 : ℕ)^43*20000000000000^35 ≤ 197346251547^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23300819 1000000000 197346251547 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484395651/10000000000 : ℝ)^43 ≤ (37333043020843/100000000000000 : ℝ)^35 := by
    have hnat : (4484395651 : ℕ)^43*100000000000000^35 ≤ 37333043020843^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484395651 10000000000 37333043020843 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13180097/19531250 : ℝ)^43 ≤ (15420056428823/25000000000000 : ℝ)^35 := by
    have hnat : (13180097 : ℕ)^43*25000000000000^35 ≤ 15420056428823^35*19531250^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13180097 19531250 15420056428823 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23300819/1000000000 : ℝ), (-4484395651/10000000000 : ℝ), (-13180097/19531250 : ℝ)] ![(197346251547/20000000000000 : ℝ), (37333043020843/100000000000000 : ℝ), (15420056428823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23300819/1000000000 : ℝ)|^43 ≤ (197346251547/20000000000000 : ℝ)^35
        have hw : |(-23300819/1000000000 : ℝ)|=(23300819/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4484395651/10000000000 : ℝ)|^43 ≤ (37333043020843/100000000000000 : ℝ)^35
        have hw : |(-4484395651/10000000000 : ℝ)|=(4484395651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13180097/19531250 : ℝ)|^43 ≤ (15420056428823/25000000000000 : ℝ)^35
        have hw : |(-13180097/19531250 : ℝ)|=(13180097/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s0_15 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2370545279/5000000000 : ℝ)*x 0 + (2138045669/5000000000 : ℝ)*x 1 + (-321560631/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2370545279/5000000000 : ℝ)^43 ≤ (39975442469501/100000000000000 : ℝ)^35 := by
    have hnat : (2370545279 : ℕ)^43*100000000000000^35 ≤ 39975442469501^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2370545279 5000000000 39975442469501 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2138045669/5000000000 : ℝ)^43 ≤ (8803489721399/25000000000000 : ℝ)^35 := by
    have hnat : (2138045669 : ℕ)^43*25000000000000^35 ≤ 8803489721399^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138045669 5000000000 8803489721399 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321560631/1000000000 : ℝ)^43 ≤ (6202649656733/25000000000000 : ℝ)^35 := by
    have hnat : (321560631 : ℕ)^43*25000000000000^35 ≤ 6202649656733^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321560631 1000000000 6202649656733 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2370545279/5000000000 : ℝ), (2138045669/5000000000 : ℝ), (-321560631/1000000000 : ℝ)] ![(39975442469501/100000000000000 : ℝ), (8803489721399/25000000000000 : ℝ), (6202649656733/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2370545279/5000000000 : ℝ)|^43 ≤ (39975442469501/100000000000000 : ℝ)^35
        have hw : |(2370545279/5000000000 : ℝ)|=(2370545279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2138045669/5000000000 : ℝ)|^43 ≤ (8803489721399/25000000000000 : ℝ)^35
        have hw : |(2138045669/5000000000 : ℝ)|=(2138045669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-321560631/1000000000 : ℝ)|^43 ≤ (6202649656733/25000000000000 : ℝ)^35
        have hw : |(-321560631/1000000000 : ℝ)|=(321560631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s0_16 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (275464589/500000000 : ℝ)*x 0 + (-380021199/1000000000 : ℝ)*x 1 + (35721833/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275464589/500000000 : ℝ)^43 ≤ (24037409898237/50000000000000 : ℝ)^35 := by
    have hnat : (275464589 : ℕ)^43*50000000000000^35 ≤ 24037409898237^35*500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275464589 500000000 24037409898237 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (380021199/1000000000 : ℝ)^43 ≤ (30462384664263/100000000000000 : ℝ)^35 := by
    have hnat : (380021199 : ℕ)^43*100000000000000^35 ≤ 30462384664263^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380021199 1000000000 30462384664263 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35721833/125000000 : ℝ)^43 ≤ (670712360041/3125000000000 : ℝ)^35 := by
    have hnat : (35721833 : ℕ)^43*3125000000000^35 ≤ 670712360041^35*125000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35721833 125000000 670712360041 3125000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(275464589/500000000 : ℝ), (-380021199/1000000000 : ℝ), (35721833/125000000 : ℝ)] ![(24037409898237/50000000000000 : ℝ), (30462384664263/100000000000000 : ℝ), (670712360041/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(275464589/500000000 : ℝ)|^43 ≤ (24037409898237/50000000000000 : ℝ)^35
        have hw : |(275464589/500000000 : ℝ)|=(275464589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-380021199/1000000000 : ℝ)|^43 ≤ (30462384664263/100000000000000 : ℝ)^35
        have hw : |(-380021199/1000000000 : ℝ)|=(380021199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35721833/125000000 : ℝ)|^43 ≤ (670712360041/3125000000000 : ℝ)^35
        have hw : |(35721833/125000000 : ℝ)|=(35721833/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s0_19 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8566423469/10000000000 : ℝ)*x 0 + (-1084604119/10000000000 : ℝ)*x 1 + (-1632134309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8566423469/10000000000 : ℝ)^43 ≤ (82687418605057/100000000000000 : ℝ)^35 := by
    have hnat : (8566423469 : ℕ)^43*100000000000000^35 ≤ 82687418605057^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8566423469 10000000000 82687418605057 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084604119/10000000000 : ℝ)^43 ≤ (6527724557283/100000000000000 : ℝ)^35 := by
    have hnat : (1084604119 : ℕ)^43*100000000000000^35 ≤ 6527724557283^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084604119 10000000000 6527724557283 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1632134309/10000000000 : ℝ)^43 ≤ (2696214207973/25000000000000 : ℝ)^35 := by
    have hnat : (1632134309 : ℕ)^43*25000000000000^35 ≤ 2696214207973^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1632134309 10000000000 2696214207973 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8566423469/10000000000 : ℝ), (-1084604119/10000000000 : ℝ), (-1632134309/10000000000 : ℝ)] ![(82687418605057/100000000000000 : ℝ), (6527724557283/100000000000000 : ℝ), (2696214207973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8566423469/10000000000 : ℝ)|^43 ≤ (82687418605057/100000000000000 : ℝ)^35
        have hw : |(8566423469/10000000000 : ℝ)|=(8566423469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1084604119/10000000000 : ℝ)|^43 ≤ (6527724557283/100000000000000 : ℝ)^35
        have hw : |(-1084604119/10000000000 : ℝ)|=(1084604119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1632134309/10000000000 : ℝ)|^43 ≤ (2696214207973/25000000000000 : ℝ)^35
        have hw : |(-1632134309/10000000000 : ℝ)|=(1632134309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s0_20 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-23927031/1000000000 : ℝ)*x 0 + (-4696987539/10000000000 : ℝ)*x 1 + (-6549959503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23927031/1000000000 : ℝ)^43 ≤ (63713157669/6250000000000 : ℝ)^35 := by
    have hnat : (23927031 : ℕ)^43*6250000000000^35 ≤ 63713157669^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23927031 1000000000 63713157669 6250000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4696987539/10000000000 : ℝ)^43 ≤ (39519068677143/100000000000000 : ℝ)^35 := by
    have hnat : (4696987539 : ℕ)^43*100000000000000^35 ≤ 39519068677143^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4696987539 10000000000 39519068677143 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6549959503/10000000000 : ℝ)^43 ≤ (29730760394167/50000000000000 : ℝ)^35 := by
    have hnat : (6549959503 : ℕ)^43*50000000000000^35 ≤ 29730760394167^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6549959503 10000000000 29730760394167 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23927031/1000000000 : ℝ), (-4696987539/10000000000 : ℝ), (-6549959503/10000000000 : ℝ)] ![(63713157669/6250000000000 : ℝ), (39519068677143/100000000000000 : ℝ), (29730760394167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23927031/1000000000 : ℝ)|^43 ≤ (63713157669/6250000000000 : ℝ)^35
        have hw : |(-23927031/1000000000 : ℝ)|=(23927031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4696987539/10000000000 : ℝ)|^43 ≤ (39519068677143/100000000000000 : ℝ)^35
        have hw : |(-4696987539/10000000000 : ℝ)|=(4696987539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6549959503/10000000000 : ℝ)|^43 ≤ (29730760394167/50000000000000 : ℝ)^35
        have hw : |(-6549959503/10000000000 : ℝ)|=(6549959503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s0_21 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1375756417/2500000000 : ℝ)*x 0 + (3903834881/10000000000 : ℝ)*x 1 + (-275364787/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1375756417/2500000000 : ℝ)^43 ≤ (48007651554191/100000000000000 : ℝ)^35 := by
    have hnat : (1375756417 : ℕ)^43*100000000000000^35 ≤ 48007651554191^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375756417 2500000000 48007651554191 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3903834881/10000000000 : ℝ)^43 ≤ (31486040888483/100000000000000 : ℝ)^35 := by
    have hnat : (3903834881 : ℕ)^43*100000000000000^35 ≤ 31486040888483^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3903834881 10000000000 31486040888483 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275364787/1000000000 : ℝ)^43 ≤ (20506307544401/100000000000000 : ℝ)^35 := by
    have hnat : (275364787 : ℕ)^43*100000000000000^35 ≤ 20506307544401^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275364787 1000000000 20506307544401 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1375756417/2500000000 : ℝ), (3903834881/10000000000 : ℝ), (-275364787/1000000000 : ℝ)] ![(48007651554191/100000000000000 : ℝ), (31486040888483/100000000000000 : ℝ), (20506307544401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1375756417/2500000000 : ℝ)|^43 ≤ (48007651554191/100000000000000 : ℝ)^35
        have hw : |(1375756417/2500000000 : ℝ)|=(1375756417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3903834881/10000000000 : ℝ)|^43 ≤ (31486040888483/100000000000000 : ℝ)^35
        have hw : |(3903834881/10000000000 : ℝ)|=(3903834881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275364787/1000000000 : ℝ)|^43 ≤ (20506307544401/100000000000000 : ℝ)^35
        have hw : |(-275364787/1000000000 : ℝ)|=(275364787/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s0_22 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4733348753/10000000000 : ℝ)*x 0 + (-4392841251/10000000000 : ℝ)*x 1 + (774644569/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4733348753/10000000000 : ℝ)^43 ≤ (19947630262989/50000000000000 : ℝ)^35 := by
    have hnat : (4733348753 : ℕ)^43*50000000000000^35 ≤ 19947630262989^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4733348753 10000000000 19947630262989 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4392841251/10000000000 : ℝ)^43 ≤ (9099705732137/25000000000000 : ℝ)^35 := by
    have hnat : (4392841251 : ℕ)^43*25000000000000^35 ≤ 9099705732137^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4392841251 10000000000 9099705732137 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (774644569/2500000000 : ℝ)^43 ≤ (23705916535161/100000000000000 : ℝ)^35 := by
    have hnat : (774644569 : ℕ)^43*100000000000000^35 ≤ 23705916535161^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774644569 2500000000 23705916535161 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4733348753/10000000000 : ℝ), (-4392841251/10000000000 : ℝ), (774644569/2500000000 : ℝ)] ![(19947630262989/50000000000000 : ℝ), (9099705732137/25000000000000 : ℝ), (23705916535161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4733348753/10000000000 : ℝ)|^43 ≤ (19947630262989/50000000000000 : ℝ)^35
        have hw : |(4733348753/10000000000 : ℝ)|=(4733348753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4392841251/10000000000 : ℝ)|^43 ≤ (9099705732137/25000000000000 : ℝ)^35
        have hw : |(-4392841251/10000000000 : ℝ)|=(4392841251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(774644569/2500000000 : ℝ)|^43 ≤ (23705916535161/100000000000000 : ℝ)^35
        have hw : |(774644569/2500000000 : ℝ)|=(774644569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s0_25 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8589391619/10000000000 : ℝ)*x 0 + (-280437467/2500000000 : ℝ)*x 1 + (-156428267/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8589391619/10000000000 : ℝ)^43 ≤ (41479938215423/50000000000000 : ℝ)^35 := by
    have hnat : (8589391619 : ℕ)^43*50000000000000^35 ≤ 41479938215423^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8589391619 10000000000 41479938215423 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280437467/2500000000 : ℝ)^43 ≤ (6803453247629/100000000000000 : ℝ)^35 := by
    have hnat : (280437467 : ℕ)^43*100000000000000^35 ≤ 6803453247629^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280437467 2500000000 6803453247629 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (156428267/1000000000 : ℝ)^43 ≤ (10236670303639/100000000000000 : ℝ)^35 := by
    have hnat : (156428267 : ℕ)^43*100000000000000^35 ≤ 10236670303639^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156428267 1000000000 10236670303639 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8589391619/10000000000 : ℝ), (-280437467/2500000000 : ℝ), (-156428267/1000000000 : ℝ)] ![(41479938215423/50000000000000 : ℝ), (6803453247629/100000000000000 : ℝ), (10236670303639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8589391619/10000000000 : ℝ)|^43 ≤ (41479938215423/50000000000000 : ℝ)^35
        have hw : |(8589391619/10000000000 : ℝ)|=(8589391619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-280437467/2500000000 : ℝ)|^43 ≤ (6803453247629/100000000000000 : ℝ)^35
        have hw : |(-280437467/2500000000 : ℝ)|=(280437467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-156428267/1000000000 : ℝ)|^43 ≤ (10236670303639/100000000000000 : ℝ)^35
        have hw : |(-156428267/1000000000 : ℝ)|=(156428267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s1_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2073179967/10000000000 : ℝ)*x 0 + (-4363806353/10000000000 : ℝ)*x 1 + (-1127027703/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073179967/10000000000 : ℝ)^43 ≤ (904315062583/6250000000000 : ℝ)^35 := by
    have hnat : (2073179967 : ℕ)^43*6250000000000^35 ≤ 904315062583^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073179967 10000000000 904315062583 6250000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4363806353/10000000000 : ℝ)^43 ≤ (18051737542373/50000000000000 : ℝ)^35 := by
    have hnat : (4363806353 : ℕ)^43*50000000000000^35 ≤ 18051737542373^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363806353 10000000000 18051737542373 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127027703/2000000000 : ℝ)^43 ≤ (1544608871889/3125000000000 : ℝ)^35 := by
    have hnat : (1127027703 : ℕ)^43*3125000000000^35 ≤ 1544608871889^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127027703 2000000000 1544608871889 3125000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2073179967/10000000000 : ℝ), (-4363806353/10000000000 : ℝ), (-1127027703/2000000000 : ℝ)] ![(904315062583/6250000000000 : ℝ), (18051737542373/50000000000000 : ℝ), (1544608871889/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2073179967/10000000000 : ℝ)|^43 ≤ (904315062583/6250000000000 : ℝ)^35
        have hw : |(-2073179967/10000000000 : ℝ)|=(2073179967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4363806353/10000000000 : ℝ)|^43 ≤ (18051737542373/50000000000000 : ℝ)^35
        have hw : |(-4363806353/10000000000 : ℝ)|=(4363806353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1127027703/2000000000 : ℝ)|^43 ≤ (1544608871889/3125000000000 : ℝ)^35
        have hw : |(-1127027703/2000000000 : ℝ)|=(1127027703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s1_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (940405411/2000000000 : ℝ)*x 0 + (4153462789/10000000000 : ℝ)*x 1 + (-1693833979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (940405411/2000000000 : ℝ)^43 ≤ (9892791930703/25000000000000 : ℝ)^35 := by
    have hnat : (940405411 : ℕ)^43*25000000000000^35 ≤ 9892791930703^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940405411 2000000000 9892791930703 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4153462789/10000000000 : ℝ)^43 ≤ (33977375247823/100000000000000 : ℝ)^35 := by
    have hnat : (4153462789 : ℕ)^43*100000000000000^35 ≤ 33977375247823^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153462789 10000000000 33977375247823 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1693833979/5000000000 : ℝ)^43 ≤ (13225728504897/50000000000000 : ℝ)^35 := by
    have hnat : (1693833979 : ℕ)^43*50000000000000^35 ≤ 13225728504897^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693833979 5000000000 13225728504897 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(940405411/2000000000 : ℝ), (4153462789/10000000000 : ℝ), (-1693833979/5000000000 : ℝ)] ![(9892791930703/25000000000000 : ℝ), (33977375247823/100000000000000 : ℝ), (13225728504897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(940405411/2000000000 : ℝ)|^43 ≤ (9892791930703/25000000000000 : ℝ)^35
        have hw : |(940405411/2000000000 : ℝ)|=(940405411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4153462789/10000000000 : ℝ)|^43 ≤ (33977375247823/100000000000000 : ℝ)^35
        have hw : |(4153462789/10000000000 : ℝ)|=(4153462789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1693833979/5000000000 : ℝ)|^43 ≤ (13225728504897/50000000000000 : ℝ)^35
        have hw : |(-1693833979/5000000000 : ℝ)|=(1693833979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s1_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (235114193/500000000 : ℝ)*x 0 + (-4153314241/10000000000 : ℝ)*x 1 + (1693773399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235114193/500000000 : ℝ)^43 ≤ (39573822941767/100000000000000 : ℝ)^35 := by
    have hnat : (235114193 : ℕ)^43*100000000000000^35 ≤ 39573822941767^35*500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235114193 500000000 39573822941767 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4153314241/10000000000 : ℝ)^43 ≤ (8493970574727/25000000000000 : ℝ)^35 := by
    have hnat : (4153314241 : ℕ)^43*25000000000000^35 ≤ 8493970574727^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153314241 10000000000 8493970574727 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1693773399/5000000000 : ℝ)^43 ≤ (2645029474077/10000000000000 : ℝ)^35 := by
    have hnat : (1693773399 : ℕ)^43*10000000000000^35 ≤ 2645029474077^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693773399 5000000000 2645029474077 10000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(235114193/500000000 : ℝ), (-4153314241/10000000000 : ℝ), (1693773399/5000000000 : ℝ)] ![(39573822941767/100000000000000 : ℝ), (8493970574727/25000000000000 : ℝ), (2645029474077/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(235114193/500000000 : ℝ)|^43 ≤ (39573822941767/100000000000000 : ℝ)^35
        have hw : |(235114193/500000000 : ℝ)|=(235114193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4153314241/10000000000 : ℝ)|^43 ≤ (8493970574727/25000000000000 : ℝ)^35
        have hw : |(-4153314241/10000000000 : ℝ)|=(4153314241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1693773399/5000000000 : ℝ)|^43 ≤ (2645029474077/10000000000000 : ℝ)^35
        have hw : |(1693773399/5000000000 : ℝ)|=(1693773399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324038_s1_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6099813623/10000000000 : ℝ)*x 0 + (-104461847/400000000 : ℝ)*x 1 + (-3372382559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6099813623/10000000000 : ℝ)^43 ≤ (5448112491769/10000000000000 : ℝ)^35 := by
    have hnat : (6099813623 : ℕ)^43*10000000000000^35 ≤ 5448112491769^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6099813623 10000000000 5448112491769 10000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104461847/400000000 : ℝ)^43 ≤ (9606986706007/50000000000000 : ℝ)^35 := by
    have hnat : (104461847 : ℕ)^43*50000000000000^35 ≤ 9606986706007^35*400000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104461847 400000000 9606986706007 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3372382559/10000000000 : ℝ)^43 ≤ (6576225414293/25000000000000 : ℝ)^35 := by
    have hnat : (3372382559 : ℕ)^43*25000000000000^35 ≤ 6576225414293^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3372382559 10000000000 6576225414293 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6099813623/10000000000 : ℝ), (-104461847/400000000 : ℝ), (-3372382559/10000000000 : ℝ)] ![(5448112491769/10000000000000 : ℝ), (9606986706007/50000000000000 : ℝ), (6576225414293/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6099813623/10000000000 : ℝ)|^43 ≤ (5448112491769/10000000000000 : ℝ)^35
        have hw : |(6099813623/10000000000 : ℝ)|=(6099813623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104461847/400000000 : ℝ)|^43 ≤ (9606986706007/50000000000000 : ℝ)^35
        have hw : |(-104461847/400000000 : ℝ)|=(104461847/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3372382559/10000000000 : ℝ)|^43 ≤ (6576225414293/25000000000000 : ℝ)^35
        have hw : |(-3372382559/10000000000 : ℝ)|=(3372382559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324038 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-710929711/10000000000 : ℝ)*X 0 0+(-4476028629/10000000000 : ℝ)*X 0 1+(-6496654157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5018652069/10000000000 : ℝ)*X 1 0+(4162459019/10000000000 : ℝ)*X 1 1+(-1514977339/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5018652157/10000000000 : ℝ)*X 2 0+(-1040614741/2500000000 : ℝ)*X 2 1+(1514977319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((3855121211/5000000000 : ℝ)*X 0 0+(-1609042193/10000000000 : ℝ)*X 0 1+(-2335416397/10000000000 : ℝ)*X 0 2+(3855121211/5000000000 : ℝ)*X 1 0+(-1609042193/10000000000 : ℝ)*X 1 1+(-2335416397/10000000000 : ℝ)*X 1 2+(3855121211/5000000000 : ℝ)*X 2 0+(-1609042193/10000000000 : ℝ)*X 2 1+(-2335416397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-339525533/5000000000 : ℝ)*X 0 0+(-1148423617/2500000000 : ℝ)*X 0 1+(-320362771/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((5018833873/10000000000 : ℝ)*X 1 0+(4401301471/10000000000 : ℝ)*X 1 1+(-173039503/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1254708467/2500000000 : ℝ)*X 2 0+(-3902258319/10000000000 : ℝ)*X 2 1+(1652362273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1522204223/2000000000 : ℝ)*X 0 0+(-1407670981/10000000000 : ℝ)*X 0 1+(-2643298533/10000000000 : ℝ)*X 0 2+(1522204223/2000000000 : ℝ)*X 1 0+(-1407670981/10000000000 : ℝ)*X 1 1+(-2643298533/10000000000 : ℝ)*X 1 2+(1522204223/2000000000 : ℝ)*X 2 0+(-1407670981/10000000000 : ℝ)*X 2 1+(-2643298533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-23300819/1000000000 : ℝ)*X 0 0+(-4484395651/10000000000 : ℝ)*X 0 1+(-13180097/19531250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2370545279/5000000000 : ℝ)*X 1 0+(2138045669/5000000000 : ℝ)*X 1 1+(-321560631/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((275464589/500000000 : ℝ)*X 2 0+(-380021199/1000000000 : ℝ)*X 2 1+(35721833/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((8566423469/10000000000 : ℝ)*X 0 0+(-1084604119/10000000000 : ℝ)*X 0 1+(-1632134309/10000000000 : ℝ)*X 0 2+(8566423469/10000000000 : ℝ)*X 1 0+(-1084604119/10000000000 : ℝ)*X 1 1+(-1632134309/10000000000 : ℝ)*X 1 2+(8566423469/10000000000 : ℝ)*X 2 0+(-1084604119/10000000000 : ℝ)*X 2 1+(-1632134309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-23927031/1000000000 : ℝ)*X 0 0+(-4696987539/10000000000 : ℝ)*X 0 1+(-6549959503/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((1375756417/2500000000 : ℝ)*X 1 0+(3903834881/10000000000 : ℝ)*X 1 1+(-275364787/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4733348753/10000000000 : ℝ)*X 2 0+(-4392841251/10000000000 : ℝ)*X 2 1+(774644569/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((8589391619/10000000000 : ℝ)*X 0 0+(-280437467/2500000000 : ℝ)*X 0 1+(-156428267/1000000000 : ℝ)*X 0 2+(8589391619/10000000000 : ℝ)*X 1 0+(-280437467/2500000000 : ℝ)*X 1 1+(-156428267/1000000000 : ℝ)*X 1 2+(8589391619/10000000000 : ℝ)*X 2 0+(-280437467/2500000000 : ℝ)*X 2 1+(-156428267/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((3253/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3253/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (217966209865366771941/40000000000000000000000000 : ℝ) := by norm_num
    linear_combination (220948227659/125000000000 : ℝ)*(base39) + (736067787601/1000000000000 : ℝ)*(base59) + (39174204773/8000000000 : ℝ)*(major_s0_0) + (39174204773/8000000000 : ℝ)*(major_s0_1) + (39174204773/8000000000 : ℝ)*(major_s0_2) + (1096173/10000000000 : ℝ)*(sp_s0_0) + (16328263/500000000000 : ℝ)*(sp_s0_2) + (3661928696587/500000000000 : ℝ)*(sp_s0_7) + (7323891546099/1000000000000 : ℝ)*(sp_s0_8) + (7323861236923/1000000000000 : ℝ)*(sp_s0_9) + (2469576766973/1000000000000 : ℝ)*(sp_s0_13) + (1399853/250000000000 : ℝ)*(sp_s0_14) + (81063787/1000000000000 : ℝ)*(sp_s0_15) + (78716437/1000000000000 : ℝ)*(sp_s0_22) + (2469576766973/1000000000000 : ℝ)*(f.failure) + (1464794521977/200000000000 : ℝ)*(f.sum) + (608855291649/4000000000000000000000000 : ℝ)*base63 + (60594454976863/80000000000000000000000000 : ℝ)*base65 + (31743130735137/80000000000000000000000000 : ℝ)*base67 + (1901349550351/8000000000000000000000000 : ℝ)*base68 + (13682403385353/80000000000000000000000000 : ℝ)*base71 + (26302586768863/80000000000000000000000000 : ℝ)*base73 + (1857712137551/8000000000000000000000000 : ℝ)*base74 + (2215797784849/8000000000000000000000000 : ℝ)*base77 + (812851549/10000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (6417/25000000000000000 : ℝ)*base86 + (6417/25000000000000000 : ℝ)*base88 + (6417/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-28997/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-28997/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1925237701833523323789/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (4765891517241/1000000000000 : ℝ)*(base39) + (220265494487/125000000000 : ℝ)*(base40) + (325608867631/250000000000 : ℝ)*(base59) + (135995692009/15625000000 : ℝ)*(major_s0_0) + (135995692009/15625000000 : ℝ)*(major_s0_1) + (135995692009/15625000000 : ℝ)*(major_s0_2) + (385449097/1000000000000 : ℝ)*(sp_s0_0) + (125826999/200000000000 : ℝ)*(sp_s0_1) + (105813183/250000000000 : ℝ)*(sp_s0_9) + (68314833/500000000000 : ℝ)*(sp_s0_13) + (6508767379209/500000000000 : ℝ)*(sp_s0_14) + (325432276813/25000000000 : ℝ)*(sp_s0_15) + (6508748477391/500000000000 : ℝ)*(sp_s0_16) + (2194693816397/500000000000 : ℝ)*(sp_s0_19) + (219476213123/50000000000 : ℝ)*(f.failure) + (2603584041503/200000000000 : ℝ)*(f.sum) + (2494220947157/31250000000000000000000000 : ℝ)*base62 + (18407689302427/78125000000000000000000000 : ℝ)*base65 + (27574701853823/78125000000000000000000000 : ℝ)*base67 + (12407338587641/31250000000000000000000000 : ℝ)*base68 + (12077902821619/39062500000000000000000000 : ℝ)*base70 + (25004493723271/156250000000000000000000000 : ℝ)*base72 + (1628989267117/15625000000000000000000000 : ℝ)*base75 + (3275739120383/15625000000000000000000000 : ℝ)*base76 + (502845707/2500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (233/1250000000000000 : ℝ)*base87 + (233/1250000000000000 : ℝ)*base89 + (233/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-28731/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-28731/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1435956248369907158043/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4602420284137/1000000000000 : ℝ)*(base39) + (1261863997341/1000000000000 : ℝ)*(base40) + (259366394693/200000000000 : ℝ)*(base59) + (2171706454479/250000000000 : ℝ)*(major_s0_0) + (2171706454479/250000000000 : ℝ)*(major_s0_1) + (2171706454479/250000000000 : ℝ)*(major_s0_2) + (18483033/125000000000 : ℝ)*(sp_s0_2) + (41451809/1000000000000 : ℝ)*(sp_s0_6) + (56581517/200000000000 : ℝ)*(sp_s0_7) + (40243897/200000000000 : ℝ)*(sp_s0_8) + (12992362993717/1000000000000 : ℝ)*(sp_s0_20) + (12992444681817/1000000000000 : ℝ)*(sp_s0_21) + (6496249018519/500000000000 : ℝ)*(sp_s0_22) + (4380960453497/1000000000000 : ℝ)*(sp_s0_25) + (876200381061/200000000000 : ℝ)*(f.failure) + (6496322950651/500000000000 : ℝ)*(f.sum) + (52846867478273/125000000000000000000000000 : ℝ)*base62 + (85736333824451/2500000000000000000000000000 : ℝ)*base64 + (50061093675549/2500000000000000000000000000 : ℝ)*base66 + (86582483015773/250000000000000000000000000 : ℝ)*base68 + (218680227232181/2500000000000000000000000000 : ℝ)*base70 + (762675280425549/2500000000000000000000000000 : ℝ)*base73 + (85643405540773/250000000000000000000000000 : ℝ)*base74 + (51773488790773/250000000000000000000000000 : ℝ)*base76 + (4030466243/10000000000000000000000 : ℝ)*base79 + (5169/5000000000000000 : ℝ)*base86 + (5169/5000000000000000 : ℝ)*base88 + (5169/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (3253/100000 : ℝ) ^ (21/4 : ℝ) ≤ (1547003628111/100000000000000000000 : ℝ) := by
    have hpowers : (3253/100000 : ℝ)^21 ≤ (1547003628111/100000000000000000000 : ℝ)^4 := by
      have hnat : (3253 : ℕ)^21*100000000000000000000^4 ≤ 1547003628111^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3253 100000 1547003628111 100000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3253/100000 : ℝ)) (X := (1547003628111/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100000001547003628111/100000000000000000000 : ℝ) ≤ (625000001841671/625000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (100000001547003628111/100000000000000000000 : ℝ)^4 ≤ (625000001841671/625000000000000 : ℝ)^21 := by
      have hnat : (100000001547003628111 : ℕ)^4*625000000000000^21 ≤ 625000001841671^21*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100000001547003628111 100000000000000000000 625000001841671 625000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000001841671/625000000000000 : ℝ)) (X := (100000001547003628111/100000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50000001547003628111/50000000000000000000 : ℝ) ≤ (10000000058933471/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (50000001547003628111/50000000000000000000 : ℝ)^4 ≤ (10000000058933471/10000000000000000 : ℝ)^21 := by
      have hnat : (50000001547003628111 : ℕ)^4*10000000000000000^21 ≤ 10000000058933471^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000001547003628111 50000000000000000000 10000000058933471 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000058933471/10000000000000000 : ℝ)) (X := (50000001547003628111/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1841671/20331250000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(5893347/65060000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (3253/100000 : ℝ)) (alpha := (1841671/20331250000000 : ℝ)) (beta := (5893347/65060000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3253/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1841671/20331250000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(5893347/65060000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (28997/100000 : ℝ) ^ (21/4 : ℝ) ≤ (150436634817872779/100000000000000000000 : ℝ) := by
    have hpowers : (28997/100000 : ℝ)^21 ≤ (150436634817872779/100000000000000000000 : ℝ)^4 := by
      have hnat : (28997 : ℕ)^21*100000000000000000000^4 ≤ 150436634817872779^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28997 100000 150436634817872779 100000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28997/100000 : ℝ)) (X := (150436634817872779/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100150436634817872779/100000000000000000000 : ℝ) ≤ (2500715929121191/2500000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (100150436634817872779/100000000000000000000 : ℝ)^4 ≤ (2500715929121191/2500000000000000 : ℝ)^21 := by
      have hnat : (100150436634817872779 : ℕ)^4*2500000000000000^21 ≤ 2500715929121191^21*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100150436634817872779 100000000000000000000 2500715929121191 2500000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500715929121191/2500000000000000 : ℝ)) (X := (100150436634817872779/100000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50150436634817872779/50000000000000000000 : ℝ) ≤ (10005723952830323/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (50150436634817872779/50000000000000000000 : ℝ)^4 ≤ (10005723952830323/10000000000000000 : ℝ)^21 := by
      have hnat : (50150436634817872779 : ℕ)^4*10000000000000000^21 ≤ 10005723952830323^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50150436634817872779 50000000000000000000 10005723952830323 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005723952830323/10000000000000000 : ℝ)) (X := (50150436634817872779/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(715929121191/724925000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(2860236345559/2899700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (28997/100000 : ℝ)) (alpha := (715929121191/724925000000000 : ℝ)) (beta := (2860236345559/2899700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (28997/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(715929121191/724925000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(2860236345559/2899700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (28731/100000 : ℝ) ^ (21/4 : ℝ) ≤ (71665708801707333/50000000000000000000 : ℝ) := by
    have hpowers : (28731/100000 : ℝ)^21 ≤ (71665708801707333/50000000000000000000 : ℝ)^4 := by
      have hnat : (28731 : ℕ)^21*50000000000000000000^4 ≤ 71665708801707333^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28731 100000 71665708801707333 50000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28731/100000 : ℝ)) (X := (71665708801707333/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50071665708801707333/50000000000000000000 : ℝ) ≤ (2000545707944987/2000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (50071665708801707333/50000000000000000000 : ℝ)^4 ≤ (2000545707944987/2000000000000000 : ℝ)^21 := by
      have hnat : (50071665708801707333 : ℕ)^4*2000000000000000^21 ≤ 2000545707944987^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50071665708801707333 50000000000000000000 2000545707944987 2000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000545707944987/2000000000000000 : ℝ)) (X := (50071665708801707333/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25071665708801707333/25000000000000000000 : ℝ) ≤ (10005453919880419/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (25071665708801707333/25000000000000000000 : ℝ)^4 ≤ (10005453919880419/10000000000000000 : ℝ)^21 := by
      have hnat : (25071665708801707333 : ℕ)^4*10000000000000000^21 ≤ 10005453919880419^21*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25071665708801707333 25000000000000000000 10005453919880419 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005453919880419/10000000000000000 : ℝ)) (X := (25071665708801707333/25000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(181902648329/191540000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(227115012957/239425000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (28731/100000 : ℝ)) (alpha := (181902648329/191540000000000 : ℝ)) (beta := (227115012957/239425000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (28731/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(181902648329/191540000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(227115012957/239425000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2073179967/10000000000 : ℝ)*X 0 0+(-4363806353/10000000000 : ℝ)*X 0 1+(-1127027703/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((940405411/2000000000 : ℝ)*X 1 0+(4153462789/10000000000 : ℝ)*X 1 1+(-1693833979/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((235114193/500000000 : ℝ)*X 2 0+(-4153314241/10000000000 : ℝ)*X 2 1+(1693773399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6099813623/10000000000 : ℝ)*X 0 0+(-104461847/400000000 : ℝ)*X 0 1+(-3372382559/10000000000 : ℝ)*X 0 2+(6099813623/10000000000 : ℝ)*X 1 0+(-104461847/400000000 : ℝ)*X 1 1+(-3372382559/10000000000 : ℝ)*X 1 2+(6099813623/10000000000 : ℝ)*X 2 0+(-104461847/400000000 : ℝ)*X 2 1+(-3372382559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324038_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-111213/12500 : ℝ) < ((-49571/25000 : ℝ)*P 0+(-49571/25000 : ℝ)*P 1+(-49571/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-111213/12500 : ℝ) < (-2732566879259687006633528265513/311539810000000000000000000000 : ℝ) := by norm_num
    linear_combination (29957/500000000000 : ℝ)*(base8) + (227967/500000000000 : ℝ)*(base12) + (48333/500000000000 : ℝ)*(base21) + (145314207903/125000000000 : ℝ)*(base39) + (507371847679/1000000000000 : ℝ)*(base40) + (52129/500000000000 : ℝ)*(base49) + (443949316261/1000000000000 : ℝ)*(base59) + (27087/1000000000000 : ℝ)*(base60) + (49571/25000 : ℝ)*(major_s1_0) + (49571/25000 : ℝ)*(major_s1_1) + (49571/25000 : ℝ)*(major_s1_2) + (2923720938623/1000000000000 : ℝ)*(sp_s1_0) + (2923721454471/1000000000000 : ℝ)*(sp_s1_1) + (1461860678903/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2923721454471/1000000000000 : ℝ)*(f.sum) + (913568328443967629/2777042690000000000000000000000 : ℝ)*base63 + (16149761568263/95770000000000000000000000 : ℝ)*base65 + (17801486117907/57994000000000000000000000 : ℝ)*base66 + (3757753701763/19154000000000000000000000 : ℝ)*base69 + (139102889321086761/311539810000000000000000000000 : ℝ)*base71 + (476658335423/16265000000000000000000000 : ℝ)*base72 + (3873880780163/7249250000000000000000000 : ℝ)*base74 + (4426798747619/16265000000000000000000000 : ℝ)*base77 + (40770421347668423/235818102500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p024_b018 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 38 ≤ c.val) (hhi : c.val < 39)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=38 := by omega
  rcases hc with rfl
  · exact collision_c324038 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 38 ≤ c.val) (hhi : c.val < 39)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b018 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

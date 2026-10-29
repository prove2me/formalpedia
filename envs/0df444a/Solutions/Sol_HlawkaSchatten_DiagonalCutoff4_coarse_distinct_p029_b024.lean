-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b024
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:27:18.177181+00:00
-- url     : https://prove2.me/submissions/65cab206-510e-407b-b9e7-a105f2227101

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
theorem collision_support_c329051_s0_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-795146453/2500000000 : ℝ)*x 0 + (1590293363/5000000000 : ℝ)*x 1 + (5577944271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (795146453/2500000000 : ℝ)^95 ≤ (3152528911457/12500000000000 : ℝ)^79 := by
    have hnat : (795146453 : ℕ)^95*12500000000000^79 ≤ 3152528911457^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795146453 2500000000 3152528911457 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1590293363/5000000000 : ℝ)^95 ≤ (12610120003501/50000000000000 : ℝ)^79 := by
    have hnat : (1590293363 : ℕ)^95*50000000000000^79 ≤ 12610120003501^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590293363 5000000000 12610120003501 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5577944271/10000000000 : ℝ)^95 ≤ (24779764344219/50000000000000 : ℝ)^79 := by
    have hnat : (5577944271 : ℕ)^95*50000000000000^79 ≤ 24779764344219^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5577944271 10000000000 24779764344219 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-795146453/2500000000 : ℝ), (1590293363/5000000000 : ℝ), (5577944271/10000000000 : ℝ)] ![(3152528911457/12500000000000 : ℝ), (12610120003501/50000000000000 : ℝ), (24779764344219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-795146453/2500000000 : ℝ)|^95 ≤ (3152528911457/12500000000000 : ℝ)^79
        have hw : |(-795146453/2500000000 : ℝ)|=(795146453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1590293363/5000000000 : ℝ)|^95 ≤ (12610120003501/50000000000000 : ℝ)^79
        have hw : |(1590293363/5000000000 : ℝ)|=(1590293363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5577944271/10000000000 : ℝ)|^95 ≤ (24779764344219/50000000000000 : ℝ)^79
        have hw : |(5577944271/10000000000 : ℝ)|=(5577944271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (297754527/1250000000 : ℝ)*x 0 + (-1191018487/5000000000 : ℝ)*x 1 + (693292923/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (297754527/1250000000 : ℝ)^95 ≤ (2226746094267/12500000000000 : ℝ)^79 := by
    have hnat : (297754527 : ℕ)^95*12500000000000^79 ≤ 2226746094267^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297754527 1250000000 2226746094267 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1191018487/5000000000 : ℝ)^95 ≤ (17813975570897/100000000000000 : ℝ)^79 := by
    have hnat : (1191018487 : ℕ)^95*100000000000000^79 ≤ 17813975570897^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191018487 5000000000 17813975570897 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (693292923/1000000000 : ℝ)^95 ≤ (8046506956421/12500000000000 : ℝ)^79 := by
    have hnat : (693292923 : ℕ)^95*12500000000000^79 ≤ 8046506956421^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693292923 1000000000 8046506956421 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(297754527/1250000000 : ℝ), (-1191018487/5000000000 : ℝ), (693292923/1000000000 : ℝ)] ![(2226746094267/12500000000000 : ℝ), (17813975570897/100000000000000 : ℝ), (8046506956421/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(297754527/1250000000 : ℝ)|^95 ≤ (2226746094267/12500000000000 : ℝ)^79
        have hw : |(297754527/1250000000 : ℝ)|=(297754527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1191018487/5000000000 : ℝ)|^95 ≤ (17813975570897/100000000000000 : ℝ)^79
        have hw : |(-1191018487/5000000000 : ℝ)|=(1191018487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(693292923/1000000000 : ℝ)|^95 ≤ (8046506956421/12500000000000 : ℝ)^79
        have hw : |(693292923/1000000000 : ℝ)|=(693292923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s0_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1461121499/2500000000 : ℝ)*x 0 + (5317892977/10000000000 : ℝ)*x 1 + (-177533961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1461121499/2500000000 : ℝ)^95 ≤ (10484194441713/20000000000000 : ℝ)^79 := by
    have hnat : (1461121499 : ℕ)^95*20000000000000^79 ≤ 10484194441713^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461121499 2500000000 10484194441713 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5317892977/10000000000 : ℝ)^95 ≤ (46794324382517/100000000000000 : ℝ)^79 := by
    have hnat : (5317892977 : ℕ)^95*100000000000000^79 ≤ 46794324382517^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5317892977 10000000000 46794324382517 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (177533961/10000000000 : ℝ)^95 ≤ (392351698341/50000000000000 : ℝ)^79 := by
    have hnat : (177533961 : ℕ)^95*50000000000000^79 ≤ 392351698341^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177533961 10000000000 392351698341 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1461121499/2500000000 : ℝ), (5317892977/10000000000 : ℝ), (-177533961/10000000000 : ℝ)] ![(10484194441713/20000000000000 : ℝ), (46794324382517/100000000000000 : ℝ), (392351698341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1461121499/2500000000 : ℝ)|^95 ≤ (10484194441713/20000000000000 : ℝ)^79
        have hw : |(1461121499/2500000000 : ℝ)|=(1461121499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5317892977/10000000000 : ℝ)|^95 ≤ (46794324382517/100000000000000 : ℝ)^79
        have hw : |(5317892977/10000000000 : ℝ)|=(5317892977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-177533961/10000000000 : ℝ)|^95 ≤ (392351698341/50000000000000 : ℝ)^79
        have hw : |(-177533961/10000000000 : ℝ)|=(177533961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s0_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2811448401/10000000000 : ℝ)*x 0 + (210626039/1250000000 : ℝ)*x 1 + (7123781317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2811448401/10000000000 : ℝ)^95 ≤ (1358942385111/6250000000000 : ℝ)^79 := by
    have hnat : (2811448401 : ℕ)^95*6250000000000^79 ≤ 1358942385111^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2811448401 10000000000 1358942385111 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210626039/1250000000 : ℝ)^95 ≤ (11748014870061/100000000000000 : ℝ)^79 := by
    have hnat : (210626039 : ℕ)^95*100000000000000^79 ≤ 11748014870061^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210626039 1250000000 11748014870061 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7123781317/10000000000 : ℝ)^95 ≤ (66508906951177/100000000000000 : ℝ)^79 := by
    have hnat : (7123781317 : ℕ)^95*100000000000000^79 ≤ 66508906951177^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7123781317 10000000000 66508906951177 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2811448401/10000000000 : ℝ), (210626039/1250000000 : ℝ), (7123781317/10000000000 : ℝ)] ![(1358942385111/6250000000000 : ℝ), (11748014870061/100000000000000 : ℝ), (66508906951177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2811448401/10000000000 : ℝ)|^95 ≤ (1358942385111/6250000000000 : ℝ)^79
        have hw : |(-2811448401/10000000000 : ℝ)|=(2811448401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210626039/1250000000 : ℝ)|^95 ≤ (11748014870061/100000000000000 : ℝ)^79
        have hw : |(210626039/1250000000 : ℝ)|=(210626039/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7123781317/10000000000 : ℝ)|^95 ≤ (66508906951177/100000000000000 : ℝ)^79
        have hw : |(7123781317/10000000000 : ℝ)|=(7123781317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s0_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1674680021/10000000000 : ℝ)*x 0 + (-462029643/5000000000 : ℝ)*x 1 + (8533179427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1674680021/10000000000 : ℝ)^95 ≤ (11661474783751/100000000000000 : ℝ)^79 := by
    have hnat : (1674680021 : ℕ)^95*100000000000000^79 ≤ 11661474783751^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674680021 10000000000 11661474783751 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (462029643/5000000000 : ℝ)^95 ≤ (1140909816989/20000000000000 : ℝ)^79 := by
    have hnat : (462029643 : ℕ)^95*20000000000000^79 ≤ 1140909816989^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462029643 5000000000 1140909816989 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8533179427/10000000000 : ℝ)^95 ≤ (4131698805981/5000000000000 : ℝ)^79 := by
    have hnat : (8533179427 : ℕ)^95*5000000000000^79 ≤ 4131698805981^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8533179427 10000000000 4131698805981 5000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1674680021/10000000000 : ℝ), (-462029643/5000000000 : ℝ), (8533179427/10000000000 : ℝ)] ![(11661474783751/100000000000000 : ℝ), (1140909816989/20000000000000 : ℝ), (4131698805981/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1674680021/10000000000 : ℝ)|^95 ≤ (11661474783751/100000000000000 : ℝ)^79
        have hw : |(1674680021/10000000000 : ℝ)|=(1674680021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-462029643/5000000000 : ℝ)|^95 ≤ (1140909816989/20000000000000 : ℝ)^79
        have hw : |(-462029643/5000000000 : ℝ)|=(462029643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8533179427/10000000000 : ℝ)|^95 ≤ (4131698805981/5000000000000 : ℝ)^79
        have hw : |(8533179427/10000000000 : ℝ)|=(8533179427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s0_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (840827599/2000000000 : ℝ)*x 0 + (1380784511/2000000000 : ℝ)*x 1 + (-15707697/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840827599/2000000000 : ℝ)^95 ≤ (35274400271201/100000000000000 : ℝ)^79 := by
    have hnat : (840827599 : ℕ)^95*100000000000000^79 ≤ 35274400271201^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840827599 2000000000 35274400271201 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1380784511/2000000000 : ℝ)^95 ≤ (64048319778777/100000000000000 : ℝ)^79 := by
    have hnat : (1380784511 : ℕ)^95*100000000000000^79 ≤ 64048319778777^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380784511 2000000000 64048319778777 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15707697/1000000000 : ℝ)^95 ≤ (84659992851/12500000000000 : ℝ)^79 := by
    have hnat : (15707697 : ℕ)^95*12500000000000^79 ≤ 84659992851^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15707697 1000000000 84659992851 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840827599/2000000000 : ℝ), (1380784511/2000000000 : ℝ), (-15707697/1000000000 : ℝ)] ![(35274400271201/100000000000000 : ℝ), (64048319778777/100000000000000 : ℝ), (84659992851/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840827599/2000000000 : ℝ)|^95 ≤ (35274400271201/100000000000000 : ℝ)^79
        have hw : |(840827599/2000000000 : ℝ)|=(840827599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1380784511/2000000000 : ℝ)|^95 ≤ (64048319778777/100000000000000 : ℝ)^79
        have hw : |(1380784511/2000000000 : ℝ)|=(1380784511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15707697/1000000000 : ℝ)|^95 ≤ (84659992851/12500000000000 : ℝ)^79
        have hw : |(-15707697/1000000000 : ℝ)|=(15707697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s0_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (360421277/1250000000 : ℝ)*x 0 + (2011190249/2500000000 : ℝ)*x 1 + (143312293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360421277/1250000000 : ℝ)^95 ≤ (43776716907/195312500000 : ℝ)^79 := by
    have hnat : (360421277 : ℕ)^95*195312500000^79 ≤ 43776716907^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360421277 1250000000 43776716907 195312500000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2011190249/2500000000 : ℝ)^95 ≤ (76979762708291/100000000000000 : ℝ)^79 := by
    have hnat : (2011190249 : ℕ)^95*100000000000000^79 ≤ 76979762708291^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011190249 2500000000 76979762708291 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (143312293/10000000000 : ℝ)^95 ≤ (303279112989/50000000000000 : ℝ)^79 := by
    have hnat : (143312293 : ℕ)^95*50000000000000^79 ≤ 303279112989^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143312293 10000000000 303279112989 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(360421277/1250000000 : ℝ), (2011190249/2500000000 : ℝ), (143312293/10000000000 : ℝ)] ![(43776716907/195312500000 : ℝ), (76979762708291/100000000000000 : ℝ), (303279112989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(360421277/1250000000 : ℝ)|^95 ≤ (43776716907/195312500000 : ℝ)^79
        have hw : |(360421277/1250000000 : ℝ)|=(360421277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2011190249/2500000000 : ℝ)|^95 ≤ (76979762708291/100000000000000 : ℝ)^79
        have hw : |(2011190249/2500000000 : ℝ)|=(2011190249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(143312293/10000000000 : ℝ)|^95 ≤ (303279112989/50000000000000 : ℝ)^79
        have hw : |(143312293/10000000000 : ℝ)|=(143312293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s0_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-450306443/2500000000 : ℝ)*x 0 + (2823571611/10000000000 : ℝ)*x 1 + (7026214309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450306443/2500000000 : ℝ)^95 ≤ (12729083784927/100000000000000 : ℝ)^79 := by
    have hnat : (450306443 : ℕ)^95*100000000000000^79 ≤ 12729083784927^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450306443 2500000000 12729083784927 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2823571611/10000000000 : ℝ)^95 ≤ (5463968588293/25000000000000 : ℝ)^79 := by
    have hnat : (2823571611 : ℕ)^95*25000000000000^79 ≤ 5463968588293^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2823571611 10000000000 5463968588293 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7026214309/10000000000 : ℝ)^95 ≤ (65415041848103/100000000000000 : ℝ)^79 := by
    have hnat : (7026214309 : ℕ)^95*100000000000000^79 ≤ 65415041848103^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7026214309 10000000000 65415041848103 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-450306443/2500000000 : ℝ), (2823571611/10000000000 : ℝ), (7026214309/10000000000 : ℝ)] ![(12729083784927/100000000000000 : ℝ), (5463968588293/25000000000000 : ℝ), (65415041848103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-450306443/2500000000 : ℝ)|^95 ≤ (12729083784927/100000000000000 : ℝ)^79
        have hw : |(-450306443/2500000000 : ℝ)|=(450306443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2823571611/10000000000 : ℝ)|^95 ≤ (5463968588293/25000000000000 : ℝ)^79
        have hw : |(2823571611/10000000000 : ℝ)|=(2823571611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7026214309/10000000000 : ℝ)|^95 ≤ (65415041848103/100000000000000 : ℝ)^79
        have hw : |(7026214309/10000000000 : ℝ)|=(7026214309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s0_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (574746613/5000000000 : ℝ)*x 0 + (-361218349/2000000000 : ℝ)*x 1 + (8290188401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (574746613/5000000000 : ℝ)^95 ≤ (1483403264623/20000000000000 : ℝ)^79 := by
    have hnat : (574746613 : ℕ)^95*20000000000000^79 ≤ 1483403264623^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574746613 5000000000 1483403264623 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (361218349/2000000000 : ℝ)^95 ≤ (6385223481947/50000000000000 : ℝ)^79 := by
    have hnat : (361218349 : ℕ)^95*50000000000000^79 ≤ 6385223481947^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361218349 2000000000 6385223481947 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8290188401/10000000000 : ℝ)^95 ≤ (2494141772041/3125000000000 : ℝ)^79 := by
    have hnat : (8290188401 : ℕ)^95*3125000000000^79 ≤ 2494141772041^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8290188401 10000000000 2494141772041 3125000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(574746613/5000000000 : ℝ), (-361218349/2000000000 : ℝ), (8290188401/10000000000 : ℝ)] ![(1483403264623/20000000000000 : ℝ), (6385223481947/50000000000000 : ℝ), (2494141772041/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(574746613/5000000000 : ℝ)|^95 ≤ (1483403264623/20000000000000 : ℝ)^79
        have hw : |(574746613/5000000000 : ℝ)|=(574746613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-361218349/2000000000 : ℝ)|^95 ≤ (6385223481947/50000000000000 : ℝ)^79
        have hw : |(-361218349/2000000000 : ℝ)|=(361218349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8290188401/10000000000 : ℝ)|^95 ≤ (2494141772041/3125000000000 : ℝ)^79
        have hw : |(8290188401/10000000000 : ℝ)|=(8290188401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s0_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3645612497/5000000000 : ℝ)*x 0 + (3798458479/10000000000 : ℝ)*x 1 + (-98089483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3645612497/5000000000 : ℝ)^95 ≤ (4274578300951/6250000000000 : ℝ)^79 := by
    have hnat : (3645612497 : ℕ)^95*6250000000000^79 ≤ 4274578300951^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3645612497 5000000000 4274578300951 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3798458479/10000000000 : ℝ)^95 ≤ (31222277191777/100000000000000 : ℝ)^79 := by
    have hnat : (3798458479 : ℕ)^95*100000000000000^79 ≤ 31222277191777^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3798458479 10000000000 31222277191777 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (98089483/10000000000 : ℝ)^95 ≤ (384469979451/100000000000000 : ℝ)^79 := by
    have hnat : (98089483 : ℕ)^95*100000000000000^79 ≤ 384469979451^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98089483 10000000000 384469979451 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3645612497/5000000000 : ℝ), (3798458479/10000000000 : ℝ), (-98089483/10000000000 : ℝ)] ![(4274578300951/6250000000000 : ℝ), (31222277191777/100000000000000 : ℝ), (384469979451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3645612497/5000000000 : ℝ)|^95 ≤ (4274578300951/6250000000000 : ℝ)^79
        have hw : |(3645612497/5000000000 : ℝ)|=(3645612497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3798458479/10000000000 : ℝ)|^95 ≤ (31222277191777/100000000000000 : ℝ)^79
        have hw : |(3798458479/10000000000 : ℝ)|=(3798458479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-98089483/10000000000 : ℝ)|^95 ≤ (384469979451/100000000000000 : ℝ)^79
        have hw : |(-98089483/10000000000 : ℝ)|=(98089483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s0_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1446182269/2000000000 : ℝ)*x 0 + (1917285399/5000000000 : ℝ)*x 1 + (162777087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1446182269/2000000000 : ℝ)^95 ≤ (16928371436389/25000000000000 : ℝ)^79 := by
    have hnat : (1446182269 : ℕ)^95*25000000000000^79 ≤ 16928371436389^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1446182269 2000000000 16928371436389 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1917285399/5000000000 : ℝ)^95 ≤ (31579571374973/100000000000000 : ℝ)^79 := by
    have hnat : (1917285399 : ℕ)^95*100000000000000^79 ≤ 31579571374973^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917285399 5000000000 31579571374973 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162777087/10000000000 : ℝ)^95 ≤ (141388572709/20000000000000 : ℝ)^79 := by
    have hnat : (162777087 : ℕ)^95*20000000000000^79 ≤ 141388572709^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162777087 10000000000 141388572709 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1446182269/2000000000 : ℝ), (1917285399/5000000000 : ℝ), (162777087/10000000000 : ℝ)] ![(16928371436389/25000000000000 : ℝ), (31579571374973/100000000000000 : ℝ), (141388572709/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1446182269/2000000000 : ℝ)|^95 ≤ (16928371436389/25000000000000 : ℝ)^79
        have hw : |(1446182269/2000000000 : ℝ)|=(1446182269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1917285399/5000000000 : ℝ)|^95 ≤ (31579571374973/100000000000000 : ℝ)^79
        have hw : |(1917285399/5000000000 : ℝ)|=(1917285399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(162777087/10000000000 : ℝ)|^95 ≤ (141388572709/20000000000000 : ℝ)^79
        have hw : |(162777087/10000000000 : ℝ)|=(162777087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s0_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2260863099/5000000000 : ℝ)*x 0 + (2113813183/5000000000 : ℝ)*x 1 + (326065557/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2260863099/5000000000 : ℝ)^95 ≤ (962570338119/2500000000000 : ℝ)^79 := by
    have hnat : (2260863099 : ℕ)^95*2500000000000^79 ≤ 962570338119^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260863099 5000000000 962570338119 2500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113813183/5000000000 : ℝ)^95 ≤ (17755762641329/50000000000000 : ℝ)^79 := by
    have hnat : (2113813183 : ℕ)^95*50000000000000^79 ≤ 17755762641329^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113813183 5000000000 17755762641329 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326065557/1000000000 : ℝ)^95 ≤ (324820764751/1250000000000 : ℝ)^79 := by
    have hnat : (326065557 : ℕ)^95*1250000000000^79 ≤ 324820764751^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326065557 1000000000 324820764751 1250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2260863099/5000000000 : ℝ), (2113813183/5000000000 : ℝ), (326065557/1000000000 : ℝ)] ![(962570338119/2500000000000 : ℝ), (17755762641329/50000000000000 : ℝ), (324820764751/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2260863099/5000000000 : ℝ)|^95 ≤ (962570338119/2500000000000 : ℝ)^79
        have hw : |(-2260863099/5000000000 : ℝ)|=(2260863099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113813183/5000000000 : ℝ)|^95 ≤ (17755762641329/50000000000000 : ℝ)^79
        have hw : |(2113813183/5000000000 : ℝ)|=(2113813183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326065557/1000000000 : ℝ)|^95 ≤ (324820764751/1250000000000 : ℝ)^79
        have hw : |(326065557/1000000000 : ℝ)|=(326065557/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s0_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (50315583/400000000 : ℝ)*x 0 + (-12415901/80000000 : ℝ)*x 1 + (2100143567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50315583/400000000 : ℝ)^95 ≤ (4132964164803/50000000000000 : ℝ)^79 := by
    have hnat : (50315583 : ℕ)^95*50000000000000^79 ≤ 4132964164803^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50315583 400000000 4132964164803 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12415901/80000000 : ℝ)^95 ≤ (10641859496193/100000000000000 : ℝ)^79 := by
    have hnat : (12415901 : ℕ)^95*100000000000000^79 ≤ 10641859496193^79*80000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12415901 80000000 10641859496193 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2100143567/2500000000 : ℝ)^95 ≤ (16218442433561/20000000000000 : ℝ)^79 := by
    have hnat : (2100143567 : ℕ)^95*20000000000000^79 ≤ 16218442433561^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100143567 2500000000 16218442433561 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(50315583/400000000 : ℝ), (-12415901/80000000 : ℝ), (2100143567/2500000000 : ℝ)] ![(4132964164803/50000000000000 : ℝ), (10641859496193/100000000000000 : ℝ), (16218442433561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(50315583/400000000 : ℝ)|^95 ≤ (4132964164803/50000000000000 : ℝ)^79
        have hw : |(50315583/400000000 : ℝ)|=(50315583/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-12415901/80000000 : ℝ)|^95 ≤ (10641859496193/100000000000000 : ℝ)^79
        have hw : |(-12415901/80000000 : ℝ)|=(12415901/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2100143567/2500000000 : ℝ)|^95 ≤ (16218442433561/20000000000000 : ℝ)^79
        have hw : |(2100143567/2500000000 : ℝ)|=(2100143567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s0_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6630589991/10000000000 : ℝ)*x 0 + (1131777629/2500000000 : ℝ)*x 1 + (-2694897/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6630589991/10000000000 : ℝ)^95 ≤ (30505689544889/50000000000000 : ℝ)^79 := by
    have hnat : (6630589991 : ℕ)^95*50000000000000^79 ≤ 30505689544889^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6630589991 10000000000 30505689544889 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131777629/2500000000 : ℝ)^95 ≤ (9639488413179/25000000000000 : ℝ)^79 := by
    have hnat : (1131777629 : ℕ)^95*25000000000000^79 ≤ 9639488413179^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131777629 2500000000 9639488413179 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2694897/250000000 : ℝ)^95 ≤ (26916702723/6250000000000 : ℝ)^79 := by
    have hnat : (2694897 : ℕ)^95*6250000000000^79 ≤ 26916702723^79*250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694897 250000000 26916702723 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6630589991/10000000000 : ℝ), (1131777629/2500000000 : ℝ), (-2694897/250000000 : ℝ)] ![(30505689544889/50000000000000 : ℝ), (9639488413179/25000000000000 : ℝ), (26916702723/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6630589991/10000000000 : ℝ)|^95 ≤ (30505689544889/50000000000000 : ℝ)^79
        have hw : |(6630589991/10000000000 : ℝ)|=(6630589991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131777629/2500000000 : ℝ)|^95 ≤ (9639488413179/25000000000000 : ℝ)^79
        have hw : |(1131777629/2500000000 : ℝ)|=(1131777629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2694897/250000000 : ℝ)|^95 ≤ (26916702723/6250000000000 : ℝ)^79
        have hw : |(-2694897/250000000 : ℝ)|=(2694897/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s0_27 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (29802747/125000000 : ℝ)*x 0 + (8460666557/10000000000 : ℝ)*x 1 + (96312529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29802747/125000000 : ℝ)^95 ≤ (17833607379733/100000000000000 : ℝ)^79 := by
    have hnat : (29802747 : ℕ)^95*100000000000000^79 ≤ 17833607379733^79*125000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29802747 125000000 17833607379733 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8460666557/10000000000 : ℝ)^95 ≤ (81790282727423/100000000000000 : ℝ)^79 := by
    have hnat : (8460666557 : ℕ)^95*100000000000000^79 ≤ 81790282727423^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8460666557 10000000000 81790282727423 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96312529/10000000000 : ℝ)^95 ≤ (376109881419/100000000000000 : ℝ)^79 := by
    have hnat : (96312529 : ℕ)^95*100000000000000^79 ≤ 376109881419^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96312529 10000000000 376109881419 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(29802747/125000000 : ℝ), (8460666557/10000000000 : ℝ), (96312529/10000000000 : ℝ)] ![(17833607379733/100000000000000 : ℝ), (81790282727423/100000000000000 : ℝ), (376109881419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(29802747/125000000 : ℝ)|^95 ≤ (17833607379733/100000000000000 : ℝ)^79
        have hw : |(29802747/125000000 : ℝ)|=(29802747/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8460666557/10000000000 : ℝ)|^95 ≤ (81790282727423/100000000000000 : ℝ)^79
        have hw : |(8460666557/10000000000 : ℝ)|=(8460666557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(96312529/10000000000 : ℝ)|^95 ≤ (376109881419/100000000000000 : ℝ)^79
        have hw : |(96312529/10000000000 : ℝ)|=(96312529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s1_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-702103843/2000000000 : ℝ)*x 0 + (1754213563/5000000000 : ℝ)*x 1 + (2489097569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (702103843/2000000000 : ℝ)^95 ≤ (28398451968677/100000000000000 : ℝ)^79 := by
    have hnat : (702103843 : ℕ)^95*100000000000000^79 ≤ 28398451968677^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702103843 2000000000 28398451968677 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1754213563/5000000000 : ℝ)^95 ≤ (5675620306069/20000000000000 : ℝ)^79 := by
    have hnat : (1754213563 : ℕ)^95*20000000000000^79 ≤ 5675620306069^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1754213563 5000000000 5675620306069 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2489097569/5000000000 : ℝ)^95 ≤ (43223446485363/100000000000000 : ℝ)^79 := by
    have hnat : (2489097569 : ℕ)^95*100000000000000^79 ≤ 43223446485363^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2489097569 5000000000 43223446485363 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-702103843/2000000000 : ℝ), (1754213563/5000000000 : ℝ), (2489097569/5000000000 : ℝ)] ![(28398451968677/100000000000000 : ℝ), (5675620306069/20000000000000 : ℝ), (43223446485363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-702103843/2000000000 : ℝ)|^95 ≤ (28398451968677/100000000000000 : ℝ)^79
        have hw : |(-702103843/2000000000 : ℝ)|=(702103843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1754213563/5000000000 : ℝ)|^95 ≤ (5675620306069/20000000000000 : ℝ)^79
        have hw : |(1754213563/5000000000 : ℝ)|=(1754213563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2489097569/5000000000 : ℝ)|^95 ≤ (43223446485363/100000000000000 : ℝ)^79
        have hw : |(2489097569/5000000000 : ℝ)|=(2489097569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s1_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2942393469/10000000000 : ℝ)*x 0 + (-1470319977/5000000000 : ℝ)*x 1 + (5998204887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2942393469/10000000000 : ℝ)^95 ≤ (4593310793989/20000000000000 : ℝ)^79 := by
    have hnat : (2942393469 : ℕ)^95*20000000000000^79 ≤ 4593310793989^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2942393469 10000000000 4593310793989 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1470319977/5000000000 : ℝ)^95 ≤ (22950096052739/100000000000000 : ℝ)^79 := by
    have hnat : (1470319977 : ℕ)^95*100000000000000^79 ≤ 22950096052739^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1470319977 5000000000 22950096052739 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5998204887/10000000000 : ℝ)^95 ≤ (54083349951127/100000000000000 : ℝ)^79 := by
    have hnat : (5998204887 : ℕ)^95*100000000000000^79 ≤ 54083349951127^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5998204887 10000000000 54083349951127 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2942393469/10000000000 : ℝ), (-1470319977/5000000000 : ℝ), (5998204887/10000000000 : ℝ)] ![(4593310793989/20000000000000 : ℝ), (22950096052739/100000000000000 : ℝ), (54083349951127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2942393469/10000000000 : ℝ)|^95 ≤ (4593310793989/20000000000000 : ℝ)^79
        have hw : |(2942393469/10000000000 : ℝ)|=(2942393469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1470319977/5000000000 : ℝ)|^95 ≤ (22950096052739/100000000000000 : ℝ)^79
        have hw : |(-1470319977/5000000000 : ℝ)|=(1470319977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5998204887/10000000000 : ℝ)|^95 ≤ (54083349951127/100000000000000 : ℝ)^79
        have hw : |(5998204887/10000000000 : ℝ)|=(5998204887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s1_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5146548681/10000000000 : ℝ)*x 0 + (5149550873/10000000000 : ℝ)*x 1 + (-1473010203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5146548681/10000000000 : ℝ)^95 ≤ (22493599976763/50000000000000 : ℝ)^79 := by
    have hnat : (5146548681 : ℕ)^95*50000000000000^79 ≤ 22493599976763^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5146548681 10000000000 22493599976763 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5149550873/10000000000 : ℝ)^95 ≤ (22509379849989/50000000000000 : ℝ)^79 := by
    have hnat : (5149550873 : ℕ)^95*50000000000000^79 ≤ 22509379849989^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149550873 10000000000 22509379849989 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1473010203/10000000000 : ℝ)^95 ≤ (9994040334193/100000000000000 : ℝ)^79 := by
    have hnat : (1473010203 : ℕ)^95*100000000000000^79 ≤ 9994040334193^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1473010203 10000000000 9994040334193 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5146548681/10000000000 : ℝ), (5149550873/10000000000 : ℝ), (-1473010203/10000000000 : ℝ)] ![(22493599976763/50000000000000 : ℝ), (22509379849989/50000000000000 : ℝ), (9994040334193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5146548681/10000000000 : ℝ)|^95 ≤ (22493599976763/50000000000000 : ℝ)^79
        have hw : |(5146548681/10000000000 : ℝ)|=(5146548681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5149550873/10000000000 : ℝ)|^95 ≤ (22509379849989/50000000000000 : ℝ)^79
        have hw : |(5149550873/10000000000 : ℝ)|=(5149550873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1473010203/10000000000 : ℝ)|^95 ≤ (9994040334193/100000000000000 : ℝ)^79
        have hw : |(-1473010203/10000000000 : ℝ)|=(1473010203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329051_s1_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4923651183/10000000000 : ℝ)*x 0 + (98530467/200000000 : ℝ)*x 1 + (2025801713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4923651183/10000000000 : ℝ)^95 ≤ (533182303581/1250000000000 : ℝ)^79 := by
    have hnat : (4923651183 : ℕ)^95*1250000000000^79 ≤ 533182303581^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4923651183 10000000000 533182303581 1250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98530467/200000000 : ℝ)^95 ≤ (42684507641701/100000000000000 : ℝ)^79 := by
    have hnat : (98530467 : ℕ)^95*100000000000000^79 ≤ 42684507641701^79*200000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98530467 200000000 42684507641701 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2025801713/10000000000 : ℝ)^95 ≤ (3665227013201/25000000000000 : ℝ)^79 := by
    have hnat : (2025801713 : ℕ)^95*25000000000000^79 ≤ 3665227013201^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025801713 10000000000 3665227013201 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4923651183/10000000000 : ℝ), (98530467/200000000 : ℝ), (2025801713/10000000000 : ℝ)] ![(533182303581/1250000000000 : ℝ), (42684507641701/100000000000000 : ℝ), (3665227013201/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4923651183/10000000000 : ℝ)|^95 ≤ (533182303581/1250000000000 : ℝ)^79
        have hw : |(4923651183/10000000000 : ℝ)|=(4923651183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(98530467/200000000 : ℝ)|^95 ≤ (42684507641701/100000000000000 : ℝ)^79
        have hw : |(98530467/200000000 : ℝ)|=(98530467/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2025801713/10000000000 : ℝ)|^95 ≤ (3665227013201/25000000000000 : ℝ)^79
        have hw : |(2025801713/10000000000 : ℝ)|=(2025801713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329051 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (160257/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-795146453/2500000000 : ℝ)*X 0 0+(1590293363/5000000000 : ℝ)*X 0 1+(5577944271/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((297754527/1250000000 : ℝ)*X 1 0+(-1191018487/5000000000 : ℝ)*X 1 1+(693292923/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1461121499/2500000000 : ℝ)*X 2 0+(5317892977/10000000000 : ℝ)*X 2 1+(-177533961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2811448401/10000000000 : ℝ)*X 0 0+(210626039/1250000000 : ℝ)*X 0 1+(7123781317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1674680021/10000000000 : ℝ)*X 1 0+(-462029643/5000000000 : ℝ)*X 1 1+(8533179427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((840827599/2000000000 : ℝ)*X 2 0+(1380784511/2000000000 : ℝ)*X 2 1+(-15707697/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((360421277/1250000000 : ℝ)*X 0 0+(2011190249/2500000000 : ℝ)*X 0 1+(143312293/10000000000 : ℝ)*X 0 2+(360421277/1250000000 : ℝ)*X 1 0+(2011190249/2500000000 : ℝ)*X 1 1+(143312293/10000000000 : ℝ)*X 1 2+(360421277/1250000000 : ℝ)*X 2 0+(2011190249/2500000000 : ℝ)*X 2 1+(143312293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-450306443/2500000000 : ℝ)*X 0 0+(2823571611/10000000000 : ℝ)*X 0 1+(7026214309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((574746613/5000000000 : ℝ)*X 1 0+(-361218349/2000000000 : ℝ)*X 1 1+(8290188401/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3645612497/5000000000 : ℝ)*X 2 0+(3798458479/10000000000 : ℝ)*X 2 1+(-98089483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1446182269/2000000000 : ℝ)*X 0 0+(1917285399/5000000000 : ℝ)*X 0 1+(162777087/10000000000 : ℝ)*X 0 2+(1446182269/2000000000 : ℝ)*X 1 0+(1917285399/5000000000 : ℝ)*X 1 1+(162777087/10000000000 : ℝ)*X 1 2+(1446182269/2000000000 : ℝ)*X 2 0+(1917285399/5000000000 : ℝ)*X 2 1+(162777087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-2260863099/5000000000 : ℝ)*X 0 0+(2113813183/5000000000 : ℝ)*X 0 1+(326065557/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((50315583/400000000 : ℝ)*X 1 0+(-12415901/80000000 : ℝ)*X 1 1+(2100143567/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((6630589991/10000000000 : ℝ)*X 2 0+(1131777629/2500000000 : ℝ)*X 2 1+(-2694897/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((29802747/125000000 : ℝ)*X 0 0+(8460666557/10000000000 : ℝ)*X 0 1+(96312529/10000000000 : ℝ)*X 0 2+(29802747/125000000 : ℝ)*X 1 0+(8460666557/10000000000 : ℝ)*X 1 1+(96312529/10000000000 : ℝ)*X 1 2+(29802747/125000000 : ℝ)*X 2 0+(8460666557/10000000000 : ℝ)*X 2 1+(96312529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((28407/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28407/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (40671683454373358150817/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (505338960733/500000000000 : ℝ)*(base7) + (64481349/8000000000 : ℝ)*(base39) + (4476438357/250000000000 : ℝ)*(base49) + (58909929949/500000000000 : ℝ)*(base60) + (1832359853261/1000000000000 : ℝ)*(major_s0_0) + (1832359853261/1000000000000 : ℝ)*(major_s0_1) + (1832359853261/1000000000000 : ℝ)*(major_s0_2) + (111177/200000000000 : ℝ)*(sp_s0_2) + (575182176193/250000000000 : ℝ)*(sp_s0_7) + (2300757109879/1000000000000 : ℝ)*(sp_s0_8) + (1150378276997/500000000000 : ℝ)*(sp_s0_9) + (5733493319/3125000000 : ℝ)*(sp_s0_13) + (28405107/1000000000000 : ℝ)*(sp_s0_14) + (12952857/500000000000 : ℝ)*(sp_s0_27) + (103008230791/125000000000 : ℝ)*(f.failure) + (2300757109879/1000000000000 : ℝ)*(f.sum) + (382278843/1250000000000000000000 : ℝ)*base62 + (3319803127283061/10000000000000000000000000000 : ℝ)*base64 + (798821575283061/10000000000000000000000000000 : ℝ)*base67 + (1834459851485477/10000000000000000000000000000 : ℝ)*base68 + (229557501237349/625000000000000000000000000 : ℝ)*base70 + (958618012716939/10000000000000000000000000000 : ℝ)*base73 + (462108062485477/10000000000000000000000000000 : ℝ)*base75 + (67978220514523/10000000000000000000000000000 : ℝ)*base76 + (88611481/10000000000000000000000 : ℝ)*base78 + (137/1562500000000000 : ℝ)*base87 + (137/1562500000000000 : ℝ)*base89 + (137/1562500000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11233/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11233/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6327815758792391376183/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (104103269353/500000000000 : ℝ)*(base5) + (497676512691/500000000000 : ℝ)*(base7) + (511/10000000000 : ℝ)*(base49) + (15117921827/62500000000 : ℝ)*(base60) + (2027179542229/1000000000000 : ℝ)*(major_s0_0) + (2027179542229/1000000000000 : ℝ)*(major_s0_1) + (2027179542229/1000000000000 : ℝ)*(major_s0_2) + (4354523/500000000000 : ℝ)*(sp_s0_0) + (1564537/40000000000 : ℝ)*(sp_s0_1) + (522190806329/200000000000 : ℝ)*(sp_s0_14) + (1305287224901/500000000000 : ℝ)*(sp_s0_15) + (704792319849/250000000000 : ℝ)*(sp_s0_16) + (849414224069/500000000000 : ℝ)*(sp_s0_20) + (349177463/1000000000000 : ℝ)*(sp_s0_22) + (455840980731/500000000000 : ℝ)*(f.failure) + (261096274069/100000000000 : ℝ)*(f.sum) + (2306442341/5000000000000000000000 : ℝ)*base63 + (1889785391605571/10000000000000000000000000000 : ℝ)*base65 + (2342989216394429/10000000000000000000000000000 : ℝ)*base67 + (5411300976278547/10000000000000000000000000000 : ℝ)*base69 + (90298677145439/625000000000000000000000000 : ℝ)*base71 + (4200817564605571/10000000000000000000000000000 : ℝ)*base73 + (4397134902721453/10000000000000000000000000000 : ℝ)*base75 + (3601411328721453/10000000000000000000000000000 : ℝ)*base77 + (2400989131/5000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (6941/12500000000000000 : ℝ)*base86 + (6941/12500000000000000 : ℝ)*base88 + (6941/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(19387/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(19387/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (41184025769229111/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (65673878051/500000000000 : ℝ)*(base7) + (134865217227/250000000000 : ℝ)*(base39) + (139900857199/250000000000 : ℝ)*(base49) + (895174949509/500000000000 : ℝ)*(major_s0_0) + (895174949509/500000000000 : ℝ)*(major_s0_1) + (895174949509/500000000000 : ℝ)*(major_s0_2) + (31392143/1000000000000 : ℝ)*(sp_s0_1) + (49982579/1000000000000 : ℝ)*(sp_s0_13) + (1938383/50000000000 : ℝ)*(sp_s0_15) + (122847/62500000000 : ℝ)*(sp_s0_16) + (2705359654029/1000000000000 : ℝ)*(sp_s0_21) + (1352644747113/500000000000 : ℝ)*(sp_s0_22) + (2705357688477/1000000000000 : ℝ)*(sp_s0_23) + (936470514091/1000000000000 : ℝ)*(sp_s0_27) + (100646592571/125000000000 : ℝ)*(f.failure) + (2705359654029/1000000000000 : ℝ)*(f.sum) + (1208723259/5000000000000000000000 : ℝ)*base63 + (227703063205709/5000000000000000000000000000 : ℝ)*base64 + (247723587294291/5000000000000000000000000000 : ℝ)*base66 + (948210144944413/5000000000000000000000000000 : ℝ)*base68 + (113769899608669/312500000000000000000000000 : ℝ)*base71 + (3625626022705709/5000000000000000000000000000 : ℝ)*base72 + (1955623275555587/5000000000000000000000000000 : ℝ)*base74 + (250091921555587/5000000000000000000000000000 : ℝ)*base76 + (8267459/1000000000000000000000 : ℝ)*base79 + (1931/3125000000000000 : ℝ)*base86 + (1931/3125000000000000 : ℝ)*base88 + (1931/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (28407/50000 : ℝ) ^ (93/16 : ℝ) ≤ (3739140810197622827/100000000000000000000 : ℝ) := by
    have hpowers : (28407/50000 : ℝ)^93 ≤ (3739140810197622827/100000000000000000000 : ℝ)^16 := by
      have hnat : (28407 : ℕ)^93*100000000000000000000^16 ≤ 3739140810197622827^16*50000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28407 50000 3739140810197622827 100000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28407/50000 : ℝ)) (X := (3739140810197622827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (103739140810197622827/100000000000000000000 : ℝ) ≤ (10063355639420093/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (103739140810197622827/100000000000000000000 : ℝ)^16 ≤ (10063355639420093/10000000000000000 : ℝ)^93 := by
      have hnat : (103739140810197622827 : ℕ)^16*10000000000000000^93 ≤ 10063355639420093^93*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103739140810197622827 100000000000000000000 10063355639420093 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10063355639420093/10000000000000000 : ℝ)) (X := (103739140810197622827/100000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (53739140810197622827/50000000000000000000 : ℝ) ≤ (2531211987873253/2500000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (53739140810197622827/50000000000000000000 : ℝ)^16 ≤ (2531211987873253/2500000000000000 : ℝ)^93 := by
      have hnat : (53739140810197622827 : ℕ)^16*2500000000000000^93 ≤ 2531211987873253^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53739140810197622827 50000000000000000000 2531211987873253 2500000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2531211987873253/2500000000000000 : ℝ)) (X := (53739140810197622827/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3726802318829/334200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(61492312072919/5681400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (28407/50000 : ℝ)) (alpha := (3726802318829/334200000000000 : ℝ)) (beta := (61492312072919/5681400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (28407/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3726802318829/334200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(61492312072919/5681400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (11233/20000 : ℝ) ^ (93/16 : ℝ) ≤ (3497596846612080469/100000000000000000000 : ℝ) := by
    have hpowers : (11233/20000 : ℝ)^93 ≤ (3497596846612080469/100000000000000000000 : ℝ)^16 := by
      have hnat : (11233 : ℕ)^93*100000000000000000000^16 ≤ 3497596846612080469^16*20000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11233 20000 3497596846612080469 100000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11233/20000 : ℝ)) (X := (3497596846612080469/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (103497596846612080469/100000000000000000000 : ℝ) ≤ (2514830139260851/2500000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (103497596846612080469/100000000000000000000 : ℝ)^16 ≤ (2514830139260851/2500000000000000 : ℝ)^93 := by
      have hnat : (103497596846612080469 : ℕ)^16*2500000000000000^93 ≤ 2514830139260851^93*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103497596846612080469 100000000000000000000 2514830139260851 2500000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514830139260851/2500000000000000 : ℝ)) (X := (103497596846612080469/100000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (53497596846612080469/50000000000000000000 : ℝ) ≤ (10117003897329969/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (53497596846612080469/50000000000000000000 : ℝ)^16 ≤ (10117003897329969/10000000000000000 : ℝ)^93 := by
      have hnat : (53497596846612080469 : ℕ)^16*10000000000000000^93 ≤ 10117003897329969^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53497596846612080469 50000000000000000000 10117003897329969 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10117003897329969/10000000000000000 : ℝ)) (X := (53497596846612080469/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(14830139260851/1404125000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(11536668057313/1123300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (11233/20000 : ℝ)) (alpha := (14830139260851/1404125000000000 : ℝ)) (beta := (11536668057313/1123300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (11233/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(14830139260851/1404125000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(11536668057313/1123300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (19387/100000 : ℝ) ^ (93/16 : ℝ) ≤ (3610982857755797/50000000000000000000 : ℝ) := by
    have hpowers : (19387/100000 : ℝ)^93 ≤ (3610982857755797/50000000000000000000 : ℝ)^16 := by
      have hnat : (19387 : ℕ)^93*50000000000000000000^16 ≤ 3610982857755797^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19387 100000 3610982857755797 50000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19387/100000 : ℝ)) (X := (3610982857755797/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50003610982857755797/50000000000000000000 : ℝ) ≤ (10000124245157973/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (50003610982857755797/50000000000000000000 : ℝ)^16 ≤ (10000124245157973/10000000000000000 : ℝ)^93 := by
      have hnat : (50003610982857755797 : ℕ)^16*10000000000000000^93 ≤ 10000124245157973^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003610982857755797 50000000000000000000 10000124245157973 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000124245157973/10000000000000000 : ℝ)) (X := (50003610982857755797/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25003610982857755797/25000000000000000000 : ℝ) ≤ (2500062120721873/2500000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (25003610982857755797/25000000000000000000 : ℝ)^16 ≤ (2500062120721873/2500000000000000 : ℝ)^93 := by
      have hnat : (25003610982857755797 : ℕ)^16*2500000000000000^93 ≤ 2500062120721873^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003610982857755797 25000000000000000000 2500062120721873 2500000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500062120721873/2500000000000000 : ℝ)) (X := (25003610982857755797/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(124245157973/1938700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(124237729519/1938700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (19387/100000 : ℝ)) (alpha := (124245157973/1938700000000000 : ℝ)) (beta := (124237729519/1938700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (19387/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(124245157973/1938700000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(124237729519/1938700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-702103843/2000000000 : ℝ)*X 0 0+(1754213563/5000000000 : ℝ)*X 0 1+(2489097569/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2942393469/10000000000 : ℝ)*X 1 0+(-1470319977/5000000000 : ℝ)*X 1 1+(5998204887/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5146548681/10000000000 : ℝ)*X 2 0+(5149550873/10000000000 : ℝ)*X 2 1+(-1473010203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4923651183/10000000000 : ℝ)*X 0 0+(98530467/200000000 : ℝ)*X 0 1+(2025801713/10000000000 : ℝ)*X 0 2+(4923651183/10000000000 : ℝ)*X 1 0+(98530467/200000000 : ℝ)*X 1 1+(2025801713/10000000000 : ℝ)*X 1 2+(4923651183/10000000000 : ℝ)*X 2 0+(98530467/200000000 : ℝ)*X 2 1+(2025801713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329051_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-129267/12500 : ℝ) < ((-55589/25000 : ℝ)*P 0+(-55589/25000 : ℝ)*P 1+(-55589/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-129267/12500 : ℝ) < (-28047599703251347553249649637877803/2742159076062500000000000000000000 : ℝ) := by norm_num
    linear_combination (294613/1000000000000 : ℝ)*(base5) + (4273/1000000000000 : ℝ)*(base11) + (826857/1000000000000 : ℝ)*(base19) + (83567/500000000000 : ℝ)*(base43) + (150431160473/500000000000 : ℝ)*(base49) + (74073/500000000000 : ℝ)*(base53) + (192987792537/1000000000000 : ℝ)*(base59) + (145572860891/200000000000 : ℝ)*(base60) + (55589/25000 : ℝ)*(major_s1_0) + (1111779916433/500000000000 : ℝ)*(major_s1_1) + (1111779925927/500000000000 : ℝ)*(major_s1_2) + (3409429856357/1000000000000 : ℝ)*(sp_s1_0) + (3409429200907/1000000000000 : ℝ)*(sp_s1_1) + (3409430303389/1000000000000 : ℝ)*(sp_s1_2) + (999999705387/1000000000000 : ℝ)*(sp_s1_6) + (340943017591/100000000000 : ℝ)*(f.sum) + (686862834223366823/1158373250000000000000000000000 : ℝ)*base62 + (941305971846807/969350000000000000000000000 : ℝ)*base64 + (2251726802011/5975000000000000000000000 : ℝ)*base66 + (394556195805711/969350000000000000000000000 : ℝ)*base68 + (1441046353250104397/1619783850000000000000000000000 : ℝ)*base70 + (1073905990477/7101750000000000000000000 : ℝ)*base72 + (2644261465897/29875000000000000000000000 : ℝ)*base74 + (933227176463/16710000000000000000000000 : ℝ)*base77 + (138851518741399909/339463650000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p029_b024 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 51 ≤ c.val) (hhi : c.val < 52)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=51 := by omega
  rcases hc with rfl
  · exact collision_c329051 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 51 ≤ c.val) (hhi : c.val < 52)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b024 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b024
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:15:50.268556+00:00
-- url     : https://prove2.me/submissions/fe78e2b9-b415-4afc-90cf-37965e9292c0

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
theorem collision_support_c310043_s0_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2664806923/10000000000 : ℝ)*x 0 + (-4539681017/10000000000 : ℝ)*x 1 + (5421051719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2664806923/10000000000 : ℝ)^9 ≤ (365258425787/2000000000000 : ℝ)^7 := by
    have hnat : (2664806923 : ℕ)^9*2000000000000^7 ≤ 365258425787^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2664806923 10000000000 365258425787 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4539681017/10000000000 : ℝ)^9 ≤ (36227017212337/100000000000000 : ℝ)^7 := by
    have hnat : (4539681017 : ℕ)^9*100000000000000^7 ≤ 36227017212337^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539681017 10000000000 36227017212337 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421051719/10000000000 : ℝ)^9 ≤ (45510061485877/100000000000000 : ℝ)^7 := by
    have hnat : (5421051719 : ℕ)^9*100000000000000^7 ≤ 45510061485877^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421051719 10000000000 45510061485877 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2664806923/10000000000 : ℝ), (-4539681017/10000000000 : ℝ), (5421051719/10000000000 : ℝ)] ![(365258425787/2000000000000 : ℝ), (36227017212337/100000000000000 : ℝ), (45510061485877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2664806923/10000000000 : ℝ)|^9 ≤ (365258425787/2000000000000 : ℝ)^7
        have hw : |(-2664806923/10000000000 : ℝ)|=(2664806923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4539681017/10000000000 : ℝ)|^9 ≤ (36227017212337/100000000000000 : ℝ)^7
        have hw : |(-4539681017/10000000000 : ℝ)|=(4539681017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421051719/10000000000 : ℝ)|^9 ≤ (45510061485877/100000000000000 : ℝ)^7
        have hw : |(5421051719/10000000000 : ℝ)|=(5421051719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s0_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6557770987/10000000000 : ℝ)*x 0 + (-3423213173/10000000000 : ℝ)*x 1 + (-2482105187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6557770987/10000000000 : ℝ)^9 ≤ (29065037796179/50000000000000 : ℝ)^7 := by
    have hnat : (6557770987 : ℕ)^9*50000000000000^7 ≤ 29065037796179^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6557770987 10000000000 29065037796179 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3423213173/10000000000 : ℝ)^9 ≤ (25200843176407/100000000000000 : ℝ)^7 := by
    have hnat : (3423213173 : ℕ)^9*100000000000000^7 ≤ 25200843176407^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3423213173 10000000000 25200843176407 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2482105187/10000000000 : ℝ)^9 ≤ (666763248903/4000000000000 : ℝ)^7 := by
    have hnat : (2482105187 : ℕ)^9*4000000000000^7 ≤ 666763248903^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2482105187 10000000000 666763248903 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6557770987/10000000000 : ℝ), (-3423213173/10000000000 : ℝ), (-2482105187/10000000000 : ℝ)] ![(29065037796179/50000000000000 : ℝ), (25200843176407/100000000000000 : ℝ), (666763248903/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6557770987/10000000000 : ℝ)|^9 ≤ (29065037796179/50000000000000 : ℝ)^7
        have hw : |(6557770987/10000000000 : ℝ)|=(6557770987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3423213173/10000000000 : ℝ)|^9 ≤ (25200843176407/100000000000000 : ℝ)^7
        have hw : |(-3423213173/10000000000 : ℝ)|=(3423213173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2482105187/10000000000 : ℝ)|^9 ≤ (666763248903/4000000000000 : ℝ)^7
        have hw : |(-2482105187/10000000000 : ℝ)|=(2482105187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s0_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2665612447/10000000000 : ℝ)*x 0 + (-4948690737/10000000000 : ℝ)*x 1 + (5022438773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2665612447/10000000000 : ℝ)^9 ≤ (18270019456233/100000000000000 : ℝ)^7 := by
    have hnat : (2665612447 : ℕ)^9*100000000000000^7 ≤ 18270019456233^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2665612447 10000000000 18270019456233 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4948690737/10000000000 : ℝ)^9 ≤ (40476395626329/100000000000000 : ℝ)^7 := by
    have hnat : (4948690737 : ℕ)^9*100000000000000^7 ≤ 40476395626329^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4948690737 10000000000 40476395626329 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5022438773/10000000000 : ℝ)^9 ≤ (20626792447297/50000000000000 : ℝ)^7 := by
    have hnat : (5022438773 : ℕ)^9*50000000000000^7 ≤ 20626792447297^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5022438773 10000000000 20626792447297 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2665612447/10000000000 : ℝ), (-4948690737/10000000000 : ℝ), (5022438773/10000000000 : ℝ)] ![(18270019456233/100000000000000 : ℝ), (40476395626329/100000000000000 : ℝ), (20626792447297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2665612447/10000000000 : ℝ)|^9 ≤ (18270019456233/100000000000000 : ℝ)^7
        have hw : |(-2665612447/10000000000 : ℝ)|=(2665612447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4948690737/10000000000 : ℝ)|^9 ≤ (40476395626329/100000000000000 : ℝ)^7
        have hw : |(-4948690737/10000000000 : ℝ)|=(4948690737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5022438773/10000000000 : ℝ)|^9 ≤ (20626792447297/50000000000000 : ℝ)^7
        have hw : |(5022438773/10000000000 : ℝ)|=(5022438773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s0_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (729614437/2500000000 : ℝ)*x 0 + (42328877/78125000 : ℝ)*x 1 + (432052521/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (729614437/2500000000 : ℝ)^9 ≤ (5131922715719/25000000000000 : ℝ)^7 := by
    have hnat : (729614437 : ℕ)^9*25000000000000^7 ≤ 5131922715719^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729614437 2500000000 5131922715719 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42328877/78125000 : ℝ)^9 ≤ (45478163736769/100000000000000 : ℝ)^7 := by
    have hnat : (42328877 : ℕ)^9*100000000000000^7 ≤ 45478163736769^7*78125000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42328877 78125000 45478163736769 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (432052521/1000000000 : ℝ)^9 ≤ (1359765815333/4000000000000 : ℝ)^7 := by
    have hnat : (432052521 : ℕ)^9*4000000000000^7 ≤ 1359765815333^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432052521 1000000000 1359765815333 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(729614437/2500000000 : ℝ), (42328877/78125000 : ℝ), (432052521/1000000000 : ℝ)] ![(5131922715719/25000000000000 : ℝ), (45478163736769/100000000000000 : ℝ), (1359765815333/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(729614437/2500000000 : ℝ)|^9 ≤ (5131922715719/25000000000000 : ℝ)^7
        have hw : |(729614437/2500000000 : ℝ)|=(729614437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42328877/78125000 : ℝ)|^9 ≤ (45478163736769/100000000000000 : ℝ)^7
        have hw : |(42328877/78125000 : ℝ)|=(42328877/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(432052521/1000000000 : ℝ)|^9 ≤ (1359765815333/4000000000000 : ℝ)^7
        have hw : |(432052521/1000000000 : ℝ)|=(432052521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s0_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6788717563/10000000000 : ℝ)*x 0 + (-3183777447/10000000000 : ℝ)*x 1 + (-304428129/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6788717563/10000000000 : ℝ)^9 ≤ (6077529774863/10000000000000 : ℝ)^7 := by
    have hnat : (6788717563 : ℕ)^9*10000000000000^7 ≤ 6077529774863^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6788717563 10000000000 6077529774863 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3183777447/10000000000 : ℝ)^9 ≤ (918303675253/4000000000000 : ℝ)^7 := by
    have hnat : (3183777447 : ℕ)^9*4000000000000^7 ≤ 918303675253^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3183777447 10000000000 918303675253 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (304428129/1250000000 : ℝ)^9 ≤ (16267110351903/100000000000000 : ℝ)^7 := by
    have hnat : (304428129 : ℕ)^9*100000000000000^7 ≤ 16267110351903^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304428129 1250000000 16267110351903 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6788717563/10000000000 : ℝ), (-3183777447/10000000000 : ℝ), (-304428129/1250000000 : ℝ)] ![(6077529774863/10000000000000 : ℝ), (918303675253/4000000000000 : ℝ), (16267110351903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6788717563/10000000000 : ℝ)|^9 ≤ (6077529774863/10000000000000 : ℝ)^7
        have hw : |(6788717563/10000000000 : ℝ)|=(6788717563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3183777447/10000000000 : ℝ)|^9 ≤ (918303675253/4000000000000 : ℝ)^7
        have hw : |(-3183777447/10000000000 : ℝ)|=(3183777447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-304428129/1250000000 : ℝ)|^9 ≤ (16267110351903/100000000000000 : ℝ)^7
        have hw : |(-304428129/1250000000 : ℝ)|=(304428129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s0_12 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (549445299/1250000000 : ℝ)*x 0 + (-515358471/2500000000 : ℝ)*x 1 + (3011885383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549445299/1250000000 : ℝ)^9 ≤ (34755102783757/100000000000000 : ℝ)^7 := by
    have hnat : (549445299 : ℕ)^9*100000000000000^7 ≤ 34755102783757^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549445299 1250000000 34755102783757 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515358471/2500000000 : ℝ)^9 ≤ (13128581763667/100000000000000 : ℝ)^7 := by
    have hnat : (515358471 : ℕ)^9*100000000000000^7 ≤ 13128581763667^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515358471 2500000000 13128581763667 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3011885383/5000000000 : ℝ)^9 ≤ (52116315440279/100000000000000 : ℝ)^7 := by
    have hnat : (3011885383 : ℕ)^9*100000000000000^7 ≤ 52116315440279^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3011885383 5000000000 52116315440279 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(549445299/1250000000 : ℝ), (-515358471/2500000000 : ℝ), (3011885383/5000000000 : ℝ)] ![(34755102783757/100000000000000 : ℝ), (13128581763667/100000000000000 : ℝ), (52116315440279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(549445299/1250000000 : ℝ)|^9 ≤ (34755102783757/100000000000000 : ℝ)^7
        have hw : |(549445299/1250000000 : ℝ)|=(549445299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-515358471/2500000000 : ℝ)|^9 ≤ (13128581763667/100000000000000 : ℝ)^7
        have hw : |(-515358471/2500000000 : ℝ)|=(515358471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3011885383/5000000000 : ℝ)|^9 ≤ (52116315440279/100000000000000 : ℝ)^7
        have hw : |(3011885383/5000000000 : ℝ)|=(3011885383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s0_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-601411741/2500000000 : ℝ)*x 0 + (-4449399469/10000000000 : ℝ)*x 1 + (285648249/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (601411741/2500000000 : ℝ)^9 ≤ (16011831313541/100000000000000 : ℝ)^7 := by
    have hnat : (601411741 : ℕ)^9*100000000000000^7 ≤ 16011831313541^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601411741 2500000000 16011831313541 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4449399469/10000000000 : ℝ)^9 ≤ (17651681731671/50000000000000 : ℝ)^7 := by
    have hnat : (4449399469 : ℕ)^9*50000000000000^7 ≤ 17651681731671^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4449399469 10000000000 17651681731671 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285648249/500000000 : ℝ)^9 ≤ (48684805208603/100000000000000 : ℝ)^7 := by
    have hnat : (285648249 : ℕ)^9*100000000000000^7 ≤ 48684805208603^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285648249 500000000 48684805208603 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-601411741/2500000000 : ℝ), (-4449399469/10000000000 : ℝ), (285648249/500000000 : ℝ)] ![(16011831313541/100000000000000 : ℝ), (17651681731671/50000000000000 : ℝ), (48684805208603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-601411741/2500000000 : ℝ)|^9 ≤ (16011831313541/100000000000000 : ℝ)^7
        have hw : |(-601411741/2500000000 : ℝ)|=(601411741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4449399469/10000000000 : ℝ)|^9 ≤ (17651681731671/50000000000000 : ℝ)^7
        have hw : |(-4449399469/10000000000 : ℝ)|=(4449399469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(285648249/500000000 : ℝ)|^9 ≤ (48684805208603/100000000000000 : ℝ)^7
        have hw : |(285648249/500000000 : ℝ)|=(285648249/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s0_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3003475957/10000000000 : ℝ)*x 0 + (1388780703/2500000000 : ℝ)*x 1 + (2047905197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3003475957/10000000000 : ℝ)^9 ≤ (5324930310279/25000000000000 : ℝ)^7 := by
    have hnat : (3003475957 : ℕ)^9*25000000000000^7 ≤ 5324930310279^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3003475957 10000000000 5324930310279 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1388780703/2500000000 : ℝ)^9 ≤ (9392452191803/20000000000000 : ℝ)^7 := by
    have hnat : (1388780703 : ℕ)^9*20000000000000^7 ≤ 9392452191803^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388780703 2500000000 9392452191803 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2047905197/5000000000 : ℝ)^9 ≤ (31738017783403/100000000000000 : ℝ)^7 := by
    have hnat : (2047905197 : ℕ)^9*100000000000000^7 ≤ 31738017783403^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047905197 5000000000 31738017783403 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3003475957/10000000000 : ℝ), (1388780703/2500000000 : ℝ), (2047905197/5000000000 : ℝ)] ![(5324930310279/25000000000000 : ℝ), (9392452191803/20000000000000 : ℝ), (31738017783403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3003475957/10000000000 : ℝ)|^9 ≤ (5324930310279/25000000000000 : ℝ)^7
        have hw : |(3003475957/10000000000 : ℝ)|=(3003475957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1388780703/2500000000 : ℝ)|^9 ≤ (9392452191803/20000000000000 : ℝ)^7
        have hw : |(1388780703/2500000000 : ℝ)|=(1388780703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2047905197/5000000000 : ℝ)|^9 ≤ (31738017783403/100000000000000 : ℝ)^7
        have hw : |(2047905197/5000000000 : ℝ)|=(2047905197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s0_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6836762983/10000000000 : ℝ)*x 0 + (-3232768887/10000000000 : ℝ)*x 1 + (-1158564383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6836762983/10000000000 : ℝ)^9 ≤ (61328869533501/100000000000000 : ℝ)^7 := by
    have hnat : (6836762983 : ℕ)^9*100000000000000^7 ≤ 61328869533501^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6836762983 10000000000 61328869533501 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3232768887/10000000000 : ℝ)^9 ≤ (2926598490969/12500000000000 : ℝ)^7 := by
    have hnat : (3232768887 : ℕ)^9*12500000000000^7 ≤ 2926598490969^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3232768887 10000000000 2926598490969 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1158564383/5000000000 : ℝ)^9 ≤ (15258342525229/100000000000000 : ℝ)^7 := by
    have hnat : (1158564383 : ℕ)^9*100000000000000^7 ≤ 15258342525229^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158564383 5000000000 15258342525229 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6836762983/10000000000 : ℝ), (-3232768887/10000000000 : ℝ), (-1158564383/5000000000 : ℝ)] ![(61328869533501/100000000000000 : ℝ), (2926598490969/12500000000000 : ℝ), (15258342525229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6836762983/10000000000 : ℝ)|^9 ≤ (61328869533501/100000000000000 : ℝ)^7
        have hw : |(6836762983/10000000000 : ℝ)|=(6836762983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3232768887/10000000000 : ℝ)|^9 ≤ (2926598490969/12500000000000 : ℝ)^7
        have hw : |(-3232768887/10000000000 : ℝ)|=(3232768887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1158564383/5000000000 : ℝ)|^9 ≤ (15258342525229/100000000000000 : ℝ)^7
        have hw : |(-1158564383/5000000000 : ℝ)|=(1158564383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s0_18 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (497851351/1000000000 : ℝ)*x 0 + (-18832753/80000000 : ℝ)*x 1 + (5246775959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (497851351/1000000000 : ℝ)^9 ≤ (637348209807/1562500000000 : ℝ)^7 := by
    have hnat : (497851351 : ℕ)^9*1562500000000^7 ≤ 637348209807^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497851351 1000000000 637348209807 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18832753/80000000 : ℝ)^9 ≤ (15572018675881/100000000000000 : ℝ)^7 := by
    have hnat : (18832753 : ℕ)^9*100000000000000^7 ≤ 15572018675881^7*80000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18832753 80000000 15572018675881 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246775959/10000000000 : ℝ)^9 ≤ (8727539176849/20000000000000 : ℝ)^7 := by
    have hnat : (5246775959 : ℕ)^9*20000000000000^7 ≤ 8727539176849^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246775959 10000000000 8727539176849 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(497851351/1000000000 : ℝ), (-18832753/80000000 : ℝ), (5246775959/10000000000 : ℝ)] ![(637348209807/1562500000000 : ℝ), (15572018675881/100000000000000 : ℝ), (8727539176849/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(497851351/1000000000 : ℝ)|^9 ≤ (637348209807/1562500000000 : ℝ)^7
        have hw : |(497851351/1000000000 : ℝ)|=(497851351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18832753/80000000 : ℝ)|^9 ≤ (15572018675881/100000000000000 : ℝ)^7
        have hw : |(-18832753/80000000 : ℝ)|=(18832753/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246775959/10000000000 : ℝ)|^9 ≤ (8727539176849/20000000000000 : ℝ)^7
        have hw : |(5246775959/10000000000 : ℝ)|=(5246775959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s0_19 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2790353669/10000000000 : ℝ)*x 0 + (-177389581/400000000 : ℝ)*x 1 + (1354325213/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2790353669/10000000000 : ℝ)^9 ≤ (1937653787203/10000000000000 : ℝ)^7 := by
    have hnat : (2790353669 : ℕ)^9*10000000000000^7 ≤ 1937653787203^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2790353669 10000000000 1937653787203 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177389581/400000000 : ℝ)^9 ≤ (7030776434453/20000000000000 : ℝ)^7 := by
    have hnat : (177389581 : ℕ)^9*20000000000000^7 ≤ 7030776434453^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177389581 400000000 7030776434453 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354325213/2500000000 : ℝ)^9 ≤ (45469579941787/100000000000000 : ℝ)^7 := by
    have hnat : (1354325213 : ℕ)^9*100000000000000^7 ≤ 45469579941787^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354325213 2500000000 45469579941787 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2790353669/10000000000 : ℝ), (-177389581/400000000 : ℝ), (1354325213/2500000000 : ℝ)] ![(1937653787203/10000000000000 : ℝ), (7030776434453/20000000000000 : ℝ), (45469579941787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2790353669/10000000000 : ℝ)|^9 ≤ (1937653787203/10000000000000 : ℝ)^7
        have hw : |(-2790353669/10000000000 : ℝ)|=(2790353669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-177389581/400000000 : ℝ)|^9 ≤ (7030776434453/20000000000000 : ℝ)^7
        have hw : |(-177389581/400000000 : ℝ)|=(177389581/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354325213/2500000000 : ℝ)|^9 ≤ (45469579941787/100000000000000 : ℝ)^7
        have hw : |(1354325213/2500000000 : ℝ)|=(1354325213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s0_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (192338597/625000000 : ℝ)*x 0 + (1376718583/2500000000 : ℝ)*x 1 + (408046769/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (192338597/625000000 : ℝ)^9 ≤ (21976269730957/100000000000000 : ℝ)^7 := by
    have hnat : (192338597 : ℕ)^9*100000000000000^7 ≤ 21976269730957^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192338597 625000000 21976269730957 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376718583/2500000000 : ℝ)^9 ≤ (928769758789/2000000000000 : ℝ)^7 := by
    have hnat : (1376718583 : ℕ)^9*2000000000000^7 ≤ 928769758789^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376718583 2500000000 928769758789 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (408046769/1000000000 : ℝ)^9 ≤ (1579262115207/5000000000000 : ℝ)^7 := by
    have hnat : (408046769 : ℕ)^9*5000000000000^7 ≤ 1579262115207^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408046769 1000000000 1579262115207 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(192338597/625000000 : ℝ), (1376718583/2500000000 : ℝ), (408046769/1000000000 : ℝ)] ![(21976269730957/100000000000000 : ℝ), (928769758789/2000000000000 : ℝ), (1579262115207/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(192338597/625000000 : ℝ)|^9 ≤ (21976269730957/100000000000000 : ℝ)^7
        have hw : |(192338597/625000000 : ℝ)|=(192338597/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1376718583/2500000000 : ℝ)|^9 ≤ (928769758789/2000000000000 : ℝ)^7
        have hw : |(1376718583/2500000000 : ℝ)|=(1376718583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(408046769/1000000000 : ℝ)|^9 ≤ (1579262115207/5000000000000 : ℝ)^7
        have hw : |(408046769/1000000000 : ℝ)|=(408046769/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s0_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1651202871/2500000000 : ℝ)*x 0 + (-1700061177/5000000000 : ℝ)*x 1 + (-1222580029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1651202871/2500000000 : ℝ)^9 ≤ (29333371407231/50000000000000 : ℝ)^7 := by
    have hnat : (1651202871 : ℕ)^9*50000000000000^7 ≤ 29333371407231^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1651202871 2500000000 29333371407231 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1700061177/5000000000 : ℝ)^9 ≤ (24982497015307/100000000000000 : ℝ)^7 := by
    have hnat : (1700061177 : ℕ)^9*100000000000000^7 ≤ 24982497015307^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1700061177 5000000000 24982497015307 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1222580029/5000000000 : ℝ)^9 ≤ (8175380077639/50000000000000 : ℝ)^7 := by
    have hnat : (1222580029 : ℕ)^9*50000000000000^7 ≤ 8175380077639^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222580029 5000000000 8175380077639 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1651202871/2500000000 : ℝ), (-1700061177/5000000000 : ℝ), (-1222580029/5000000000 : ℝ)] ![(29333371407231/50000000000000 : ℝ), (24982497015307/100000000000000 : ℝ), (8175380077639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1651202871/2500000000 : ℝ)|^9 ≤ (29333371407231/50000000000000 : ℝ)^7
        have hw : |(1651202871/2500000000 : ℝ)|=(1651202871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1700061177/5000000000 : ℝ)|^9 ≤ (24982497015307/100000000000000 : ℝ)^7
        have hw : |(-1700061177/5000000000 : ℝ)|=(1700061177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1222580029/5000000000 : ℝ)|^9 ≤ (8175380077639/50000000000000 : ℝ)^7
        have hw : |(-1222580029/5000000000 : ℝ)|=(1222580029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s0_24 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-489/1250000000 : ℝ)*x 0 + (0 : ℝ)*x 1 + (1999999991/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (489/1250000000 : ℝ)^9 ≤ (288819/50000000000000 : ℝ)^7 := by
    have hnat : (489 : ℕ)^9*50000000000000^7 ≤ 288819^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489 1250000000 288819 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^9 ≤ (0 : ℝ)^7 := by
    have hnat : (0 : ℕ)^9*1^7 ≤ 0^7*1^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1999999991/2000000000 : ℝ)^9 ≤ (99999999421429/100000000000000 : ℝ)^7 := by
    have hnat : (1999999991 : ℕ)^9*100000000000000^7 ≤ 99999999421429^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999999991 2000000000 99999999421429 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-489/1250000000 : ℝ), (0 : ℝ), (1999999991/2000000000 : ℝ)] ![(288819/50000000000000 : ℝ), (0 : ℝ), (99999999421429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-489/1250000000 : ℝ)|^9 ≤ (288819/50000000000000 : ℝ)^7
        have hw : |(-489/1250000000 : ℝ)|=(489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^9 ≤ (0 : ℝ)^7
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1999999991/2000000000 : ℝ)|^9 ≤ (99999999421429/100000000000000 : ℝ)^7
        have hw : |(1999999991/2000000000 : ℝ)|=(1999999991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s0_25 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4471651229/10000000000 : ℝ)*x 0 + (-2528345749/10000000000 : ℝ)*x 1 + (5595361159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4471651229/10000000000 : ℝ)^9 ≤ (7106104845343/20000000000000 : ℝ)^7 := by
    have hnat : (4471651229 : ℕ)^9*20000000000000^7 ≤ 7106104845343^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4471651229 10000000000 7106104845343 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2528345749/10000000000 : ℝ)^9 ≤ (4267350530337/25000000000000 : ℝ)^7 := by
    have hnat : (2528345749 : ℕ)^9*25000000000000^7 ≤ 4267350530337^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2528345749 10000000000 4267350530337 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5595361159/10000000000 : ℝ)^9 ≤ (11850018408149/25000000000000 : ℝ)^7 := by
    have hnat : (5595361159 : ℕ)^9*25000000000000^7 ≤ 11850018408149^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595361159 10000000000 11850018408149 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4471651229/10000000000 : ℝ), (-2528345749/10000000000 : ℝ), (5595361159/10000000000 : ℝ)] ![(7106104845343/20000000000000 : ℝ), (4267350530337/25000000000000 : ℝ), (11850018408149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4471651229/10000000000 : ℝ)|^9 ≤ (7106104845343/20000000000000 : ℝ)^7
        have hw : |(4471651229/10000000000 : ℝ)|=(4471651229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2528345749/10000000000 : ℝ)|^9 ≤ (4267350530337/25000000000000 : ℝ)^7
        have hw : |(-2528345749/10000000000 : ℝ)|=(2528345749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5595361159/10000000000 : ℝ)|^9 ≤ (11850018408149/25000000000000 : ℝ)^7
        have hw : |(5595361159/10000000000 : ℝ)|=(5595361159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-335794091/1000000000 : ℝ)*x 0 + (-512049557/1250000000 : ℝ)*x 1 + (5249929297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335794091/1000000000 : ℝ)^9 ≤ (24584724700023/100000000000000 : ℝ)^7 := by
    have hnat : (335794091 : ℕ)^9*100000000000000^7 ≤ 24584724700023^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335794091 1000000000 24584724700023 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512049557/1250000000 : ℝ)^9 ≤ (126975427047/400000000000 : ℝ)^7 := by
    have hnat : (512049557 : ℕ)^9*400000000000^7 ≤ 126975427047^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512049557 1250000000 126975427047 400000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5249929297/10000000000 : ℝ)^9 ≤ (43671418524211/100000000000000 : ℝ)^7 := by
    have hnat : (5249929297 : ℕ)^9*100000000000000^7 ≤ 43671418524211^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5249929297 10000000000 43671418524211 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-335794091/1000000000 : ℝ), (-512049557/1250000000 : ℝ), (5249929297/10000000000 : ℝ)] ![(24584724700023/100000000000000 : ℝ), (126975427047/400000000000 : ℝ), (43671418524211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-335794091/1000000000 : ℝ)|^9 ≤ (24584724700023/100000000000000 : ℝ)^7
        have hw : |(-335794091/1000000000 : ℝ)|=(335794091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-512049557/1250000000 : ℝ)|^9 ≤ (126975427047/400000000000 : ℝ)^7
        have hw : |(-512049557/1250000000 : ℝ)|=(512049557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5249929297/10000000000 : ℝ)|^9 ≤ (43671418524211/100000000000000 : ℝ)^7
        have hw : |(5249929297/10000000000 : ℝ)|=(5249929297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (989812871/2500000000 : ℝ)*x 0 + (2414971583/5000000000 : ℝ)*x 1 + (1979625779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989812871/2500000000 : ℝ)^9 ≤ (30384031600911/100000000000000 : ℝ)^7 := by
    have hnat : (989812871 : ℕ)^9*100000000000000^7 ≤ 30384031600911^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989812871 2500000000 30384031600911 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2414971583/5000000000 : ℝ)^9 ≤ (3923193604779/10000000000000 : ℝ)^7 := by
    have hnat : (2414971583 : ℕ)^9*10000000000000^7 ≤ 3923193604779^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2414971583 5000000000 3923193604779 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1979625779/5000000000 : ℝ)^9 ≤ (6076806466211/20000000000000 : ℝ)^7 := by
    have hnat : (1979625779 : ℕ)^9*20000000000000^7 ≤ 6076806466211^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979625779 5000000000 6076806466211 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(989812871/2500000000 : ℝ), (2414971583/5000000000 : ℝ), (1979625779/5000000000 : ℝ)] ![(30384031600911/100000000000000 : ℝ), (3923193604779/10000000000000 : ℝ), (6076806466211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(989812871/2500000000 : ℝ)|^9 ≤ (30384031600911/100000000000000 : ℝ)^7
        have hw : |(989812871/2500000000 : ℝ)|=(989812871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2414971583/5000000000 : ℝ)|^9 ≤ (3923193604779/10000000000000 : ℝ)^7
        have hw : |(2414971583/5000000000 : ℝ)|=(2414971583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1979625779/5000000000 : ℝ)|^9 ≤ (6076806466211/20000000000000 : ℝ)^7
        have hw : |(1979625779/5000000000 : ℝ)|=(1979625779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (656241153/1250000000 : ℝ)*x 0 + (-4096396467/10000000000 : ℝ)*x 1 + (-3357940981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656241153/1250000000 : ℝ)^9 ≤ (21835708871731/50000000000000 : ℝ)^7 := by
    have hnat : (656241153 : ℕ)^9*50000000000000^7 ≤ 21835708871731^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656241153 1250000000 21835708871731 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4096396467/10000000000 : ℝ)^9 ≤ (15871928435673/50000000000000 : ℝ)^7 := by
    have hnat : (4096396467 : ℕ)^9*50000000000000^7 ≤ 15871928435673^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4096396467 10000000000 15871928435673 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3357940981/10000000000 : ℝ)^9 ≤ (614618134209/2500000000000 : ℝ)^7 := by
    have hnat : (3357940981 : ℕ)^9*2500000000000^7 ≤ 614618134209^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3357940981 10000000000 614618134209 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656241153/1250000000 : ℝ), (-4096396467/10000000000 : ℝ), (-3357940981/10000000000 : ℝ)] ![(21835708871731/50000000000000 : ℝ), (15871928435673/50000000000000 : ℝ), (614618134209/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656241153/1250000000 : ℝ)|^9 ≤ (21835708871731/50000000000000 : ℝ)^7
        have hw : |(656241153/1250000000 : ℝ)|=(656241153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4096396467/10000000000 : ℝ)|^9 ≤ (15871928435673/50000000000000 : ℝ)^7
        have hw : |(-4096396467/10000000000 : ℝ)|=(4096396467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3357940981/10000000000 : ℝ)|^9 ≤ (614618134209/2500000000000 : ℝ)^7
        have hw : |(-3357940981/10000000000 : ℝ)|=(3357940981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310043_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2291493943/5000000000 : ℝ)*x 0 + (-715199561/2000000000 : ℝ)*x 1 + (4582987961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2291493943/5000000000 : ℝ)^9 ≤ (18335977152873/50000000000000 : ℝ)^7 := by
    have hnat : (2291493943 : ℕ)^9*50000000000000^7 ≤ 18335977152873^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291493943 5000000000 18335977152873 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (715199561/2000000000 : ℝ)^9 ≤ (26656090609801/100000000000000 : ℝ)^7 := by
    have hnat : (715199561 : ℕ)^9*100000000000000^7 ≤ 26656090609801^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715199561 2000000000 26656090609801 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4582987961/10000000000 : ℝ)^9 ≤ (1145998596167/3125000000000 : ℝ)^7 := by
    have hnat : (4582987961 : ℕ)^9*3125000000000^7 ≤ 1145998596167^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582987961 10000000000 1145998596167 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2291493943/5000000000 : ℝ), (-715199561/2000000000 : ℝ), (4582987961/10000000000 : ℝ)] ![(18335977152873/50000000000000 : ℝ), (26656090609801/100000000000000 : ℝ), (1145998596167/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2291493943/5000000000 : ℝ)|^9 ≤ (18335977152873/50000000000000 : ℝ)^7
        have hw : |(2291493943/5000000000 : ℝ)|=(2291493943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-715199561/2000000000 : ℝ)|^9 ≤ (26656090609801/100000000000000 : ℝ)^7
        have hw : |(-715199561/2000000000 : ℝ)|=(715199561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4582987961/10000000000 : ℝ)|^9 ≤ (1145998596167/3125000000000 : ℝ)^7
        have hw : |(4582987961/10000000000 : ℝ)|=(4582987961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310043 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2664806923/10000000000 : ℝ)*X 0 0+(-4539681017/10000000000 : ℝ)*X 0 1+(5421051719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((6557770987/10000000000 : ℝ)*X 2 0+(-3423213173/10000000000 : ℝ)*X 2 1+(-2482105187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2665612447/10000000000 : ℝ)*X 0 0+(-4948690737/10000000000 : ℝ)*X 0 1+(5022438773/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((729614437/2500000000 : ℝ)*X 1 0+(42328877/78125000 : ℝ)*X 1 1+(432052521/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((6788717563/10000000000 : ℝ)*X 2 0+(-3183777447/10000000000 : ℝ)*X 2 1+(-304428129/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((549445299/1250000000 : ℝ)*X 0 0+(-515358471/2500000000 : ℝ)*X 0 1+(3011885383/5000000000 : ℝ)*X 0 2+(549445299/1250000000 : ℝ)*X 1 0+(-515358471/2500000000 : ℝ)*X 1 1+(3011885383/5000000000 : ℝ)*X 1 2+(549445299/1250000000 : ℝ)*X 2 0+(-515358471/2500000000 : ℝ)*X 2 1+(3011885383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-601411741/2500000000 : ℝ)*X 0 0+(-4449399469/10000000000 : ℝ)*X 0 1+(285648249/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((3003475957/10000000000 : ℝ)*X 1 0+(1388780703/2500000000 : ℝ)*X 1 1+(2047905197/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((6836762983/10000000000 : ℝ)*X 2 0+(-3232768887/10000000000 : ℝ)*X 2 1+(-1158564383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_18 : ((497851351/1000000000 : ℝ)*X 0 0+(-18832753/80000000 : ℝ)*X 0 1+(5246775959/10000000000 : ℝ)*X 0 2+(497851351/1000000000 : ℝ)*X 1 0+(-18832753/80000000 : ℝ)*X 1 1+(5246775959/10000000000 : ℝ)*X 1 2+(497851351/1000000000 : ℝ)*X 2 0+(-18832753/80000000 : ℝ)*X 2 1+(5246775959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s0_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((-2790353669/10000000000 : ℝ)*X 0 0+(-177389581/400000000 : ℝ)*X 0 1+(1354325213/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s0_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((192338597/625000000 : ℝ)*X 1 0+(1376718583/2500000000 : ℝ)*X 1 1+(408046769/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s0_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((1651202871/2500000000 : ℝ)*X 2 0+(-1700061177/5000000000 : ℝ)*X 2 1+(-1222580029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s0_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_24 : ((-489/1250000000 : ℝ)*X 0 0+(1999999991/2000000000 : ℝ)*X 0 2+(-489/1250000000 : ℝ)*X 1 0+(1999999991/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s0_24 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((4471651229/10000000000 : ℝ)*X 0 0+(-2528345749/10000000000 : ℝ)*X 0 1+(5595361159/10000000000 : ℝ)*X 0 2+(4471651229/10000000000 : ℝ)*X 1 0+(-2528345749/10000000000 : ℝ)*X 1 1+(5595361159/10000000000 : ℝ)*X 1 2+(4471651229/10000000000 : ℝ)*X 2 0+(-2528345749/10000000000 : ℝ)*X 2 1+(5595361159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1587/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1587/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6555830334223333415097/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1239089856487/1000000000000 : ℝ)*(base40) + (406746713079/1000000000000 : ℝ)*(base50) + (375891181253/200000000000 : ℝ)*(base59) + (1236430654647/1000000000000 : ℝ)*(base60) + (2145223882861/250000000000 : ℝ)*(major_s0_0) + (2145223882861/250000000000 : ℝ)*(major_s0_1) + (2145223882861/250000000000 : ℝ)*(major_s0_2) + (1185812609661/100000000000 : ℝ)*(sp_s0_7) + (59290816829/5000000000 : ℝ)*(sp_s0_8) + (1482238300691/125000000000 : ℝ)*(sp_s0_9) + (5303625948863/1000000000000 : ℝ)*(sp_s0_12) + (3726919/100000000000 : ℝ)*(sp_s0_13) + (44351313/1000000000000 : ℝ)*(sp_s0_15) + (212608959/1000000000000 : ℝ)*(sp_s0_21) + (5303625948863/1000000000000 : ℝ)*(f.failure) + (59290816829/5000000000 : ℝ)*(f.sum) + (2301608233/5000000000000000000000 : ℝ)*base62 + (420358039778301/2500000000000000000000000000 : ℝ)*base64 + (13058129778301/2500000000000000000000000000 : ℝ)*base66 + (1398803281472017/2500000000000000000000000000 : ℝ)*base68 + (361312763076571/625000000000000000000000000 : ℝ)*base70 + (723306197278301/2500000000000000000000000000 : ℝ)*base72 + (1328286491277983/2500000000000000000000000000 : ℝ)*base74 + (737900863722017/2500000000000000000000000000 : ℝ)*base77 + (322978969471699/1250000000000000000000000000 : ℝ)*base79 + (8641/100000000000000000 : ℝ)*base86 + (8641/100000000000000000 : ℝ)*base88 + (8641/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1949/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-1949/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20427850347222583282089/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (276498196047/100000000000 : ℝ)*(base40) + (267764634163/500000000000 : ℝ)*(base59) + (12372468611373/1000000000000 : ℝ)*(major_s0_0) + (12372468611373/1000000000000 : ℝ)*(major_s0_1) + (9990020194681/500000000000 : ℝ)*(major_s0_2) + (5515757/200000000000 : ℝ)*(sp_s0_0) + (65080139/500000000000 : ℝ)*(sp_s0_8) + (31066193/1000000000000 : ℝ)*(sp_s0_12) + (341956186511/20000000000 : ℝ)*(sp_s0_13) + (17096954352037/1000000000000 : ℝ)*(sp_s0_14) + (1068614806521/62500000000 : ℝ)*(sp_s0_15) + (3823533264247/500000000000 : ℝ)*(sp_s0_18) + (37619601/50000000000 : ℝ)*(sp_s0_20) + (760757177799/100000000000 : ℝ)*(sp_s0_24) + (7647097594687/1000000000000 : ℝ)*(f.failure) + (1068614806521/62500000000 : ℝ)*(f.sum) + (1313675287544567/10000000000000000000000000000 : ℝ)*base63 + (4558892171282921/5000000000000000000000000000 : ℝ)*base64 + (222116093600707/10000000000000000000000000000 : ℝ)*base67 + (4124144877391443/5000000000000000000000000000 : ℝ)*base69 + (3696123895195839/10000000000000000000000000000 : ℝ)*base71 + (2319578249399293/10000000000000000000000000000 : ℝ)*base72 + (4367821500761681/10000000000000000000000000000 : ℝ)*base75 + (1579041221238319/10000000000000000000000000000 : ℝ)*base76 + (1117386438600707/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (106209/100000000000000000 : ℝ)*base86 + (106209/100000000000000000 : ℝ)*base88 + (6209/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1477/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1477/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1002390676858292833539/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (399044575039/250000000000 : ℝ)*(base40) + (137712144059/1000000000000 : ℝ)*(base50) + (924484339497/1000000000000 : ℝ)*(base59) + (493417887707/62500000000 : ℝ)*(major_s0_0) + (493417887707/62500000000 : ℝ)*(major_s0_1) + (493417887707/62500000000 : ℝ)*(major_s0_2) + (100491493/500000000000 : ℝ)*(sp_s0_0) + (11494697/25000000000 : ℝ)*(sp_s0_2) + (11542469/250000000000 : ℝ)*(sp_s0_7) + (156478521/1000000000000 : ℝ)*(sp_s0_18) + (1363703139093/125000000000 : ℝ)*(sp_s0_19) + (5454936132803/500000000000 : ℝ)*(sp_s0_20) + (5454706238863/500000000000 : ℝ)*(sp_s0_21) + (2439670762029/500000000000 : ℝ)*(sp_s0_25) + (4879498002579/1000000000000 : ℝ)*(f.failure) + (5454936132803/500000000000 : ℝ)*(f.sum) + (1443515197/5000000000000000000000 : ℝ)*base63 + (523841634069513/625000000000000000000000000 : ℝ)*base65 + (628120451680487/625000000000000000000000000 : ℝ)*base66 + (354965316809079/625000000000000000000000000 : ℝ)*base68 + (16415144187051/78125000000000000000000000 : ℝ)*base70 + (415742774805487/625000000000000000000000000 : ℝ)*base72 + (404517898190921/625000000000000000000000000 : ℝ)*base74 + (297424460996579/625000000000000000000000000 : ℝ)*base77 + (67615218274237/312500000000000000000000000 : ℝ)*base78 + (64147/100000000000000000 : ℝ)*base87 + (64147/100000000000000000 : ℝ)*base89 + (64147/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (1587/20000 : ℝ) ^ (35/8 : ℝ) ≤ (191614264517393/12500000000000000000 : ℝ) := by
    have hpowers : (1587/20000 : ℝ)^35 ≤ (191614264517393/12500000000000000000 : ℝ)^8 := by
      have hnat : (1587 : ℕ)^35*12500000000000000000^8 ≤ 191614264517393^8*20000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1587 20000 191614264517393 12500000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1587/20000 : ℝ)) (X := (191614264517393/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (12500191614264517393/12500000000000000000 : ℝ) ≤ (5000017518914887/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (12500191614264517393/12500000000000000000 : ℝ)^8 ≤ (5000017518914887/5000000000000000 : ℝ)^35 := by
      have hnat : (12500191614264517393 : ℕ)^8*5000000000000000^35 ≤ 5000017518914887^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500191614264517393 12500000000000000000 5000017518914887 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000017518914887/5000000000000000 : ℝ)) (X := (12500191614264517393/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (6250191614264517393/6250000000000000000 : ℝ) ≤ (10000070075245223/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (6250191614264517393/6250000000000000000 : ℝ)^8 ≤ (10000070075245223/10000000000000000 : ℝ)^35 := by
      have hnat : (6250191614264517393 : ℕ)^8*10000000000000000^35 ≤ 10000070075245223^35*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250191614264517393 6250000000000000000 10000070075245223 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000070075245223/10000000000000000 : ℝ)) (X := (6250191614264517393/6250000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(17518914887/396750000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(11679138483/264500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1587/20000 : ℝ)) (alpha := (17518914887/396750000000000 : ℝ)) (beta := (11679138483/264500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1587/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(17518914887/396750000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(11679138483/264500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1949/12500 : ℝ) ^ (35/8 : ℝ) ≤ (14720260429422019/50000000000000000000 : ℝ) := by
    have hpowers : (1949/12500 : ℝ)^35 ≤ (14720260429422019/50000000000000000000 : ℝ)^8 := by
      have hnat : (1949 : ℕ)^35*50000000000000000000^8 ≤ 14720260429422019^8*12500^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1949 12500 14720260429422019 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1949/12500 : ℝ)) (X := (14720260429422019/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50014720260429422019/50000000000000000000 : ℝ) ≤ (1250084106223667/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50014720260429422019/50000000000000000000 : ℝ)^8 ≤ (1250084106223667/1250000000000000 : ℝ)^35 := by
      have hnat : (50014720260429422019 : ℕ)^8*1250000000000000^35 ≤ 1250084106223667^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014720260429422019 50000000000000000000 1250084106223667 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250084106223667/1250000000000000 : ℝ)) (X := (50014720260429422019/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25014720260429422019/25000000000000000000 : ℝ) ≤ (1250168193353541/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25014720260429422019/25000000000000000000 : ℝ)^8 ≤ (1250168193353541/1250000000000000 : ℝ)^35 := by
      have hnat : (25014720260429422019 : ℕ)^8*1250000000000000^35 ≤ 1250168193353541^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014720260429422019 25000000000000000000 1250168193353541 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250168193353541/1250000000000000 : ℝ)) (X := (25014720260429422019/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(84106223667/194900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(42043564937/97450000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1949/12500 : ℝ)) (alpha := (84106223667/194900000000000 : ℝ)) (beta := (42043564937/97450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1949/12500 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(84106223667/194900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(42043564937/97450000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1477/100000 : ℝ) ^ (35/8 : ℝ) ≤ (979579452799/100000000000000000000 : ℝ) := by
    have hpowers : (1477/100000 : ℝ)^35 ≤ (979579452799/100000000000000000000 : ℝ)^8 := by
      have hnat : (1477 : ℕ)^35*100000000000000000000^8 ≤ 979579452799^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1477 100000 979579452799 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1477/100000 : ℝ)) (X := (979579452799/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100000000979579452799/100000000000000000000 : ℝ) ≤ (2500000005597597/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (100000000979579452799/100000000000000000000 : ℝ)^8 ≤ (2500000005597597/2500000000000000 : ℝ)^35 := by
      have hnat : (100000000979579452799 : ℕ)^8*2500000000000000^35 ≤ 2500000005597597^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100000000979579452799 100000000000000000000 2500000005597597 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000005597597/2500000000000000 : ℝ)) (X := (100000000979579452799/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50000000979579452799/50000000000000000000 : ℝ) ≤ (400000001791231/400000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50000000979579452799/50000000000000000000 : ℝ)^8 ≤ (400000001791231/400000000000000 : ℝ)^35 := by
      have hnat : (50000000979579452799 : ℕ)^8*400000000000000^35 ≤ 400000001791231^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000979579452799 50000000000000000000 400000001791231 400000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400000001791231/400000000000000 : ℝ)) (X := (50000000979579452799/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(5597597/36925000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(22390387/147700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1477/100000 : ℝ)) (alpha := (5597597/36925000000000 : ℝ)) (beta := (22390387/147700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1477/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(5597597/36925000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(22390387/147700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-335794091/1000000000 : ℝ)*X 0 0+(-512049557/1250000000 : ℝ)*X 0 1+(5249929297/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((989812871/2500000000 : ℝ)*X 1 0+(2414971583/5000000000 : ℝ)*X 1 1+(1979625779/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((656241153/1250000000 : ℝ)*X 2 0+(-4096396467/10000000000 : ℝ)*X 2 1+(-3357940981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2291493943/5000000000 : ℝ)*X 0 0+(-715199561/2000000000 : ℝ)*X 0 1+(4582987961/10000000000 : ℝ)*X 0 2+(2291493943/5000000000 : ℝ)*X 1 0+(-715199561/2000000000 : ℝ)*X 1 1+(4582987961/10000000000 : ℝ)*X 1 2+(2291493943/5000000000 : ℝ)*X 2 0+(-715199561/2000000000 : ℝ)*X 2 1+(4582987961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310043_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-20194219590960371884844559125229/3045636034000000000000000000000 : ℝ) := by norm_num
    linear_combination (209899/1000000000000 : ℝ)*(base5) + (9709/1000000000000 : ℝ)*(base17) + (1231/62500000000 : ℝ)*(base21) + (70244534927/1000000000000 : ℝ)*(base39) + (354881070101/1000000000000 : ℝ)*(base40) + (127903443957/200000000000 : ℝ)*(base59) + (711412183/2500000000 : ℝ)*(base60) + (62587/1000000000000 : ℝ)*(ratio_s0_1) + (161793/100000 : ℝ)*(major_s1_0) + (161793/100000 : ℝ)*(major_s1_1) + (161793/100000 : ℝ)*(major_s1_2) + (2210180880171/1000000000000 : ℝ)*(sp_s1_0) + (2210180870463/1000000000000 : ℝ)*(sp_s1_1) + (17681448563/8000000000 : ℝ)*(sp_s1_2) + (999999790101/1000000000000 : ℝ)*(sp_s1_6) + (2210180880171/1000000000000 : ℝ)*(f.sum) + (2265009691294387/7196682500000000000000000000 : ℝ)*base62 + (4269927830963/14770000000000000000000000 : ℝ)*base64 + (519930717531/2436250000000000000000000 : ℝ)*base67 + (3144109497353/7385000000000000000000000 : ℝ)*base68 + (1594676101018149/7813330000000000000000000000 : ℝ)*base70 + (264155432907/1058000000000000000000000 : ℝ)*base72 + (2613549171107/9745000000000000000000000 : ℝ)*base74 + (198769162447/529000000000000000000000 : ℝ)*base77 + (457199362362953/5155105000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p010_b024 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 43 ≤ c.val) (hhi : c.val < 44)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=43 := by omega
  rcases hc with rfl
  · exact collision_c310043 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 43 ≤ c.val) (hhi : c.val < 44)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b024 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

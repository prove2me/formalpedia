-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p008_b011
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:42:59.61697+00:00
-- url     : https://prove2.me/submissions/f67582ef-bc07-4558-ba97-098b580245b4

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
theorem collision_support_c308020_s0_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3161481321/5000000000 : ℝ)*x 0 + (-24400949/100000000 : ℝ)*x 1 + (-955307067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3161481321/5000000000 : ℝ)^35 ≤ (11039874269759/20000000000000 : ℝ)^27 := by
    have hnat : (3161481321 : ℕ)^35*20000000000000^27 ≤ 11039874269759^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3161481321 5000000000 11039874269759 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24400949/100000000 : ℝ)^35 ≤ (16065623921533/100000000000000 : ℝ)^27 := by
    have hnat : (24400949 : ℕ)^35*100000000000000^27 ≤ 16065623921533^27*100000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24400949 100000000 16065623921533 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955307067/2500000000 : ℝ)^35 ≤ (14367502357953/50000000000000 : ℝ)^27 := by
    have hnat : (955307067 : ℕ)^35*50000000000000^27 ≤ 14367502357953^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955307067 2500000000 14367502357953 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3161481321/5000000000 : ℝ), (-24400949/100000000 : ℝ), (-955307067/2500000000 : ℝ)] ![(11039874269759/20000000000000 : ℝ), (16065623921533/100000000000000 : ℝ), (14367502357953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3161481321/5000000000 : ℝ)|^35 ≤ (11039874269759/20000000000000 : ℝ)^27
        have hw : |(3161481321/5000000000 : ℝ)|=(3161481321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24400949/100000000 : ℝ)|^35 ≤ (16065623921533/100000000000000 : ℝ)^27
        have hw : |(-24400949/100000000 : ℝ)|=(24400949/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-955307067/2500000000 : ℝ)|^35 ≤ (14367502357953/50000000000000 : ℝ)^27
        have hw : |(-955307067/2500000000 : ℝ)|=(955307067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s0_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (610023801/2500000000 : ℝ)*x 0 + (6322962443/10000000000 : ℝ)*x 1 + (477653529/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (610023801/2500000000 : ℝ)^35 ≤ (16065626516123/100000000000000 : ℝ)^27 := by
    have hnat : (610023801 : ℕ)^35*100000000000000^27 ≤ 16065626516123^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610023801 2500000000 16065626516123 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6322962443/10000000000 : ℝ)^35 ≤ (27599684548391/50000000000000 : ℝ)^27 := by
    have hnat : (6322962443 : ℕ)^35*50000000000000^27 ≤ 27599684548391^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6322962443 10000000000 27599684548391 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477653529/1250000000 : ℝ)^35 ≤ (1436750218249/5000000000000 : ℝ)^27 := by
    have hnat : (477653529 : ℕ)^35*5000000000000^27 ≤ 1436750218249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477653529 1250000000 1436750218249 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(610023801/2500000000 : ℝ), (6322962443/10000000000 : ℝ), (477653529/1250000000 : ℝ)] ![(16065626516123/100000000000000 : ℝ), (27599684548391/50000000000000 : ℝ), (1436750218249/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(610023801/2500000000 : ℝ)|^35 ≤ (16065626516123/100000000000000 : ℝ)^27
        have hw : |(610023801/2500000000 : ℝ)|=(610023801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6322962443/10000000000 : ℝ)|^35 ≤ (27599684548391/50000000000000 : ℝ)^27
        have hw : |(6322962443/10000000000 : ℝ)|=(6322962443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(477653529/1250000000 : ℝ)|^35 ≤ (1436750218249/5000000000000 : ℝ)^27
        have hw : |(477653529/1250000000 : ℝ)|=(477653529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s0_4 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^35 ≤ (0 : ℝ)^27 := by
    have hnat : (0 : ℕ)^35*1^27 ≤ 0^27*1^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^35 ≤ (1 : ℝ)^27 := by
    have hnat : (1 : ℕ)^35*1^27 ≤ 1^27*1^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^35 ≤ (0 : ℝ)^27 := by
    have hnat : (0 : ℕ)^35*1^27 ≤ 0^27*1^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^35 ≤ (0 : ℝ)^27
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1 : ℝ)|^35 ≤ (1 : ℝ)^27
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^35 ≤ (0 : ℝ)^27
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s0_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-470213347/1250000000 : ℝ)*x 0 + (2770733427/10000000000 : ℝ)*x 1 + (-6118913917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (470213347/1250000000 : ℝ)^35 ≤ (14078068496697/50000000000000 : ℝ)^27 := by
    have hnat : (470213347 : ℕ)^35*50000000000000^27 ≤ 14078068496697^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470213347 1250000000 14078068496697 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2770733427/10000000000 : ℝ)^35 ≤ (236781432893/1250000000000 : ℝ)^27 := by
    have hnat : (2770733427 : ℕ)^35*1250000000000^27 ≤ 236781432893^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2770733427 10000000000 236781432893 1250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6118913917/10000000000 : ℝ)^35 ≤ (26450674175703/50000000000000 : ℝ)^27 := by
    have hnat : (6118913917 : ℕ)^35*50000000000000^27 ≤ 26450674175703^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6118913917 10000000000 26450674175703 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-470213347/1250000000 : ℝ), (2770733427/10000000000 : ℝ), (-6118913917/10000000000 : ℝ)] ![(14078068496697/50000000000000 : ℝ), (236781432893/1250000000000 : ℝ), (26450674175703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-470213347/1250000000 : ℝ)|^35 ≤ (14078068496697/50000000000000 : ℝ)^27
        have hw : |(-470213347/1250000000 : ℝ)|=(470213347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2770733427/10000000000 : ℝ)|^35 ≤ (236781432893/1250000000000 : ℝ)^27
        have hw : |(2770733427/10000000000 : ℝ)|=(2770733427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6118913917/10000000000 : ℝ)|^35 ≤ (26450674175703/50000000000000 : ℝ)^27
        have hw : |(-6118913917/10000000000 : ℝ)|=(6118913917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s0_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3208139261/5000000000 : ℝ)*x 0 + (-1889561943/10000000000 : ℝ)*x 1 + (-2086463237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3208139261/5000000000 : ℝ)^35 ≤ (56257695241199/100000000000000 : ℝ)^27 := by
    have hnat : (3208139261 : ℕ)^35*100000000000000^27 ≤ 56257695241199^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3208139261 5000000000 56257695241199 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1889561943/10000000000 : ℝ)^35 ≤ (5766597265421/50000000000000 : ℝ)^27 := by
    have hnat : (1889561943 : ℕ)^35*50000000000000^27 ≤ 5766597265421^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889561943 10000000000 5766597265421 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086463237/5000000000 : ℝ)^35 ≤ (20130693883/62500000000 : ℝ)^27 := by
    have hnat : (2086463237 : ℕ)^35*62500000000^27 ≤ 20130693883^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086463237 5000000000 20130693883 62500000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3208139261/5000000000 : ℝ), (-1889561943/10000000000 : ℝ), (-2086463237/5000000000 : ℝ)] ![(56257695241199/100000000000000 : ℝ), (5766597265421/50000000000000 : ℝ), (20130693883/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3208139261/5000000000 : ℝ)|^35 ≤ (56257695241199/100000000000000 : ℝ)^27
        have hw : |(3208139261/5000000000 : ℝ)|=(3208139261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1889561943/10000000000 : ℝ)|^35 ≤ (5766597265421/50000000000000 : ℝ)^27
        have hw : |(-1889561943/10000000000 : ℝ)|=(1889561943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2086463237/5000000000 : ℝ)|^35 ≤ (20130693883/62500000000 : ℝ)^27
        have hw : |(-2086463237/5000000000 : ℝ)|=(2086463237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s0_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (972383453/5000000000 : ℝ)*x 0 + (7218066439/10000000000 : ℝ)*x 1 + (632684151/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (972383453/5000000000 : ℝ)^35 ≤ (478874418237/4000000000000 : ℝ)^27 := by
    have hnat : (972383453 : ℕ)^35*4000000000000^27 ≤ 478874418237^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972383453 5000000000 478874418237 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7218066439/10000000000 : ℝ)^35 ≤ (32767364277479/50000000000000 : ℝ)^27 := by
    have hnat : (7218066439 : ℕ)^35*50000000000000^27 ≤ 32767364277479^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7218066439 10000000000 32767364277479 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (632684151/2000000000 : ℝ)^35 ≤ (22493410965693/100000000000000 : ℝ)^27 := by
    have hnat : (632684151 : ℕ)^35*100000000000000^27 ≤ 22493410965693^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632684151 2000000000 22493410965693 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(972383453/5000000000 : ℝ), (7218066439/10000000000 : ℝ), (632684151/2000000000 : ℝ)] ![(478874418237/4000000000000 : ℝ), (32767364277479/50000000000000 : ℝ), (22493410965693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(972383453/5000000000 : ℝ)|^35 ≤ (478874418237/4000000000000 : ℝ)^27
        have hw : |(972383453/5000000000 : ℝ)|=(972383453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7218066439/10000000000 : ℝ)|^35 ≤ (32767364277479/50000000000000 : ℝ)^27
        have hw : |(7218066439/10000000000 : ℝ)|=(7218066439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(632684151/2000000000 : ℝ)|^35 ≤ (22493410965693/100000000000000 : ℝ)^27
        have hw : |(632684151/2000000000 : ℝ)|=(632684151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s0_12 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2018643707/5000000000 : ℝ)*x 0 + (47929301/80000000 : ℝ)*x 1 + (-2625712627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2018643707/5000000000 : ℝ)^35 ≤ (12054120541/39062500000 : ℝ)^27 := by
    have hnat : (2018643707 : ℕ)^35*39062500000^27 ≤ 12054120541^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018643707 5000000000 12054120541 39062500000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47929301/80000000 : ℝ)^35 ≤ (25737032920871/50000000000000 : ℝ)^27 := by
    have hnat : (47929301 : ℕ)^35*50000000000000^27 ≤ 25737032920871^27*80000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47929301 80000000 25737032920871 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2625712627/10000000000 : ℝ)^35 ≤ (17667385557829/100000000000000 : ℝ)^27 := by
    have hnat : (2625712627 : ℕ)^35*100000000000000^27 ≤ 17667385557829^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625712627 10000000000 17667385557829 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2018643707/5000000000 : ℝ), (47929301/80000000 : ℝ), (-2625712627/10000000000 : ℝ)] ![(12054120541/39062500000 : ℝ), (25737032920871/50000000000000 : ℝ), (17667385557829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2018643707/5000000000 : ℝ)|^35 ≤ (12054120541/39062500000 : ℝ)^27
        have hw : |(2018643707/5000000000 : ℝ)|=(2018643707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(47929301/80000000 : ℝ)|^35 ≤ (25737032920871/50000000000000 : ℝ)^27
        have hw : |(47929301/80000000 : ℝ)|=(47929301/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2625712627/10000000000 : ℝ)|^35 ≤ (17667385557829/100000000000000 : ℝ)^27
        have hw : |(-2625712627/10000000000 : ℝ)|=(2625712627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s0_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1877403009/5000000000 : ℝ)*x 0 + (3168791203/10000000000 : ℝ)*x 1 + (-1160230513/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1877403009/5000000000 : ℝ)^35 ≤ (14044599621629/50000000000000 : ℝ)^27 := by
    have hnat : (1877403009 : ℕ)^35*50000000000000^27 ≤ 14044599621629^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877403009 5000000000 14044599621629 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3168791203/10000000000 : ℝ)^35 ≤ (5635731079329/25000000000000 : ℝ)^27 := by
    have hnat : (3168791203 : ℕ)^35*25000000000000^27 ≤ 5635731079329^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3168791203 10000000000 5635731079329 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1160230513/2000000000 : ℝ)^35 ≤ (24683938213621/50000000000000 : ℝ)^27 := by
    have hnat : (1160230513 : ℕ)^35*50000000000000^27 ≤ 24683938213621^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1160230513 2000000000 24683938213621 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1877403009/5000000000 : ℝ), (3168791203/10000000000 : ℝ), (-1160230513/2000000000 : ℝ)] ![(14044599621629/50000000000000 : ℝ), (5635731079329/25000000000000 : ℝ), (24683938213621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1877403009/5000000000 : ℝ)|^35 ≤ (14044599621629/50000000000000 : ℝ)^27
        have hw : |(-1877403009/5000000000 : ℝ)|=(1877403009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3168791203/10000000000 : ℝ)|^35 ≤ (5635731079329/25000000000000 : ℝ)^27
        have hw : |(3168791203/10000000000 : ℝ)|=(3168791203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1160230513/2000000000 : ℝ)|^35 ≤ (24683938213621/50000000000000 : ℝ)^27
        have hw : |(-1160230513/2000000000 : ℝ)|=(1160230513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s0_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1370207311/2000000000 : ℝ)*x 0 + (-1367315579/5000000000 : ℝ)*x 1 + (-290366491/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1370207311/2000000000 : ℝ)^35 ≤ (30623969574279/50000000000000 : ℝ)^27 := by
    have hnat : (1370207311 : ℕ)^35*50000000000000^27 ≤ 30623969574279^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370207311 2000000000 30623969574279 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367315579/5000000000 : ℝ)^35 ≤ (9311592237699/50000000000000 : ℝ)^27 := by
    have hnat : (1367315579 : ℕ)^35*50000000000000^27 ≤ 9311592237699^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367315579 5000000000 9311592237699 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (290366491/1000000000 : ℝ)^35 ≤ (10064438179109/50000000000000 : ℝ)^27 := by
    have hnat : (290366491 : ℕ)^35*50000000000000^27 ≤ 10064438179109^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290366491 1000000000 10064438179109 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1370207311/2000000000 : ℝ), (-1367315579/5000000000 : ℝ), (-290366491/1000000000 : ℝ)] ![(30623969574279/50000000000000 : ℝ), (9311592237699/50000000000000 : ℝ), (10064438179109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1370207311/2000000000 : ℝ)|^35 ≤ (30623969574279/50000000000000 : ℝ)^27
        have hw : |(1370207311/2000000000 : ℝ)|=(1370207311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1367315579/5000000000 : ℝ)|^35 ≤ (9311592237699/50000000000000 : ℝ)^27
        have hw : |(-1367315579/5000000000 : ℝ)|=(1367315579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-290366491/1000000000 : ℝ)|^35 ≤ (10064438179109/50000000000000 : ℝ)^27
        have hw : |(-290366491/1000000000 : ℝ)|=(290366491/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s0_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1143610921/5000000000 : ℝ)*x 0 + (3211690473/5000000000 : ℝ)*x 1 + (1918477219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1143610921/5000000000 : ℝ)^35 ≤ (14773170457003/100000000000000 : ℝ)^27 := by
    have hnat : (1143610921 : ℕ)^35*100000000000000^27 ≤ 14773170457003^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143610921 5000000000 14773170457003 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3211690473/5000000000 : ℝ)^35 ≤ (28169216882037/50000000000000 : ℝ)^27 := by
    have hnat : (3211690473 : ℕ)^35*50000000000000^27 ≤ 28169216882037^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3211690473 5000000000 28169216882037 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1918477219/5000000000 : ℝ)^35 ≤ (28888395755497/100000000000000 : ℝ)^27 := by
    have hnat : (1918477219 : ℕ)^35*100000000000000^27 ≤ 28888395755497^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918477219 5000000000 28888395755497 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1143610921/5000000000 : ℝ), (3211690473/5000000000 : ℝ), (1918477219/5000000000 : ℝ)] ![(14773170457003/100000000000000 : ℝ), (28169216882037/50000000000000 : ℝ), (28888395755497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1143610921/5000000000 : ℝ)|^35 ≤ (14773170457003/100000000000000 : ℝ)^27
        have hw : |(1143610921/5000000000 : ℝ)|=(1143610921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3211690473/5000000000 : ℝ)|^35 ≤ (28169216882037/50000000000000 : ℝ)^27
        have hw : |(3211690473/5000000000 : ℝ)|=(3211690473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1918477219/5000000000 : ℝ)|^35 ≤ (28888395755497/100000000000000 : ℝ)^27
        have hw : |(1918477219/5000000000 : ℝ)|=(1918477219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s0_19 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (76511277/200000000 : ℝ)*x 0 + (4442460729/10000000000 : ℝ)*x 1 + (-2287649523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76511277/200000000 : ℝ)^35 ≤ (14388637392147/50000000000000 : ℝ)^27 := by
    have hnat : (76511277 : ℕ)^35*50000000000000^27 ≤ 14388637392147^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76511277 200000000 14388637392147 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4442460729/10000000000 : ℝ)^35 ≤ (8732845626111/25000000000000 : ℝ)^27 := by
    have hnat : (4442460729 : ℕ)^35*25000000000000^27 ≤ 8732845626111^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4442460729 10000000000 8732845626111 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2287649523/5000000000 : ℝ)^35 ≤ (36291342698541/100000000000000 : ℝ)^27 := by
    have hnat : (2287649523 : ℕ)^35*100000000000000^27 ≤ 36291342698541^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287649523 5000000000 36291342698541 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(76511277/200000000 : ℝ), (4442460729/10000000000 : ℝ), (-2287649523/5000000000 : ℝ)] ![(14388637392147/50000000000000 : ℝ), (8732845626111/25000000000000 : ℝ), (36291342698541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(76511277/200000000 : ℝ)|^35 ≤ (14388637392147/50000000000000 : ℝ)^27
        have hw : |(76511277/200000000 : ℝ)|=(76511277/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4442460729/10000000000 : ℝ)|^35 ≤ (8732845626111/25000000000000 : ℝ)^27
        have hw : |(4442460729/10000000000 : ℝ)|=(4442460729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2287649523/5000000000 : ℝ)|^35 ≤ (36291342698541/100000000000000 : ℝ)^27
        have hw : |(-2287649523/5000000000 : ℝ)|=(2287649523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s0_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-5463391/19531250 : ℝ)*x 0 + (997847049/2500000000 : ℝ)*x 1 + (-589607637/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5463391/19531250 : ℝ)^35 ≤ (3835580063007/20000000000000 : ℝ)^27 := by
    have hnat : (5463391 : ℕ)^35*20000000000000^27 ≤ 3835580063007^27*19531250^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463391 19531250 3835580063007 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (997847049/2500000000 : ℝ)^35 ≤ (30404542844057/100000000000000 : ℝ)^27 := by
    have hnat : (997847049 : ℕ)^35*100000000000000^27 ≤ 30404542844057^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997847049 2500000000 30404542844057 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (589607637/1000000000 : ℝ)^35 ≤ (12604389207877/25000000000000 : ℝ)^27 := by
    have hnat : (589607637 : ℕ)^35*25000000000000^27 ≤ 12604389207877^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589607637 1000000000 12604389207877 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5463391/19531250 : ℝ), (997847049/2500000000 : ℝ), (-589607637/1000000000 : ℝ)] ![(3835580063007/20000000000000 : ℝ), (30404542844057/100000000000000 : ℝ), (12604389207877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5463391/19531250 : ℝ)|^35 ≤ (3835580063007/20000000000000 : ℝ)^27
        have hw : |(-5463391/19531250 : ℝ)|=(5463391/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(997847049/2500000000 : ℝ)|^35 ≤ (30404542844057/100000000000000 : ℝ)^27
        have hw : |(997847049/2500000000 : ℝ)|=(997847049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-589607637/1000000000 : ℝ)|^35 ≤ (12604389207877/25000000000000 : ℝ)^27
        have hw : |(-589607637/1000000000 : ℝ)|=(589607637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s0_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1812533781/2500000000 : ℝ)*x 0 + (-2050639573/10000000000 : ℝ)*x 1 + (-3029203609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1812533781/2500000000 : ℝ)^35 ≤ (65912406411077/100000000000000 : ℝ)^27 := by
    have hnat : (1812533781 : ℕ)^35*100000000000000^27 ≤ 65912406411077^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812533781 2500000000 65912406411077 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050639573/10000000000 : ℝ)^35 ≤ (6411722188273/50000000000000 : ℝ)^27 := by
    have hnat : (2050639573 : ℕ)^35*50000000000000^27 ≤ 6411722188273^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050639573 10000000000 6411722188273 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3029203609/10000000000 : ℝ)^35 ≤ (10632074602167/50000000000000 : ℝ)^27 := by
    have hnat : (3029203609 : ℕ)^35*50000000000000^27 ≤ 10632074602167^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3029203609 10000000000 10632074602167 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1812533781/2500000000 : ℝ), (-2050639573/10000000000 : ℝ), (-3029203609/10000000000 : ℝ)] ![(65912406411077/100000000000000 : ℝ), (6411722188273/50000000000000 : ℝ), (10632074602167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1812533781/2500000000 : ℝ)|^35 ≤ (65912406411077/100000000000000 : ℝ)^27
        have hw : |(1812533781/2500000000 : ℝ)|=(1812533781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2050639573/10000000000 : ℝ)|^35 ≤ (6411722188273/50000000000000 : ℝ)^27
        have hw : |(-2050639573/10000000000 : ℝ)|=(2050639573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3029203609/10000000000 : ℝ)|^35 ≤ (10632074602167/50000000000000 : ℝ)^27
        have hw : |(-3029203609/10000000000 : ℝ)|=(3029203609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s0_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1856538071/10000000000 : ℝ)*x 0 + (1666070303/2500000000 : ℝ)*x 1 + (978306017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1856538071/10000000000 : ℝ)^35 ≤ (5636292536453/50000000000000 : ℝ)^27 := by
    have hnat : (1856538071 : ℕ)^35*50000000000000^27 ≤ 5636292536453^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856538071 10000000000 5636292536453 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1666070303/2500000000 : ℝ)^35 ≤ (59092460635673/100000000000000 : ℝ)^27 := by
    have hnat : (1666070303 : ℕ)^35*100000000000000^27 ≤ 59092460635673^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1666070303 2500000000 59092460635673 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (978306017/2500000000 : ℝ)^35 ≤ (29634954271111/100000000000000 : ℝ)^27 := by
    have hnat : (978306017 : ℕ)^35*100000000000000^27 ≤ 29634954271111^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978306017 2500000000 29634954271111 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1856538071/10000000000 : ℝ), (1666070303/2500000000 : ℝ), (978306017/2500000000 : ℝ)] ![(5636292536453/50000000000000 : ℝ), (59092460635673/100000000000000 : ℝ), (29634954271111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1856538071/10000000000 : ℝ)|^35 ≤ (5636292536453/50000000000000 : ℝ)^27
        have hw : |(1856538071/10000000000 : ℝ)|=(1856538071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1666070303/2500000000 : ℝ)|^35 ≤ (59092460635673/100000000000000 : ℝ)^27
        have hw : |(1666070303/2500000000 : ℝ)|=(1666070303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(978306017/2500000000 : ℝ)|^35 ≤ (29634954271111/100000000000000 : ℝ)^27
        have hw : |(978306017/2500000000 : ℝ)|=(978306017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s0_25 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5936595799/10000000000 : ℝ)*x 0 + (2112070683/5000000000 : ℝ)*x 1 + (-2480389277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5936595799/10000000000 : ℝ)^35 ≤ (50867158091453/100000000000000 : ℝ)^27 := by
    have hnat : (5936595799 : ℕ)^35*100000000000000^27 ≤ 50867158091453^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5936595799 10000000000 50867158091453 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112070683/5000000000 : ℝ)^35 ≤ (32722473981379/100000000000000 : ℝ)^27 := by
    have hnat : (2112070683 : ℕ)^35*100000000000000^27 ≤ 32722473981379^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112070683 5000000000 32722473981379 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2480389277/10000000000 : ℝ)^35 ≤ (4102591977991/25000000000000 : ℝ)^27 := by
    have hnat : (2480389277 : ℕ)^35*25000000000000^27 ≤ 4102591977991^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2480389277 10000000000 4102591977991 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5936595799/10000000000 : ℝ), (2112070683/5000000000 : ℝ), (-2480389277/10000000000 : ℝ)] ![(50867158091453/100000000000000 : ℝ), (32722473981379/100000000000000 : ℝ), (4102591977991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5936595799/10000000000 : ℝ)|^35 ≤ (50867158091453/100000000000000 : ℝ)^27
        have hw : |(5936595799/10000000000 : ℝ)|=(5936595799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112070683/5000000000 : ℝ)|^35 ≤ (32722473981379/100000000000000 : ℝ)^27
        have hw : |(2112070683/5000000000 : ℝ)|=(2112070683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2480389277/10000000000 : ℝ)|^35 ≤ (4102591977991/25000000000000 : ℝ)^27
        have hw : |(-2480389277/10000000000 : ℝ)|=(2480389277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-998392313/2500000000 : ℝ)*x 0 + (998581243/2500000000 : ℝ)*x 1 + (-2424986129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998392313/2500000000 : ℝ)^35 ≤ (7606520401769/25000000000000 : ℝ)^27 := by
    have hnat : (998392313 : ℕ)^35*25000000000000^27 ≤ 7606520401769^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998392313 2500000000 7606520401769 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (998581243/2500000000 : ℝ)^35 ≤ (15216772722297/50000000000000 : ℝ)^27 := by
    have hnat : (998581243 : ℕ)^35*50000000000000^27 ≤ 15216772722297^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998581243 2500000000 15216772722297 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2424986129/5000000000 : ℝ)^35 ≤ (19570186471393/50000000000000 : ℝ)^27 := by
    have hnat : (2424986129 : ℕ)^35*50000000000000^27 ≤ 19570186471393^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2424986129 5000000000 19570186471393 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-998392313/2500000000 : ℝ), (998581243/2500000000 : ℝ), (-2424986129/5000000000 : ℝ)] ![(7606520401769/25000000000000 : ℝ), (15216772722297/50000000000000 : ℝ), (19570186471393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-998392313/2500000000 : ℝ)|^35 ≤ (7606520401769/25000000000000 : ℝ)^27
        have hw : |(-998392313/2500000000 : ℝ)|=(998392313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(998581243/2500000000 : ℝ)|^35 ≤ (15216772722297/50000000000000 : ℝ)^27
        have hw : |(998581243/2500000000 : ℝ)|=(998581243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2424986129/5000000000 : ℝ)|^35 ≤ (19570186471393/50000000000000 : ℝ)^27
        have hw : |(-2424986129/5000000000 : ℝ)|=(2424986129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5255602489/10000000000 : ℝ)*x 0 + (-1702395751/5000000000 : ℝ)*x 1 + (-2067075719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255602489/10000000000 : ℝ)^35 ≤ (43435416868301/100000000000000 : ℝ)^27 := by
    have hnat : (5255602489 : ℕ)^35*100000000000000^27 ≤ 43435416868301^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255602489 10000000000 43435416868301 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1702395751/5000000000 : ℝ)^35 ≤ (2474290439727/10000000000000 : ℝ)^27 := by
    have hnat : (1702395751 : ℕ)^35*10000000000000^27 ≤ 2474290439727^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1702395751 5000000000 2474290439727 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2067075719/5000000000 : ℝ)^35 ≤ (15910839363051/50000000000000 : ℝ)^27 := by
    have hnat : (2067075719 : ℕ)^35*50000000000000^27 ≤ 15910839363051^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067075719 5000000000 15910839363051 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255602489/10000000000 : ℝ), (-1702395751/5000000000 : ℝ), (-2067075719/5000000000 : ℝ)] ![(43435416868301/100000000000000 : ℝ), (2474290439727/10000000000000 : ℝ), (15910839363051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255602489/10000000000 : ℝ)|^35 ≤ (43435416868301/100000000000000 : ℝ)^27
        have hw : |(5255602489/10000000000 : ℝ)|=(5255602489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1702395751/5000000000 : ℝ)|^35 ≤ (2474290439727/10000000000000 : ℝ)^27
        have hw : |(-1702395751/5000000000 : ℝ)|=(1702395751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2067075719/5000000000 : ℝ)|^35 ≤ (15910839363051/50000000000000 : ℝ)^27
        have hw : |(-2067075719/5000000000 : ℝ)|=(2067075719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (680927653/2000000000 : ℝ)*x 0 + (1051036383/2000000000 : ℝ)*x 1 + (258421729/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (680927653/2000000000 : ℝ)^35 ≤ (24741460869377/100000000000000 : ℝ)^27 := by
    have hnat : (680927653 : ℕ)^35*100000000000000^27 ≤ 24741460869377^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680927653 2000000000 24741460869377 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051036383/2000000000 : ℝ)^35 ≤ (2714431947523/6250000000000 : ℝ)^27 := by
    have hnat : (1051036383 : ℕ)^35*6250000000000^27 ≤ 2714431947523^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051036383 2000000000 2714431947523 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258421729/625000000 : ℝ)^35 ≤ (15913813980899/50000000000000 : ℝ)^27 := by
    have hnat : (258421729 : ℕ)^35*50000000000000^27 ≤ 15913813980899^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258421729 625000000 15913813980899 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(680927653/2000000000 : ℝ), (1051036383/2000000000 : ℝ), (258421729/625000000 : ℝ)] ![(24741460869377/100000000000000 : ℝ), (2714431947523/6250000000000 : ℝ), (15913813980899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(680927653/2000000000 : ℝ)|^35 ≤ (24741460869377/100000000000000 : ℝ)^27
        have hw : |(680927653/2000000000 : ℝ)|=(680927653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051036383/2000000000 : ℝ)|^35 ≤ (2714431947523/6250000000000 : ℝ)^27
        have hw : |(1051036383/2000000000 : ℝ)|=(1051036383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258421729/625000000 : ℝ)|^35 ≤ (15913813980899/50000000000000 : ℝ)^27
        have hw : |(258421729/625000000 : ℝ)|=(258421729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308020_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1151293029/2500000000 : ℝ)*x 0 + (920827917/2000000000 : ℝ)*x 1 + (-3622511209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1151293029/2500000000 : ℝ)^35 ≤ (36598801501857/100000000000000 : ℝ)^27 := by
    have hnat : (1151293029 : ℕ)^35*100000000000000^27 ≤ 36598801501857^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1151293029 2500000000 36598801501857 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (920827917/2000000000 : ℝ)^35 ≤ (7317632925887/20000000000000 : ℝ)^27 := by
    have hnat : (920827917 : ℕ)^35*20000000000000^27 ≤ 7317632925887^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920827917 2000000000 7317632925887 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3622511209/10000000000 : ℝ)^35 ≤ (26813033860163/100000000000000 : ℝ)^27 := by
    have hnat : (3622511209 : ℕ)^35*100000000000000^27 ≤ 26813033860163^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3622511209 10000000000 26813033860163 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1151293029/2500000000 : ℝ), (920827917/2000000000 : ℝ), (-3622511209/10000000000 : ℝ)] ![(36598801501857/100000000000000 : ℝ), (7317632925887/20000000000000 : ℝ), (26813033860163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1151293029/2500000000 : ℝ)|^35 ≤ (36598801501857/100000000000000 : ℝ)^27
        have hw : |(1151293029/2500000000 : ℝ)|=(1151293029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(920827917/2000000000 : ℝ)|^35 ≤ (7317632925887/20000000000000 : ℝ)^27
        have hw : |(920827917/2000000000 : ℝ)|=(920827917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3622511209/10000000000 : ℝ)|^35 ≤ (26813033860163/100000000000000 : ℝ)^27
        have hw : |(-3622511209/10000000000 : ℝ)|=(3622511209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308020 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((3161481321/5000000000 : ℝ)*X 1 0+(-24400949/100000000 : ℝ)*X 1 1+(-955307067/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((610023801/2500000000 : ℝ)*X 2 0+(6322962443/10000000000 : ℝ)*X 2 1+(477653529/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_4 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s0_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-470213347/1250000000 : ℝ)*X 0 0+(2770733427/10000000000 : ℝ)*X 0 1+(-6118913917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3208139261/5000000000 : ℝ)*X 1 0+(-1889561943/10000000000 : ℝ)*X 1 1+(-2086463237/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((972383453/5000000000 : ℝ)*X 2 0+(7218066439/10000000000 : ℝ)*X 2 1+(632684151/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((2018643707/5000000000 : ℝ)*X 0 0+(47929301/80000000 : ℝ)*X 0 1+(-2625712627/10000000000 : ℝ)*X 0 2+(2018643707/5000000000 : ℝ)*X 1 0+(47929301/80000000 : ℝ)*X 1 1+(-2625712627/10000000000 : ℝ)*X 1 2+(2018643707/5000000000 : ℝ)*X 2 0+(47929301/80000000 : ℝ)*X 2 1+(-2625712627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-1877403009/5000000000 : ℝ)*X 0 0+(3168791203/10000000000 : ℝ)*X 0 1+(-1160230513/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((1370207311/2000000000 : ℝ)*X 1 0+(-1367315579/5000000000 : ℝ)*X 1 1+(-290366491/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1143610921/5000000000 : ℝ)*X 2 0+(3211690473/5000000000 : ℝ)*X 2 1+(1918477219/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((76511277/200000000 : ℝ)*X 0 0+(4442460729/10000000000 : ℝ)*X 0 1+(-2287649523/5000000000 : ℝ)*X 0 2+(76511277/200000000 : ℝ)*X 1 0+(4442460729/10000000000 : ℝ)*X 1 1+(-2287649523/5000000000 : ℝ)*X 1 2+(76511277/200000000 : ℝ)*X 2 0+(4442460729/10000000000 : ℝ)*X 2 1+(-2287649523/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-5463391/19531250 : ℝ)*X 0 0+(997847049/2500000000 : ℝ)*X 0 1+(-589607637/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((1812533781/2500000000 : ℝ)*X 1 0+(-2050639573/10000000000 : ℝ)*X 1 1+(-3029203609/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1856538071/10000000000 : ℝ)*X 2 0+(1666070303/2500000000 : ℝ)*X 2 1+(978306017/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((5936595799/10000000000 : ℝ)*X 0 0+(2112070683/5000000000 : ℝ)*X 0 1+(-2480389277/10000000000 : ℝ)*X 0 2+(5936595799/10000000000 : ℝ)*X 1 0+(2112070683/5000000000 : ℝ)*X 1 1+(-2480389277/10000000000 : ℝ)*X 1 2+(5936595799/10000000000 : ℝ)*X 2 0+(2112070683/5000000000 : ℝ)*X 2 1+(-2480389277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((12143/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12143/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (544939868369969622123/39062500000000000000000000 : ℝ) := by norm_num
    linear_combination (31101618927/40000000000 : ℝ)*(base39) + (913906749879/1000000000000 : ℝ)*(base50) + (651085590289/1000000000000 : ℝ)*(base59) + (664283351839/125000000000 : ℝ)*(major_s0_0) + (1948809962917/250000000000 : ℝ)*(major_s0_1) + (664283351839/125000000000 : ℝ)*(major_s0_2) + (305238703/1000000000000 : ℝ)*(sp_s0_1) + (620243259239/250000000000 : ℝ)*(sp_s0_4) + (3618695715391/500000000000 : ℝ)*(sp_s0_7) + (904637269509/125000000000 : ℝ)*(sp_s0_8) + (7237173535033/1000000000000 : ℝ)*(sp_s0_9) + (3391125584491/1000000000000 : ℝ)*(sp_s0_12) + (11963993/1000000000000 : ℝ)*(sp_s0_20) + (114929871/500000000000 : ℝ)*(sp_s0_22) + (3391125584491/1000000000000 : ℝ)*(f.failure) + (289496135791/40000000000 : ℝ)*(f.sum) + (587961753343697/2500000000000000000000000000 : ℝ)*base63 + (27985194467791/78125000000000000000000000 : ℝ)*base64 + (160049909170179/312500000000000000000000000 : ℝ)*base67 + (548717110053497/1250000000000000000000000000 : ℝ)*base68 + (69366568711847/1250000000000000000000000000 : ℝ)*base71 + (8282391688459/78125000000000000000000000 : ℝ)*base72 + (603315089549309/2500000000000000000000000000 : ℝ)*base74 + (424436920303497/1250000000000000000000000000 : ℝ)*base76 + (195223197083657/312500000000000000000000000 : ℝ)*base78 + (30899/100000000000000000 : ℝ)*base86 + (30899/100000000000000000 : ℝ)*base88 + (30899/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4079/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(4079/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (39310052323051440815517/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3073943/250000000000 : ℝ)*(base3) + (841609731347/1000000000000 : ℝ)*(base39) + (30964778689/200000000000 : ℝ)*(base50) + (640647448261/1000000000000 : ℝ)*(base59) + (2160606317457/500000000000 : ℝ)*(major_s0_0) + (2160606317457/500000000000 : ℝ)*(major_s0_1) + (2160606317457/500000000000 : ℝ)*(major_s0_2) + (50154011/250000000000 : ℝ)*(sp_s0_2) + (57063519/200000000000 : ℝ)*(sp_s0_7) + (5884692432457/1000000000000 : ℝ)*(sp_s0_13) + (294249589523/50000000000 : ℝ)*(sp_s0_14) + (5884778878643/1000000000000 : ℝ)*(sp_s0_15) + (2757428238021/1000000000000 : ℝ)*(sp_s0_19) + (436159/250000000000 : ℝ)*(sp_s0_20) + (1378720266897/500000000000 : ℝ)*(f.failure) + (5884979494687/1000000000000 : ℝ)*(f.sum) + (68286901/1250000000000000000000 : ℝ)*base63 + (140382372764409/625000000000000000000000000 : ℝ)*base65 + (75475820548091/625000000000000000000000000 : ℝ)*base66 + (2943740619862889/5000000000000000000000000000 : ℝ)*base69 + (338949262978161/5000000000000000000000000000 : ℝ)*base71 + (388378074951909/625000000000000000000000000 : ℝ)*base72 + (1869599189137111/5000000000000000000000000000 : ℝ)*base75 + (5127969155362889/5000000000000000000000000000 : ℝ)*base77 + (473751531/2500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (4233/50000000000000000 : ℝ)*base86 + (4233/50000000000000000 : ℝ)*base88 + (4233/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-24667/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-24667/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (58700186649903967063059/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (700065684867/500000000000 : ℝ)*(base39) + (150639765553/200000000000 : ℝ)*(base50) + (91286594639/250000000000 : ℝ)*(base59) + (2644658603359/500000000000 : ℝ)*(major_s0_0) + (53968662727/8000000000 : ℝ)*(major_s0_1) + (2644658603359/500000000000 : ℝ)*(major_s0_2) + (1456765634157/1000000000000 : ℝ)*(sp_s0_4) + (24718007/250000000000 : ℝ)*(sp_s0_9) + (2142007/62500000000 : ℝ)*(sp_s0_14) + (119860929/1000000000000 : ℝ)*(sp_s0_15) + (144068513841/20000000000 : ℝ)*(sp_s0_20) + (3601695709969/500000000000 : ℝ)*(sp_s0_21) + (7203206959093/1000000000000 : ℝ)*(sp_s0_22) + (1687602404017/500000000000 : ℝ)*(sp_s0_25) + (1687602404017/500000000000 : ℝ)*(f.failure) + (144068513841/20000000000 : ℝ)*(f.sum) + (902799946218789/10000000000000000000000000000 : ℝ)*base62 + (556265517578717/625000000000000000000000000 : ℝ)*base64 + (10388750929899/10000000000000000000000000 : ℝ)*base67 + (3825734446254457/5000000000000000000000000000 : ℝ)*base68 + (1049198782884193/5000000000000000000000000000 : ℝ)*base70 + (631116851078717/625000000000000000000000000 : ℝ)*base73 + (57523651845679/80000000000000000000000000 : ℝ)*base74 + (3880492770254457/5000000000000000000000000000 : ℝ)*base76 + (703127512644809/1250000000000000000000000000 : ℝ)*base79 + (8087/50000000000000000 : ℝ)*base87 + (8087/50000000000000000 : ℝ)*base89 + (8087/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (12143/50000 : ℝ) ^ (17/4 : ℝ) ≤ (244209728274065723/100000000000000000000 : ℝ) := by
    have hpowers : (12143/50000 : ℝ)^17 ≤ (244209728274065723/100000000000000000000 : ℝ)^4 := by
      have hnat : (12143 : ℕ)^17*100000000000000000000^4 ≤ 244209728274065723^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12143 50000 244209728274065723 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12143/50000 : ℝ)) (X := (244209728274065723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100244209728274065723/100000000000000000000 : ℝ) ≤ (2501435188389111/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100244209728274065723/100000000000000000000 : ℝ)^4 ≤ (2501435188389111/2500000000000000 : ℝ)^17 := by
      have hnat : (100244209728274065723 : ℕ)^4*2500000000000000^17 ≤ 2501435188389111^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100244209728274065723 100000000000000000000 2501435188389111 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501435188389111/2500000000000000 : ℝ)) (X := (100244209728274065723/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50244209728274065723/50000000000000000000 : ℝ) ≤ (10011470822393447/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50244209728274065723/50000000000000000000 : ℝ)^4 ≤ (10011470822393447/10000000000000000 : ℝ)^17 := by
      have hnat : (50244209728274065723 : ℕ)^4*10000000000000000^17 ≤ 10011470822393447^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50244209728274065723 50000000000000000000 10011470822393447 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011470822393447/10000000000000000 : ℝ)) (X := (50244209728274065723/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1435188389111/607150000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(5730068837003/2428600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (12143/50000 : ℝ)) (alpha := (1435188389111/607150000000000 : ℝ)) (beta := (5730068837003/2428600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (12143/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1435188389111/607150000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(5730068837003/2428600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (4079/50000 : ℝ) ^ (17/4 : ℝ) ≤ (2367176981985307/100000000000000000000 : ℝ) := by
    have hpowers : (4079/50000 : ℝ)^17 ≤ (2367176981985307/100000000000000000000 : ℝ)^4 := by
      have hnat : (4079 : ℕ)^17*100000000000000000000^4 ≤ 2367176981985307^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4079 50000 2367176981985307 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4079/50000 : ℝ)) (X := (2367176981985307/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100002367176981985307/100000000000000000000 : ℝ) ≤ (10000055697777813/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100002367176981985307/100000000000000000000 : ℝ)^4 ≤ (10000055697777813/10000000000000000 : ℝ)^17 := by
      have hnat : (100002367176981985307 : ℕ)^4*10000000000000000^17 ≤ 10000055697777813^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100002367176981985307 100000000000000000000 10000055697777813 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000055697777813/10000000000000000 : ℝ)) (X := (100002367176981985307/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50002367176981985307/50000000000000000000 : ℝ) ≤ (10000111394547421/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50002367176981985307/50000000000000000000 : ℝ)^4 ≤ (10000111394547421/10000000000000000 : ℝ)^17 := by
      have hnat : (50002367176981985307 : ℕ)^4*10000000000000000^17 ≤ 10000111394547421^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002367176981985307 50000000000000000000 10000111394547421 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000111394547421/10000000000000000 : ℝ)) (X := (50002367176981985307/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(55697777813/815800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(6962096201/101975000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (4079/50000 : ℝ)) (alpha := (55697777813/815800000000000 : ℝ)) (beta := (6962096201/101975000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (4079/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(55697777813/815800000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(6962096201/101975000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (24667/100000 : ℝ) ^ (17/4 : ℝ) ≤ (65228054799667359/25000000000000000000 : ℝ) := by
    have hpowers : (24667/100000 : ℝ)^17 ≤ (65228054799667359/25000000000000000000 : ℝ)^4 := by
      have hnat : (24667 : ℕ)^17*25000000000000000000^4 ≤ 65228054799667359^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24667 100000 65228054799667359 25000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24667/100000 : ℝ)) (X := (65228054799667359/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25065228054799667359/25000000000000000000 : ℝ) ≤ (10006132996011453/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (25065228054799667359/25000000000000000000 : ℝ)^4 ≤ (10006132996011453/10000000000000000 : ℝ)^17 := by
      have hnat : (25065228054799667359 : ℕ)^4*10000000000000000^17 ≤ 10006132996011453^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25065228054799667359 25000000000000000000 10006132996011453 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006132996011453/10000000000000000 : ℝ)) (X := (25065228054799667359/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12565228054799667359/12500000000000000000 : ℝ) ≤ (10012253799361831/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (12565228054799667359/12500000000000000000 : ℝ)^4 ≤ (10012253799361831/10000000000000000 : ℝ)^17 := by
      have hnat : (12565228054799667359 : ℕ)^4*10000000000000000^17 ≤ 10012253799361831^17*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12565228054799667359 12500000000000000000 10012253799361831 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012253799361831/10000000000000000 : ℝ)) (X := (12565228054799667359/12500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(6132996011453/2466700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(3060401675189/1233350000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (24667/100000 : ℝ)) (alpha := (6132996011453/2466700000000000 : ℝ)) (beta := (3060401675189/1233350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (24667/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(6132996011453/2466700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(3060401675189/1233350000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-998392313/2500000000 : ℝ)*X 0 0+(998581243/2500000000 : ℝ)*X 0 1+(-2424986129/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5255602489/10000000000 : ℝ)*X 1 0+(-1702395751/5000000000 : ℝ)*X 1 1+(-2067075719/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((680927653/2000000000 : ℝ)*X 2 0+(1051036383/2000000000 : ℝ)*X 2 1+(258421729/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1151293029/2500000000 : ℝ)*X 0 0+(920827917/2000000000 : ℝ)*X 0 1+(-3622511209/10000000000 : ℝ)*X 0 2+(1151293029/2500000000 : ℝ)*X 1 0+(920827917/2000000000 : ℝ)*X 1 1+(-3622511209/10000000000 : ℝ)*X 1 2+(1151293029/2500000000 : ℝ)*X 2 0+(920827917/2000000000 : ℝ)*X 2 1+(-3622511209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308020_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-320133/50000 : ℝ) < ((-156711/100000 : ℝ)*P 0+(-156711/100000 : ℝ)*P 1+(-156711/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-320133/50000 : ℝ) < (-15489561815151429121218551122586883/2443577006198000000000000000000000 : ℝ) := by norm_num
    linear_combination (21927/100000000000 : ℝ)*(base5) + (4917/500000000000 : ℝ)*(base11) + (240827/1000000000000 : ℝ)*(base12) + (20476916121/62500000000 : ℝ)*(base39) + (206913711407/1000000000000 : ℝ)*(base49) + (96774606941/250000000000 : ℝ)*(base50) + (6199/125000000000 : ℝ)*(base53) + (258821666929/1000000000000 : ℝ)*(base59) + (156711/100000 : ℝ)*(major_s1_0) + (156711/100000 : ℝ)*(major_s1_1) + (195888743801/125000000000 : ℝ)*(major_s1_2) + (528240620709/250000000000 : ℝ)*(sp_s1_0) + (2112962733497/1000000000000 : ℝ)*(sp_s1_1) + (2112963002359/1000000000000 : ℝ)*(sp_s1_2) + (99999978073/100000000000 : ℝ)*(sp_s1_6) + (2112962783089/1000000000000 : ℝ)*(f.sum) + (540857138410047957/1257708662500000000000000000000 : ℝ)*base63 + (593748697248409/616675000000000000000000000 : ℝ)*base65 + (9919039016809/20395000000000000000000000 : ℝ)*base66 + (385964828743557/1233350000000000000000000000 : ℝ)*base69 + (2155246194941167451/3744142262500000000000000000000 : ℝ)*base71 + (2368987013951/15178750000000000000000000 : ℝ)*base73 + (1647842937323/8158000000000000000000000 : ℝ)*base75 + (1125000748299/24286000000000000000000000 : ℝ)*base77 + (99215258116958691/247656485000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p008_b011 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 20 ≤ c.val) (hhi : c.val < 21)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=20 := by omega
  rcases hc with rfl
  · exact collision_c308020 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 20 ≤ c.val) (hhi : c.val < 21)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p008_b011 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

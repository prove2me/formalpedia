-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p004_b027
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:36:06.730962+00:00
-- url     : https://prove2.me/submissions/cbb57a68-c941-451b-a975-635983a78f82

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304062
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
theorem collision_support_c304064_s0_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3266790361/10000000000 : ℝ)*x 0 + (-1891458669/5000000000 : ℝ)*x 1 + (-5842740767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3266790361/10000000000 : ℝ)^133 ≤ (22918146340149/100000000000000 : ℝ)^101 := by
    have hnat : (3266790361 : ℕ)^133*100000000000000^101 ≤ 22918146340149^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3266790361 10000000000 22918146340149 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1891458669/5000000000 : ℝ)^133 ≤ (27801550813891/100000000000000 : ℝ)^101 := by
    have hnat : (1891458669 : ℕ)^133*100000000000000^101 ≤ 27801550813891^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891458669 5000000000 27801550813891 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5842740767/10000000000 : ℝ)^133 ≤ (9856060567259/20000000000000 : ℝ)^101 := by
    have hnat : (5842740767 : ℕ)^133*20000000000000^101 ≤ 9856060567259^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5842740767 10000000000 9856060567259 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3266790361/10000000000 : ℝ), (-1891458669/5000000000 : ℝ), (-5842740767/10000000000 : ℝ)] ![(22918146340149/100000000000000 : ℝ), (27801550813891/100000000000000 : ℝ), (9856060567259/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3266790361/10000000000 : ℝ)|^133 ≤ (22918146340149/100000000000000 : ℝ)^101
        have hw : |(-3266790361/10000000000 : ℝ)|=(3266790361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1891458669/5000000000 : ℝ)|^133 ≤ (27801550813891/100000000000000 : ℝ)^101
        have hw : |(-1891458669/5000000000 : ℝ)|=(1891458669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5842740767/10000000000 : ℝ)|^133 ≤ (9856060567259/20000000000000 : ℝ)^101
        have hw : |(-5842740767/10000000000 : ℝ)|=(5842740767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304064_s0_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (265227897/400000000 : ℝ)*x 0 + (-3640453987/10000000000 : ℝ)*x 1 + (2410171049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265227897/400000000 : ℝ)^133 ≤ (11642694728419/20000000000000 : ℝ)^101 := by
    have hnat : (265227897 : ℕ)^133*20000000000000^101 ≤ 11642694728419^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265227897 400000000 11642694728419 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3640453987/10000000000 : ℝ)^133 ≤ (6607782325391/25000000000000 : ℝ)^101 := by
    have hnat : (3640453987 : ℕ)^133*25000000000000^101 ≤ 6607782325391^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3640453987 10000000000 6607782325391 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2410171049/10000000000 : ℝ)^133 ≤ (1535539704437/10000000000000 : ℝ)^101 := by
    have hnat : (2410171049 : ℕ)^133*10000000000000^101 ≤ 1535539704437^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2410171049 10000000000 1535539704437 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265227897/400000000 : ℝ), (-3640453987/10000000000 : ℝ), (2410171049/10000000000 : ℝ)] ![(11642694728419/20000000000000 : ℝ), (6607782325391/25000000000000 : ℝ), (1535539704437/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265227897/400000000 : ℝ)|^133 ≤ (11642694728419/20000000000000 : ℝ)^101
        have hw : |(265227897/400000000 : ℝ)|=(265227897/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3640453987/10000000000 : ℝ)|^133 ≤ (6607782325391/25000000000000 : ℝ)^101
        have hw : |(-3640453987/10000000000 : ℝ)|=(3640453987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2410171049/10000000000 : ℝ)|^133 ≤ (1535539704437/10000000000000 : ℝ)^101
        have hw : |(2410171049/10000000000 : ℝ)|=(2410171049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304064_s0_3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1 : ℝ)*x 0 + (0 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1 : ℝ)^133 ≤ (1 : ℝ)^101 := by
    have hnat : (1 : ℕ)^133*1^101 ≤ 1^101*1^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^133 ≤ (0 : ℝ)^101 := by
    have hnat : (0 : ℕ)^133*1^101 ≤ 0^101*1^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^133 ≤ (0 : ℝ)^101 := by
    have hnat : (0 : ℕ)^133*1^101 ≤ 0^101*1^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1 : ℝ)|^133 ≤ (1 : ℝ)^101
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^133 ≤ (0 : ℝ)^101
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^133 ≤ (0 : ℝ)^101
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304064_s0_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-319226711/1000000000 : ℝ)*x 0 + (-3855461173/10000000000 : ℝ)*x 1 + (-730137531/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (319226711/1000000000 : ℝ)^133 ≤ (11116092448411/50000000000000 : ℝ)^101 := by
    have hnat : (319226711 : ℕ)^133*50000000000000^101 ≤ 11116092448411^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319226711 1000000000 11116092448411 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3855461173/10000000000 : ℝ)^133 ≤ (7126433069839/25000000000000 : ℝ)^101 := by
    have hnat : (3855461173 : ℕ)^133*25000000000000^101 ≤ 7126433069839^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3855461173 10000000000 7126433069839 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (730137531/1250000000 : ℝ)^133 ≤ (6157760351441/12500000000000 : ℝ)^101 := by
    have hnat : (730137531 : ℕ)^133*12500000000000^101 ≤ 6157760351441^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730137531 1250000000 6157760351441 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-319226711/1000000000 : ℝ), (-3855461173/10000000000 : ℝ), (-730137531/1250000000 : ℝ)] ![(11116092448411/50000000000000 : ℝ), (7126433069839/25000000000000 : ℝ), (6157760351441/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-319226711/1000000000 : ℝ)|^133 ≤ (11116092448411/50000000000000 : ℝ)^101
        have hw : |(-319226711/1000000000 : ℝ)|=(319226711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3855461173/10000000000 : ℝ)|^133 ≤ (7126433069839/25000000000000 : ℝ)^101
        have hw : |(-3855461173/10000000000 : ℝ)|=(3855461173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-730137531/1250000000 : ℝ)|^133 ≤ (6157760351441/12500000000000 : ℝ)^101
        have hw : |(-730137531/1250000000 : ℝ)|=(730137531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304064_s0_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (681456483/2000000000 : ℝ)*x 0 + (3070419333/5000000000 : ℝ)*x 1 + (-3292671517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (681456483/2000000000 : ℝ)^133 ≤ (378512511369/1562500000000 : ℝ)^101 := by
    have hnat : (681456483 : ℕ)^133*1562500000000^101 ≤ 378512511369^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681456483 2000000000 378512511369 1562500000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3070419333/5000000000 : ℝ)^133 ≤ (52617657467047/100000000000000 : ℝ)^101 := by
    have hnat : (3070419333 : ℕ)^133*100000000000000^101 ≤ 52617657467047^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3070419333 5000000000 52617657467047 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3292671517/10000000000 : ℝ)^133 ≤ (1157877089761/5000000000000 : ℝ)^101 := by
    have hnat : (3292671517 : ℕ)^133*5000000000000^101 ≤ 1157877089761^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3292671517 10000000000 1157877089761 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(681456483/2000000000 : ℝ), (3070419333/5000000000 : ℝ), (-3292671517/10000000000 : ℝ)] ![(378512511369/1562500000000 : ℝ), (52617657467047/100000000000000 : ℝ), (1157877089761/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(681456483/2000000000 : ℝ)|^133 ≤ (378512511369/1562500000000 : ℝ)^101
        have hw : |(681456483/2000000000 : ℝ)|=(681456483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3070419333/5000000000 : ℝ)|^133 ≤ (52617657467047/100000000000000 : ℝ)^101
        have hw : |(3070419333/5000000000 : ℝ)|=(3070419333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3292671517/10000000000 : ℝ)|^133 ≤ (1157877089761/5000000000000 : ℝ)^101
        have hw : |(-3292671517/10000000000 : ℝ)|=(3292671517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304064_s0_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (203267809/312500000 : ℝ)*x 0 + (-3249078913/10000000000 : ℝ)*x 1 + (2999958651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203267809/312500000 : ℝ)^133 ≤ (28379864548209/50000000000000 : ℝ)^101 := by
    have hnat : (203267809 : ℕ)^133*50000000000000^101 ≤ 28379864548209^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203267809 312500000 28379864548209 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3249078913/10000000000 : ℝ)^133 ≤ (22754664721091/100000000000000 : ℝ)^101 := by
    have hnat : (3249078913 : ℕ)^133*100000000000000^101 ≤ 22754664721091^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3249078913 10000000000 22754664721091 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2999958651/10000000000 : ℝ)^133 ≤ (10242803085833/50000000000000 : ℝ)^101 := by
    have hnat : (2999958651 : ℕ)^133*50000000000000^101 ≤ 10242803085833^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2999958651 10000000000 10242803085833 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(203267809/312500000 : ℝ), (-3249078913/10000000000 : ℝ), (2999958651/10000000000 : ℝ)] ![(28379864548209/50000000000000 : ℝ), (22754664721091/100000000000000 : ℝ), (10242803085833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(203267809/312500000 : ℝ)|^133 ≤ (28379864548209/50000000000000 : ℝ)^101
        have hw : |(203267809/312500000 : ℝ)|=(203267809/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3249078913/10000000000 : ℝ)|^133 ≤ (22754664721091/100000000000000 : ℝ)^101
        have hw : |(-3249078913/10000000000 : ℝ)|=(3249078913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2999958651/10000000000 : ℝ)|^133 ≤ (10242803085833/50000000000000 : ℝ)^101
        have hw : |(2999958651/10000000000 : ℝ)|=(2999958651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304064_s0_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-565025083/2000000000 : ℝ)*x 0 + (-297172737/1000000000 : ℝ)*x 1 + (-3428324327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (565025083/2000000000 : ℝ)^133 ≤ (18928190262979/100000000000000 : ℝ)^101 := by
    have hnat : (565025083 : ℕ)^133*100000000000000^101 ≤ 18928190262979^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565025083 2000000000 18928190262979 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297172737/1000000000 : ℝ)^133 ≤ (404642507233/2000000000000 : ℝ)^101 := by
    have hnat : (297172737 : ℕ)^133*2000000000000^101 ≤ 404642507233^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297172737 1000000000 404642507233 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3428324327/5000000000 : ℝ)^133 ≤ (12167936872249/20000000000000 : ℝ)^101 := by
    have hnat : (3428324327 : ℕ)^133*20000000000000^101 ≤ 12167936872249^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3428324327 5000000000 12167936872249 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-565025083/2000000000 : ℝ), (-297172737/1000000000 : ℝ), (-3428324327/5000000000 : ℝ)] ![(18928190262979/100000000000000 : ℝ), (404642507233/2000000000000 : ℝ), (12167936872249/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-565025083/2000000000 : ℝ)|^133 ≤ (18928190262979/100000000000000 : ℝ)^101
        have hw : |(-565025083/2000000000 : ℝ)|=(565025083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-297172737/1000000000 : ℝ)|^133 ≤ (404642507233/2000000000000 : ℝ)^101
        have hw : |(-297172737/1000000000 : ℝ)|=(297172737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3428324327/5000000000 : ℝ)|^133 ≤ (12167936872249/20000000000000 : ℝ)^101
        have hw : |(-3428324327/5000000000 : ℝ)|=(3428324327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304064_s0_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2273760883/5000000000 : ℝ)*x 0 + (5322721241/10000000000 : ℝ)*x 1 + (-763812633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2273760883/5000000000 : ℝ)^133 ≤ (7085605873097/20000000000000 : ℝ)^101 := by
    have hnat : (2273760883 : ℕ)^133*20000000000000^101 ≤ 7085605873097^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273760883 5000000000 7085605873097 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5322721241/10000000000 : ℝ)^133 ≤ (43587725612091/100000000000000 : ℝ)^101 := by
    have hnat : (5322721241 : ℕ)^133*100000000000000^101 ≤ 43587725612091^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5322721241 10000000000 43587725612091 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (763812633/2500000000 : ℝ)^133 ≤ (4196849000921/20000000000000 : ℝ)^101 := by
    have hnat : (763812633 : ℕ)^133*20000000000000^101 ≤ 4196849000921^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      763812633 2500000000 4196849000921 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2273760883/5000000000 : ℝ), (5322721241/10000000000 : ℝ), (-763812633/2500000000 : ℝ)] ![(7085605873097/20000000000000 : ℝ), (43587725612091/100000000000000 : ℝ), (4196849000921/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2273760883/5000000000 : ℝ)|^133 ≤ (7085605873097/20000000000000 : ℝ)^101
        have hw : |(2273760883/5000000000 : ℝ)|=(2273760883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5322721241/10000000000 : ℝ)|^133 ≤ (43587725612091/100000000000000 : ℝ)^101
        have hw : |(5322721241/10000000000 : ℝ)|=(5322721241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-763812633/2500000000 : ℝ)|^133 ≤ (4196849000921/20000000000000 : ℝ)^101
        have hw : |(-763812633/2500000000 : ℝ)|=(763812633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304064_s0_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1896627847/2500000000 : ℝ)*x 0 + (-3010759429/10000000000 : ℝ)*x 1 + (864090371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1896627847/2500000000 : ℝ)^133 ≤ (69508138076727/100000000000000 : ℝ)^101 := by
    have hnat : (1896627847 : ℕ)^133*100000000000000^101 ≤ 69508138076727^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896627847 2500000000 69508138076727 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3010759429/10000000000 : ℝ)^133 ≤ (20582783796977/100000000000000 : ℝ)^101 := by
    have hnat : (3010759429 : ℕ)^133*100000000000000^101 ≤ 20582783796977^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3010759429 10000000000 20582783796977 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864090371/5000000000 : ℝ)^133 ≤ (990907811303/10000000000000 : ℝ)^101 := by
    have hnat : (864090371 : ℕ)^133*10000000000000^101 ≤ 990907811303^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864090371 5000000000 990907811303 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1896627847/2500000000 : ℝ), (-3010759429/10000000000 : ℝ), (864090371/5000000000 : ℝ)] ![(69508138076727/100000000000000 : ℝ), (20582783796977/100000000000000 : ℝ), (990907811303/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1896627847/2500000000 : ℝ)|^133 ≤ (69508138076727/100000000000000 : ℝ)^101
        have hw : |(1896627847/2500000000 : ℝ)|=(1896627847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3010759429/10000000000 : ℝ)|^133 ≤ (20582783796977/100000000000000 : ℝ)^101
        have hw : |(-3010759429/10000000000 : ℝ)|=(3010759429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(864090371/5000000000 : ℝ)|^133 ≤ (990907811303/10000000000000 : ℝ)^101
        have hw : |(864090371/5000000000 : ℝ)|=(864090371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304064_s0_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3732264369/10000000000 : ℝ)*x 0 + (-2279105007/5000000000 : ℝ)*x 1 + (-589299963/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3732264369/10000000000 : ℝ)^133 ≤ (27312389255321/100000000000000 : ℝ)^101 := by
    have hnat : (3732264369 : ℕ)^133*100000000000000^101 ≤ 27312389255321^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3732264369 10000000000 27312389255321 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279105007/5000000000 : ℝ)^133 ≤ (17768860130763/50000000000000 : ℝ)^101 := by
    have hnat : (2279105007 : ℕ)^133*50000000000000^101 ≤ 17768860130763^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279105007 5000000000 17768860130763 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (589299963/1250000000 : ℝ)^133 ≤ (18574945237393/50000000000000 : ℝ)^101 := by
    have hnat : (589299963 : ℕ)^133*50000000000000^101 ≤ 18574945237393^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589299963 1250000000 18574945237393 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3732264369/10000000000 : ℝ), (-2279105007/5000000000 : ℝ), (-589299963/1250000000 : ℝ)] ![(27312389255321/100000000000000 : ℝ), (17768860130763/50000000000000 : ℝ), (18574945237393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3732264369/10000000000 : ℝ)|^133 ≤ (27312389255321/100000000000000 : ℝ)^101
        have hw : |(-3732264369/10000000000 : ℝ)|=(3732264369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2279105007/5000000000 : ℝ)|^133 ≤ (17768860130763/50000000000000 : ℝ)^101
        have hw : |(-2279105007/5000000000 : ℝ)|=(2279105007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-589299963/1250000000 : ℝ)|^133 ≤ (18574945237393/50000000000000 : ℝ)^101
        have hw : |(-589299963/1250000000 : ℝ)|=(589299963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304064_s0_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (290041497/1000000000 : ℝ)*x 0 + (615910163/1000000000 : ℝ)*x 1 + (-3760100233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (290041497/1000000000 : ℝ)^133 ≤ (19595235114449/100000000000000 : ℝ)^101 := by
    have hnat : (290041497 : ℕ)^133*100000000000000^101 ≤ 19595235114449^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290041497 1000000000 19595235114449 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (615910163/1000000000 : ℝ)^133 ≤ (10564764003223/20000000000000 : ℝ)^101 := by
    have hnat : (615910163 : ℕ)^133*20000000000000^101 ≤ 10564764003223^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615910163 1000000000 10564764003223 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3760100233/10000000000 : ℝ)^133 ≤ (2758094485529/10000000000000 : ℝ)^101 := by
    have hnat : (3760100233 : ℕ)^133*10000000000000^101 ≤ 2758094485529^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3760100233 10000000000 2758094485529 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(290041497/1000000000 : ℝ), (615910163/1000000000 : ℝ), (-3760100233/10000000000 : ℝ)] ![(19595235114449/100000000000000 : ℝ), (10564764003223/20000000000000 : ℝ), (2758094485529/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(290041497/1000000000 : ℝ)|^133 ≤ (19595235114449/100000000000000 : ℝ)^101
        have hw : |(290041497/1000000000 : ℝ)|=(290041497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(615910163/1000000000 : ℝ)|^133 ≤ (10564764003223/20000000000000 : ℝ)^101
        have hw : |(615910163/1000000000 : ℝ)|=(615910163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3760100233/10000000000 : ℝ)|^133 ≤ (2758094485529/10000000000000 : ℝ)^101
        have hw : |(-3760100233/10000000000 : ℝ)|=(3760100233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304064_s0_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1916217349/2500000000 : ℝ)*x 0 + (-1439799047/5000000000 : ℝ)*x 1 + (1757979997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1916217349/2500000000 : ℝ)^133 ≤ (70455063008677/100000000000000 : ℝ)^101 := by
    have hnat : (1916217349 : ℕ)^133*100000000000000^101 ≤ 70455063008677^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916217349 2500000000 70455063008677 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1439799047/5000000000 : ℝ)^133 ≤ (19410248081651/100000000000000 : ℝ)^101 := by
    have hnat : (1439799047 : ℕ)^133*100000000000000^101 ≤ 19410248081651^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1439799047 5000000000 19410248081651 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1757979997/10000000000 : ℝ)^133 ≤ (5067344446677/50000000000000 : ℝ)^101 := by
    have hnat : (1757979997 : ℕ)^133*50000000000000^101 ≤ 5067344446677^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1757979997 10000000000 5067344446677 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1916217349/2500000000 : ℝ), (-1439799047/5000000000 : ℝ), (1757979997/10000000000 : ℝ)] ![(70455063008677/100000000000000 : ℝ), (19410248081651/100000000000000 : ℝ), (5067344446677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1916217349/2500000000 : ℝ)|^133 ≤ (70455063008677/100000000000000 : ℝ)^101
        have hw : |(1916217349/2500000000 : ℝ)|=(1916217349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1439799047/5000000000 : ℝ)|^133 ≤ (19410248081651/100000000000000 : ℝ)^101
        have hw : |(-1439799047/5000000000 : ℝ)|=(1439799047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1757979997/10000000000 : ℝ)|^133 ≤ (5067344446677/50000000000000 : ℝ)^101
        have hw : |(1757979997/10000000000 : ℝ)|=(1757979997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304064_s1_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3704662217/10000000000 : ℝ)*x 0 + (-3704662277/10000000000 : ℝ)*x 1 + (-173012823/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3704662217/10000000000 : ℝ)^133 ≤ (13523357173731/50000000000000 : ℝ)^101 := by
    have hnat : (3704662217 : ℕ)^133*50000000000000^101 ≤ 13523357173731^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3704662217 10000000000 13523357173731 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3704662277/10000000000 : ℝ)^133 ≤ (27046714924291/100000000000000 : ℝ)^101 := by
    have hnat : (3704662277 : ℕ)^133*100000000000000^101 ≤ 27046714924291^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3704662277 10000000000 27046714924291 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173012823/312500000 : ℝ)^133 ≤ (5738321339757/12500000000000 : ℝ)^101 := by
    have hnat : (173012823 : ℕ)^133*12500000000000^101 ≤ 5738321339757^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173012823 312500000 5738321339757 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3704662217/10000000000 : ℝ), (-3704662277/10000000000 : ℝ), (-173012823/312500000 : ℝ)] ![(13523357173731/50000000000000 : ℝ), (27046714924291/100000000000000 : ℝ), (5738321339757/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3704662217/10000000000 : ℝ)|^133 ≤ (13523357173731/50000000000000 : ℝ)^101
        have hw : |(-3704662217/10000000000 : ℝ)|=(3704662217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3704662277/10000000000 : ℝ)|^133 ≤ (27046714924291/100000000000000 : ℝ)^101
        have hw : |(-3704662277/10000000000 : ℝ)|=(3704662277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173012823/312500000 : ℝ)|^133 ≤ (5738321339757/12500000000000 : ℝ)^101
        have hw : |(-173012823/312500000 : ℝ)|=(173012823/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304064_s1_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1195888319/2500000000 : ℝ)*x 0 + (2391776677/5000000000 : ℝ)*x 1 + (-3411224611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1195888319/2500000000 : ℝ)^133 ≤ (37869141838863/100000000000000 : ℝ)^101 := by
    have hnat : (1195888319 : ℕ)^133*100000000000000^101 ≤ 37869141838863^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195888319 2500000000 37869141838863 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2391776677/5000000000 : ℝ)^133 ≤ (37869142651993/100000000000000 : ℝ)^101 := by
    have hnat : (2391776677 : ℕ)^133*100000000000000^101 ≤ 37869142651993^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2391776677 5000000000 37869142651993 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3411224611/10000000000 : ℝ)^133 ≤ (12130857747379/50000000000000 : ℝ)^101 := by
    have hnat : (3411224611 : ℕ)^133*50000000000000^101 ≤ 12130857747379^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3411224611 10000000000 12130857747379 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1195888319/2500000000 : ℝ), (2391776677/5000000000 : ℝ), (-3411224611/10000000000 : ℝ)] ![(37869141838863/100000000000000 : ℝ), (37869142651993/100000000000000 : ℝ), (12130857747379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1195888319/2500000000 : ℝ)|^133 ≤ (37869141838863/100000000000000 : ℝ)^101
        have hw : |(1195888319/2500000000 : ℝ)|=(1195888319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2391776677/5000000000 : ℝ)|^133 ≤ (37869142651993/100000000000000 : ℝ)^101
        have hw : |(2391776677/5000000000 : ℝ)|=(2391776677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3411224611/10000000000 : ℝ)|^133 ≤ (12130857747379/50000000000000 : ℝ)^101
        have hw : |(-3411224611/10000000000 : ℝ)|=(3411224611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304064_s1_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1195888319/2500000000 : ℝ)*x 0 + (-2391776677/5000000000 : ℝ)*x 1 + (3411224611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1195888319/2500000000 : ℝ)^133 ≤ (37869141838863/100000000000000 : ℝ)^101 := by
    have hnat : (1195888319 : ℕ)^133*100000000000000^101 ≤ 37869141838863^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195888319 2500000000 37869141838863 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2391776677/5000000000 : ℝ)^133 ≤ (37869142651993/100000000000000 : ℝ)^101 := by
    have hnat : (2391776677 : ℕ)^133*100000000000000^101 ≤ 37869142651993^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2391776677 5000000000 37869142651993 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3411224611/10000000000 : ℝ)^133 ≤ (12130857747379/50000000000000 : ℝ)^101 := by
    have hnat : (3411224611 : ℕ)^133*50000000000000^101 ≤ 12130857747379^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3411224611 10000000000 12130857747379 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1195888319/2500000000 : ℝ), (-2391776677/5000000000 : ℝ), (3411224611/10000000000 : ℝ)] ![(37869141838863/100000000000000 : ℝ), (37869142651993/100000000000000 : ℝ), (12130857747379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1195888319/2500000000 : ℝ)|^133 ≤ (37869141838863/100000000000000 : ℝ)^101
        have hw : |(1195888319/2500000000 : ℝ)|=(1195888319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2391776677/5000000000 : ℝ)|^133 ≤ (37869142651993/100000000000000 : ℝ)^101
        have hw : |(-2391776677/5000000000 : ℝ)|=(2391776677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3411224611/10000000000 : ℝ)|^133 ≤ (12130857747379/50000000000000 : ℝ)^101
        have hw : |(3411224611/10000000000 : ℝ)|=(3411224611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304064_s1_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3704662217/10000000000 : ℝ)*x 0 + (-3704662277/10000000000 : ℝ)*x 1 + (-173012823/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3704662217/10000000000 : ℝ)^133 ≤ (13523357173731/50000000000000 : ℝ)^101 := by
    have hnat : (3704662217 : ℕ)^133*50000000000000^101 ≤ 13523357173731^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3704662217 10000000000 13523357173731 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3704662277/10000000000 : ℝ)^133 ≤ (27046714924291/100000000000000 : ℝ)^101 := by
    have hnat : (3704662277 : ℕ)^133*100000000000000^101 ≤ 27046714924291^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3704662277 10000000000 27046714924291 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173012823/312500000 : ℝ)^133 ≤ (5738321339757/12500000000000 : ℝ)^101 := by
    have hnat : (173012823 : ℕ)^133*12500000000000^101 ≤ 5738321339757^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173012823 312500000 5738321339757 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3704662217/10000000000 : ℝ), (-3704662277/10000000000 : ℝ), (-173012823/312500000 : ℝ)] ![(13523357173731/50000000000000 : ℝ), (27046714924291/100000000000000 : ℝ), (5738321339757/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3704662217/10000000000 : ℝ)|^133 ≤ (13523357173731/50000000000000 : ℝ)^101
        have hw : |(3704662217/10000000000 : ℝ)|=(3704662217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3704662277/10000000000 : ℝ)|^133 ≤ (27046714924291/100000000000000 : ℝ)^101
        have hw : |(-3704662277/10000000000 : ℝ)|=(3704662277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173012823/312500000 : ℝ)|^133 ≤ (5738321339757/12500000000000 : ℝ)^101
        have hw : |(-173012823/312500000 : ℝ)|=(173012823/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304064 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3266790361/10000000000 : ℝ)*X 0 0+(-1891458669/5000000000 : ℝ)*X 0 1+(-5842740767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((265227897/400000000 : ℝ)*X 2 0+(-3640453987/10000000000 : ℝ)*X 2 1+(2410171049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-319226711/1000000000 : ℝ)*X 0 0+(-3855461173/10000000000 : ℝ)*X 0 1+(-730137531/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((681456483/2000000000 : ℝ)*X 1 0+(3070419333/5000000000 : ℝ)*X 1 1+(-3292671517/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((203267809/312500000 : ℝ)*X 2 0+(-3249078913/10000000000 : ℝ)*X 2 1+(2999958651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-565025083/2000000000 : ℝ)*X 0 0+(-297172737/1000000000 : ℝ)*X 0 1+(-3428324327/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2273760883/5000000000 : ℝ)*X 1 0+(5322721241/10000000000 : ℝ)*X 1 1+(-763812633/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1896627847/2500000000 : ℝ)*X 2 0+(-3010759429/10000000000 : ℝ)*X 2 1+(864090371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-3732264369/10000000000 : ℝ)*X 0 0+(-2279105007/5000000000 : ℝ)*X 0 1+(-589299963/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((290041497/1000000000 : ℝ)*X 1 0+(615910163/1000000000 : ℝ)*X 1 1+(-3760100233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1916217349/2500000000 : ℝ)*X 2 0+(-1439799047/5000000000 : ℝ)*X 2 1+(1757979997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((8421/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8421/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5889482032870302957099/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (459863695581/250000000000 : ℝ)*(base1) + (171000916059/1000000000000 : ℝ)*(base7) + (279081/40000000000 : ℝ)*(base22) + (1139514092219/1000000000000 : ℝ)*(base39) + (863821016639/1000000000000 : ℝ)*(base60) + (2530577348041/1000000000000 : ℝ)*(major_s0_0) + (2530577348041/1000000000000 : ℝ)*(major_s0_1) + (2530577348041/1000000000000 : ℝ)*(major_s0_2) + (3362741/1000000000000 : ℝ)*(sp_s0_2) + (1281273769171/250000000000 : ℝ)*(sp_s0_7) + (3285518847339/1000000000000 : ℝ)*(sp_s0_8) + (328562993247/100000000000 : ℝ)*(sp_s0_9) + (60712449/500000000000 : ℝ)*(sp_s0_21) + (208556733283/125000000000 : ℝ)*(f.failure) + (3285640272237/1000000000000 : ℝ)*(f.sum) + (16513193404809983647/2000000000000000000000000000 : ℝ)*base63 + (1008418202910999933/100000000000000000000000000 : ℝ)*base65 + (20858799335534784987/2000000000000000000000000000 : ℝ)*base67 + (74218659384987/2000000000000000000000000000 : ℝ)*base69 + (683729442413673/2000000000000000000000000000 : ℝ)*base71 + (61423562709933/100000000000000000000000000 : ℝ)*base72 + (92755954829933/100000000000000000000000000 : ℝ)*base75 + (1546711312984987/2000000000000000000000000000 : ℝ)*base76 + (124244801013673/2000000000000000000000000000 : ℝ)*base78 + (22123/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base84 + (3331/3125000000000000 : ℝ)*base86 + (3331/3125000000000000 : ℝ)*base88 + (3331/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-77563/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-77563/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10018155183220813121817/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1807283495743/500000000000 : ℝ)*(base1) + (1112818138831/1000000000000 : ℝ)*(base7) + (598417782647/200000000000 : ℝ)*(base39) + (1002662643563/1000000000000 : ℝ)*(base40) + (110358102451/100000000000 : ℝ)*(base60) + (3794452519799/1000000000000 : ℝ)*(major_s0_0) + (3794452519799/1000000000000 : ℝ)*(major_s0_1) + (3794452519799/1000000000000 : ℝ)*(major_s0_2) + (24496491/1000000000000 : ℝ)*(sp_s0_0) + (32000967/500000000000 : ℝ)*(sp_s0_2) + (2001248322593/250000000000 : ℝ)*(sp_s0_14) + (4390450795377/1000000000000 : ℝ)*(sp_s0_15) + (137181225507/31250000000 : ℝ)*(sp_s0_16) + (587577219/1000000000000 : ℝ)*(sp_s0_22) + (500349770531/200000000000 : ℝ)*(f.failure) + (4390450795377/1000000000000 : ℝ)*(f.sum) + (481166306862367/2000000000000000000000000000 : ℝ)*base62 + (28204161077987/100000000000000000000000000 : ℝ)*base65 + (28464958022107/2000000000000000000000000000 : ℝ)*base66 + (776221691422107/2000000000000000000000000000 : ℝ)*base68 + (785080665581847/2000000000000000000000000000 : ℝ)*base71 + (20640829457987/100000000000000000000000000 : ℝ)*base72 + (20525950762013/100000000000000000000000000 : ℝ)*base74 + (779088043022107/2000000000000000000000000000 : ℝ)*base77 + (708072300381847/2000000000000000000000000000 : ℝ)*base78 + (271/2500000000000000 : ℝ)*base86 + (271/2500000000000000 : ℝ)*base88 + (271/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-56507/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-56507/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2700844186468341531093/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1483120896497/500000000000 : ℝ)*(base1) + (953143471567/1000000000000 : ℝ)*(base7) + (115773712209/1000000000000 : ℝ)*(base40) + (480403070343/1000000000000 : ℝ)*(base60) + (2637734662963/250000000000 : ℝ)*(major_s0_0) + (1526653243037/500000000000 : ℝ)*(major_s0_1) + (1526653243037/500000000000 : ℝ)*(major_s0_2) + (7497632165777/1000000000000 : ℝ)*(sp_s0_3) + (4941/320000000 : ℝ)*(sp_s0_7) + (26695183/500000000000 : ℝ)*(sp_s0_8) + (82551/320000000 : ℝ)*(sp_s0_16) + (1615750717179/250000000000 : ℝ)*(sp_s0_20) + (3496723125981/1000000000000 : ℝ)*(sp_s0_21) + (437064818059/125000000000 : ℝ)*(sp_s0_22) + (2013098321427/1000000000000 : ℝ)*(f.failure) + (3496776516347/1000000000000 : ℝ)*(f.sum) + (53975224587221/1000000000000000000000000000 : ℝ)*base62 + (39952813942281/50000000000000000000000000 : ℝ)*base65 + (516367122467159/1000000000000000000000000000 : ℝ)*base67 + (509508670067159/1000000000000000000000000000 : ℝ)*base69 + (359685589197969/500000000000000000000000000 : ℝ)*base71 + (1885606006781/25000000000000000000000000 : ℝ)*base73 + (42243481137281/50000000000000000000000000 : ℝ)*base75 + (293583033675159/500000000000000000000000000 : ℝ)*base77 + (120053806561601/1000000000000000000000000000 : ℝ)*base78 + (3007/12500000000000000 : ℝ)*base86 + (9493/12500000000000000 : ℝ)*base89 + (9493/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (8421/100000 : ℝ) ^ (33/8 : ℝ) ≤ (3690839227855931/100000000000000000000 : ℝ) := by
    have hpowers : (8421/100000 : ℝ)^33 ≤ (3690839227855931/100000000000000000000 : ℝ)^8 := by
      have hnat : (8421 : ℕ)^33*100000000000000000000^8 ≤ 3690839227855931^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8421 100000 3690839227855931 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8421/100000 : ℝ)) (X := (3690839227855931/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100003690839227855931/100000000000000000000 : ℝ) ≤ (20000178947279/20000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (100003690839227855931/100000000000000000000 : ℝ)^8 ≤ (20000178947279/20000000000000 : ℝ)^33 := by
      have hnat : (100003690839227855931 : ℕ)^8*20000000000000^33 ≤ 20000178947279^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100003690839227855931 100000000000000000000 20000178947279 20000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20000178947279/20000000000000 : ℝ)) (X := (100003690839227855931/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50003690839227855931/50000000000000000000 : ℝ) ≤ (2500044736194341/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50003690839227855931/50000000000000000000 : ℝ)^8 ≤ (2500044736194341/2500000000000000 : ℝ)^33 := by
      have hnat : (50003690839227855931 : ℕ)^8*2500000000000000^33 ≤ 2500044736194341^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003690839227855931 50000000000000000000 2500044736194341 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500044736194341/2500000000000000 : ℝ)) (X := (50003690839227855931/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(8521299/80200000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(11183892233/105262500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (8421/100000 : ℝ)) (alpha := (8521299/80200000000 : ℝ)) (beta := (11183892233/105262500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (8421/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(8521299/80200000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(11183892233/105262500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (77563/100000 : ℝ) ^ (33/8 : ℝ) ≤ (3506107426877061003/10000000000000000000 : ℝ) := by
    have hpowers : (77563/100000 : ℝ)^33 ≤ (3506107426877061003/10000000000000000000 : ℝ)^8 := by
      have hnat : (77563 : ℕ)^33*10000000000000000000^8 ≤ 3506107426877061003^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77563 100000 3506107426877061003 10000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (77563/100000 : ℝ)) (X := (3506107426877061003/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (13506107426877061003/10000000000000000000 : ℝ) ≤ (10755823941526217/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (13506107426877061003/10000000000000000000 : ℝ)^8 ≤ (10755823941526217/10000000000000000 : ℝ)^33 := by
      have hnat : (13506107426877061003 : ℕ)^8*10000000000000000^33 ≤ 10755823941526217^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13506107426877061003 10000000000000000000 10755823941526217 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10755823941526217/10000000000000000 : ℝ)) (X := (13506107426877061003/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (8506107426877061003/5000000000000000000 : ℝ) ≤ (11374754350927997/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (8506107426877061003/5000000000000000000 : ℝ)^8 ≤ (11374754350927997/10000000000000000 : ℝ)^33 := by
      have hnat : (8506107426877061003 : ℕ)^8*10000000000000000^33 ≤ 11374754350927997^33*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8506107426877061003 5000000000000000000 11374754350927997 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11374754350927997/10000000000000000 : ℝ)) (X := (8506107426877061003/5000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(755823941526217/7756300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(30946520470089/387815000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (77563/100000 : ℝ)) (alpha := (755823941526217/7756300000000000 : ℝ)) (beta := (30946520470089/387815000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (77563/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(755823941526217/7756300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(30946520470089/387815000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (56507/100000 : ℝ) ^ (33/8 : ℝ) ≤ (4746700052848521749/50000000000000000000 : ℝ) := by
    have hpowers : (56507/100000 : ℝ)^33 ≤ (4746700052848521749/50000000000000000000 : ℝ)^8 := by
      have hnat : (56507 : ℕ)^33*50000000000000000000^8 ≤ 4746700052848521749^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56507 100000 4746700052848521749 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (56507/100000 : ℝ)) (X := (4746700052848521749/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (54746700052848521749/50000000000000000000 : ℝ) ≤ (2555574821871491/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (54746700052848521749/50000000000000000000 : ℝ)^8 ≤ (2555574821871491/2500000000000000 : ℝ)^33 := by
      have hnat : (54746700052848521749 : ℕ)^8*2500000000000000^33 ≤ 2555574821871491^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54746700052848521749 50000000000000000000 2555574821871491 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2555574821871491/2500000000000000 : ℝ)) (X := (54746700052848521749/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (29746700052848521749/25000000000000000000 : ℝ) ≤ (2607610640816859/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (29746700052848521749/25000000000000000000 : ℝ)^8 ≤ (2607610640816859/2500000000000000 : ℝ)^33 := by
      have hnat : (29746700052848521749 : ℕ)^8*2500000000000000^33 ≤ 2607610640816859^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29746700052848521749 25000000000000000000 2607610640816859 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2607610640816859/2500000000000000 : ℝ)) (X := (29746700052848521749/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(55574821871491/1412675000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(6504477368171/176584375000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (56507/100000 : ℝ)) (alpha := (55574821871491/1412675000000000 : ℝ)) (beta := (6504477368171/176584375000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (56507/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(55574821871491/1412675000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(6504477368171/176584375000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3704662217/10000000000 : ℝ)*X 0 0+(-3704662277/10000000000 : ℝ)*X 0 1+(-173012823/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1195888319/2500000000 : ℝ)*X 1 0+(2391776677/5000000000 : ℝ)*X 1 1+(-3411224611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1195888319/2500000000 : ℝ)*X 2 0+(-2391776677/5000000000 : ℝ)*X 2 1+(3411224611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3704662217/10000000000 : ℝ)*X 0 0+(-3704662277/10000000000 : ℝ)*X 0 1+(-173012823/312500000 : ℝ)*X 0 2+(3704662217/10000000000 : ℝ)*X 1 0+(-3704662277/10000000000 : ℝ)*X 1 1+(-173012823/312500000 : ℝ)*X 1 2+(3704662217/10000000000 : ℝ)*X 2 0+(-3704662277/10000000000 : ℝ)*X 2 1+(-173012823/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304064_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-38127/6250 : ℝ) < ((-18959/12500 : ℝ)*P 0+(-18959/12500 : ℝ)*P 1+(-18959/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-38127/6250 : ℝ) < (-3702785926521262574550673329835506481/615133340094350000000000000000000000 : ℝ) := by norm_num
    linear_combination (224052288491/250000000000 : ℝ)*(base1) + (3599/250000000000 : ℝ)*(base5) + (9243/250000000000 : ℝ)*(base21) + (64646287793/50000000000 : ℝ)*(base39) + (518290281247/1000000000000 : ℝ)*(base40) + (15896860679/40000000000 : ℝ)*(base49) + (229391732017/500000000000 : ℝ)*(base60) + (18959/12500 : ℝ)*(major_s1_0) + (189590000773/125000000000 : ℝ)*(major_s1_1) + (18959/12500 : ℝ)*(major_s1_2) + (2902704142357/1000000000000 : ℝ)*(sp_s1_0) + (2006494994577/1000000000000 : ℝ)*(sp_s1_1) + (1003247482909/500000000000 : ℝ)*(sp_s1_2) + (103790837823/1000000000000 : ℝ)*(sp_s1_6) + (2006494988393/1000000000000 : ℝ)*(f.sum) + (12165543484273080467/21914262205000000000000000000000 : ℝ)*base63 + (10572118811049/28253500000000000000000000 : ℝ)*base64 + (449956058452941/969537500000000000000000000 : ℝ)*base66 + (223901011345599/565070000000000000000000000 : ℝ)*base69 + (37040383977427109/226593070000000000000000000000 : ℝ)*base70 + (1986908393417/3368400000000000000000000 : ℝ)*base72 + (462795573755131/775630000000000000000000000 : ℝ)*base75 + (258764773743/4010000000000000000000000 : ℝ)*base77 + (10688976855179735447/16328950575000000000000000000000 : ℝ)*base78 + (773/125000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (773/125000000000 : ℝ)*base88 + (6183/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c304065_s0_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167216527/5000000000 : ℝ)*x 0 + (-2481129019/5000000000 : ℝ)*x 1 + (924914267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167216527/5000000000 : ℝ)^133 ≤ (2078648069629/6250000000000 : ℝ)^101 := by
    have hnat : (2167216527 : ℕ)^133*6250000000000^101 ≤ 2078648069629^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167216527 5000000000 2078648069629 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2481129019/5000000000 : ℝ)^133 ≤ (9935756210487/25000000000000 : ℝ)^101 := by
    have hnat : (2481129019 : ℕ)^133*25000000000000^101 ≤ 9935756210487^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2481129019 5000000000 9935756210487 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (924914267/2500000000 : ℝ)^133 ≤ (26998606027909/100000000000000 : ℝ)^101 := by
    have hnat : (924914267 : ℕ)^133*100000000000000^101 ≤ 26998606027909^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924914267 2500000000 26998606027909 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167216527/5000000000 : ℝ), (-2481129019/5000000000 : ℝ), (924914267/2500000000 : ℝ)] ![(2078648069629/6250000000000 : ℝ), (9935756210487/25000000000000 : ℝ), (26998606027909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167216527/5000000000 : ℝ)|^133 ≤ (2078648069629/6250000000000 : ℝ)^101
        have hw : |(-2167216527/5000000000 : ℝ)|=(2167216527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2481129019/5000000000 : ℝ)|^133 ≤ (9935756210487/25000000000000 : ℝ)^101
        have hw : |(-2481129019/5000000000 : ℝ)|=(2481129019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(924914267/2500000000 : ℝ)|^133 ≤ (26998606027909/100000000000000 : ℝ)^101
        have hw : |(924914267/2500000000 : ℝ)|=(924914267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304065_s0_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3688443101/10000000000 : ℝ)*x 0 + (850420457/2000000000 : ℝ)*x 1 + (2525429873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3688443101/10000000000 : ℝ)^133 ≤ (13445447436511/50000000000000 : ℝ)^101 := by
    have hnat : (3688443101 : ℕ)^133*50000000000000^101 ≤ 13445447436511^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688443101 10000000000 13445447436511 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (850420457/2000000000 : ℝ)^133 ≤ (2026812651131/6250000000000 : ℝ)^101 := by
    have hnat : (850420457 : ℕ)^133*6250000000000^101 ≤ 2026812651131^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850420457 2000000000 2026812651131 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2525429873/5000000000 : ℝ)^133 ≤ (4068010269611/10000000000000 : ℝ)^101 := by
    have hnat : (2525429873 : ℕ)^133*10000000000000^101 ≤ 4068010269611^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2525429873 5000000000 4068010269611 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3688443101/10000000000 : ℝ), (850420457/2000000000 : ℝ), (2525429873/5000000000 : ℝ)] ![(13445447436511/50000000000000 : ℝ), (2026812651131/6250000000000 : ℝ), (4068010269611/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3688443101/10000000000 : ℝ)|^133 ≤ (13445447436511/50000000000000 : ℝ)^101
        have hw : |(3688443101/10000000000 : ℝ)|=(3688443101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(850420457/2000000000 : ℝ)|^133 ≤ (2026812651131/6250000000000 : ℝ)^101
        have hw : |(850420457/2000000000 : ℝ)|=(850420457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2525429873/5000000000 : ℝ)|^133 ≤ (4068010269611/10000000000000 : ℝ)^101
        have hw : |(2525429873/5000000000 : ℝ)|=(2525429873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304065_s0_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5074038481/10000000000 : ℝ)*x 0 + (-1789792831/5000000000 : ℝ)*x 1 + (-4330947577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5074038481/10000000000 : ℝ)^133 ≤ (20463056135089/50000000000000 : ℝ)^101 := by
    have hnat : (5074038481 : ℕ)^133*50000000000000^101 ≤ 20463056135089^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074038481 10000000000 20463056135089 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1789792831/5000000000 : ℝ)^133 ≤ (25850731816263/100000000000000 : ℝ)^101 := by
    have hnat : (1789792831 : ℕ)^133*100000000000000^101 ≤ 25850731816263^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789792831 5000000000 25850731816263 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4330947577/10000000000 : ℝ)^133 ≤ (16611577944591/50000000000000 : ℝ)^101 := by
    have hnat : (4330947577 : ℕ)^133*50000000000000^101 ≤ 16611577944591^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330947577 10000000000 16611577944591 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5074038481/10000000000 : ℝ), (-1789792831/5000000000 : ℝ), (-4330947577/10000000000 : ℝ)] ![(20463056135089/50000000000000 : ℝ), (25850731816263/100000000000000 : ℝ), (16611577944591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5074038481/10000000000 : ℝ)|^133 ≤ (20463056135089/50000000000000 : ℝ)^101
        have hw : |(5074038481/10000000000 : ℝ)|=(5074038481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1789792831/5000000000 : ℝ)|^133 ≤ (25850731816263/100000000000000 : ℝ)^101
        have hw : |(-1789792831/5000000000 : ℝ)|=(1789792831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4330947577/10000000000 : ℝ)|^133 ≤ (16611577944591/50000000000000 : ℝ)^101
        have hw : |(-4330947577/10000000000 : ℝ)|=(4330947577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304065 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2167216527/5000000000 : ℝ)*X 0 0+(-2481129019/5000000000 : ℝ)*X 0 1+(924914267/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304065_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3688443101/10000000000 : ℝ)*X 1 0+(850420457/2000000000 : ℝ)*X 1 1+(2525429873/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304065_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5074038481/10000000000 : ℝ)*X 2 0+(-1789792831/5000000000 : ℝ)*X 2 1+(-4330947577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304065_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-38127/6250 : ℝ) < ((-18959/12500 : ℝ)*P 0+(-18959/12500 : ℝ)*P 1+(-18959/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-38127/6250 : ℝ) < (-3002457531392715709698600741/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (666679421407/1000000000000 : ℝ)*(base1) + (83330121429/250000000000 : ℝ)*(base3) + (3277/40000000000 : ℝ)*(base33) + (92877/1000000000000 : ℝ)*(base34) + (522688832011/1000000000000 : ℝ)*(base40) + (567763418543/1000000000000 : ℝ)*(base49) + (252006328561/1000000000000 : ℝ)*(base50) + (252621/1000000000000 : ℝ)*(base59) + (75591187803/200000000000 : ℝ)*(base60) + (758359912599/500000000000 : ℝ)*(major_s0_0) + (18959/12500 : ℝ)*(major_s0_1) + (18959/12500 : ℝ)*(major_s0_2) + (2668317682789/1000000000000 : ℝ)*(sp_s0_0) + (46699175161/20000000000 : ℝ)*(sp_s0_1) + (1000819136167/500000000000 : ℝ)*(sp_s0_2) + (2001638354259/1000000000000 : ℝ)*(f.sum) + (754675597/5000000000000000000000 : ℝ)*base62 + (189021991/5000000000000000000000 : ℝ)*base65 + (581950637/2500000000000000000000 : ℝ)*base67 + (140342157/200000000000000000000 : ℝ)*base68 + (529305327312507/1000000000000000000000000000 : ℝ)*base71 + (18500956024387/50000000000000000000000000 : ℝ)*base72 + (972574327/5000000000000000000000 : ℝ)*base74 + (456933663112507/1000000000000000000000000000 : ℝ)*base77 + (6823479934387/50000000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p004_b027 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (c : Fin 88) (hlo : 62 ≤ c.val) (hhi : c.val < 66)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=62 ∨ c=63 ∨ c=64 ∨ c=65 := by omega
  rcases hc with rfl|rfl|rfl|rfl
  · exact collision_c304062 p hpa (by linarith only [hpb]) X hX
  · exact (hn63 rfl).elim
  · exact collision_c304064 p hpa (by linarith only [hpb]) X hX
  · exact collision_c304065 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (c : Fin 88) (hlo : 62 ≤ c.val) (hhi : c.val < 66)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p004_b027 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b025
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:26:07.930524+00:00
-- url     : https://prove2.me/submissions/965d35a4-8d89-4704-851f-523fba471789

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301045
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
theorem collision_support_c301044_s0_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-878631849/10000000000 : ℝ)*x 0 + (-1362097951/2000000000 : ℝ)*x 1 + (-2312352787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (878631849/10000000000 : ℝ)^65 ≤ (1985626590547/50000000000000 : ℝ)^49 := by
    have hnat : (878631849 : ℕ)^65*50000000000000^49 ≤ 1985626590547^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878631849 10000000000 1985626590547 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362097951/2000000000 : ℝ)^65 ≤ (60076685824891/100000000000000 : ℝ)^49 := by
    have hnat : (1362097951 : ℕ)^65*100000000000000^49 ≤ 60076685824891^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362097951 2000000000 60076685824891 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2312352787/5000000000 : ℝ)^65 ≤ (8988015245523/25000000000000 : ℝ)^49 := by
    have hnat : (2312352787 : ℕ)^65*25000000000000^49 ≤ 8988015245523^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312352787 5000000000 8988015245523 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-878631849/10000000000 : ℝ), (-1362097951/2000000000 : ℝ), (-2312352787/5000000000 : ℝ)] ![(1985626590547/50000000000000 : ℝ), (60076685824891/100000000000000 : ℝ), (8988015245523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-878631849/10000000000 : ℝ)|^65 ≤ (1985626590547/50000000000000 : ℝ)^49
        have hw : |(-878631849/10000000000 : ℝ)|=(878631849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1362097951/2000000000 : ℝ)|^65 ≤ (60076685824891/100000000000000 : ℝ)^49
        have hw : |(-1362097951/2000000000 : ℝ)|=(1362097951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2312352787/5000000000 : ℝ)|^65 ≤ (8988015245523/25000000000000 : ℝ)^49
        have hw : |(-2312352787/5000000000 : ℝ)|=(2312352787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s0_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1034523489/2000000000 : ℝ)*x 0 + (-3256334983/10000000000 : ℝ)*x 1 + (4601850361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034523489/2000000000 : ℝ)^65 ≤ (20854416029371/50000000000000 : ℝ)^49 := by
    have hnat : (1034523489 : ℕ)^65*50000000000000^49 ≤ 20854416029371^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034523489 2000000000 20854416029371 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3256334983/10000000000 : ℝ)^65 ≤ (112873035767/500000000000 : ℝ)^49 := by
    have hnat : (3256334983 : ℕ)^65*500000000000^49 ≤ 112873035767^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3256334983 10000000000 112873035767 500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4601850361/10000000000 : ℝ)^65 ≤ (7143312153349/20000000000000 : ℝ)^49 := by
    have hnat : (4601850361 : ℕ)^65*20000000000000^49 ≤ 7143312153349^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4601850361 10000000000 7143312153349 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034523489/2000000000 : ℝ), (-3256334983/10000000000 : ℝ), (4601850361/10000000000 : ℝ)] ![(20854416029371/50000000000000 : ℝ), (112873035767/500000000000 : ℝ), (7143312153349/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034523489/2000000000 : ℝ)|^65 ≤ (20854416029371/50000000000000 : ℝ)^49
        have hw : |(1034523489/2000000000 : ℝ)|=(1034523489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3256334983/10000000000 : ℝ)|^65 ≤ (112873035767/500000000000 : ℝ)^49
        have hw : |(-3256334983/10000000000 : ℝ)|=(3256334983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4601850361/10000000000 : ℝ)|^65 ≤ (7143312153349/20000000000000 : ℝ)^49
        have hw : |(4601850361/10000000000 : ℝ)|=(4601850361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s0_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7295301709/10000000000 : ℝ)*x 0 + (-3126309873/10000000000 : ℝ)*x 1 + (-2122940231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7295301709/10000000000 : ℝ)^65 ≤ (65814667050651/100000000000000 : ℝ)^49 := by
    have hnat : (7295301709 : ℕ)^65*100000000000000^49 ≤ 65814667050651^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7295301709 10000000000 65814667050651 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3126309873/10000000000 : ℝ)^65 ≤ (2138673652539/10000000000000 : ℝ)^49 := by
    have hnat : (3126309873 : ℕ)^65*10000000000000^49 ≤ 2138673652539^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3126309873 10000000000 2138673652539 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122940231/10000000000 : ℝ)^65 ≤ (6399298205863/50000000000000 : ℝ)^49 := by
    have hnat : (2122940231 : ℕ)^65*50000000000000^49 ≤ 6399298205863^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122940231 10000000000 6399298205863 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7295301709/10000000000 : ℝ), (-3126309873/10000000000 : ℝ), (-2122940231/10000000000 : ℝ)] ![(65814667050651/100000000000000 : ℝ), (2138673652539/10000000000000 : ℝ), (6399298205863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7295301709/10000000000 : ℝ)|^65 ≤ (65814667050651/100000000000000 : ℝ)^49
        have hw : |(7295301709/10000000000 : ℝ)|=(7295301709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3126309873/10000000000 : ℝ)|^65 ≤ (2138673652539/10000000000000 : ℝ)^49
        have hw : |(-3126309873/10000000000 : ℝ)|=(3126309873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2122940231/10000000000 : ℝ)|^65 ≤ (6399298205863/50000000000000 : ℝ)^49
        have hw : |(-2122940231/10000000000 : ℝ)|=(2122940231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s0_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-191681123/2000000000 : ℝ)*x 0 + (-1463447249/2000000000 : ℝ)*x 1 + (-31845061/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (191681123/2000000000 : ℝ)^65 ≤ (4456501273693/100000000000000 : ℝ)^49 := by
    have hnat : (191681123 : ℕ)^65*100000000000000^49 ≤ 4456501273693^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191681123 2000000000 4456501273693 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1463447249/2000000000 : ℝ)^65 ≤ (1651932332809/2500000000000 : ℝ)^49 := by
    have hnat : (1463447249 : ℕ)^65*2500000000000^49 ≤ 1651932332809^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1463447249 2000000000 1651932332809 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31845061/80000000 : ℝ)^65 ≤ (7366551349101/25000000000000 : ℝ)^49 := by
    have hnat : (31845061 : ℕ)^65*25000000000000^49 ≤ 7366551349101^49*80000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31845061 80000000 7366551349101 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-191681123/2000000000 : ℝ), (-1463447249/2000000000 : ℝ), (-31845061/80000000 : ℝ)] ![(4456501273693/100000000000000 : ℝ), (1651932332809/2500000000000 : ℝ), (7366551349101/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-191681123/2000000000 : ℝ)|^65 ≤ (4456501273693/100000000000000 : ℝ)^49
        have hw : |(-191681123/2000000000 : ℝ)|=(191681123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1463447249/2000000000 : ℝ)|^65 ≤ (1651932332809/2500000000000 : ℝ)^49
        have hw : |(-1463447249/2000000000 : ℝ)|=(1463447249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31845061/80000000 : ℝ)|^65 ≤ (7366551349101/25000000000000 : ℝ)^49
        have hw : |(-31845061/80000000 : ℝ)|=(31845061/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s0_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4817465719/10000000000 : ℝ)*x 0 + (4274787543/10000000000 : ℝ)*x 1 + (-25000793/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4817465719/10000000000 : ℝ)^65 ≤ (37953270600893/100000000000000 : ℝ)^49 := by
    have hnat : (4817465719 : ℕ)^65*100000000000000^49 ≤ 37953270600893^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4817465719 10000000000 37953270600893 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4274787543/10000000000 : ℝ)^65 ≤ (32388947261113/100000000000000 : ℝ)^49 := by
    have hnat : (4274787543 : ℕ)^65*100000000000000^49 ≤ 32388947261113^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274787543 10000000000 32388947261113 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25000793/62500000 : ℝ)^65 ≤ (29657782126357/100000000000000 : ℝ)^49 := by
    have hnat : (25000793 : ℕ)^65*100000000000000^49 ≤ 29657782126357^49*62500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25000793 62500000 29657782126357 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4817465719/10000000000 : ℝ), (4274787543/10000000000 : ℝ), (-25000793/62500000 : ℝ)] ![(37953270600893/100000000000000 : ℝ), (32388947261113/100000000000000 : ℝ), (29657782126357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4817465719/10000000000 : ℝ)|^65 ≤ (37953270600893/100000000000000 : ℝ)^49
        have hw : |(4817465719/10000000000 : ℝ)|=(4817465719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4274787543/10000000000 : ℝ)|^65 ≤ (32388947261113/100000000000000 : ℝ)^49
        have hw : |(4274787543/10000000000 : ℝ)|=(4274787543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25000793/62500000 : ℝ)|^65 ≤ (29657782126357/100000000000000 : ℝ)^49
        have hw : |(-25000793/62500000 : ℝ)|=(25000793/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s0_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (602183207/1250000000 : ℝ)*x 0 + (-2329070771/10000000000 : ℝ)*x 1 + (2855990961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (602183207/1250000000 : ℝ)^65 ≤ (7590653988499/20000000000000 : ℝ)^49 := by
    have hnat : (602183207 : ℕ)^65*20000000000000^49 ≤ 7590653988499^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602183207 1250000000 7590653988499 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2329070771/10000000000 : ℝ)^65 ≤ (14472663345781/100000000000000 : ℝ)^49 := by
    have hnat : (2329070771 : ℕ)^65*100000000000000^49 ≤ 14472663345781^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2329070771 10000000000 14472663345781 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2855990961/5000000000 : ℝ)^65 ≤ (47574066694879/100000000000000 : ℝ)^49 := by
    have hnat : (2855990961 : ℕ)^65*100000000000000^49 ≤ 47574066694879^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2855990961 5000000000 47574066694879 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(602183207/1250000000 : ℝ), (-2329070771/10000000000 : ℝ), (2855990961/5000000000 : ℝ)] ![(7590653988499/20000000000000 : ℝ), (14472663345781/100000000000000 : ℝ), (47574066694879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(602183207/1250000000 : ℝ)|^65 ≤ (7590653988499/20000000000000 : ℝ)^49
        have hw : |(602183207/1250000000 : ℝ)|=(602183207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2329070771/10000000000 : ℝ)|^65 ≤ (14472663345781/100000000000000 : ℝ)^49
        have hw : |(-2329070771/10000000000 : ℝ)|=(2329070771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2855990961/5000000000 : ℝ)|^65 ≤ (47574066694879/100000000000000 : ℝ)^49
        have hw : |(2855990961/5000000000 : ℝ)|=(2855990961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s0_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7427443213/10000000000 : ℝ)*x 0 + (-2320614871/10000000000 : ℝ)*x 1 + (-553567993/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7427443213/10000000000 : ℝ)^65 ≤ (131641999373/195312500000 : ℝ)^49 := by
    have hnat : (7427443213 : ℕ)^65*195312500000^49 ≤ 131641999373^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7427443213 10000000000 131641999373 195312500000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2320614871/10000000000 : ℝ)^65 ≤ (14403003072263/100000000000000 : ℝ)^49 := by
    have hnat : (2320614871 : ℕ)^65*100000000000000^49 ≤ 14403003072263^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320614871 10000000000 14403003072263 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553567993/2000000000 : ℝ)^65 ≤ (18196293244367/100000000000000 : ℝ)^49 := by
    have hnat : (553567993 : ℕ)^65*100000000000000^49 ≤ 18196293244367^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553567993 2000000000 18196293244367 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7427443213/10000000000 : ℝ), (-2320614871/10000000000 : ℝ), (-553567993/2000000000 : ℝ)] ![(131641999373/195312500000 : ℝ), (14403003072263/100000000000000 : ℝ), (18196293244367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7427443213/10000000000 : ℝ)|^65 ≤ (131641999373/195312500000 : ℝ)^49
        have hw : |(7427443213/10000000000 : ℝ)|=(7427443213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2320614871/10000000000 : ℝ)|^65 ≤ (14403003072263/100000000000000 : ℝ)^49
        have hw : |(-2320614871/10000000000 : ℝ)|=(2320614871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-553567993/2000000000 : ℝ)|^65 ≤ (18196293244367/100000000000000 : ℝ)^49
        have hw : |(-553567993/2000000000 : ℝ)|=(553567993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s0_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-18477309/10000000000 : ℝ)*x 0 + (-6836134391/10000000000 : ℝ)*x 1 + (-4974150823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18477309/10000000000 : ℝ)^65 ≤ (2366533137/10000000000000 : ℝ)^49 := by
    have hnat : (18477309 : ℕ)^65*10000000000000^49 ≤ 2366533137^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18477309 10000000000 2366533137 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6836134391/10000000000 : ℝ)^65 ≤ (30188476591147/50000000000000 : ℝ)^49 := by
    have hnat : (6836134391 : ℕ)^65*50000000000000^49 ≤ 30188476591147^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6836134391 10000000000 30188476591147 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4974150823/10000000000 : ℝ)^65 ≤ (7919876294101/20000000000000 : ℝ)^49 := by
    have hnat : (4974150823 : ℕ)^65*20000000000000^49 ≤ 7919876294101^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4974150823 10000000000 7919876294101 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18477309/10000000000 : ℝ), (-6836134391/10000000000 : ℝ), (-4974150823/10000000000 : ℝ)] ![(2366533137/10000000000000 : ℝ), (30188476591147/50000000000000 : ℝ), (7919876294101/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18477309/10000000000 : ℝ)|^65 ≤ (2366533137/10000000000000 : ℝ)^49
        have hw : |(-18477309/10000000000 : ℝ)|=(18477309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6836134391/10000000000 : ℝ)|^65 ≤ (30188476591147/50000000000000 : ℝ)^49
        have hw : |(-6836134391/10000000000 : ℝ)|=(6836134391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4974150823/10000000000 : ℝ)|^65 ≤ (7919876294101/20000000000000 : ℝ)^49
        have hw : |(-4974150823/10000000000 : ℝ)|=(4974150823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s0_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4464184083/10000000000 : ℝ)*x 0 + (647094133/2000000000 : ℝ)*x 1 + (-2660848853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4464184083/10000000000 : ℝ)^65 ≤ (34306164550389/100000000000000 : ℝ)^49 := by
    have hnat : (4464184083 : ℕ)^65*100000000000000^49 ≤ 34306164550389^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4464184083 10000000000 34306164550389 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647094133/2000000000 : ℝ)^65 ≤ (11191467859791/50000000000000 : ℝ)^49 := by
    have hnat : (647094133 : ℕ)^65*50000000000000^49 ≤ 11191467859791^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647094133 2000000000 11191467859791 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2660848853/5000000000 : ℝ)^65 ≤ (4331089972617/10000000000000 : ℝ)^49 := by
    have hnat : (2660848853 : ℕ)^65*10000000000000^49 ≤ 4331089972617^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2660848853 5000000000 4331089972617 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4464184083/10000000000 : ℝ), (647094133/2000000000 : ℝ), (-2660848853/5000000000 : ℝ)] ![(34306164550389/100000000000000 : ℝ), (11191467859791/50000000000000 : ℝ), (4331089972617/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4464184083/10000000000 : ℝ)|^65 ≤ (34306164550389/100000000000000 : ℝ)^49
        have hw : |(4464184083/10000000000 : ℝ)|=(4464184083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647094133/2000000000 : ℝ)|^65 ≤ (11191467859791/50000000000000 : ℝ)^49
        have hw : |(647094133/2000000000 : ℝ)|=(647094133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2660848853/5000000000 : ℝ)|^65 ≤ (4331089972617/10000000000000 : ℝ)^49
        have hw : |(-2660848853/5000000000 : ℝ)|=(2660848853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s0_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6117499219/10000000000 : ℝ)*x 0 + (-2549647981/10000000000 : ℝ)*x 1 + (2096828749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6117499219/10000000000 : ℝ)^65 ≤ (52105524852543/100000000000000 : ℝ)^49 := by
    have hnat : (6117499219 : ℕ)^65*100000000000000^49 ≤ 52105524852543^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6117499219 10000000000 52105524852543 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2549647981/10000000000 : ℝ)^65 ≤ (16318410254601/100000000000000 : ℝ)^49 := by
    have hnat : (2549647981 : ℕ)^65*100000000000000^49 ≤ 16318410254601^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2549647981 10000000000 16318410254601 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2096828749/5000000000 : ℝ)^65 ≤ (3947008109419/12500000000000 : ℝ)^49 := by
    have hnat : (2096828749 : ℕ)^65*12500000000000^49 ≤ 3947008109419^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096828749 5000000000 3947008109419 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6117499219/10000000000 : ℝ), (-2549647981/10000000000 : ℝ), (2096828749/5000000000 : ℝ)] ![(52105524852543/100000000000000 : ℝ), (16318410254601/100000000000000 : ℝ), (3947008109419/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6117499219/10000000000 : ℝ)|^65 ≤ (52105524852543/100000000000000 : ℝ)^49
        have hw : |(6117499219/10000000000 : ℝ)|=(6117499219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2549647981/10000000000 : ℝ)|^65 ≤ (16318410254601/100000000000000 : ℝ)^49
        have hw : |(-2549647981/10000000000 : ℝ)|=(2549647981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2096828749/5000000000 : ℝ)|^65 ≤ (3947008109419/12500000000000 : ℝ)^49
        have hw : |(2096828749/5000000000 : ℝ)|=(2096828749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s0_19 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4412298673/5000000000 : ℝ)*x 0 + (-1659357987/10000000000 : ℝ)*x 1 + (-1207392427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4412298673/5000000000 : ℝ)^65 ≤ (4235772480827/5000000000000 : ℝ)^49 := by
    have hnat : (4412298673 : ℕ)^65*5000000000000^49 ≤ 4235772480827^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412298673 5000000000 4235772480827 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1659357987/10000000000 : ℝ)^65 ≤ (4615265127093/50000000000000 : ℝ)^49 := by
    have hnat : (1659357987 : ℕ)^65*50000000000000^49 ≤ 4615265127093^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1659357987 10000000000 4615265127093 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207392427/10000000000 : ℝ)^65 ≤ (6054020106453/100000000000000 : ℝ)^49 := by
    have hnat : (1207392427 : ℕ)^65*100000000000000^49 ≤ 6054020106453^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207392427 10000000000 6054020106453 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4412298673/5000000000 : ℝ), (-1659357987/10000000000 : ℝ), (-1207392427/10000000000 : ℝ)] ![(4235772480827/5000000000000 : ℝ), (4615265127093/50000000000000 : ℝ), (6054020106453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4412298673/5000000000 : ℝ)|^65 ≤ (4235772480827/5000000000000 : ℝ)^49
        have hw : |(4412298673/5000000000 : ℝ)|=(4412298673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1659357987/10000000000 : ℝ)|^65 ≤ (4615265127093/50000000000000 : ℝ)^49
        have hw : |(-1659357987/10000000000 : ℝ)|=(1659357987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1207392427/10000000000 : ℝ)|^65 ≤ (6054020106453/100000000000000 : ℝ)^49
        have hw : |(-1207392427/10000000000 : ℝ)|=(1207392427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s0_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-13008083/10000000000 : ℝ)*x 0 + (-1879904361/2500000000 : ℝ)*x 1 + (-418329801/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13008083/10000000000 : ℝ)^65 ≤ (14856469003/100000000000000 : ℝ)^49 := by
    have hnat : (13008083 : ℕ)^65*100000000000000^49 ≤ 14856469003^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13008083 10000000000 14856469003 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1879904361/2500000000 : ℝ)^65 ≤ (17128127089077/25000000000000 : ℝ)^49 := by
    have hnat : (1879904361 : ℕ)^65*25000000000000^49 ≤ 17128127089077^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879904361 2500000000 17128127089077 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418329801/1000000000 : ℝ)^65 ≤ (3147263516039/10000000000000 : ℝ)^49 := by
    have hnat : (418329801 : ℕ)^65*10000000000000^49 ≤ 3147263516039^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418329801 1000000000 3147263516039 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13008083/10000000000 : ℝ), (-1879904361/2500000000 : ℝ), (-418329801/1000000000 : ℝ)] ![(14856469003/100000000000000 : ℝ), (17128127089077/25000000000000 : ℝ), (3147263516039/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13008083/10000000000 : ℝ)|^65 ≤ (14856469003/100000000000000 : ℝ)^49
        have hw : |(-13008083/10000000000 : ℝ)|=(13008083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1879904361/2500000000 : ℝ)|^65 ≤ (17128127089077/25000000000000 : ℝ)^49
        have hw : |(-1879904361/2500000000 : ℝ)|=(1879904361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418329801/1000000000 : ℝ)|^65 ≤ (3147263516039/10000000000000 : ℝ)^49
        have hw : |(-418329801/1000000000 : ℝ)|=(418329801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s0_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3061484233/5000000000 : ℝ)*x 0 + (1458720809/5000000000 : ℝ)*x 1 + (-3863372729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3061484233/5000000000 : ℝ)^65 ≤ (2086693162393/4000000000000 : ℝ)^49 := by
    have hnat : (3061484233 : ℕ)^65*4000000000000^49 ≤ 2086693162393^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3061484233 5000000000 2086693162393 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1458720809/5000000000 : ℝ)^65 ≤ (9756162168903/50000000000000 : ℝ)^49 := by
    have hnat : (1458720809 : ℕ)^65*50000000000000^49 ≤ 9756162168903^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458720809 5000000000 9756162168903 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3863372729/10000000000 : ℝ)^65 ≤ (5664069318947/20000000000000 : ℝ)^49 := by
    have hnat : (3863372729 : ℕ)^65*20000000000000^49 ≤ 5664069318947^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3863372729 10000000000 5664069318947 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3061484233/5000000000 : ℝ), (1458720809/5000000000 : ℝ), (-3863372729/10000000000 : ℝ)] ![(2086693162393/4000000000000 : ℝ), (9756162168903/50000000000000 : ℝ), (5664069318947/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3061484233/5000000000 : ℝ)|^65 ≤ (2086693162393/4000000000000 : ℝ)^49
        have hw : |(3061484233/5000000000 : ℝ)|=(3061484233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1458720809/5000000000 : ℝ)|^65 ≤ (9756162168903/50000000000000 : ℝ)^49
        have hw : |(1458720809/5000000000 : ℝ)|=(1458720809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3863372729/10000000000 : ℝ)|^65 ≤ (5664069318947/20000000000000 : ℝ)^49
        have hw : |(-3863372729/10000000000 : ℝ)|=(3863372729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s0_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1127197527/2500000000 : ℝ)*x 0 + (-3686416897/10000000000 : ℝ)*x 1 + (4881675239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1127197527/2500000000 : ℝ)^65 ≤ (34761621358111/100000000000000 : ℝ)^49 := by
    have hnat : (1127197527 : ℕ)^65*100000000000000^49 ≤ 34761621358111^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127197527 2500000000 34761621358111 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3686416897/10000000000 : ℝ)^65 ≤ (13306306947293/50000000000000 : ℝ)^49 := by
    have hnat : (3686416897 : ℕ)^65*50000000000000^49 ≤ 13306306947293^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3686416897 10000000000 13306306947293 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4881675239/10000000000 : ℝ)^65 ≤ (19312882367427/50000000000000 : ℝ)^49 := by
    have hnat : (4881675239 : ℕ)^65*50000000000000^49 ≤ 19312882367427^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4881675239 10000000000 19312882367427 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1127197527/2500000000 : ℝ), (-3686416897/10000000000 : ℝ), (4881675239/10000000000 : ℝ)] ![(34761621358111/100000000000000 : ℝ), (13306306947293/50000000000000 : ℝ), (19312882367427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1127197527/2500000000 : ℝ)|^65 ≤ (34761621358111/100000000000000 : ℝ)^49
        have hw : |(1127197527/2500000000 : ℝ)|=(1127197527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3686416897/10000000000 : ℝ)|^65 ≤ (13306306947293/50000000000000 : ℝ)^49
        have hw : |(-3686416897/10000000000 : ℝ)|=(3686416897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4881675239/10000000000 : ℝ)|^65 ≤ (19312882367427/50000000000000 : ℝ)^49
        have hw : |(4881675239/10000000000 : ℝ)|=(4881675239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s0_25 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (136519307/156250000 : ℝ)*x 0 + (-384851227/2000000000 : ℝ)*x 1 + (-1070498189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136519307/156250000 : ℝ)^65 ≤ (83604736294099/100000000000000 : ℝ)^49 := by
    have hnat : (136519307 : ℕ)^65*100000000000000^49 ≤ 83604736294099^49*156250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136519307 156250000 83604736294099 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (384851227/2000000000 : ℝ)^65 ≤ (11234475457417/100000000000000 : ℝ)^49 := by
    have hnat : (384851227 : ℕ)^65*100000000000000^49 ≤ 11234475457417^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384851227 2000000000 11234475457417 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1070498189/10000000000 : ℝ)^65 ≤ (5160788234297/100000000000000 : ℝ)^49 := by
    have hnat : (1070498189 : ℕ)^65*100000000000000^49 ≤ 5160788234297^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070498189 10000000000 5160788234297 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136519307/156250000 : ℝ), (-384851227/2000000000 : ℝ), (-1070498189/10000000000 : ℝ)] ![(83604736294099/100000000000000 : ℝ), (11234475457417/100000000000000 : ℝ), (5160788234297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136519307/156250000 : ℝ)|^65 ≤ (83604736294099/100000000000000 : ℝ)^49
        have hw : |(136519307/156250000 : ℝ)|=(136519307/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-384851227/2000000000 : ℝ)|^65 ≤ (11234475457417/100000000000000 : ℝ)^49
        have hw : |(-384851227/2000000000 : ℝ)|=(384851227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1070498189/10000000000 : ℝ)|^65 ≤ (5160788234297/100000000000000 : ℝ)^49
        have hw : |(-1070498189/10000000000 : ℝ)|=(1070498189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2542046223/10000000000 : ℝ)*x 0 + (-1446194443/2500000000 : ℝ)*x 1 + (-57097097/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2542046223/10000000000 : ℝ)^65 ≤ (8126950847571/50000000000000 : ℝ)^49 := by
    have hnat : (2542046223 : ℕ)^65*50000000000000^49 ≤ 8126950847571^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542046223 10000000000 8126950847571 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1446194443/2500000000 : ℝ)^65 ≤ (12095003891401/25000000000000 : ℝ)^49 := by
    have hnat : (1446194443 : ℕ)^65*25000000000000^49 ≤ 12095003891401^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1446194443 2500000000 12095003891401 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57097097/125000000 : ℝ)^65 ≤ (17683041364483/50000000000000 : ℝ)^49 := by
    have hnat : (57097097 : ℕ)^65*50000000000000^49 ≤ 17683041364483^49*125000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57097097 125000000 17683041364483 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2542046223/10000000000 : ℝ), (-1446194443/2500000000 : ℝ), (-57097097/125000000 : ℝ)] ![(8126950847571/50000000000000 : ℝ), (12095003891401/25000000000000 : ℝ), (17683041364483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2542046223/10000000000 : ℝ)|^65 ≤ (8126950847571/50000000000000 : ℝ)^49
        have hw : |(-2542046223/10000000000 : ℝ)|=(2542046223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1446194443/2500000000 : ℝ)|^65 ≤ (12095003891401/25000000000000 : ℝ)^49
        have hw : |(-1446194443/2500000000 : ℝ)|=(1446194443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-57097097/125000000 : ℝ)|^65 ≤ (17683041364483/50000000000000 : ℝ)^49
        have hw : |(-57097097/125000000 : ℝ)|=(57097097/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s1_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (19441713/40000000 : ℝ)*x 0 + (73930953/200000000 : ℝ)*x 1 + (-2260542157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19441713/40000000 : ℝ)^65 ≤ (38402914109567/100000000000000 : ℝ)^49 := by
    have hnat : (19441713 : ℕ)^65*100000000000000^49 ≤ 38402914109567^49*40000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19441713 40000000 38402914109567 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73930953/200000000 : ℝ)^65 ≤ (13354836555587/50000000000000 : ℝ)^49 := by
    have hnat : (73930953 : ℕ)^65*50000000000000^49 ≤ 13354836555587^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73930953 200000000 13354836555587 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2260542157/5000000000 : ℝ)^65 ≤ (34887412756761/100000000000000 : ℝ)^49 := by
    have hnat : (2260542157 : ℕ)^65*100000000000000^49 ≤ 34887412756761^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260542157 5000000000 34887412756761 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(19441713/40000000 : ℝ), (73930953/200000000 : ℝ), (-2260542157/5000000000 : ℝ)] ![(38402914109567/100000000000000 : ℝ), (13354836555587/50000000000000 : ℝ), (34887412756761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(19441713/40000000 : ℝ)|^65 ≤ (38402914109567/100000000000000 : ℝ)^49
        have hw : |(19441713/40000000 : ℝ)|=(19441713/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(73930953/200000000 : ℝ)|^65 ≤ (13354836555587/50000000000000 : ℝ)^49
        have hw : |(73930953/200000000 : ℝ)|=(73930953/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2260542157/5000000000 : ℝ)|^65 ≤ (34887412756761/100000000000000 : ℝ)^49
        have hw : |(-2260542157/5000000000 : ℝ)|=(2260542157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4847082137/10000000000 : ℝ)*x 0 + (-925717813/2500000000 : ℝ)*x 1 + (17690697/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4847082137/10000000000 : ℝ)^65 ≤ (38263094894953/100000000000000 : ℝ)^49 := by
    have hnat : (4847082137 : ℕ)^65*100000000000000^49 ≤ 38263094894953^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4847082137 10000000000 38263094894953 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (925717813/2500000000 : ℝ)^65 ≤ (13385150699337/50000000000000 : ℝ)^49 := by
    have hnat : (925717813 : ℕ)^65*50000000000000^49 ≤ 13385150699337^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925717813 2500000000 13385150699337 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17690697/39062500 : ℝ)^65 ≤ (34966603689839/100000000000000 : ℝ)^49 := by
    have hnat : (17690697 : ℕ)^65*100000000000000^49 ≤ 34966603689839^49*39062500^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17690697 39062500 34966603689839 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4847082137/10000000000 : ℝ), (-925717813/2500000000 : ℝ), (17690697/39062500 : ℝ)] ![(38263094894953/100000000000000 : ℝ), (13385150699337/50000000000000 : ℝ), (34966603689839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4847082137/10000000000 : ℝ)|^65 ≤ (38263094894953/100000000000000 : ℝ)^49
        have hw : |(4847082137/10000000000 : ℝ)|=(4847082137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-925717813/2500000000 : ℝ)|^65 ≤ (13385150699337/50000000000000 : ℝ)^49
        have hw : |(-925717813/2500000000 : ℝ)|=(925717813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17690697/39062500 : ℝ)|^65 ≤ (34966603689839/100000000000000 : ℝ)^49
        have hw : |(17690697/39062500 : ℝ)|=(17690697/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301044_s1_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2906231459/5000000000 : ℝ)*x 0 + (-3998646607/10000000000 : ℝ)*x 1 + (-3157405483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2906231459/5000000000 : ℝ)^65 ≤ (3042962517417/6250000000000 : ℝ)^49 := by
    have hnat : (2906231459 : ℕ)^65*6250000000000^49 ≤ 3042962517417^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2906231459 5000000000 3042962517417 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3998646607/10000000000 : ℝ)^65 ≤ (29643224259071/100000000000000 : ℝ)^49 := by
    have hnat : (3998646607 : ℕ)^65*100000000000000^49 ≤ 29643224259071^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3998646607 10000000000 29643224259071 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3157405483/10000000000 : ℝ)^65 ≤ (10834687724421/50000000000000 : ℝ)^49 := by
    have hnat : (3157405483 : ℕ)^65*50000000000000^49 ≤ 10834687724421^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3157405483 10000000000 10834687724421 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2906231459/5000000000 : ℝ), (-3998646607/10000000000 : ℝ), (-3157405483/10000000000 : ℝ)] ![(3042962517417/6250000000000 : ℝ), (29643224259071/100000000000000 : ℝ), (10834687724421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2906231459/5000000000 : ℝ)|^65 ≤ (3042962517417/6250000000000 : ℝ)^49
        have hw : |(2906231459/5000000000 : ℝ)|=(2906231459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3998646607/10000000000 : ℝ)|^65 ≤ (29643224259071/100000000000000 : ℝ)^49
        have hw : |(-3998646607/10000000000 : ℝ)|=(3998646607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3157405483/10000000000 : ℝ)|^65 ≤ (10834687724421/50000000000000 : ℝ)^49
        have hw : |(-3157405483/10000000000 : ℝ)|=(3157405483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301044 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]]) : False := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-878631849/10000000000 : ℝ)*X 0 0+(-1362097951/2000000000 : ℝ)*X 0 1+(-2312352787/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1034523489/2000000000 : ℝ)*X 2 0+(-3256334983/10000000000 : ℝ)*X 2 1+(4601850361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((7295301709/10000000000 : ℝ)*X 0 0+(-3126309873/10000000000 : ℝ)*X 0 1+(-2122940231/10000000000 : ℝ)*X 0 2+(7295301709/10000000000 : ℝ)*X 1 0+(-3126309873/10000000000 : ℝ)*X 1 1+(-2122940231/10000000000 : ℝ)*X 1 2+(7295301709/10000000000 : ℝ)*X 2 0+(-3126309873/10000000000 : ℝ)*X 2 1+(-2122940231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-191681123/2000000000 : ℝ)*X 0 0+(-1463447249/2000000000 : ℝ)*X 0 1+(-31845061/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4817465719/10000000000 : ℝ)*X 1 0+(4274787543/10000000000 : ℝ)*X 1 1+(-25000793/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((602183207/1250000000 : ℝ)*X 2 0+(-2329070771/10000000000 : ℝ)*X 2 1+(2855990961/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((7427443213/10000000000 : ℝ)*X 0 0+(-2320614871/10000000000 : ℝ)*X 0 1+(-553567993/2000000000 : ℝ)*X 0 2+(7427443213/10000000000 : ℝ)*X 1 0+(-2320614871/10000000000 : ℝ)*X 1 1+(-553567993/2000000000 : ℝ)*X 1 2+(7427443213/10000000000 : ℝ)*X 2 0+(-2320614871/10000000000 : ℝ)*X 2 1+(-553567993/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-18477309/10000000000 : ℝ)*X 0 0+(-6836134391/10000000000 : ℝ)*X 0 1+(-4974150823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4464184083/10000000000 : ℝ)*X 1 0+(647094133/2000000000 : ℝ)*X 1 1+(-2660848853/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((6117499219/10000000000 : ℝ)*X 2 0+(-2549647981/10000000000 : ℝ)*X 2 1+(2096828749/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((4412298673/5000000000 : ℝ)*X 0 0+(-1659357987/10000000000 : ℝ)*X 0 1+(-1207392427/10000000000 : ℝ)*X 0 2+(4412298673/5000000000 : ℝ)*X 1 0+(-1659357987/10000000000 : ℝ)*X 1 1+(-1207392427/10000000000 : ℝ)*X 1 2+(4412298673/5000000000 : ℝ)*X 2 0+(-1659357987/10000000000 : ℝ)*X 2 1+(-1207392427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-13008083/10000000000 : ℝ)*X 0 0+(-1879904361/2500000000 : ℝ)*X 0 1+(-418329801/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((3061484233/5000000000 : ℝ)*X 1 0+(1458720809/5000000000 : ℝ)*X 1 1+(-3863372729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1127197527/2500000000 : ℝ)*X 2 0+(-3686416897/10000000000 : ℝ)*X 2 1+(4881675239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((136519307/156250000 : ℝ)*X 0 0+(-384851227/2000000000 : ℝ)*X 0 1+(-1070498189/10000000000 : ℝ)*X 0 2+(136519307/156250000 : ℝ)*X 1 0+(-384851227/2000000000 : ℝ)*X 1 1+(-1070498189/10000000000 : ℝ)*X 1 2+(136519307/156250000 : ℝ)*X 2 0+(-384851227/2000000000 : ℝ)*X 2 1+(-1070498189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((2747/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2747/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16189414916451595411701/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (454049937131/1000000000000 : ℝ)*(base39) + (9229521421/20000000000 : ℝ)*(base49) + (2880694568121/1000000000000 : ℝ)*(major_s0_0) + (2880694568121/1000000000000 : ℝ)*(major_s0_1) + (2880694568121/1000000000000 : ℝ)*(major_s0_2) + (255191947/1000000000000 : ℝ)*(sp_s0_0) + (99364389/500000000000 : ℝ)*(sp_s0_6) + (1906855717811/500000000000 : ℝ)*(sp_s0_7) + (3813912191761/1000000000000 : ℝ)*(sp_s0_8) + (1906952340999/500000000000 : ℝ)*(sp_s0_9) + (486804136003/250000000000 : ℝ)*(sp_s0_13) + (14338627/250000000000 : ℝ)*(sp_s0_15) + (29187/10000000000 : ℝ)*(sp_s0_20) + (64864271/1000000000000 : ℝ)*(sp_s0_22) + (1947415272789/1000000000000 : ℝ)*(f.failure) + (3813969546269/1000000000000 : ℝ)*(f.sum) + (2539966478070669/5000000000000000000000000000 : ℝ)*base62 + (1894366063011803/10000000000000000000000000000 : ℝ)*base64 + (5981806489988197/10000000000000000000000000000 : ℝ)*base66 + (1906734696570669/10000000000000000000000000000 : ℝ)*base68 + (435092812927191/1250000000000000000000000000 : ℝ)*base71 + (3591779489988197/10000000000000000000000000000 : ℝ)*base72 + (1846989329570669/10000000000000000000000000000 : ℝ)*base74 + (15530024570669/10000000000000000000000000000 : ℝ)*base76 + (1554790429488197/5000000000000000000000000000 : ℝ)*base78 + (14991/25000000000000000 : ℝ)*base86 + (14991/25000000000000000 : ℝ)*base88 + (14991/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-24761/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-24761/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6586827979669907953473/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1608883/1000000000000 : ℝ)*(base12) + (1564140632459/1000000000000 : ℝ)*(base39) + (290377012403/250000000000 : ℝ)*(base40) + (612848956417/1000000000000 : ℝ)*(base49) + (571055792697/125000000000 : ℝ)*(major_s0_0) + (571055792697/125000000000 : ℝ)*(major_s0_1) + (571055792697/125000000000 : ℝ)*(major_s0_2) + (124316623/1000000000000 : ℝ)*(sp_s0_0) + (65786791/1000000000000 : ℝ)*(sp_s0_9) + (378024328391/62500000000 : ℝ)*(sp_s0_14) + (302425271523/50000000000 : ℝ)*(sp_s0_15) + (6048449392971/1000000000000 : ℝ)*(sp_s0_16) + (3088373990411/1000000000000 : ℝ)*(sp_s0_19) + (4874651/500000000000 : ℝ)*(sp_s0_21) + (3088373990411/1000000000000 : ℝ)*(f.failure) + (3024257589881/500000000000 : ℝ)*(f.sum) + (148517830042167/625000000000000000000000000 : ℝ)*base63 + (4914119575829/1250000000000000000000000000 : ℝ)*base65 + (37123993549171/1250000000000000000000000000 : ℝ)*base67 + (245429701229667/1250000000000000000000000000 : ℝ)*base69 + (918673492459/4882812500000000000000000 : ℝ)*base70 + (515936572049171/1250000000000000000000000000 : ℝ)*base73 + (236597122104667/1250000000000000000000000000 : ℝ)*base75 + (201705525395333/1250000000000000000000000000 : ℝ)*base76 + (310356809986671/625000000000000000000000000 : ℝ)*base79 + (10809/25000000000000000 : ℝ)*base86 + (10809/25000000000000000 : ℝ)*base88 + (10809/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-12631/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-12631/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4077467968347387189129/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (561747/31250000000 : ℝ)*(base10) + (440690232307/250000000000 : ℝ)*(base39) + (908852794041/1000000000000 : ℝ)*(base40) + (327859623789/500000000000 : ℝ)*(base49) + (2339597923567/500000000000 : ℝ)*(major_s0_0) + (2339597923567/500000000000 : ℝ)*(major_s0_1) + (2339597923567/500000000000 : ℝ)*(major_s0_2) + (3834997/100000000000 : ℝ)*(sp_s0_2) + (36376117/500000000000 : ℝ)*(sp_s0_7) + (3230323/100000000000 : ℝ)*(sp_s0_8) + (6195053433071/1000000000000 : ℝ)*(sp_s0_20) + (6195111857979/1000000000000 : ℝ)*(sp_s0_21) + (6195105811239/1000000000000 : ℝ)*(sp_s0_22) + (395405397969/125000000000 : ℝ)*(sp_s0_25) + (395405397969/125000000000 : ℝ)*(f.failure) + (6195144161209/1000000000000 : ℝ)*(f.sum) + (937208440769237/2500000000000000000000000000 : ℝ)*base63 + (3072746242023581/5000000000000000000000000000 : ℝ)*base64 + (3466914526976419/5000000000000000000000000000 : ℝ)*base66 + (3479302624019237/5000000000000000000000000000 : ℝ)*base69 + (107679945125543/625000000000000000000000000 : ℝ)*base70 + (1747437461476419/5000000000000000000000000000 : ℝ)*base72 + (3314208685019237/5000000000000000000000000000 : ℝ)*base75 + (2929358229480763/5000000000000000000000000000 : ℝ)*base76 + (567494861726419/2500000000000000000000000000 : ℝ)*base78 + (2161/3125000000000000 : ℝ)*base86 + (2161/3125000000000000 : ℝ)*base88 + (2161/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (2747/20000 : ℝ) ^ (129/32 : ℝ) ≤ (6689625357487083/20000000000000000000 : ℝ) := by
    have hpowers : (2747/20000 : ℝ)^129 ≤ (6689625357487083/20000000000000000000 : ℝ)^32 := by
      have hnat : (2747 : ℕ)^129*20000000000000000000^32 ≤ 6689625357487083^32*20000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2747 20000 6689625357487083 20000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2747/20000 : ℝ)) (X := (6689625357487083/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (20006689625357487083/20000000000000000000 : ℝ) ≤ (2500207404163433/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (20006689625357487083/20000000000000000000 : ℝ)^32 ≤ (2500207404163433/2500000000000000 : ℝ)^129 := by
      have hnat : (20006689625357487083 : ℕ)^32*2500000000000000^129 ≤ 2500207404163433^129*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006689625357487083 20000000000000000000 2500207404163433 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500207404163433/2500000000000000 : ℝ)) (X := (20006689625357487083/20000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (10006689625357487083/10000000000000000000 : ℝ) ≤ (10001659024747249/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (10006689625357487083/10000000000000000000 : ℝ)^32 ≤ (10001659024747249/10000000000000000 : ℝ)^129 := by
      have hnat : (10006689625357487083 : ℕ)^32*10000000000000000^129 ≤ 10001659024747249^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006689625357487083 10000000000000000000 10001659024747249 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001659024747249/10000000000000000 : ℝ)) (X := (10006689625357487083/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(207404163433/343375000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(829408093517/1373500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (2747/20000 : ℝ)) (alpha := (207404163433/343375000000000 : ℝ)) (beta := (829408093517/1373500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2747/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(207404163433/343375000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(829408093517/1373500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (24761/50000 : ℝ) ^ (129/32 : ℝ) ≤ (5883762666842575973/100000000000000000000 : ℝ) := by
    have hpowers : (24761/50000 : ℝ)^129 ≤ (5883762666842575973/100000000000000000000 : ℝ)^32 := by
      have hnat : (24761 : ℕ)^129*100000000000000000000^32 ≤ 5883762666842575973^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24761 50000 5883762666842575973 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24761/50000 : ℝ)) (X := (5883762666842575973/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (105883762666842575973/100000000000000000000 : ℝ) ≤ (10142831776035857/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (105883762666842575973/100000000000000000000 : ℝ)^32 ≤ (10142831776035857/10000000000000000 : ℝ)^129 := by
      have hnat : (105883762666842575973 : ℕ)^32*10000000000000000^129 ≤ 10142831776035857^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105883762666842575973 100000000000000000000 10142831776035857 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10142831776035857/10000000000000000 : ℝ)) (X := (105883762666842575973/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (55883762666842575973/50000000000000000000 : ℝ) ≤ (5139907202700961/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (55883762666842575973/50000000000000000000 : ℝ)^32 ≤ (5139907202700961/5000000000000000 : ℝ)^129 := by
      have hnat : (55883762666842575973 : ℕ)^32*5000000000000000^129 ≤ 5139907202700961^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55883762666842575973 50000000000000000000 5139907202700961 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5139907202700961/5000000000000000 : ℝ)) (X := (55883762666842575973/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(142831776035857/4952200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(27396525873213/990440000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (24761/50000 : ℝ)) (alpha := (142831776035857/4952200000000000 : ℝ)) (beta := (27396525873213/990440000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (24761/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(142831776035857/4952200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(27396525873213/990440000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (12631/25000 : ℝ) ^ (129/32 : ℝ) ≤ (159464941722892901/2500000000000000000 : ℝ) := by
    have hpowers : (12631/25000 : ℝ)^129 ≤ (159464941722892901/2500000000000000000 : ℝ)^32 := by
      have hnat : (12631 : ℕ)^129*2500000000000000000^32 ≤ 159464941722892901^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12631 25000 159464941722892901 2500000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12631/25000 : ℝ)) (X := (159464941722892901/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (2659464941722892901/2500000000000000000 : ℝ) ≤ (2538642408632257/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2659464941722892901/2500000000000000000 : ℝ)^32 ≤ (2538642408632257/2500000000000000 : ℝ)^129 := by
      have hnat : (2659464941722892901 : ℕ)^32*2500000000000000^129 ≤ 2538642408632257^129*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2659464941722892901 2500000000000000000 2538642408632257 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2538642408632257/2500000000000000 : ℝ)) (X := (2659464941722892901/2500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1409464941722892901/1250000000000000000 : ℝ) ≤ (1030231943291683/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (1409464941722892901/1250000000000000000 : ℝ)^32 ≤ (1030231943291683/1000000000000000 : ℝ)^129 := by
      have hnat : (1409464941722892901 : ℕ)^32*1000000000000000^129 ≤ 1030231943291683^129*1250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409464941722892901 1250000000000000000 1030231943291683 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1030231943291683/1000000000000000 : ℝ)) (X := (1409464941722892901/1250000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(2273082860721/74300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(73874899193901/2526200000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (12631/25000 : ℝ)) (alpha := (2273082860721/74300000000000 : ℝ)) (beta := (73874899193901/2526200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (12631/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(2273082860721/74300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(73874899193901/2526200000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2542046223/10000000000 : ℝ)*X 0 0+(-1446194443/2500000000 : ℝ)*X 0 1+(-57097097/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((19441713/40000000 : ℝ)*X 1 0+(73930953/200000000 : ℝ)*X 1 1+(-2260542157/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4847082137/10000000000 : ℝ)*X 2 0+(-925717813/2500000000 : ℝ)*X 2 1+(17690697/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2906231459/5000000000 : ℝ)*X 0 0+(-3998646607/10000000000 : ℝ)*X 0 1+(-3157405483/10000000000 : ℝ)*X 0 2+(2906231459/5000000000 : ℝ)*X 1 0+(-3998646607/10000000000 : ℝ)*X 1 1+(-3157405483/10000000000 : ℝ)*X 1 2+(2906231459/5000000000 : ℝ)*X 2 0+(-3998646607/10000000000 : ℝ)*X 2 1+(-3157405483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301044_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-73443/12500 : ℝ) < ((-36981/25000 : ℝ)*P 0+(-36981/25000 : ℝ)*P 1+(-36981/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-73443/12500 : ℝ) < (-1250481656730358628517985605668793/214785314169250000000000000000000 : ℝ) := by norm_num
    linear_combination (107039/100000000000 : ℝ)*(base12) + (833199/1000000000000 : ℝ)*(base15) + (29427/500000000000 : ℝ)*(base25) + (322545405931/500000000000 : ℝ)*(base39) + (359877099649/1000000000000 : ℝ)*(base40) + (236129239091/1000000000000 : ℝ)*(base49) + (141749/1000000000000 : ℝ)*(base50) + (15757/100000000000 : ℝ)*(base60) + (36981/25000 : ℝ)*(major_s1_0) + (36981/25000 : ℝ)*(major_s1_1) + (36981/25000 : ℝ)*(major_s1_2) + (1940668013629/1000000000000 : ℝ)*(sp_s1_0) + (97033412541/50000000000 : ℝ)*(sp_s1_1) + (388133805033/200000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1940669084019/1000000000000 : ℝ)*(f.sum) + (37832636463690941/183974230000000000000000000000 : ℝ)*base63 + (11821511425257/31577500000000000000000000 : ℝ)*base65 + (779231381893/3095125000000000000000000 : ℝ)*base67 + (51650181/1486000000000000000000 : ℝ)*base69 + (17599988925039/346973570000000000000000000 : ℝ)*base71 + (253509643939/686750000000000000000000 : ℝ)*base73 + (4416297295481/49522000000000000000000000 : ℝ)*base74 + (299357498737/1373500000000000000000000 : ℝ)*base76 + (1018020597579191/1062788546875000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p001_b025 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 44 ≤ c.val) (hhi : c.val < 46)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=44 ∨ c=45 := by omega
  rcases hc with rfl|rfl
  · exact collision_c301044 p hpa (by linarith only [hpb]) X hX
  · exact collision_c301045 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 44 ≤ c.val) (hhi : c.val < 46)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b025 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

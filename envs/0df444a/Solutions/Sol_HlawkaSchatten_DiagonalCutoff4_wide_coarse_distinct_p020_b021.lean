-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b021
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:38:44.402738+00:00
-- url     : https://prove2.me/submissions/acff0bc3-b5dd-4d24-b227-d54a599da6db

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
theorem collision_support_c320039_s0_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-47390437/400000000 : ℝ)*x 0 + (-1564788069/2500000000 : ℝ)*x 1 + (4498506221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47390437/400000000 : ℝ)^41 ≤ (1412818416447/20000000000000 : ℝ)^33 := by
    have hnat : (47390437 : ℕ)^41*20000000000000^33 ≤ 1412818416447^33*400000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47390437 400000000 1412818416447 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1564788069/2500000000 : ℝ)^41 ≤ (55870935843859/100000000000000 : ℝ)^33 := by
    have hnat : (1564788069 : ℕ)^41*100000000000000^33 ≤ 55870935843859^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564788069 2500000000 55870935843859 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498506221/10000000000 : ℝ)^41 ≤ (4633121506797/12500000000000 : ℝ)^33 := by
    have hnat : (4498506221 : ℕ)^41*12500000000000^33 ≤ 4633121506797^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498506221 10000000000 4633121506797 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-47390437/400000000 : ℝ), (-1564788069/2500000000 : ℝ), (4498506221/10000000000 : ℝ)] ![(1412818416447/20000000000000 : ℝ), (55870935843859/100000000000000 : ℝ), (4633121506797/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-47390437/400000000 : ℝ)|^41 ≤ (1412818416447/20000000000000 : ℝ)^33
        have hw : |(-47390437/400000000 : ℝ)|=(47390437/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1564788069/2500000000 : ℝ)|^41 ≤ (55870935843859/100000000000000 : ℝ)^33
        have hw : |(-1564788069/2500000000 : ℝ)|=(1564788069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498506221/10000000000 : ℝ)|^41 ≤ (4633121506797/12500000000000 : ℝ)^33
        have hw : |(4498506221/10000000000 : ℝ)|=(4498506221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s0_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1178766603/2500000000 : ℝ)*x 0 + (953486821/2500000000 : ℝ)*x 1 + (3846617483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1178766603/2500000000 : ℝ)^41 ≤ (1964732138327/5000000000000 : ℝ)^33 := by
    have hnat : (1178766603 : ℕ)^41*5000000000000^33 ≤ 1964732138327^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178766603 2500000000 1964732138327 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (953486821/2500000000 : ℝ)^41 ≤ (15095926258731/50000000000000 : ℝ)^33 := by
    have hnat : (953486821 : ℕ)^41*50000000000000^33 ≤ 15095926258731^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953486821 2500000000 15095926258731 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3846617483/10000000000 : ℝ)^41 ≤ (476773510857/1562500000000 : ℝ)^33 := by
    have hnat : (3846617483 : ℕ)^41*1562500000000^33 ≤ 476773510857^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3846617483 10000000000 476773510857 1562500000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1178766603/2500000000 : ℝ), (953486821/2500000000 : ℝ), (3846617483/10000000000 : ℝ)] ![(1964732138327/5000000000000 : ℝ), (15095926258731/50000000000000 : ℝ), (476773510857/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1178766603/2500000000 : ℝ)|^41 ≤ (1964732138327/5000000000000 : ℝ)^33
        have hw : |(1178766603/2500000000 : ℝ)|=(1178766603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(953486821/2500000000 : ℝ)|^41 ≤ (15095926258731/50000000000000 : ℝ)^33
        have hw : |(953486821/2500000000 : ℝ)|=(953486821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3846617483/10000000000 : ℝ)|^41 ≤ (476773510857/1562500000000 : ℝ)^33
        have hw : |(3846617483/10000000000 : ℝ)|=(3846617483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s0_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4715066417/10000000000 : ℝ)*x 0 + (-47361051/125000000 : ℝ)*x 1 + (-1935794669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4715066417/10000000000 : ℝ)^41 ≤ (39294642818311/100000000000000 : ℝ)^33 := by
    have hnat : (4715066417 : ℕ)^41*100000000000000^33 ≤ 39294642818311^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4715066417 10000000000 39294642818311 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47361051/125000000 : ℝ)^41 ≤ (7486386637497/25000000000000 : ℝ)^33 := by
    have hnat : (47361051 : ℕ)^41*25000000000000^33 ≤ 7486386637497^33*125000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47361051 125000000 7486386637497 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1935794669/5000000000 : ℝ)^41 ≤ (15379905311577/50000000000000 : ℝ)^33 := by
    have hnat : (1935794669 : ℕ)^41*50000000000000^33 ≤ 15379905311577^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935794669 5000000000 15379905311577 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4715066417/10000000000 : ℝ), (-47361051/125000000 : ℝ), (-1935794669/5000000000 : ℝ)] ![(39294642818311/100000000000000 : ℝ), (7486386637497/25000000000000 : ℝ), (15379905311577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4715066417/10000000000 : ℝ)|^41 ≤ (39294642818311/100000000000000 : ℝ)^33
        have hw : |(4715066417/10000000000 : ℝ)|=(4715066417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-47361051/125000000 : ℝ)|^41 ≤ (7486386637497/25000000000000 : ℝ)^33
        have hw : |(-47361051/125000000 : ℝ)|=(47361051/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1935794669/5000000000 : ℝ)|^41 ≤ (15379905311577/50000000000000 : ℝ)^33
        have hw : |(-1935794669/5000000000 : ℝ)|=(1935794669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s0_7 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-134662837/10000000000 : ℝ)*x 0 + (-8061499617/10000000000 : ℝ)*x 1 + (766345009/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134662837/10000000000 : ℝ)^41 ≤ (236974747621/50000000000000 : ℝ)^33 := by
    have hnat : (134662837 : ℕ)^41*50000000000000^33 ≤ 236974747621^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134662837 10000000000 236974747621 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8061499617/10000000000 : ℝ)^41 ≤ (9563982681969/12500000000000 : ℝ)^33 := by
    have hnat : (8061499617 : ℕ)^41*12500000000000^33 ≤ 9563982681969^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8061499617 10000000000 9563982681969 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (766345009/2500000000 : ℝ)^41 ≤ (23014189038009/100000000000000 : ℝ)^33 := by
    have hnat : (766345009 : ℕ)^41*100000000000000^33 ≤ 23014189038009^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766345009 2500000000 23014189038009 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-134662837/10000000000 : ℝ), (-8061499617/10000000000 : ℝ), (766345009/2500000000 : ℝ)] ![(236974747621/50000000000000 : ℝ), (9563982681969/12500000000000 : ℝ), (23014189038009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-134662837/10000000000 : ℝ)|^41 ≤ (236974747621/50000000000000 : ℝ)^33
        have hw : |(-134662837/10000000000 : ℝ)|=(134662837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8061499617/10000000000 : ℝ)|^41 ≤ (9563982681969/12500000000000 : ℝ)^33
        have hw : |(-8061499617/10000000000 : ℝ)|=(8061499617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(766345009/2500000000 : ℝ)|^41 ≤ (23014189038009/100000000000000 : ℝ)^33
        have hw : |(766345009/2500000000 : ℝ)|=(766345009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s0_8 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1480839537/5000000000 : ℝ)*x 0 + (4528211749/10000000000 : ℝ)*x 1 + (4838796233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1480839537/5000000000 : ℝ)^41 ≤ (551272089099/2500000000000 : ℝ)^33 := by
    have hnat : (1480839537 : ℕ)^41*2500000000000^33 ≤ 551272089099^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1480839537 5000000000 551272089099 2500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4528211749/10000000000 : ℝ)^41 ≤ (37369305332247/100000000000000 : ℝ)^33 := by
    have hnat : (4528211749 : ℕ)^41*100000000000000^33 ≤ 37369305332247^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528211749 10000000000 37369305332247 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4838796233/10000000000 : ℝ)^41 ≤ (2536238192747/6250000000000 : ℝ)^33 := by
    have hnat : (4838796233 : ℕ)^41*6250000000000^33 ≤ 2536238192747^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838796233 10000000000 2536238192747 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1480839537/5000000000 : ℝ), (4528211749/10000000000 : ℝ), (4838796233/10000000000 : ℝ)] ![(551272089099/2500000000000 : ℝ), (37369305332247/100000000000000 : ℝ), (2536238192747/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1480839537/5000000000 : ℝ)|^41 ≤ (551272089099/2500000000000 : ℝ)^33
        have hw : |(1480839537/5000000000 : ℝ)|=(1480839537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4528211749/10000000000 : ℝ)|^41 ≤ (37369305332247/100000000000000 : ℝ)^33
        have hw : |(4528211749/10000000000 : ℝ)|=(4528211749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4838796233/10000000000 : ℝ)|^41 ≤ (2536238192747/6250000000000 : ℝ)^33
        have hw : |(4838796233/10000000000 : ℝ)|=(4838796233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s0_9 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4736175783/10000000000 : ℝ)*x 0 + (-318578509/1250000000 : ℝ)*x 1 + (-199708393/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4736175783/10000000000 : ℝ)^41 ≤ (39513331338147/100000000000000 : ℝ)^33 := by
    have hnat : (4736175783 : ℕ)^41*100000000000000^33 ≤ 39513331338147^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4736175783 10000000000 39513331338147 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (318578509/1250000000 : ℝ)^41 ≤ (3659407315397/20000000000000 : ℝ)^33 := by
    have hnat : (318578509 : ℕ)^41*20000000000000^33 ≤ 3659407315397^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318578509 1250000000 3659407315397 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199708393/400000000 : ℝ)^41 ≤ (42189632072193/100000000000000 : ℝ)^33 := by
    have hnat : (199708393 : ℕ)^41*100000000000000^33 ≤ 42189632072193^33*400000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199708393 400000000 42189632072193 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4736175783/10000000000 : ℝ), (-318578509/1250000000 : ℝ), (-199708393/400000000 : ℝ)] ![(39513331338147/100000000000000 : ℝ), (3659407315397/20000000000000 : ℝ), (42189632072193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4736175783/10000000000 : ℝ)|^41 ≤ (39513331338147/100000000000000 : ℝ)^33
        have hw : |(4736175783/10000000000 : ℝ)|=(4736175783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-318578509/1250000000 : ℝ)|^41 ≤ (3659407315397/20000000000000 : ℝ)^33
        have hw : |(-318578509/1250000000 : ℝ)|=(318578509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199708393/400000000 : ℝ)|^41 ≤ (42189632072193/100000000000000 : ℝ)^33
        have hw : |(-199708393/400000000 : ℝ)|=(199708393/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s0_13 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6575978051/10000000000 : ℝ)*x 0 + (4021363/5000000000 : ℝ)*x 1 + (4838796233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6575978051/10000000000 : ℝ)^41 ≤ (1188117868943/2000000000000 : ℝ)^33 := by
    have hnat : (6575978051 : ℕ)^41*2000000000000^33 ≤ 1188117868943^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6575978051 10000000000 1188117868943 2000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4021363/5000000000 : ℝ)^41 ≤ (446732993/3125000000000 : ℝ)^33 := by
    have hnat : (4021363 : ℕ)^41*3125000000000^33 ≤ 446732993^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021363 5000000000 446732993 3125000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4838796233/10000000000 : ℝ)^41 ≤ (2536238192747/6250000000000 : ℝ)^33 := by
    have hnat : (4838796233 : ℕ)^41*6250000000000^33 ≤ 2536238192747^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838796233 10000000000 2536238192747 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6575978051/10000000000 : ℝ), (4021363/5000000000 : ℝ), (4838796233/10000000000 : ℝ)] ![(1188117868943/2000000000000 : ℝ), (446732993/3125000000000 : ℝ), (2536238192747/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6575978051/10000000000 : ℝ)|^41 ≤ (1188117868943/2000000000000 : ℝ)^33
        have hw : |(6575978051/10000000000 : ℝ)|=(6575978051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4021363/5000000000 : ℝ)|^41 ≤ (446732993/3125000000000 : ℝ)^33
        have hw : |(4021363/5000000000 : ℝ)|=(4021363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4838796233/10000000000 : ℝ)|^41 ≤ (2536238192747/6250000000000 : ℝ)^33
        have hw : |(4838796233/10000000000 : ℝ)|=(4838796233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s0_14 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-27888783/1000000000 : ℝ)*x 0 + (-667050879/1250000000 : ℝ)*x 1 + (93735603/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27888783/1000000000 : ℝ)^41 ≤ (73188697781/6250000000000 : ℝ)^33 := by
    have hnat : (27888783 : ℕ)^41*6250000000000^33 ≤ 73188697781^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27888783 1000000000 73188697781 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (667050879/1250000000 : ℝ)^41 ≤ (45827638707967/100000000000000 : ℝ)^33 := by
    have hnat : (667050879 : ℕ)^41*100000000000000^33 ≤ 45827638707967^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667050879 1250000000 45827638707967 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93735603/156250000 : ℝ)^41 ≤ (5300134211267/10000000000000 : ℝ)^33 := by
    have hnat : (93735603 : ℕ)^41*10000000000000^33 ≤ 5300134211267^33*156250000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93735603 156250000 5300134211267 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27888783/1000000000 : ℝ), (-667050879/1250000000 : ℝ), (93735603/156250000 : ℝ)] ![(73188697781/6250000000000 : ℝ), (45827638707967/100000000000000 : ℝ), (5300134211267/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27888783/1000000000 : ℝ)|^41 ≤ (73188697781/6250000000000 : ℝ)^33
        have hw : |(-27888783/1000000000 : ℝ)|=(27888783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-667050879/1250000000 : ℝ)|^41 ≤ (45827638707967/100000000000000 : ℝ)^33
        have hw : |(-667050879/1250000000 : ℝ)|=(667050879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(93735603/156250000 : ℝ)|^41 ≤ (5300134211267/10000000000000 : ℝ)^33
        have hw : |(93735603/156250000 : ℝ)|=(93735603/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s0_15 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (366776233/1250000000 : ℝ)*x 0 + (4309337999/10000000000 : ℝ)*x 1 + (2537934693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (366776233/1250000000 : ℝ)^41 ≤ (4359414048129/20000000000000 : ℝ)^33 := by
    have hnat : (366776233 : ℕ)^41*20000000000000^33 ≤ 4359414048129^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366776233 1250000000 4359414048129 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4309337999/10000000000 : ℝ)^41 ≤ (2196154213747/6250000000000 : ℝ)^33 := by
    have hnat : (4309337999 : ℕ)^41*6250000000000^33 ≤ 2196154213747^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309337999 10000000000 2196154213747 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2537934693/5000000000 : ℝ)^41 ≤ (43064462320441/100000000000000 : ℝ)^33 := by
    have hnat : (2537934693 : ℕ)^41*100000000000000^33 ≤ 43064462320441^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537934693 5000000000 43064462320441 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(366776233/1250000000 : ℝ), (4309337999/10000000000 : ℝ), (2537934693/5000000000 : ℝ)] ![(4359414048129/20000000000000 : ℝ), (2196154213747/6250000000000 : ℝ), (43064462320441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(366776233/1250000000 : ℝ)|^41 ≤ (4359414048129/20000000000000 : ℝ)^33
        have hw : |(366776233/1250000000 : ℝ)|=(366776233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4309337999/10000000000 : ℝ)|^41 ≤ (2196154213747/6250000000000 : ℝ)^33
        have hw : |(4309337999/10000000000 : ℝ)|=(4309337999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2537934693/5000000000 : ℝ)|^41 ≤ (43064462320441/100000000000000 : ℝ)^33
        have hw : |(2537934693/5000000000 : ℝ)|=(2537934693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s0_16 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1568887771/2500000000 : ℝ)*x 0 + (-1260618969/5000000000 : ℝ)*x 1 + (-3370529421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1568887771/2500000000 : ℝ)^41 ≤ (11210572005383/20000000000000 : ℝ)^33 := by
    have hnat : (1568887771 : ℕ)^41*20000000000000^33 ≤ 11210572005383^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568887771 2500000000 11210572005383 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1260618969/5000000000 : ℝ)^41 ≤ (2256630914423/12500000000000 : ℝ)^33 := by
    have hnat : (1260618969 : ℕ)^41*12500000000000^33 ≤ 2256630914423^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1260618969 5000000000 2256630914423 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3370529421/10000000000 : ℝ)^41 ≤ (6473523161617/25000000000000 : ℝ)^33 := by
    have hnat : (3370529421 : ℕ)^41*25000000000000^33 ≤ 6473523161617^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3370529421 10000000000 6473523161617 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1568887771/2500000000 : ℝ), (-1260618969/5000000000 : ℝ), (-3370529421/10000000000 : ℝ)] ![(11210572005383/20000000000000 : ℝ), (2256630914423/12500000000000 : ℝ), (6473523161617/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1568887771/2500000000 : ℝ)|^41 ≤ (11210572005383/20000000000000 : ℝ)^33
        have hw : |(1568887771/2500000000 : ℝ)|=(1568887771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1260618969/5000000000 : ℝ)|^41 ≤ (2256630914423/12500000000000 : ℝ)^33
        have hw : |(-1260618969/5000000000 : ℝ)|=(1260618969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3370529421/10000000000 : ℝ)|^41 ≤ (6473523161617/25000000000000 : ℝ)^33
        have hw : |(-3370529421/10000000000 : ℝ)|=(3370529421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s0_20 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4618524507/5000000000 : ℝ)*x 0 + (7/10000000000 : ℝ)*x 1 + (1489735317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4618524507/5000000000 : ℝ)^41 ≤ (90610321610007/100000000000000 : ℝ)^33 := by
    have hnat : (4618524507 : ℕ)^41*100000000000000^33 ≤ 90610321610007^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4618524507 5000000000 90610321610007 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7/10000000000 : ℝ)^41 ≤ (423/100000000000000 : ℝ)^33 := by
    have hnat : (7 : ℕ)^41*100000000000000^33 ≤ 423^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7 10000000000 423 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1489735317/10000000000 : ℝ)^41 ≤ (37558713531/400000000000 : ℝ)^33 := by
    have hnat : (1489735317 : ℕ)^41*400000000000^33 ≤ 37558713531^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489735317 10000000000 37558713531 400000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4618524507/5000000000 : ℝ), (7/10000000000 : ℝ), (1489735317/10000000000 : ℝ)] ![(90610321610007/100000000000000 : ℝ), (423/100000000000000 : ℝ), (37558713531/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4618524507/5000000000 : ℝ)|^41 ≤ (90610321610007/100000000000000 : ℝ)^33
        have hw : |(4618524507/5000000000 : ℝ)|=(4618524507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7/10000000000 : ℝ)|^41 ≤ (423/100000000000000 : ℝ)^33
        have hw : |(7/10000000000 : ℝ)|=(7/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1489735317/10000000000 : ℝ)|^41 ≤ (37558713531/400000000000 : ℝ)^33
        have hw : |(1489735317/10000000000 : ℝ)|=(1489735317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s0_21 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-591149283/10000000000 : ℝ)*x 0 + (-2050120347/2500000000 : ℝ)*x 1 + (326554027/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (591149283/10000000000 : ℝ)^41 ≤ (2978014331623/100000000000000 : ℝ)^33 := by
    have hnat : (591149283 : ℕ)^41*100000000000000^33 ≤ 2978014331623^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591149283 10000000000 2978014331623 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050120347/2500000000 : ℝ)^41 ≤ (39077063501809/50000000000000 : ℝ)^33 := by
    have hnat : (2050120347 : ℕ)^41*50000000000000^33 ≤ 39077063501809^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050120347 2500000000 39077063501809 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326554027/1250000000 : ℝ)^41 ≤ (235848233089/1250000000000 : ℝ)^33 := by
    have hnat : (326554027 : ℕ)^41*1250000000000^33 ≤ 235848233089^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326554027 1250000000 235848233089 1250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-591149283/10000000000 : ℝ), (-2050120347/2500000000 : ℝ), (326554027/1250000000 : ℝ)] ![(2978014331623/100000000000000 : ℝ), (39077063501809/50000000000000 : ℝ), (235848233089/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-591149283/10000000000 : ℝ)|^41 ≤ (2978014331623/100000000000000 : ℝ)^33
        have hw : |(-591149283/10000000000 : ℝ)|=(591149283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2050120347/2500000000 : ℝ)|^41 ≤ (39077063501809/50000000000000 : ℝ)^33
        have hw : |(-2050120347/2500000000 : ℝ)|=(2050120347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326554027/1250000000 : ℝ)|^41 ≤ (235848233089/1250000000000 : ℝ)^33
        have hw : |(326554027/1250000000 : ℝ)|=(326554027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s0_22 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3158975943/5000000000 : ℝ)*x 0 + (3267457119/10000000000 : ℝ)*x 1 + (257832257/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3158975943/5000000000 : ℝ)^41 ≤ (56523777516309/100000000000000 : ℝ)^33 := by
    have hnat : (3158975943 : ℕ)^41*100000000000000^33 ≤ 56523777516309^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3158975943 5000000000 56523777516309 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3267457119/10000000000 : ℝ)^41 ≤ (6228487650243/25000000000000 : ℝ)^33 := by
    have hnat : (3267457119 : ℕ)^41*25000000000000^33 ≤ 6228487650243^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3267457119 10000000000 6228487650243 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257832257/1000000000 : ℝ)^41 ≤ (18562271869271/100000000000000 : ℝ)^33 := by
    have hnat : (257832257 : ℕ)^41*100000000000000^33 ≤ 18562271869271^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257832257 1000000000 18562271869271 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3158975943/5000000000 : ℝ), (3267457119/10000000000 : ℝ), (257832257/1000000000 : ℝ)] ![(56523777516309/100000000000000 : ℝ), (6228487650243/25000000000000 : ℝ), (18562271869271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3158975943/5000000000 : ℝ)|^41 ≤ (56523777516309/100000000000000 : ℝ)^33
        have hw : |(3158975943/5000000000 : ℝ)|=(3158975943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3267457119/10000000000 : ℝ)|^41 ≤ (6228487650243/25000000000000 : ℝ)^33
        have hw : |(3267457119/10000000000 : ℝ)|=(3267457119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(257832257/1000000000 : ℝ)|^41 ≤ (18562271869271/100000000000000 : ℝ)^33
        have hw : |(257832257/1000000000 : ℝ)|=(257832257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s0_23 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1123928363/5000000000 : ℝ)*x 0 + (-3135116903/5000000000 : ℝ)*x 1 + (-1812884043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1123928363/5000000000 : ℝ)^41 ≤ (782693327483/5000000000000 : ℝ)^33 := by
    have hnat : (1123928363 : ℕ)^41*5000000000000^33 ≤ 782693327483^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123928363 5000000000 782693327483 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3135116903/5000000000 : ℝ)^41 ≤ (27996929431697/50000000000000 : ℝ)^33 := by
    have hnat : (3135116903 : ℕ)^41*50000000000000^33 ≤ 27996929431697^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3135116903 5000000000 27996929431697 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1812884043/5000000000 : ℝ)^41 ≤ (14176137287391/50000000000000 : ℝ)^33 := by
    have hnat : (1812884043 : ℕ)^41*50000000000000^33 ≤ 14176137287391^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812884043 5000000000 14176137287391 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1123928363/5000000000 : ℝ), (-3135116903/5000000000 : ℝ), (-1812884043/5000000000 : ℝ)] ![(782693327483/5000000000000 : ℝ), (27996929431697/50000000000000 : ℝ), (14176137287391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1123928363/5000000000 : ℝ)|^41 ≤ (782693327483/5000000000000 : ℝ)^33
        have hw : |(1123928363/5000000000 : ℝ)|=(1123928363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3135116903/5000000000 : ℝ)|^41 ≤ (27996929431697/50000000000000 : ℝ)^33
        have hw : |(-3135116903/5000000000 : ℝ)|=(3135116903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1812884043/5000000000 : ℝ)|^41 ≤ (14176137287391/50000000000000 : ℝ)^33
        have hw : |(-1812884043/5000000000 : ℝ)|=(1812884043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s0_27 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8684052837/10000000000 : ℝ)*x 0 + (11787/2500000000 : ℝ)*x 1 + (2296935977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8684052837/10000000000 : ℝ)^41 ≤ (41960175854191/50000000000000 : ℝ)^33 := by
    have hnat : (8684052837 : ℕ)^41*50000000000000^33 ≤ 41960175854191^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8684052837 10000000000 41960175854191 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11787/2500000000 : ℝ)^41 ≤ (1506821/6250000000000 : ℝ)^33 := by
    have hnat : (11787 : ℕ)^41*6250000000000^33 ≤ 1506821^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11787 2500000000 1506821 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2296935977/10000000000 : ℝ)^41 ≤ (4019906043587/25000000000000 : ℝ)^33 := by
    have hnat : (2296935977 : ℕ)^41*25000000000000^33 ≤ 4019906043587^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296935977 10000000000 4019906043587 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8684052837/10000000000 : ℝ), (11787/2500000000 : ℝ), (2296935977/10000000000 : ℝ)] ![(41960175854191/50000000000000 : ℝ), (1506821/6250000000000 : ℝ), (4019906043587/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8684052837/10000000000 : ℝ)|^41 ≤ (41960175854191/50000000000000 : ℝ)^33
        have hw : |(8684052837/10000000000 : ℝ)|=(8684052837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(11787/2500000000 : ℝ)|^41 ≤ (1506821/6250000000000 : ℝ)^33
        have hw : |(11787/2500000000 : ℝ)|=(11787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2296935977/10000000000 : ℝ)|^41 ≤ (4019906043587/25000000000000 : ℝ)^33
        have hw : |(2296935977/10000000000 : ℝ)|=(2296935977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s1_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-426636977/2000000000 : ℝ)*x 0 + (-529497911/1000000000 : ℝ)*x 1 + (4777876623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426636977/2000000000 : ℝ)^41 ≤ (14667926992157/100000000000000 : ℝ)^33 := by
    have hnat : (426636977 : ℕ)^41*100000000000000^33 ≤ 14667926992157^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426636977 2000000000 14667926992157 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529497911/1000000000 : ℝ)^41 ≤ (45386035793711/100000000000000 : ℝ)^33 := by
    have hnat : (529497911 : ℕ)^41*100000000000000^33 ≤ 45386035793711^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529497911 1000000000 45386035793711 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4777876623/10000000000 : ℝ)^41 ≤ (19973018599859/50000000000000 : ℝ)^33 := by
    have hnat : (4777876623 : ℕ)^41*50000000000000^33 ≤ 19973018599859^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4777876623 10000000000 19973018599859 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-426636977/2000000000 : ℝ), (-529497911/1000000000 : ℝ), (4777876623/10000000000 : ℝ)] ![(14667926992157/100000000000000 : ℝ), (45386035793711/100000000000000 : ℝ), (19973018599859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-426636977/2000000000 : ℝ)|^41 ≤ (14667926992157/100000000000000 : ℝ)^33
        have hw : |(-426636977/2000000000 : ℝ)|=(426636977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-529497911/1000000000 : ℝ)|^41 ≤ (45386035793711/100000000000000 : ℝ)^33
        have hw : |(-529497911/1000000000 : ℝ)|=(529497911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4777876623/10000000000 : ℝ)|^41 ≤ (19973018599859/50000000000000 : ℝ)^33
        have hw : |(4777876623/10000000000 : ℝ)|=(4777876623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s1_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (586391121/1250000000 : ℝ)*x 0 + (150446199/400000000 : ℝ)*x 1 + (1962078219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (586391121/1250000000 : ℝ)^41 ≤ (1952347151479/5000000000000 : ℝ)^33 := by
    have hnat : (586391121 : ℕ)^41*5000000000000^33 ≤ 1952347151479^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586391121 1250000000 1952347151479 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150446199/400000000 : ℝ)^41 ≤ (14836750837727/50000000000000 : ℝ)^33 := by
    have hnat : (150446199 : ℕ)^41*50000000000000^33 ≤ 14836750837727^33*400000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150446199 400000000 14836750837727 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1962078219/5000000000 : ℝ)^41 ≤ (31279555287463/100000000000000 : ℝ)^33 := by
    have hnat : (1962078219 : ℕ)^41*100000000000000^33 ≤ 31279555287463^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962078219 5000000000 31279555287463 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(586391121/1250000000 : ℝ), (150446199/400000000 : ℝ), (1962078219/5000000000 : ℝ)] ![(1952347151479/5000000000000 : ℝ), (14836750837727/50000000000000 : ℝ), (31279555287463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(586391121/1250000000 : ℝ)|^41 ≤ (1952347151479/5000000000000 : ℝ)^33
        have hw : |(586391121/1250000000 : ℝ)|=(586391121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(150446199/400000000 : ℝ)|^41 ≤ (14836750837727/50000000000000 : ℝ)^33
        have hw : |(150446199/400000000 : ℝ)|=(150446199/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1962078219/5000000000 : ℝ)|^41 ≤ (31279555287463/100000000000000 : ℝ)^33
        have hw : |(1962078219/5000000000 : ℝ)|=(1962078219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s1_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4455186603/10000000000 : ℝ)*x 0 + (-484760731/1250000000 : ℝ)*x 1 + (-4052341987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4455186603/10000000000 : ℝ)^41 ≤ (36622035602131/100000000000000 : ℝ)^33 := by
    have hnat : (4455186603 : ℕ)^41*100000000000000^33 ≤ 36622035602131^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4455186603 10000000000 36622035602131 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484760731/1250000000 : ℝ)^41 ≤ (15411975587087/50000000000000 : ℝ)^33 := by
    have hnat : (484760731 : ℕ)^41*50000000000000^33 ≤ 15411975587087^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484760731 1250000000 15411975587087 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4052341987/10000000000 : ℝ)^41 ≤ (32554013205559/100000000000000 : ℝ)^33 := by
    have hnat : (4052341987 : ℕ)^41*100000000000000^33 ≤ 32554013205559^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4052341987 10000000000 32554013205559 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4455186603/10000000000 : ℝ), (-484760731/1250000000 : ℝ), (-4052341987/10000000000 : ℝ)] ![(36622035602131/100000000000000 : ℝ), (15411975587087/50000000000000 : ℝ), (32554013205559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4455186603/10000000000 : ℝ)|^41 ≤ (36622035602131/100000000000000 : ℝ)^33
        have hw : |(4455186603/10000000000 : ℝ)|=(4455186603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-484760731/1250000000 : ℝ)|^41 ≤ (15411975587087/50000000000000 : ℝ)^33
        have hw : |(-484760731/1250000000 : ℝ)|=(484760731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4052341987/10000000000 : ℝ)|^41 ≤ (32554013205559/100000000000000 : ℝ)^33
        have hw : |(-4052341987/10000000000 : ℝ)|=(4052341987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s1_3 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4999999993/5000000000 : ℝ)*x 0 + (63/1250000000 : ℝ)*x 1 + (63/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4999999993/5000000000 : ℝ)^41 ≤ (99999999826061/100000000000000 : ℝ)^33 := by
    have hnat : (4999999993 : ℕ)^41*100000000000000^33 ≤ 99999999826061^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999999993 5000000000 99999999826061 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63/1250000000 : ℝ)^41 ≤ (10721/12500000000000 : ℝ)^33 := by
    have hnat : (63 : ℕ)^41*12500000000000^33 ≤ 10721^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63 1250000000 10721 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63/1250000000 : ℝ)^41 ≤ (10721/12500000000000 : ℝ)^33 := by
    have hnat : (63 : ℕ)^41*12500000000000^33 ≤ 10721^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63 1250000000 10721 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4999999993/5000000000 : ℝ), (63/1250000000 : ℝ), (63/1250000000 : ℝ)] ![(99999999826061/100000000000000 : ℝ), (10721/12500000000000 : ℝ), (10721/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4999999993/5000000000 : ℝ)|^41 ≤ (99999999826061/100000000000000 : ℝ)^33
        have hw : |(4999999993/5000000000 : ℝ)|=(4999999993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(63/1250000000 : ℝ)|^41 ≤ (10721/12500000000000 : ℝ)^33
        have hw : |(63/1250000000 : ℝ)|=(63/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(63/1250000000 : ℝ)|^41 ≤ (10721/12500000000000 : ℝ)^33
        have hw : |(63/1250000000 : ℝ)|=(63/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320039_s1_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6852724703/10000000000 : ℝ)*x 0 + (-1175133861/5000000000 : ℝ)*x 1 + (1419810603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6852724703/10000000000 : ℝ)^41 ≤ (31263858085367/50000000000000 : ℝ)^33 := by
    have hnat : (6852724703 : ℕ)^41*50000000000000^33 ≤ 31263858085367^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6852724703 10000000000 31263858085367 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1175133861/5000000000 : ℝ)^41 ≤ (16544777567681/100000000000000 : ℝ)^33 := by
    have hnat : (1175133861 : ℕ)^41*100000000000000^33 ≤ 16544777567681^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175133861 5000000000 16544777567681 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1419810603/5000000000 : ℝ)^41 ≤ (20927506238349/100000000000000 : ℝ)^33 := by
    have hnat : (1419810603 : ℕ)^41*100000000000000^33 ≤ 20927506238349^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419810603 5000000000 20927506238349 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6852724703/10000000000 : ℝ), (-1175133861/5000000000 : ℝ), (1419810603/5000000000 : ℝ)] ![(31263858085367/50000000000000 : ℝ), (16544777567681/100000000000000 : ℝ), (20927506238349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6852724703/10000000000 : ℝ)|^41 ≤ (31263858085367/50000000000000 : ℝ)^33
        have hw : |(6852724703/10000000000 : ℝ)|=(6852724703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1175133861/5000000000 : ℝ)|^41 ≤ (16544777567681/100000000000000 : ℝ)^33
        have hw : |(-1175133861/5000000000 : ℝ)|=(1175133861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1419810603/5000000000 : ℝ)|^41 ≤ (20927506238349/100000000000000 : ℝ)^33
        have hw : |(1419810603/5000000000 : ℝ)|=(1419810603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320039 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80273/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80273/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (1059/625 : ℝ) := by
    linarith only [f.Tcap]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-47390437/400000000 : ℝ)*X 0 0+(-1564788069/2500000000 : ℝ)*X 0 1+(4498506221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1178766603/2500000000 : ℝ)*X 1 0+(953486821/2500000000 : ℝ)*X 1 1+(3846617483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4715066417/10000000000 : ℝ)*X 2 0+(-47361051/125000000 : ℝ)*X 2 1+(-1935794669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-134662837/10000000000 : ℝ)*X 0 0+(-8061499617/10000000000 : ℝ)*X 0 1+(766345009/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1480839537/5000000000 : ℝ)*X 1 0+(4528211749/10000000000 : ℝ)*X 1 1+(4838796233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4736175783/10000000000 : ℝ)*X 2 0+(-318578509/1250000000 : ℝ)*X 2 1+(-199708393/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((6575978051/10000000000 : ℝ)*X 0 0+(4021363/5000000000 : ℝ)*X 0 1+(4838796233/10000000000 : ℝ)*X 0 2+(6575978051/10000000000 : ℝ)*X 1 0+(4021363/5000000000 : ℝ)*X 1 1+(4838796233/10000000000 : ℝ)*X 1 2+(6575978051/10000000000 : ℝ)*X 2 0+(4021363/5000000000 : ℝ)*X 2 1+(4838796233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-27888783/1000000000 : ℝ)*X 0 0+(-667050879/1250000000 : ℝ)*X 0 1+(93735603/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((366776233/1250000000 : ℝ)*X 1 0+(4309337999/10000000000 : ℝ)*X 1 1+(2537934693/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1568887771/2500000000 : ℝ)*X 2 0+(-1260618969/5000000000 : ℝ)*X 2 1+(-3370529421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((4618524507/5000000000 : ℝ)*X 0 0+(7/10000000000 : ℝ)*X 0 1+(1489735317/10000000000 : ℝ)*X 0 2+(4618524507/5000000000 : ℝ)*X 1 0+(7/10000000000 : ℝ)*X 1 1+(1489735317/10000000000 : ℝ)*X 1 2+(4618524507/5000000000 : ℝ)*X 2 0+(7/10000000000 : ℝ)*X 2 1+(1489735317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-591149283/10000000000 : ℝ)*X 0 0+(-2050120347/2500000000 : ℝ)*X 0 1+(326554027/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3158975943/5000000000 : ℝ)*X 1 0+(3267457119/10000000000 : ℝ)*X 1 1+(257832257/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1123928363/5000000000 : ℝ)*X 2 0+(-3135116903/5000000000 : ℝ)*X 2 1+(-1812884043/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((8684052837/10000000000 : ℝ)*X 0 0+(11787/2500000000 : ℝ)*X 0 1+(2296935977/10000000000 : ℝ)*X 0 2+(8684052837/10000000000 : ℝ)*X 1 0+(11787/2500000000 : ℝ)*X 1 1+(2296935977/10000000000 : ℝ)*X 1 2+(8684052837/10000000000 : ℝ)*X 2 0+(11787/2500000000 : ℝ)*X 2 1+(2296935977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((10793/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10793/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9143978585088447311979/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (148251863617/125000000000 : ℝ)*(base3) + (542207973319/500000000000 : ℝ)*(base7) + (14553004659/25000000000 : ℝ)*(base49) + (441626783791/250000000000 : ℝ)*(major_s0_0) + (441626783791/250000000000 : ℝ)*(major_s0_1) + (441626783791/250000000000 : ℝ)*(major_s0_2) + (3152563/500000000000 : ℝ)*(sp_s0_2) + (1979497382851/1000000000000 : ℝ)*(sp_s0_7) + (3165416101483/1000000000000 : ℝ)*(sp_s0_8) + (197948453581/100000000000 : ℝ)*(sp_s0_9) + (839434031077/1000000000000 : ℝ)*(sp_s0_13) + (1664521/500000000000 : ℝ)*(sp_s0_14) + (49759673/500000000000 : ℝ)*(sp_s0_15) + (9870957/1000000000000 : ℝ)*(sp_s0_23) + (7528263947/8000000000 : ℝ)*(f.failure) + (1979500711893/1000000000000 : ℝ)*(f.sum) + (190630064880641/1250000000000000000000000000 : ℝ)*base63 + (371373123853993/2500000000000000000000000000 : ℝ)*base65 + (693359643146007/2500000000000000000000000000 : ℝ)*base67 + (559501115869359/2500000000000000000000000000 : ℝ)*base68 + (227871148382683/1250000000000000000000000000 : ℝ)*base70 + (754747762396007/2500000000000000000000000000 : ℝ)*base72 + (486214582869359/2500000000000000000000000000 : ℝ)*base74 + (537402747380641/2500000000000000000000000000 : ℝ)*base77 + (6224025199/10000000000000000000000 : ℝ)*base79 + (9/20000000000000 : ℝ)*base86 + (9/20000000000000 : ℝ)*base88 + (9/20000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-48359/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-48359/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5064784303955845726473/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (171835649679/250000000000 : ℝ)*(base7) + (1102297/1000000000000 : ℝ)*(base34) + (90434126623/125000000000 : ℝ)*(base40) + (3159979/500000000000 : ℝ)*(base53) + (2304260800347/1000000000000 : ℝ)*(major_s0_0) + (576065475661/250000000000 : ℝ)*(major_s0_1) + (1152127791343/500000000000 : ℝ)*(major_s0_2) + (18672537/1000000000000 : ℝ)*(sp_s0_0) + (2109953/250000000000 : ℝ)*(sp_s0_1) + (748196460169/250000000000 : ℝ)*(sp_s0_14) + (1496398587849/500000000000 : ℝ)*(sp_s0_15) + (748202983867/250000000000 : ℝ)*(sp_s0_16) + (1914811987483/1000000000000 : ℝ)*(sp_s0_20) + (5784873/200000000000 : ℝ)*(sp_s0_27) + (1227499415429/1000000000000 : ℝ)*(f.failure) + (748202983867/250000000000 : ℝ)*(f.sum) + (33981111545083/1000000000000000000000000000 : ℝ)*base63 + (6702807131821112711/5000000000000000000000000000 : ℝ)*base64 + (356928010343003/2500000000000000000000000000 : ℝ)*base66 + (1884148322971393/5000000000000000000000000000 : ℝ)*base69 + (107258687176125709/80000000000000000000000000 : ℝ)*base70 + (3119031124533581/10000000000000000000000000000 : ℝ)*base73 + (375708117377011/2500000000000000000000000000 : ℝ)*base75 + (13408776225036488203/10000000000000000000000000000 : ℝ)*base76 + (4610715320161569/10000000000000000000000000000 : ℝ)*base79 + (1703/2500000000000000 : ℝ)*base86 + (1703/2500000000000000 : ℝ)*base88 + (1703/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2799/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2799/4000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (43138112414446613755641/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (132996004693/500000000000 : ℝ)*(base3) + (240699949463/200000000000 : ℝ)*(base7) + (149323297479/500000000000 : ℝ)*(base40) + (1393671/100000000000 : ℝ)*(base43) + (134313/15625000000 : ℝ)*(base49) + (928172999379/500000000000 : ℝ)*(major_s0_0) + (58010376939/31250000000 : ℝ)*(major_s0_1) + (928172999379/500000000000 : ℝ)*(major_s0_2) + (19736213/1000000000000 : ℝ)*(sp_s0_2) + (143272177/1000000000000 : ℝ)*(sp_s0_20) + (408808950217/200000000000 : ℝ)*(sp_s0_21) + (115502534859/50000000000 : ℝ)*(sp_s0_22) + (2044025014871/1000000000000 : ℝ)*(sp_s0_23) + (60195480201/31250000000 : ℝ)*(sp_s0_27) + (988890900681/1000000000000 : ℝ)*(f.failure) + (408811737559/200000000000 : ℝ)*(f.sum) + (3290060234081453/5000000000000000000000000000 : ℝ)*base63 + (358699699275083/5000000000000000000000000000 : ℝ)*base64 + (128212286096953/312500000000000000000000000 : ℝ)*base67 + (5428047920412029/5000000000000000000000000000 : ℝ)*base69 + (592674646068473/2500000000000000000000000000 : ℝ)*base71 + (2119042011724917/5000000000000000000000000000 : ℝ)*base73 + (349963714479339/312500000000000000000000000 : ℝ)*base75 + (2779847363087971/5000000000000000000000000000 : ℝ)*base76 + (230501278844767/1000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (933/2500000000000000 : ℝ)*base87 + (933/2500000000000000 : ℝ)*base89 + (933/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (10793/20000 : ℝ) ^ (5 : ℝ) ≤ (4576789168841701163/100000000000000000000 : ℝ) := by
    have hpowers : (10793/20000 : ℝ)^5 ≤ (4576789168841701163/100000000000000000000 : ℝ)^1 := by
      have hnat : (10793 : ℕ)^5*100000000000000000000^1 ≤ 4576789168841701163^1*20000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10793 20000 4576789168841701163 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10793/20000 : ℝ)) (X := (4576789168841701163/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0a : (104576789168841701163/100000000000000000000 : ℝ) ≤ (5044952308115273/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (104576789168841701163/100000000000000000000 : ℝ)^1 ≤ (5044952308115273/5000000000000000 : ℝ)^5 := by
      have hnat : (104576789168841701163 : ℕ)^1*5000000000000000^5 ≤ 5044952308115273^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104576789168841701163 100000000000000000000 5044952308115273 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5044952308115273/5000000000000000 : ℝ)) (X := (104576789168841701163/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0b : (54576789168841701163/50000000000000000000 : ℝ) ≤ (10176714608482857/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (54576789168841701163/50000000000000000000 : ℝ)^1 ≤ (10176714608482857/10000000000000000 : ℝ)^5 := by
      have hnat : (54576789168841701163 : ℕ)^1*10000000000000000^5 ≤ 10176714608482857^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54576789168841701163 50000000000000000000 10176714608482857 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10176714608482857/10000000000000000 : ℝ)) (X := (54576789168841701163/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(44952308115273/2698250000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(86809992252311/5396500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (10793/20000 : ℝ)) (alpha := (44952308115273/2698250000000000 : ℝ)) (beta := (86809992252311/5396500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (10793/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(44952308115273/2698250000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(86809992252311/5396500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (48359/100000 : ℝ) ^ (5 : ℝ) ≤ (165297610505691363/6250000000000000000 : ℝ) := by
    have hpowers : (48359/100000 : ℝ)^5 ≤ (165297610505691363/6250000000000000000 : ℝ)^1 := by
      have hnat : (48359 : ℕ)^5*6250000000000000000^1 ≤ 165297610505691363^1*100000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48359 100000 165297610505691363 6250000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48359/100000 : ℝ)) (X := (165297610505691363/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1a : (6415297610505691363/6250000000000000000 : ℝ) ≤ (1005234437277267/1000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (6415297610505691363/6250000000000000000 : ℝ)^1 ≤ (1005234437277267/1000000000000000 : ℝ)^5 := by
      have hnat : (6415297610505691363 : ℕ)^1*1000000000000000^5 ≤ 1005234437277267^5*6250000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6415297610505691363 6250000000000000000 1005234437277267 1000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1005234437277267/1000000000000000 : ℝ)) (X := (6415297610505691363/6250000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1b : (3290297610505691363/3125000000000000000 : ℝ) ≤ (31573814547387/31250000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3290297610505691363/3125000000000000000 : ℝ)^1 ≤ (31573814547387/31250000000000 : ℝ)^5 := by
      have hnat : (3290297610505691363 : ℕ)^1*31250000000000^5 ≤ 31573814547387^5*3125000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3290297610505691363 3125000000000000000 31573814547387 31250000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31573814547387/31250000000000 : ℝ)) (X := (3290297610505691363/3125000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(5234437277267/483590000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(5127628239117/483590000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (48359/100000 : ℝ)) (alpha := (5234437277267/483590000000000 : ℝ)) (beta := (5127628239117/483590000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (48359/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(5234437277267/483590000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(5127628239117/483590000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (2799/4000 : ℝ) ^ (5 : ℝ) ≤ (1677700892984511709/10000000000000000000 : ℝ) := by
    have hpowers : (2799/4000 : ℝ)^5 ≤ (1677700892984511709/10000000000000000000 : ℝ)^1 := by
      have hnat : (2799 : ℕ)^5*10000000000000000000^1 ≤ 1677700892984511709^1*4000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2799 4000 1677700892984511709 10000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2799/4000 : ℝ)) (X := (1677700892984511709/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2a : (11677700892984511709/10000000000000000000 : ℝ) ≤ (2063010626965481/2000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (11677700892984511709/10000000000000000000 : ℝ)^1 ≤ (2063010626965481/2000000000000000 : ℝ)^5 := by
      have hnat : (11677700892984511709 : ℕ)^1*2000000000000000^5 ≤ 2063010626965481^5*10000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11677700892984511709 10000000000000000000 2063010626965481 2000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2063010626965481/2000000000000000 : ℝ)) (X := (11677700892984511709/10000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2b : (6677700892984511709/5000000000000000000 : ℝ) ≤ (5297871203048799/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (6677700892984511709/5000000000000000000 : ℝ)^1 ≤ (5297871203048799/5000000000000000 : ℝ)^5 := by
      have hnat : (6677700892984511709 : ℕ)^1*5000000000000000^5 ≤ 5297871203048799^5*5000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6677700892984511709 5000000000000000000 5297871203048799 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5297871203048799/5000000000000000 : ℝ)) (X := (6677700892984511709/5000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(21003542321827/466500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(280689271270193/6997500000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (2799/4000 : ℝ)) (alpha := (21003542321827/466500000000000 : ℝ)) (beta := (280689271270193/6997500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (2799/4000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(21003542321827/466500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(280689271270193/6997500000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-426636977/2000000000 : ℝ)*X 0 0+(-529497911/1000000000 : ℝ)*X 0 1+(4777876623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((586391121/1250000000 : ℝ)*X 1 0+(150446199/400000000 : ℝ)*X 1 1+(1962078219/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4455186603/10000000000 : ℝ)*X 2 0+(-484760731/1250000000 : ℝ)*X 2 1+(-4052341987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_3 : ((4999999993/5000000000 : ℝ)*X 1 0+(63/1250000000 : ℝ)*X 1 1+(63/1250000000 : ℝ)*X 1 2+(4999999993/5000000000 : ℝ)*X 2 0+(63/1250000000 : ℝ)*X 2 1+(63/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s1_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6852724703/10000000000 : ℝ)*X 0 0+(-1175133861/5000000000 : ℝ)*X 0 1+(1419810603/5000000000 : ℝ)*X 0 2+(6852724703/10000000000 : ℝ)*X 1 0+(-1175133861/5000000000 : ℝ)*X 1 1+(1419810603/5000000000 : ℝ)*X 1 2+(6852724703/10000000000 : ℝ)*X 2 0+(-1175133861/5000000000 : ℝ)*X 2 1+(1419810603/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320039_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-10329/1250 : ℝ) < ((-4693/2500 : ℝ)*P 0+(-4693/2500 : ℝ)*P 1+(-4693/2500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-10329/1250 : ℝ) < (-3683030324450353890386390843443/451189470000000000000000000000 : ℝ) := by norm_num
    linear_combination (3911/500000000000 : ℝ)*(base1) + (65493/500000000000 : ℝ)*(base19) + (88359/1000000000000 : ℝ)*(base22) + (17391/1000000000000 : ℝ)*(base24) + (555680638777/1000000000000 : ℝ)*(base40) + (8540111471/31250000000 : ℝ)*(base49) + (31530285827/250000000000 : ℝ)*(base59) + (938600179257/500000000000 : ℝ)*(major_s1_0) + (4693/2500 : ℝ)*(major_s1_1) + (4693/2500 : ℝ)*(major_s1_2) + (340122293397/125000000000 : ℝ)*(sp_s1_0) + (2720978208369/1000000000000 : ℝ)*(sp_s1_1) + (544195646721/200000000000 : ℝ)*(sp_s1_2) + (179257/500000000000 : ℝ)*(sp_s1_3) + (499999996089/500000000000 : ℝ)*(sp_s1_6) + (544195667871/200000000000 : ℝ)*(f.sum) + (39777324483813911/225594735000000000000000000000 : ℝ)*base63 + (3715203429769/6997500000000000000000000 : ℝ)*base64 + (61439222657889/120897500000000000000000000 : ℝ)*base67 + (242866610771/933000000000000000000000 : ℝ)*base69 + (1800204093738187847/7552401750000000000000000000000 : ℝ)*base70 + (325508432621523/2698250000000000000000000000 : ℝ)*base72 + (237000301412673/483590000000000000000000000 : ℝ)*base75 + (218368202410911/1349125000000000000000000000 : ℝ)*base77 + (21527713617051135359/65242335875000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c320040_s0_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2939361941/10000000000 : ℝ)*x 0 + (-2347050671/5000000000 : ℝ)*x 1 + (-293381339/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2939361941/10000000000 : ℝ)^41 ≤ (21844631308173/100000000000000 : ℝ)^33 := by
    have hnat : (2939361941 : ℕ)^41*100000000000000^33 ≤ 21844631308173^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2939361941 10000000000 21844631308173 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2347050671/5000000000 : ℝ)^41 ≤ (39077683915891/100000000000000 : ℝ)^33 := by
    have hnat : (2347050671 : ℕ)^41*100000000000000^33 ≤ 39077683915891^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2347050671 5000000000 39077683915891 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (293381339/625000000 : ℝ)^41 ≤ (2442355297751/6250000000000 : ℝ)^33 := by
    have hnat : (293381339 : ℕ)^41*6250000000000^33 ≤ 2442355297751^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293381339 625000000 2442355297751 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2939361941/10000000000 : ℝ), (-2347050671/5000000000 : ℝ), (-293381339/625000000 : ℝ)] ![(21844631308173/100000000000000 : ℝ), (39077683915891/100000000000000 : ℝ), (2442355297751/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2939361941/10000000000 : ℝ)|^41 ≤ (21844631308173/100000000000000 : ℝ)^33
        have hw : |(-2939361941/10000000000 : ℝ)|=(2939361941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2347050671/5000000000 : ℝ)|^41 ≤ (39077683915891/100000000000000 : ℝ)^33
        have hw : |(-2347050671/5000000000 : ℝ)|=(2347050671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-293381339/625000000 : ℝ)|^41 ≤ (2442355297751/6250000000000 : ℝ)^33
        have hw : |(-293381339/625000000 : ℝ)|=(293381339/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320040_s0_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2939361941/10000000000 : ℝ)*x 0 + (2347050671/5000000000 : ℝ)*x 1 + (-293381339/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2939361941/10000000000 : ℝ)^41 ≤ (21844631308173/100000000000000 : ℝ)^33 := by
    have hnat : (2939361941 : ℕ)^41*100000000000000^33 ≤ 21844631308173^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2939361941 10000000000 21844631308173 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2347050671/5000000000 : ℝ)^41 ≤ (39077683915891/100000000000000 : ℝ)^33 := by
    have hnat : (2347050671 : ℕ)^41*100000000000000^33 ≤ 39077683915891^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2347050671 5000000000 39077683915891 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (293381339/625000000 : ℝ)^41 ≤ (2442355297751/6250000000000 : ℝ)^33 := by
    have hnat : (293381339 : ℕ)^41*6250000000000^33 ≤ 2442355297751^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293381339 625000000 2442355297751 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2939361941/10000000000 : ℝ), (2347050671/5000000000 : ℝ), (-293381339/625000000 : ℝ)] ![(21844631308173/100000000000000 : ℝ), (39077683915891/100000000000000 : ℝ), (2442355297751/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2939361941/10000000000 : ℝ)|^41 ≤ (21844631308173/100000000000000 : ℝ)^33
        have hw : |(2939361941/10000000000 : ℝ)|=(2939361941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2347050671/5000000000 : ℝ)|^41 ≤ (39077683915891/100000000000000 : ℝ)^33
        have hw : |(2347050671/5000000000 : ℝ)|=(2347050671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-293381339/625000000 : ℝ)|^41 ≤ (2442355297751/6250000000000 : ℝ)^33
        have hw : |(-293381339/625000000 : ℝ)|=(293381339/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320040_s0_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5799121203/10000000000 : ℝ)*x 0 + (-3233460237/10000000000 : ℝ)*x 1 + (1616730147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5799121203/10000000000 : ℝ)^41 ≤ (50815411034459/100000000000000 : ℝ)^33 := by
    have hnat : (5799121203 : ℕ)^41*100000000000000^33 ≤ 50815411034459^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5799121203 10000000000 50815411034459 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3233460237/10000000000 : ℝ)^41 ≤ (12296147102143/50000000000000 : ℝ)^33 := by
    have hnat : (3233460237 : ℕ)^41*50000000000000^33 ≤ 12296147102143^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3233460237 10000000000 12296147102143 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1616730147/5000000000 : ℝ)^41 ≤ (12296147371449/50000000000000 : ℝ)^33 := by
    have hnat : (1616730147 : ℕ)^41*50000000000000^33 ≤ 12296147371449^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616730147 5000000000 12296147371449 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5799121203/10000000000 : ℝ), (-3233460237/10000000000 : ℝ), (1616730147/5000000000 : ℝ)] ![(50815411034459/100000000000000 : ℝ), (12296147102143/50000000000000 : ℝ), (12296147371449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5799121203/10000000000 : ℝ)|^41 ≤ (50815411034459/100000000000000 : ℝ)^33
        have hw : |(5799121203/10000000000 : ℝ)|=(5799121203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3233460237/10000000000 : ℝ)|^41 ≤ (12296147102143/50000000000000 : ℝ)^33
        have hw : |(-3233460237/10000000000 : ℝ)|=(3233460237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1616730147/5000000000 : ℝ)|^41 ≤ (12296147371449/50000000000000 : ℝ)^33
        have hw : |(1616730147/5000000000 : ℝ)|=(1616730147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320040_s0_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5799121203/10000000000 : ℝ)*x 0 + (-3233460237/10000000000 : ℝ)*x 1 + (-1616730147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5799121203/10000000000 : ℝ)^41 ≤ (50815411034459/100000000000000 : ℝ)^33 := by
    have hnat : (5799121203 : ℕ)^41*100000000000000^33 ≤ 50815411034459^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5799121203 10000000000 50815411034459 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3233460237/10000000000 : ℝ)^41 ≤ (12296147102143/50000000000000 : ℝ)^33 := by
    have hnat : (3233460237 : ℕ)^41*50000000000000^33 ≤ 12296147102143^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3233460237 10000000000 12296147102143 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1616730147/5000000000 : ℝ)^41 ≤ (12296147371449/50000000000000 : ℝ)^33 := by
    have hnat : (1616730147 : ℕ)^41*50000000000000^33 ≤ 12296147371449^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616730147 5000000000 12296147371449 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5799121203/10000000000 : ℝ), (-3233460237/10000000000 : ℝ), (-1616730147/5000000000 : ℝ)] ![(50815411034459/100000000000000 : ℝ), (12296147102143/50000000000000 : ℝ), (12296147371449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5799121203/10000000000 : ℝ)|^41 ≤ (50815411034459/100000000000000 : ℝ)^33
        have hw : |(5799121203/10000000000 : ℝ)|=(5799121203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3233460237/10000000000 : ℝ)|^41 ≤ (12296147102143/50000000000000 : ℝ)^33
        have hw : |(-3233460237/10000000000 : ℝ)|=(3233460237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1616730147/5000000000 : ℝ)|^41 ≤ (12296147371449/50000000000000 : ℝ)^33
        have hw : |(-1616730147/5000000000 : ℝ)|=(1616730147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320040 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80273/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80273/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2939361941/10000000000 : ℝ)*X 0 0+(-2347050671/5000000000 : ℝ)*X 0 1+(-293381339/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320040_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2939361941/10000000000 : ℝ)*X 1 0+(2347050671/5000000000 : ℝ)*X 1 1+(-293381339/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320040_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5799121203/10000000000 : ℝ)*X 2 0+(-3233460237/10000000000 : ℝ)*X 2 1+(1616730147/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320040_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((5799121203/10000000000 : ℝ)*X 0 0+(-3233460237/10000000000 : ℝ)*X 0 1+(-1616730147/5000000000 : ℝ)*X 0 2+(5799121203/10000000000 : ℝ)*X 1 0+(-3233460237/10000000000 : ℝ)*X 1 1+(-1616730147/5000000000 : ℝ)*X 1 2+(5799121203/10000000000 : ℝ)*X 2 0+(-3233460237/10000000000 : ℝ)*X 2 1+(-1616730147/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320040_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-10329/1250 : ℝ) < ((-4693/2500 : ℝ)*P 0+(-4693/2500 : ℝ)*P 1+(-4693/2500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-10329/1250 : ℝ) < (-40775776397936962069741880697/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (469365289361/500000000000 : ℝ)*(base5) + (76953/500000000000 : ℝ)*(base10) + (397470065857/500000000000 : ℝ)*(base39) + (12366826661/31250000000 : ℝ)*(base40) + (399201759767/1000000000000 : ℝ)*(base49) + (5001/250000000000 : ℝ)*(base53) + (763500808651/1000000000000 : ℝ)*(base60) + (4693/2500 : ℝ)*(major_s0_0) + (1877200024061/1000000000000 : ℝ)*(major_s0_1) + (469299994999/250000000000 : ℝ)*(major_s0_2) + (2718384847099/1000000000000 : ℝ)*(sp_s0_0) + (1359192512533/500000000000 : ℝ)*(sp_s0_1) + (365711559973/100000000000 : ℝ)*(sp_s0_2) + (3063472267/50000000000 : ℝ)*(sp_s0_6) + (2718385021009/1000000000000 : ℝ)*(f.sum) + (118288916503363/2000000000000000000000000000 : ℝ)*base63 + (516035979799823/2500000000000000000000000000 : ℝ)*base65 + (4891419589026203/10000000000000000000000000000 : ℝ)*base67 + (175269820225351/2500000000000000000000000000 : ℝ)*base69 + (378023922299823/2500000000000000000000000000 : ℝ)*base71 + (378669943/1250000000000000000000 : ℝ)*base73 + (893526173384589/10000000000000000000000000000 : ℝ)*base74 + (364077879/1000000000000000000000 : ℝ)*base77 + (650865593026203/10000000000000000000000000000 : ℝ)*base79 + (24061/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base84 + (24061/1000000000000 : ℝ)*base88 + (12031/500000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p020_b021 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 39 ≤ c.val) (hhi : c.val < 41)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=39 ∨ c=40 := by omega
  rcases hc with rfl|rfl
  · exact collision_c320039 p hpa (by linarith only [hpb]) X hX
  · exact collision_c320040 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 39 ≤ c.val) (hhi : c.val < 41)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b021 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

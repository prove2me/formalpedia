-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b032
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:02:54.896291+00:00
-- url     : https://prove2.me/submissions/3805b37a-4e92-4c76-9a36-dec023f99200

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
theorem collision_support_c325059_s0_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2929126157/10000000000 : ℝ)*x 0 + (29291273/100000000 : ℝ)*x 1 + (193494403/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2929126157/10000000000 : ℝ)^87 ≤ (22210911217669/100000000000000 : ℝ)^71 := by
    have hnat : (2929126157 : ℕ)^87*100000000000000^71 ≤ 22210911217669^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2929126157 10000000000 22210911217669 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (29291273/100000000 : ℝ)^87 ≤ (1388182614871/6250000000000 : ℝ)^71 := by
    have hnat : (29291273 : ℕ)^87*6250000000000^71 ≤ 1388182614871^71*100000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29291273 100000000 1388182614871 6250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (193494403/312500000 : ℝ)^87 ≤ (55578166930079/100000000000000 : ℝ)^71 := by
    have hnat : (193494403 : ℕ)^87*100000000000000^71 ≤ 55578166930079^71*312500000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193494403 312500000 55578166930079 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2929126157/10000000000 : ℝ), (29291273/100000000 : ℝ), (193494403/312500000 : ℝ)] ![(22210911217669/100000000000000 : ℝ), (1388182614871/6250000000000 : ℝ), (55578166930079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2929126157/10000000000 : ℝ)|^87 ≤ (22210911217669/100000000000000 : ℝ)^71
        have hw : |(-2929126157/10000000000 : ℝ)|=(2929126157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(29291273/100000000 : ℝ)|^87 ≤ (1388182614871/6250000000000 : ℝ)^71
        have hw : |(29291273/100000000 : ℝ)|=(29291273/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(193494403/312500000 : ℝ)|^87 ≤ (55578166930079/100000000000000 : ℝ)^71
        have hw : |(193494403/312500000 : ℝ)|=(193494403/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s0_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (732281521/2500000000 : ℝ)*x 0 + (-183070477/625000000 : ℝ)*x 1 + (3095910339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (732281521/2500000000 : ℝ)^87 ≤ (2776363817423/12500000000000 : ℝ)^71 := by
    have hnat : (732281521 : ℕ)^87*12500000000000^71 ≤ 2776363817423^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732281521 2500000000 2776363817423 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183070477/625000000 : ℝ)^87 ≤ (22210924922739/100000000000000 : ℝ)^71 := by
    have hnat : (183070477 : ℕ)^87*100000000000000^71 ≤ 22210924922739^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183070477 625000000 22210924922739 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3095910339/5000000000 : ℝ)^87 ≤ (55578164532333/100000000000000 : ℝ)^71 := by
    have hnat : (3095910339 : ℕ)^87*100000000000000^71 ≤ 55578164532333^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3095910339 5000000000 55578164532333 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(732281521/2500000000 : ℝ), (-183070477/625000000 : ℝ), (3095910339/5000000000 : ℝ)] ![(2776363817423/12500000000000 : ℝ), (22210924922739/100000000000000 : ℝ), (55578164532333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(732281521/2500000000 : ℝ)|^87 ≤ (2776363817423/12500000000000 : ℝ)^71
        have hw : |(732281521/2500000000 : ℝ)|=(732281521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-183070477/625000000 : ℝ)|^87 ≤ (22210924922739/100000000000000 : ℝ)^71
        have hw : |(-183070477/625000000 : ℝ)|=(183070477/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3095910339/5000000000 : ℝ)|^87 ≤ (55578164532333/100000000000000 : ℝ)^71
        have hw : |(3095910339/5000000000 : ℝ)|=(3095910339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s0_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2902439841/10000000000 : ℝ)*x 0 + (3188739671/5000000000 : ℝ)*x 1 + (2733783457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2902439841/10000000000 : ℝ)^87 ≤ (171587566649/781250000000 : ℝ)^71 := by
    have hnat : (2902439841 : ℕ)^87*781250000000^71 ≤ 171587566649^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2902439841 10000000000 171587566649 781250000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3188739671/5000000000 : ℝ)^87 ≤ (28813520057757/50000000000000 : ℝ)^71 := by
    have hnat : (3188739671 : ℕ)^87*50000000000000^71 ≤ 28813520057757^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3188739671 5000000000 28813520057757 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733783457/10000000000 : ℝ)^87 ≤ (4081950268613/20000000000000 : ℝ)^71 := by
    have hnat : (2733783457 : ℕ)^87*20000000000000^71 ≤ 4081950268613^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733783457 10000000000 4081950268613 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2902439841/10000000000 : ℝ), (3188739671/5000000000 : ℝ), (2733783457/10000000000 : ℝ)] ![(171587566649/781250000000 : ℝ), (28813520057757/50000000000000 : ℝ), (4081950268613/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2902439841/10000000000 : ℝ)|^87 ≤ (171587566649/781250000000 : ℝ)^71
        have hw : |(2902439841/10000000000 : ℝ)|=(2902439841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3188739671/5000000000 : ℝ)|^87 ≤ (28813520057757/50000000000000 : ℝ)^71
        have hw : |(3188739671/5000000000 : ℝ)|=(3188739671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733783457/10000000000 : ℝ)|^87 ≤ (4081950268613/20000000000000 : ℝ)^71
        have hw : |(2733783457/10000000000 : ℝ)|=(2733783457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s0_7 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-44849437/200000000 : ℝ)*x 0 + (513733223/10000000000 : ℝ)*x 1 + (4225200713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44849437/200000000 : ℝ)^87 ≤ (400269009417/2500000000000 : ℝ)^71 := by
    have hnat : (44849437 : ℕ)^87*2500000000000^71 ≤ 400269009417^71*200000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44849437 200000000 400269009417 2500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513733223/10000000000 : ℝ)^87 ≤ (21051819879/800000000000 : ℝ)^71 := by
    have hnat : (513733223 : ℕ)^87*800000000000^71 ≤ 21051819879^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513733223 10000000000 21051819879 800000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225200713/5000000000 : ℝ)^87 ≤ (40678881067379/50000000000000 : ℝ)^71 := by
    have hnat : (4225200713 : ℕ)^87*50000000000000^71 ≤ 40678881067379^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225200713 5000000000 40678881067379 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44849437/200000000 : ℝ), (513733223/10000000000 : ℝ), (4225200713/5000000000 : ℝ)] ![(400269009417/2500000000000 : ℝ), (21051819879/800000000000 : ℝ), (40678881067379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44849437/200000000 : ℝ)|^87 ≤ (400269009417/2500000000000 : ℝ)^71
        have hw : |(-44849437/200000000 : ℝ)|=(44849437/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513733223/10000000000 : ℝ)|^87 ≤ (21051819879/800000000000 : ℝ)^71
        have hw : |(513733223/10000000000 : ℝ)|=(513733223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225200713/5000000000 : ℝ)|^87 ≤ (40678881067379/50000000000000 : ℝ)^71
        have hw : |(4225200713/5000000000 : ℝ)|=(4225200713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s0_8 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1554702141/10000000000 : ℝ)*x 0 + (-331862943/2500000000 : ℝ)*x 1 + (4225200009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1554702141/10000000000 : ℝ)^87 ≤ (102207598621/1000000000000 : ℝ)^71 := by
    have hnat : (1554702141 : ℕ)^87*1000000000000^71 ≤ 102207598621^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554702141 10000000000 102207598621 1000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (331862943/2500000000 : ℝ)^87 ≤ (105268682489/1250000000000 : ℝ)^71 := by
    have hnat : (331862943 : ℕ)^87*1250000000000^71 ≤ 105268682489^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331862943 2500000000 105268682489 1250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225200009/5000000000 : ℝ)^87 ≤ (81357745524163/100000000000000 : ℝ)^71 := by
    have hnat : (4225200009 : ℕ)^87*100000000000000^71 ≤ 81357745524163^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225200009 5000000000 81357745524163 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1554702141/10000000000 : ℝ), (-331862943/2500000000 : ℝ), (4225200009/5000000000 : ℝ)] ![(102207598621/1000000000000 : ℝ), (105268682489/1250000000000 : ℝ), (81357745524163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1554702141/10000000000 : ℝ)|^87 ≤ (102207598621/1000000000000 : ℝ)^71
        have hw : |(1554702141/10000000000 : ℝ)|=(1554702141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-331862943/2500000000 : ℝ)|^87 ≤ (105268682489/1250000000000 : ℝ)^71
        have hw : |(-331862943/2500000000 : ℝ)|=(331862943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225200009/5000000000 : ℝ)|^87 ≤ (81357745524163/100000000000000 : ℝ)^71
        have hw : |(4225200009/5000000000 : ℝ)|=(4225200009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s0_9 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (129524647/312500000 : ℝ)*x 0 + (3562520567/5000000000 : ℝ)*x 1 + (-2093507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129524647/312500000 : ℝ)^87 ≤ (6797289202223/20000000000000 : ℝ)^71 := by
    have hnat : (129524647 : ℕ)^87*20000000000000^71 ≤ 6797289202223^71*312500000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129524647 312500000 6797289202223 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3562520567/5000000000 : ℝ)^87 ≤ (66010451018793/100000000000000 : ℝ)^71 := by
    have hnat : (3562520567 : ℕ)^87*100000000000000^71 ≤ 66010451018793^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3562520567 5000000000 66010451018793 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2093507/10000000000 : ℝ)^87 ≤ (387869569/12500000000000 : ℝ)^71 := by
    have hnat : (2093507 : ℕ)^87*12500000000000^71 ≤ 387869569^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093507 10000000000 387869569 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129524647/312500000 : ℝ), (3562520567/5000000000 : ℝ), (-2093507/10000000000 : ℝ)] ![(6797289202223/20000000000000 : ℝ), (66010451018793/100000000000000 : ℝ), (387869569/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129524647/312500000 : ℝ)|^87 ≤ (6797289202223/20000000000000 : ℝ)^71
        have hw : |(129524647/312500000 : ℝ)|=(129524647/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3562520567/5000000000 : ℝ)|^87 ≤ (66010451018793/100000000000000 : ℝ)^71
        have hw : |(3562520567/5000000000 : ℝ)|=(3562520567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2093507/10000000000 : ℝ)|^87 ≤ (387869569/12500000000000 : ℝ)^71
        have hw : |(-2093507/10000000000 : ℝ)|=(2093507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s0_13 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (474725591/2500000000 : ℝ)*x 0 + (4072263281/5000000000 : ℝ)*x 1 + (56953661/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (474725591/2500000000 : ℝ)^87 ≤ (13059052856997/100000000000000 : ℝ)^71 := by
    have hnat : (474725591 : ℕ)^87*100000000000000^71 ≤ 13059052856997^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474725591 2500000000 13059052856997 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4072263281/5000000000 : ℝ)^87 ≤ (19441030532161/25000000000000 : ℝ)^71 := by
    have hnat : (4072263281 : ℕ)^87*25000000000000^71 ≤ 19441030532161^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4072263281 5000000000 19441030532161 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56953661/400000000 : ℝ)^87 ≤ (4588412500939/50000000000000 : ℝ)^71 := by
    have hnat : (56953661 : ℕ)^87*50000000000000^71 ≤ 4588412500939^71*400000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56953661 400000000 4588412500939 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(474725591/2500000000 : ℝ), (4072263281/5000000000 : ℝ), (56953661/400000000 : ℝ)] ![(13059052856997/100000000000000 : ℝ), (19441030532161/25000000000000 : ℝ), (4588412500939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(474725591/2500000000 : ℝ)|^87 ≤ (13059052856997/100000000000000 : ℝ)^71
        have hw : |(474725591/2500000000 : ℝ)|=(474725591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4072263281/5000000000 : ℝ)|^87 ≤ (19441030532161/25000000000000 : ℝ)^71
        have hw : |(4072263281/5000000000 : ℝ)|=(4072263281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56953661/400000000 : ℝ)|^87 ≤ (4588412500939/50000000000000 : ℝ)^71
        have hw : |(56953661/400000000 : ℝ)|=(56953661/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s0_14 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-905107279/10000000000 : ℝ)*x 0 + (1838336649/10000000000 : ℝ)*x 1 + (4260108193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (905107279/10000000000 : ℝ)^87 ≤ (2633663080537/50000000000000 : ℝ)^71 := by
    have hnat : (905107279 : ℕ)^87*50000000000000^71 ≤ 2633663080537^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905107279 10000000000 2633663080537 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1838336649/10000000000 : ℝ)^87 ≤ (12550518704917/100000000000000 : ℝ)^71 := by
    have hnat : (1838336649 : ℕ)^87*100000000000000^71 ≤ 12550518704917^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1838336649 10000000000 12550518704917 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4260108193/5000000000 : ℝ)^87 ≤ (3287286204933/4000000000000 : ℝ)^71 := by
    have hnat : (4260108193 : ℕ)^87*4000000000000^71 ≤ 3287286204933^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260108193 5000000000 3287286204933 4000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-905107279/10000000000 : ℝ), (1838336649/10000000000 : ℝ), (4260108193/5000000000 : ℝ)] ![(2633663080537/50000000000000 : ℝ), (12550518704917/100000000000000 : ℝ), (3287286204933/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-905107279/10000000000 : ℝ)|^87 ≤ (2633663080537/50000000000000 : ℝ)^71
        have hw : |(-905107279/10000000000 : ℝ)|=(905107279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1838336649/10000000000 : ℝ)|^87 ≤ (12550518704917/100000000000000 : ℝ)^71
        have hw : |(1838336649/10000000000 : ℝ)|=(1838336649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4260108193/5000000000 : ℝ)|^87 ≤ (3287286204933/4000000000000 : ℝ)^71
        have hw : |(4260108193/5000000000 : ℝ)|=(4260108193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s0_15 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (813302593/10000000000 : ℝ)*x 0 + (-383062913/2000000000 : ℝ)*x 1 + (1704043273/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (813302593/10000000000 : ℝ)^87 ≤ (1155088305379/25000000000000 : ℝ)^71 := by
    have hnat : (813302593 : ℕ)^87*25000000000000^71 ≤ 1155088305379^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      813302593 10000000000 1155088305379 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (383062913/2000000000 : ℝ)^87 ≤ (2639498378933/20000000000000 : ℝ)^71 := by
    have hnat : (383062913 : ℕ)^87*20000000000000^71 ≤ 2639498378933^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383062913 2000000000 2639498378933 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1704043273/2000000000 : ℝ)^87 ≤ (41091077437561/50000000000000 : ℝ)^71 := by
    have hnat : (1704043273 : ℕ)^87*50000000000000^71 ≤ 41091077437561^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704043273 2000000000 41091077437561 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(813302593/10000000000 : ℝ), (-383062913/2000000000 : ℝ), (1704043273/2000000000 : ℝ)] ![(1155088305379/25000000000000 : ℝ), (2639498378933/20000000000000 : ℝ), (41091077437561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(813302593/10000000000 : ℝ)|^87 ≤ (1155088305379/25000000000000 : ℝ)^71
        have hw : |(813302593/10000000000 : ℝ)|=(813302593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-383062913/2000000000 : ℝ)|^87 ≤ (2639498378933/20000000000000 : ℝ)^71
        have hw : |(-383062913/2000000000 : ℝ)|=(383062913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1704043273/2000000000 : ℝ)|^87 ≤ (41091077437561/50000000000000 : ℝ)^71
        have hw : |(1704043273/2000000000 : ℝ)|=(1704043273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s0_16 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1056977127/1250000000 : ℝ)*x 0 + (506363787/2000000000 : ℝ)*x 1 + (-242207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056977127/1250000000 : ℝ)^87 ≤ (20355414019437/25000000000000 : ℝ)^71 := by
    have hnat : (1056977127 : ℕ)^87*25000000000000^71 ≤ 20355414019437^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056977127 1250000000 20355414019437 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506363787/2000000000 : ℝ)^87 ≤ (18577827645231/100000000000000 : ℝ)^71 := by
    have hnat : (506363787 : ℕ)^87*100000000000000^71 ≤ 18577827645231^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506363787 2000000000 18577827645231 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (242207/5000000000 : ℝ)^87 ≤ (516263179/100000000000000 : ℝ)^71 := by
    have hnat : (242207 : ℕ)^87*100000000000000^71 ≤ 516263179^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242207 5000000000 516263179 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056977127/1250000000 : ℝ), (506363787/2000000000 : ℝ), (-242207/5000000000 : ℝ)] ![(20355414019437/25000000000000 : ℝ), (18577827645231/100000000000000 : ℝ), (516263179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056977127/1250000000 : ℝ)|^87 ≤ (20355414019437/25000000000000 : ℝ)^71
        have hw : |(1056977127/1250000000 : ℝ)|=(1056977127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506363787/2000000000 : ℝ)|^87 ≤ (18577827645231/100000000000000 : ℝ)^71
        have hw : |(506363787/2000000000 : ℝ)|=(506363787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-242207/5000000000 : ℝ)|^87 ≤ (516263179/100000000000000 : ℝ)^71
        have hw : |(-242207/5000000000 : ℝ)|=(242207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s0_20 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3364601849/5000000000 : ℝ)*x 0 + (3359728779/10000000000 : ℝ)*x 1 + (1793792037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3364601849/5000000000 : ℝ)^87 ≤ (3077265231179/5000000000000 : ℝ)^71 := by
    have hnat : (3364601849 : ℕ)^87*5000000000000^71 ≤ 3077265231179^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3364601849 5000000000 3077265231179 5000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3359728779/10000000000 : ℝ)^87 ≤ (328447444823/1250000000000 : ℝ)^71 := by
    have hnat : (3359728779 : ℕ)^87*1250000000000^71 ≤ 328447444823^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3359728779 10000000000 328447444823 1250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1793792037/10000000000 : ℝ)^87 ≤ (12178899763779/100000000000000 : ℝ)^71 := by
    have hnat : (1793792037 : ℕ)^87*100000000000000^71 ≤ 12178899763779^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793792037 10000000000 12178899763779 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3364601849/5000000000 : ℝ), (3359728779/10000000000 : ℝ), (1793792037/10000000000 : ℝ)] ![(3077265231179/5000000000000 : ℝ), (328447444823/1250000000000 : ℝ), (12178899763779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3364601849/5000000000 : ℝ)|^87 ≤ (3077265231179/5000000000000 : ℝ)^71
        have hw : |(3364601849/5000000000 : ℝ)|=(3364601849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3359728779/10000000000 : ℝ)|^87 ≤ (328447444823/1250000000000 : ℝ)^71
        have hw : |(3359728779/10000000000 : ℝ)|=(3359728779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1793792037/10000000000 : ℝ)|^87 ≤ (12178899763779/100000000000000 : ℝ)^71
        have hw : |(1793792037/10000000000 : ℝ)|=(1793792037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s0_21 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5554179579/10000000000 : ℝ)*x 0 + (404132637/2000000000 : ℝ)*x 1 + (1116930093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5554179579/10000000000 : ℝ)^87 ≤ (48648502482903/100000000000000 : ℝ)^71 := by
    have hnat : (5554179579 : ℕ)^87*100000000000000^71 ≤ 48648502482903^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5554179579 10000000000 48648502482903 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404132637/2000000000 : ℝ)^87 ≤ (14092418071027/100000000000000 : ℝ)^71 := by
    have hnat : (404132637 : ℕ)^87*100000000000000^71 ≤ 14092418071027^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404132637 2000000000 14092418071027 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1116930093/2500000000 : ℝ)^87 ≤ (37259079438331/100000000000000 : ℝ)^71 := by
    have hnat : (1116930093 : ℕ)^87*100000000000000^71 ≤ 37259079438331^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116930093 2500000000 37259079438331 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5554179579/10000000000 : ℝ), (404132637/2000000000 : ℝ), (1116930093/2500000000 : ℝ)] ![(48648502482903/100000000000000 : ℝ), (14092418071027/100000000000000 : ℝ), (37259079438331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5554179579/10000000000 : ℝ)|^87 ≤ (48648502482903/100000000000000 : ℝ)^71
        have hw : |(-5554179579/10000000000 : ℝ)|=(5554179579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(404132637/2000000000 : ℝ)|^87 ≤ (14092418071027/100000000000000 : ℝ)^71
        have hw : |(404132637/2000000000 : ℝ)|=(404132637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1116930093/2500000000 : ℝ)|^87 ≤ (37259079438331/100000000000000 : ℝ)^71
        have hw : |(1116930093/2500000000 : ℝ)|=(1116930093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s0_22 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1660997207/10000000000 : ℝ)*x 0 + (-1071292261/5000000000 : ℝ)*x 1 + (3900970279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1660997207/10000000000 : ℝ)^87 ≤ (1385438972419/12500000000000 : ℝ)^71 := by
    have hnat : (1660997207 : ℕ)^87*12500000000000^71 ≤ 1385438972419^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1660997207 10000000000 1385438972419 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1071292261/5000000000 : ℝ)^87 ≤ (3785327225963/25000000000000 : ℝ)^71 := by
    have hnat : (1071292261 : ℕ)^87*25000000000000^71 ≤ 3785327225963^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071292261 5000000000 3785327225963 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3900970279/5000000000 : ℝ)^87 ≤ (73775179305339/100000000000000 : ℝ)^71 := by
    have hnat : (3900970279 : ℕ)^87*100000000000000^71 ≤ 73775179305339^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3900970279 5000000000 73775179305339 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1660997207/10000000000 : ℝ), (-1071292261/5000000000 : ℝ), (3900970279/5000000000 : ℝ)] ![(1385438972419/12500000000000 : ℝ), (3785327225963/25000000000000 : ℝ), (73775179305339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1660997207/10000000000 : ℝ)|^87 ≤ (1385438972419/12500000000000 : ℝ)^71
        have hw : |(1660997207/10000000000 : ℝ)|=(1660997207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1071292261/5000000000 : ℝ)|^87 ≤ (3785327225963/25000000000000 : ℝ)^71
        have hw : |(-1071292261/5000000000 : ℝ)|=(1071292261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3900970279/5000000000 : ℝ)|^87 ≤ (73775179305339/100000000000000 : ℝ)^71
        have hw : |(3900970279/5000000000 : ℝ)|=(3900970279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s0_23 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8553056289/10000000000 : ℝ)*x 0 + (2403362877/10000000000 : ℝ)*x 1 + (-11281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8553056289/10000000000 : ℝ)^87 ≤ (82570464657297/100000000000000 : ℝ)^71 := by
    have hnat : (8553056289 : ℕ)^87*100000000000000^71 ≤ 82570464657297^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8553056289 10000000000 82570464657297 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2403362877/10000000000 : ℝ)^87 ≤ (17429530182541/100000000000000 : ℝ)^71 := by
    have hnat : (2403362877 : ℕ)^87*100000000000000^71 ≤ 17429530182541^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2403362877 10000000000 17429530182541 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11281/10000000000 : ℝ)^87 ≤ (5152661/100000000000000 : ℝ)^71 := by
    have hnat : (11281 : ℕ)^87*100000000000000^71 ≤ 5152661^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11281 10000000000 5152661 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8553056289/10000000000 : ℝ), (2403362877/10000000000 : ℝ), (-11281/10000000000 : ℝ)] ![(82570464657297/100000000000000 : ℝ), (17429530182541/100000000000000 : ℝ), (5152661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8553056289/10000000000 : ℝ)|^87 ≤ (82570464657297/100000000000000 : ℝ)^71
        have hw : |(8553056289/10000000000 : ℝ)|=(8553056289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2403362877/10000000000 : ℝ)|^87 ≤ (17429530182541/100000000000000 : ℝ)^71
        have hw : |(2403362877/10000000000 : ℝ)|=(2403362877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11281/10000000000 : ℝ)|^87 ≤ (5152661/100000000000000 : ℝ)^71
        have hw : |(-11281/10000000000 : ℝ)|=(11281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s0_27 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1036999917/10000000000 : ℝ)*x 0 + (1716346971/2000000000 : ℝ)*x 1 + (1634519397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036999917/10000000000 : ℝ)^87 ≤ (777843792491/12500000000000 : ℝ)^71 := by
    have hnat : (1036999917 : ℕ)^87*12500000000000^71 ≤ 777843792491^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036999917 10000000000 777843792491 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1716346971/2000000000 : ℝ)^87 ≤ (82909844184137/100000000000000 : ℝ)^71 := by
    have hnat : (1716346971 : ℕ)^87*100000000000000^71 ≤ 82909844184137^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1716346971 2000000000 82909844184137 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1634519397/10000000000 : ℝ)^87 ≤ (10867405469621/100000000000000 : ℝ)^71 := by
    have hnat : (1634519397 : ℕ)^87*100000000000000^71 ≤ 10867405469621^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1634519397 10000000000 10867405469621 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036999917/10000000000 : ℝ), (1716346971/2000000000 : ℝ), (1634519397/10000000000 : ℝ)] ![(777843792491/12500000000000 : ℝ), (82909844184137/100000000000000 : ℝ), (10867405469621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036999917/10000000000 : ℝ)|^87 ≤ (777843792491/12500000000000 : ℝ)^71
        have hw : |(1036999917/10000000000 : ℝ)|=(1036999917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1716346971/2000000000 : ℝ)|^87 ≤ (82909844184137/100000000000000 : ℝ)^71
        have hw : |(1716346971/2000000000 : ℝ)|=(1716346971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1634519397/10000000000 : ℝ)|^87 ≤ (10867405469621/100000000000000 : ℝ)^71
        have hw : |(1634519397/10000000000 : ℝ)|=(1634519397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s1_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-161322893/500000000 : ℝ)*x 0 + (1612183211/5000000000 : ℝ)*x 1 + (1420202581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161322893/500000000 : ℝ)^87 ≤ (25004395685821/100000000000000 : ℝ)^71 := by
    have hnat : (161322893 : ℕ)^87*100000000000000^71 ≤ 25004395685821^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161322893 500000000 25004395685821 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1612183211/5000000000 : ℝ)^87 ≤ (390383380599/1562500000000 : ℝ)^71 := by
    have hnat : (1612183211 : ℕ)^87*1562500000000^71 ≤ 390383380599^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1612183211 5000000000 390383380599 1562500000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1420202581/2500000000 : ℝ)^87 ≤ (12502766986593/25000000000000 : ℝ)^71 := by
    have hnat : (1420202581 : ℕ)^87*25000000000000^71 ≤ 12502766986593^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1420202581 2500000000 12502766986593 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-161322893/500000000 : ℝ), (1612183211/5000000000 : ℝ), (1420202581/2500000000 : ℝ)] ![(25004395685821/100000000000000 : ℝ), (390383380599/1562500000000 : ℝ), (12502766986593/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-161322893/500000000 : ℝ)|^87 ≤ (25004395685821/100000000000000 : ℝ)^71
        have hw : |(-161322893/500000000 : ℝ)|=(161322893/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1612183211/5000000000 : ℝ)|^87 ≤ (390383380599/1562500000000 : ℝ)^71
        have hw : |(1612183211/5000000000 : ℝ)|=(1612183211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1420202581/2500000000 : ℝ)|^87 ≤ (12502766986593/25000000000000 : ℝ)^71
        have hw : |(1420202581/2500000000 : ℝ)|=(1420202581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s1_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3224529627/10000000000 : ℝ)*x 0 + (-1611200507/5000000000 : ℝ)*x 1 + (5684237207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3224529627/10000000000 : ℝ)^87 ≤ (249860859731/1000000000000 : ℝ)^71 := by
    have hnat : (3224529627 : ℕ)^87*1000000000000^71 ≤ 249860859731^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3224529627 10000000000 249860859731 1000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1611200507/5000000000 : ℝ)^87 ≤ (1248293819947/5000000000000 : ℝ)^71 := by
    have hnat : (1611200507 : ℕ)^87*5000000000000^71 ≤ 1248293819947^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1611200507 5000000000 1248293819947 5000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5684237207/10000000000 : ℝ)^87 ≤ (50048037612999/100000000000000 : ℝ)^71 := by
    have hnat : (5684237207 : ℕ)^87*100000000000000^71 ≤ 50048037612999^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5684237207 10000000000 50048037612999 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3224529627/10000000000 : ℝ), (-1611200507/5000000000 : ℝ), (5684237207/10000000000 : ℝ)] ![(249860859731/1000000000000 : ℝ), (1248293819947/5000000000000 : ℝ), (50048037612999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3224529627/10000000000 : ℝ)|^87 ≤ (249860859731/1000000000000 : ℝ)^71
        have hw : |(3224529627/10000000000 : ℝ)|=(3224529627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1611200507/5000000000 : ℝ)|^87 ≤ (1248293819947/5000000000000 : ℝ)^71
        have hw : |(-1611200507/5000000000 : ℝ)|=(1611200507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5684237207/10000000000 : ℝ)|^87 ≤ (50048037612999/100000000000000 : ℝ)^71
        have hw : |(5684237207/10000000000 : ℝ)|=(5684237207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s1_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5536422261/10000000000 : ℝ)*x 0 + (1082015567/2000000000 : ℝ)*x 1 + (-196664483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5536422261/10000000000 : ℝ)^87 ≤ (48457986582289/100000000000000 : ℝ)^71 := by
    have hnat : (5536422261 : ℕ)^87*100000000000000^71 ≤ 48457986582289^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5536422261 10000000000 48457986582289 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082015567/2000000000 : ℝ)^87 ≤ (368019127863/781250000000 : ℝ)^71 := by
    have hnat : (1082015567 : ℕ)^87*781250000000^71 ≤ 368019127863^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082015567 2000000000 368019127863 781250000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196664483/2500000000 : ℝ)^87 ≤ (4331606483/97656250000 : ℝ)^71 := by
    have hnat : (196664483 : ℕ)^87*97656250000^71 ≤ 4331606483^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196664483 2500000000 4331606483 97656250000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5536422261/10000000000 : ℝ), (1082015567/2000000000 : ℝ), (-196664483/2500000000 : ℝ)] ![(48457986582289/100000000000000 : ℝ), (368019127863/781250000000 : ℝ), (4331606483/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5536422261/10000000000 : ℝ)|^87 ≤ (48457986582289/100000000000000 : ℝ)^71
        have hw : |(5536422261/10000000000 : ℝ)|=(5536422261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082015567/2000000000 : ℝ)|^87 ≤ (368019127863/781250000000 : ℝ)^71
        have hw : |(1082015567/2000000000 : ℝ)|=(1082015567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-196664483/2500000000 : ℝ)|^87 ≤ (4331606483/97656250000 : ℝ)^71
        have hw : |(-196664483/2500000000 : ℝ)|=(196664483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325059_s1_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4109849177/10000000000 : ℝ)*x 0 + (1125701719/2500000000 : ℝ)*x 1 + (1807688247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4109849177/10000000000 : ℝ)^87 ≤ (33635720240951/100000000000000 : ℝ)^71 := by
    have hnat : (4109849177 : ℕ)^87*100000000000000^71 ≤ 33635720240951^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109849177 10000000000 33635720240951 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125701719/2500000000 : ℝ)^87 ≤ (37617943933129/100000000000000 : ℝ)^71 := by
    have hnat : (1125701719 : ℕ)^87*100000000000000^71 ≤ 37617943933129^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125701719 2500000000 37617943933129 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1807688247/5000000000 : ℝ)^87 ≤ (3593291975797/12500000000000 : ℝ)^71 := by
    have hnat : (1807688247 : ℕ)^87*12500000000000^71 ≤ 3593291975797^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1807688247 5000000000 3593291975797 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4109849177/10000000000 : ℝ), (1125701719/2500000000 : ℝ), (1807688247/5000000000 : ℝ)] ![(33635720240951/100000000000000 : ℝ), (37617943933129/100000000000000 : ℝ), (3593291975797/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4109849177/10000000000 : ℝ)|^87 ≤ (33635720240951/100000000000000 : ℝ)^71
        have hw : |(4109849177/10000000000 : ℝ)|=(4109849177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125701719/2500000000 : ℝ)|^87 ≤ (37617943933129/100000000000000 : ℝ)^71
        have hw : |(1125701719/2500000000 : ℝ)|=(1125701719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1807688247/5000000000 : ℝ)|^87 ≤ (3593291975797/12500000000000 : ℝ)^71
        have hw : |(1807688247/5000000000 : ℝ)|=(1807688247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325059 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81317/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81317/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (33069/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1393691857257931/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1393691857257931/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2929126157/10000000000 : ℝ)*X 0 0+(29291273/100000000 : ℝ)*X 0 1+(193494403/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((732281521/2500000000 : ℝ)*X 1 0+(-183070477/625000000 : ℝ)*X 1 1+(3095910339/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((2902439841/10000000000 : ℝ)*X 0 0+(3188739671/5000000000 : ℝ)*X 0 1+(2733783457/10000000000 : ℝ)*X 0 2+(2902439841/10000000000 : ℝ)*X 1 0+(3188739671/5000000000 : ℝ)*X 1 1+(2733783457/10000000000 : ℝ)*X 1 2+(2902439841/10000000000 : ℝ)*X 2 0+(3188739671/5000000000 : ℝ)*X 2 1+(2733783457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-44849437/200000000 : ℝ)*X 0 0+(513733223/10000000000 : ℝ)*X 0 1+(4225200713/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1554702141/10000000000 : ℝ)*X 1 0+(-331862943/2500000000 : ℝ)*X 1 1+(4225200009/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((129524647/312500000 : ℝ)*X 2 0+(3562520567/5000000000 : ℝ)*X 2 1+(-2093507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((474725591/2500000000 : ℝ)*X 0 0+(4072263281/5000000000 : ℝ)*X 0 1+(56953661/400000000 : ℝ)*X 0 2+(474725591/2500000000 : ℝ)*X 1 0+(4072263281/5000000000 : ℝ)*X 1 1+(56953661/400000000 : ℝ)*X 1 2+(474725591/2500000000 : ℝ)*X 2 0+(4072263281/5000000000 : ℝ)*X 2 1+(56953661/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-905107279/10000000000 : ℝ)*X 0 0+(1838336649/10000000000 : ℝ)*X 0 1+(4260108193/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((813302593/10000000000 : ℝ)*X 1 0+(-383062913/2000000000 : ℝ)*X 1 1+(1704043273/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1056977127/1250000000 : ℝ)*X 2 0+(506363787/2000000000 : ℝ)*X 2 1+(-242207/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((3364601849/5000000000 : ℝ)*X 0 0+(3359728779/10000000000 : ℝ)*X 0 1+(1793792037/10000000000 : ℝ)*X 0 2+(3364601849/5000000000 : ℝ)*X 1 0+(3359728779/10000000000 : ℝ)*X 1 1+(1793792037/10000000000 : ℝ)*X 1 2+(3364601849/5000000000 : ℝ)*X 2 0+(3359728779/10000000000 : ℝ)*X 2 1+(1793792037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-5554179579/10000000000 : ℝ)*X 0 0+(404132637/2000000000 : ℝ)*X 0 1+(1116930093/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1660997207/10000000000 : ℝ)*X 1 0+(-1071292261/5000000000 : ℝ)*X 1 1+(3900970279/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((8553056289/10000000000 : ℝ)*X 2 0+(2403362877/10000000000 : ℝ)*X 2 1+(-11281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1036999917/10000000000 : ℝ)*X 0 0+(1716346971/2000000000 : ℝ)*X 0 1+(1634519397/10000000000 : ℝ)*X 0 2+(1036999917/10000000000 : ℝ)*X 1 0+(1716346971/2000000000 : ℝ)*X 1 1+(1634519397/10000000000 : ℝ)*X 1 2+(1036999917/10000000000 : ℝ)*X 2 0+(1716346971/2000000000 : ℝ)*X 2 1+(1634519397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((68227/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68227/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (37593684471286744964133/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1167150976053/1000000000000 : ℝ)*(base7) + (93061/500000000000 : ℝ)*(base59) + (1337/15625000000 : ℝ)*(base60) + (754736160973/500000000000 : ℝ)*(major_s0_0) + (754736160973/500000000000 : ℝ)*(major_s0_1) + (754736160973/500000000000 : ℝ)*(major_s0_2) + (1158749/500000000000 : ℝ)*(sp_s0_0) + (2312617/1000000000000 : ℝ)*(sp_s0_6) + (1624410607917/1000000000000 : ℝ)*(sp_s0_7) + (64978205493/40000000000 : ℝ)*(sp_s0_8) + (64978205493/40000000000 : ℝ)*(sp_s0_9) + (959154666209/500000000000 : ℝ)*(sp_s0_13) + (4221191/100000000000 : ℝ)*(sp_s0_14) + (48564639/1000000000000 : ℝ)*(sp_s0_27) + (751209233621/1000000000000 : ℝ)*(f.failure) + (64978205493/40000000000 : ℝ)*(f.sum) + (1930110243/5000000000000000000000 : ℝ)*base62 + (1336267416991563/5000000000000000000000000000 : ℝ)*base65 + (1438630688991563/5000000000000000000000000000 : ℝ)*base67 + (60378515426863/5000000000000000000000000000 : ℝ)*base68 + (8983852209213/2500000000000000000000000000 : ℝ)*base71 + (1328837318991563/5000000000000000000000000000 : ℝ)*base73 + (1400788690926863/5000000000000000000000000000 : ℝ)*base75 + (429817684426863/5000000000000000000000000000 : ℝ)*base77 + (109005286758437/2500000000000000000000000000 : ℝ)*base78 + (29881/100000000000000000 : ℝ)*base86 + (29881/100000000000000000 : ℝ)*base88 + (29881/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16979/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16979/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10798049566907085777747/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (411492518247/1000000000000 : ℝ)*(base5) + (232989256807/200000000000 : ℝ)*(base7) + (263563/125000000000 : ℝ)*(base19) + (75741/500000000000 : ℝ)*(base53) + (35284788469/250000000000 : ℝ)*(base60) + (369177533029/250000000000 : ℝ)*(major_s0_0) + (369177533029/250000000000 : ℝ)*(major_s0_1) + (738354990317/500000000000 : ℝ)*(major_s0_2) + (44216353/1000000000000 : ℝ)*(sp_s0_8) + (1576452400273/1000000000000 : ℝ)*(sp_s0_14) + (315281215083/200000000000 : ℝ)*(sp_s0_15) + (993904439179/500000000000 : ℝ)*(sp_s0_16) + (1488358454333/1000000000000 : ℝ)*(sp_s0_20) + (34047911/250000000000 : ℝ)*(sp_s0_23) + (146980937709/200000000000 : ℝ)*(f.failure) + (315290510351/200000000000 : ℝ)*(f.sum) + (1921957560548129/5000000000000000000000000000 : ℝ)*base62 + (1721546436479573/5000000000000000000000000000 : ℝ)*base64 + (83049811523901/2500000000000000000000000000 : ℝ)*base66 + (1479932827454127/5000000000000000000000000000 : ℝ)*base68 + (84754804122943/200000000000000000000000000 : ℝ)*base70 + (2054753325726099/2500000000000000000000000000 : ℝ)*base73 + (122747055202999/2500000000000000000000000000 : ℝ)*base75 + (143010643452999/2500000000000000000000000000 : ℝ)*base77 + (3882154898901/1250000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (11249/20000000000000000 : ℝ)*base86 + (11249/20000000000000000 : ℝ)*base88 + (11249/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(50603/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(50603/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (118844639397980003409/12500000000000000000000000 : ℝ) := by norm_num
    linear_combination (4827311853/8000000000 : ℝ)*(base7) + (1184301/500000000000 : ℝ)*(base40) + (12497929137/20000000000 : ℝ)*(base44) + (750275607/7812500000 : ℝ)*(base50) + (749568703271/500000000000 : ℝ)*(major_s0_0) + (218560237423/250000000000 : ℝ)*(major_s0_1) + (749568703271/500000000000 : ℝ)*(major_s0_2) + (19966083/500000000000 : ℝ)*(sp_s0_1) + (4552477/100000000000 : ℝ)*(sp_s0_13) + (44068233/200000000000 : ℝ)*(sp_s0_16) + (11997713151/6250000000 : ℝ)*(sp_s0_21) + (161837214393/125000000000 : ℝ)*(sp_s0_22) + (383882752599/200000000000 : ℝ)*(sp_s0_23) + (181134480941/250000000000 : ℝ)*(sp_s0_27) + (746065923759/1000000000000 : ℝ)*(f.failure) + (11997713151/6250000000 : ℝ)*(f.sum) + (74799473795547/200000000000000000000000000 : ℝ)*base62 + (1812036859560799/5000000000000000000000000000 : ℝ)*base64 + (122569421971513/2500000000000000000000000000 : ℝ)*base67 + (419321760392301/5000000000000000000000000000 : ℝ)*base68 + (390793284584249/2500000000000000000000000000 : ℝ)*base70 + (460473691439201/5000000000000000000000000000 : ℝ)*base73 + (671368155998187/2500000000000000000000000000 : ℝ)*base74 + (1876945974607699/5000000000000000000000000000 : ℝ)*base76 + (693242476882227/5000000000000000000000000000 : ℝ)*base79 + (9701/100000000000000000 : ℝ)*base87 + (9701/100000000000000000 : ℝ)*base89 + (9701/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (68227/100000 : ℝ) ^ (85/16 : ℝ) ≤ (2623751553368161041/20000000000000000000 : ℝ) := by
    have hpowers : (68227/100000 : ℝ)^85 ≤ (2623751553368161041/20000000000000000000 : ℝ)^16 := by
      have hnat : (68227 : ℕ)^85*20000000000000000000^16 ≤ 2623751553368161041^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68227 100000 2623751553368161041 20000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68227/100000 : ℝ)) (X := (2623751553368161041/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (22623751553368161041/20000000000000000000 : ℝ) ≤ (10234746877447777/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (22623751553368161041/20000000000000000000 : ℝ)^16 ≤ (10234746877447777/10000000000000000 : ℝ)^85 := by
      have hnat : (22623751553368161041 : ℕ)^16*10000000000000000^85 ≤ 10234746877447777^85*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22623751553368161041 20000000000000000000 10234746877447777 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10234746877447777/10000000000000000 : ℝ)) (X := (22623751553368161041/20000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (12623751553368161041/10000000000000000000 : ℝ) ≤ (5224169265612307/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (12623751553368161041/10000000000000000000 : ℝ)^16 ≤ (5224169265612307/5000000000000000 : ℝ)^85 := by
      have hnat : (12623751553368161041 : ℕ)^16*5000000000000000^85 ≤ 5224169265612307^85*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12623751553368161041 10000000000000000000 5224169265612307 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5224169265612307/5000000000000000 : ℝ)) (X := (12623751553368161041/10000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(234746877447777/6822700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(213591653776837/6822700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (68227/100000 : ℝ)) (alpha := (234746877447777/6822700000000000 : ℝ)) (beta := (213591653776837/6822700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (68227/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(234746877447777/6822700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(213591653776837/6822700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (16979/25000 : ℝ) ^ (85/16 : ℝ) ≤ (3201045063729095419/25000000000000000000 : ℝ) := by
    have hpowers : (16979/25000 : ℝ)^85 ≤ (3201045063729095419/25000000000000000000 : ℝ)^16 := by
      have hnat : (16979 : ℕ)^85*25000000000000000000^16 ≤ 3201045063729095419^16*25000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16979 25000 3201045063729095419 25000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16979/25000 : ℝ)) (X := (3201045063729095419/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (28201045063729095419/25000000000000000000 : ℝ) ≤ (511469160427059/500000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (28201045063729095419/25000000000000000000 : ℝ)^16 ≤ (511469160427059/500000000000000 : ℝ)^85 := by
      have hnat : (28201045063729095419 : ℕ)^16*500000000000000^85 ≤ 511469160427059^85*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28201045063729095419 25000000000000000000 511469160427059 500000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (511469160427059/500000000000000 : ℝ)) (X := (28201045063729095419/25000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (15701045063729095419/12500000000000000000 : ℝ) ≤ (2609629144804977/2500000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (15701045063729095419/12500000000000000000 : ℝ)^16 ≤ (2609629144804977/2500000000000000 : ℝ)^85 := by
      have hnat : (15701045063729095419 : ℕ)^16*2500000000000000^85 ≤ 2609629144804977^85*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15701045063729095419 12500000000000000000 2609629144804977 2500000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2609629144804977/2500000000000000 : ℝ)) (X := (15701045063729095419/12500000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(11469160427059/339580000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(26141671334841/848950000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (16979/25000 : ℝ)) (alpha := (11469160427059/339580000000000 : ℝ)) (beta := (26141671334841/848950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (16979/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(11469160427059/339580000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(26141671334841/848950000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (50603/100000 : ℝ) ^ (85/16 : ℝ) ≤ (268186187558093869/10000000000000000000 : ℝ) := by
    have hpowers : (50603/100000 : ℝ)^85 ≤ (268186187558093869/10000000000000000000 : ℝ)^16 := by
      have hnat : (50603 : ℕ)^85*10000000000000000000^16 ≤ 268186187558093869^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50603 100000 268186187558093869 10000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (50603/100000 : ℝ)) (X := (268186187558093869/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (10268186187558093869/10000000000000000000 : ℝ) ≤ (10049941333463957/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (10268186187558093869/10000000000000000000 : ℝ)^16 ≤ (10049941333463957/10000000000000000 : ℝ)^85 := by
      have hnat : (10268186187558093869 : ℕ)^16*10000000000000000^85 ≤ 10049941333463957^85*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10268186187558093869 10000000000000000000 10049941333463957 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10049941333463957/10000000000000000 : ℝ)) (X := (10268186187558093869/10000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (5268186187558093869/5000000000000000000 : ℝ) ≤ (5049417400289373/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (5268186187558093869/5000000000000000000 : ℝ)^16 ≤ (5049417400289373/5000000000000000 : ℝ)^85 := by
      have hnat : (5268186187558093869 : ℕ)^16*5000000000000000^85 ≤ 5049417400289373^85*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5268186187558093869 5000000000000000000 5049417400289373 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5049417400289373/5000000000000000 : ℝ)) (X := (5268186187558093869/5000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(49941333463957/5060300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(48893467114789/5060300000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (50603/100000 : ℝ)) (alpha := (49941333463957/5060300000000000 : ℝ)) (beta := (48893467114789/5060300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (50603/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(49941333463957/5060300000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(48893467114789/5060300000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-161322893/500000000 : ℝ)*X 0 0+(1612183211/5000000000 : ℝ)*X 0 1+(1420202581/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3224529627/10000000000 : ℝ)*X 1 0+(-1611200507/5000000000 : ℝ)*X 1 1+(5684237207/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5536422261/10000000000 : ℝ)*X 2 0+(1082015567/2000000000 : ℝ)*X 2 1+(-196664483/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4109849177/10000000000 : ℝ)*X 0 0+(1125701719/2500000000 : ℝ)*X 0 1+(1807688247/5000000000 : ℝ)*X 0 2+(4109849177/10000000000 : ℝ)*X 1 0+(1125701719/2500000000 : ℝ)*X 1 1+(1807688247/5000000000 : ℝ)*X 1 2+(4109849177/10000000000 : ℝ)*X 2 0+(1125701719/2500000000 : ℝ)*X 2 1+(1807688247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325059_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-452817/50000 : ℝ) < ((-200939/100000 : ℝ)*P 0+(-200939/100000 : ℝ)*P 1+(-200939/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-452817/50000 : ℝ) < (-26463812644839704530876850644758201303/2930992133424950000000000000000000000 : ℝ) := by norm_num
    linear_combination (144083/1000000000000 : ℝ)*(base7) + (100243/250000000000 : ℝ)*(base13) + (32477/1000000000000 : ℝ)*(base16) + (60169/500000000000 : ℝ)*(base21) + (77037/500000000000 : ℝ)*(base33) + (11151/100000000000 : ℝ)*(base50) + (210761/1000000000000 : ℝ)*(base59) + (304051045601/500000000000 : ℝ)*(base60) + (1004694922963/500000000000 : ℝ)*(major_s1_0) + (200939/100000 : ℝ)*(major_s1_1) + (200939/100000 : ℝ)*(major_s1_2) + (3009653070373/1000000000000 : ℝ)*(sp_s1_0) + (1504826642397/500000000000 : ℝ)*(sp_s1_1) + (3009653196933/1000000000000 : ℝ)*(sp_s1_2) + (1000000144083/1000000000000 : ℝ)*(sp_s1_6) + (601930694269/200000000000 : ℝ)*(f.sum) + (217325395274194007/8591883370000000000000000000000 : ℝ)*base62 + (203489757379371/253015000000000000000000000 : ℝ)*base64 + (49915938442533/84895000000000000000000000 : ℝ)*base66 + (348602598051987/506030000000000000000000000 : ℝ)*base68 + (152925930635060562407/172624544050000000000000000000000 : ℝ)*base70 + (381443646474431/3411350000000000000000000000 : ℝ)*base73 + (14170501382821/42447500000000000000000000 : ℝ)*base75 + (234235228436377/1705675000000000000000000000 : ℝ)*base76 + (28431239828793171241/57921311650000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p025_b032 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 59 ≤ c.val) (hhi : c.val < 60)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=59 := by omega
  rcases hc with rfl
  · exact collision_c325059 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 59 ≤ c.val) (hhi : c.val < 60)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b032 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

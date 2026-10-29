-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b005
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:08:11.432988+00:00
-- url     : https://prove2.me/submissions/3aa42573-3297-4323-814a-c5b765513da7

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
theorem collision_support_c326014_s0_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-22640021/78125000 : ℝ)*x 0 + (-901367/1953125 : ℝ)*x 1 + (-922999807/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22640021/78125000 : ℝ)^89 ≤ (22089608068577/100000000000000 : ℝ)^73 := by
    have hnat : (22640021 : ℕ)^89*100000000000000^73 ≤ 22089608068577^73*78125000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22640021 78125000 22089608068577 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901367/1953125 : ℝ)^89 ≤ (38955195986273/100000000000000 : ℝ)^73 := by
    have hnat : (901367 : ℕ)^89*100000000000000^73 ≤ 38955195986273^73*1953125^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901367 1953125 38955195986273 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (922999807/2000000000 : ℝ)^89 ≤ (38955195934817/100000000000000 : ℝ)^73 := by
    have hnat : (922999807 : ℕ)^89*100000000000000^73 ≤ 38955195934817^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922999807 2000000000 38955195934817 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22640021/78125000 : ℝ), (-901367/1953125 : ℝ), (-922999807/2000000000 : ℝ)] ![(22089608068577/100000000000000 : ℝ), (38955195986273/100000000000000 : ℝ), (38955195934817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22640021/78125000 : ℝ)|^89 ≤ (22089608068577/100000000000000 : ℝ)^73
        have hw : |(-22640021/78125000 : ℝ)|=(22640021/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-901367/1953125 : ℝ)|^89 ≤ (38955195986273/100000000000000 : ℝ)^73
        have hw : |(-901367/1953125 : ℝ)|=(901367/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-922999807/2000000000 : ℝ)|^89 ≤ (38955195934817/100000000000000 : ℝ)^73
        have hw : |(-922999807/2000000000 : ℝ)|=(922999807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326014_s0_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (574990247/1000000000 : ℝ)*x 0 + (1579244003/5000000000 : ℝ)*x 1 + (-3158488003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (574990247/1000000000 : ℝ)^89 ≤ (2546556563823/5000000000000 : ℝ)^73 := by
    have hnat : (574990247 : ℕ)^89*5000000000000^73 ≤ 2546556563823^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574990247 1000000000 2546556563823 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1579244003/5000000000 : ℝ)^89 ≤ (1533402148331/6250000000000 : ℝ)^73 := by
    have hnat : (1579244003 : ℕ)^89*6250000000000^73 ≤ 1533402148331^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1579244003 5000000000 1533402148331 6250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3158488003/10000000000 : ℝ)^89 ≤ (4906886868977/20000000000000 : ℝ)^73 := by
    have hnat : (3158488003 : ℕ)^89*20000000000000^73 ≤ 4906886868977^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3158488003 10000000000 4906886868977 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(574990247/1000000000 : ℝ), (1579244003/5000000000 : ℝ), (-3158488003/10000000000 : ℝ)] ![(2546556563823/5000000000000 : ℝ), (1533402148331/6250000000000 : ℝ), (4906886868977/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(574990247/1000000000 : ℝ)|^89 ≤ (2546556563823/5000000000000 : ℝ)^73
        have hw : |(574990247/1000000000 : ℝ)|=(574990247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1579244003/5000000000 : ℝ)|^89 ≤ (1533402148331/6250000000000 : ℝ)^73
        have hw : |(1579244003/5000000000 : ℝ)|=(1579244003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3158488003/10000000000 : ℝ)|^89 ≤ (4906886868977/20000000000000 : ℝ)^73
        have hw : |(-3158488003/10000000000 : ℝ)|=(3158488003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326014_s0_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (22640021/78125000 : ℝ)*x 0 + (-901367/1953125 : ℝ)*x 1 + (922999807/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22640021/78125000 : ℝ)^89 ≤ (22089608068577/100000000000000 : ℝ)^73 := by
    have hnat : (22640021 : ℕ)^89*100000000000000^73 ≤ 22089608068577^73*78125000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22640021 78125000 22089608068577 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901367/1953125 : ℝ)^89 ≤ (38955195986273/100000000000000 : ℝ)^73 := by
    have hnat : (901367 : ℕ)^89*100000000000000^73 ≤ 38955195986273^73*1953125^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901367 1953125 38955195986273 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (922999807/2000000000 : ℝ)^89 ≤ (38955195934817/100000000000000 : ℝ)^73 := by
    have hnat : (922999807 : ℕ)^89*100000000000000^73 ≤ 38955195934817^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922999807 2000000000 38955195934817 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(22640021/78125000 : ℝ), (-901367/1953125 : ℝ), (922999807/2000000000 : ℝ)] ![(22089608068577/100000000000000 : ℝ), (38955195986273/100000000000000 : ℝ), (38955195934817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(22640021/78125000 : ℝ)|^89 ≤ (22089608068577/100000000000000 : ℝ)^73
        have hw : |(22640021/78125000 : ℝ)|=(22640021/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-901367/1953125 : ℝ)|^89 ≤ (38955195986273/100000000000000 : ℝ)^73
        have hw : |(-901367/1953125 : ℝ)|=(901367/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(922999807/2000000000 : ℝ)|^89 ≤ (38955195934817/100000000000000 : ℝ)^73
        have hw : |(922999807/2000000000 : ℝ)|=(922999807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326014_s0_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (574990247/1000000000 : ℝ)*x 0 + (-1579244003/5000000000 : ℝ)*x 1 + (-3158488003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (574990247/1000000000 : ℝ)^89 ≤ (2546556563823/5000000000000 : ℝ)^73 := by
    have hnat : (574990247 : ℕ)^89*5000000000000^73 ≤ 2546556563823^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574990247 1000000000 2546556563823 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1579244003/5000000000 : ℝ)^89 ≤ (1533402148331/6250000000000 : ℝ)^73 := by
    have hnat : (1579244003 : ℕ)^89*6250000000000^73 ≤ 1533402148331^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1579244003 5000000000 1533402148331 6250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3158488003/10000000000 : ℝ)^89 ≤ (4906886868977/20000000000000 : ℝ)^73 := by
    have hnat : (3158488003 : ℕ)^89*20000000000000^73 ≤ 4906886868977^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3158488003 10000000000 4906886868977 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(574990247/1000000000 : ℝ), (-1579244003/5000000000 : ℝ), (-3158488003/10000000000 : ℝ)] ![(2546556563823/5000000000000 : ℝ), (1533402148331/6250000000000 : ℝ), (4906886868977/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(574990247/1000000000 : ℝ)|^89 ≤ (2546556563823/5000000000000 : ℝ)^73
        have hw : |(574990247/1000000000 : ℝ)|=(574990247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1579244003/5000000000 : ℝ)|^89 ≤ (1533402148331/6250000000000 : ℝ)^73
        have hw : |(-1579244003/5000000000 : ℝ)|=(1579244003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3158488003/10000000000 : ℝ)|^89 ≤ (4906886868977/20000000000000 : ℝ)^73
        have hw : |(-3158488003/10000000000 : ℝ)|=(3158488003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326014 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(27191371846757/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(27191371846757/200000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-22640021/78125000 : ℝ)*X 0 0+(-901367/1953125 : ℝ)*X 0 1+(-922999807/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326014_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((574990247/1000000000 : ℝ)*X 1 0+(1579244003/5000000000 : ℝ)*X 1 1+(-3158488003/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326014_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((22640021/78125000 : ℝ)*X 2 0+(-901367/1953125 : ℝ)*X 2 1+(922999807/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326014_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((574990247/1000000000 : ℝ)*X 0 0+(-1579244003/5000000000 : ℝ)*X 0 1+(-3158488003/10000000000 : ℝ)*X 0 2+(574990247/1000000000 : ℝ)*X 1 0+(-1579244003/5000000000 : ℝ)*X 1 1+(-3158488003/10000000000 : ℝ)*X 1 2+(574990247/1000000000 : ℝ)*X 2 0+(-1579244003/5000000000 : ℝ)*X 2 1+(-3158488003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326014_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-93759/10000 : ℝ) < ((-41253/20000 : ℝ)*P 0+(-41253/20000 : ℝ)*P 1+(-41253/20000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-93759/10000 : ℝ) < (-2306245005821906932133478201/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (641430062067/1000000000000 : ℝ)*(base39) + (47260660381/1000000000000 : ℝ)*(base40) + (57801535113/125000000000 : ℝ)*(base49) + (3951488063/12500000000 : ℝ)*(base50) + (49/10000000000 : ℝ)*(base53) + (36573308263/250000000000 : ℝ)*(base59) + (41253/20000 : ℝ)*(major_s0_0) + (25783125011/12500000000 : ℝ)*(major_s0_1) + (20626499951/10000000000 : ℝ)*(major_s0_2) + (768748331793/250000000000 : ℝ)*(sp_s0_0) + (307499331903/100000000000 : ℝ)*(sp_s0_1) + (307499332481/100000000000 : ℝ)*(sp_s0_2) + (1 : ℝ)*(sp_s0_6) + (307499332393/100000000000 : ℝ)*(f.sum) + (2039214623227/10000000000000000000000000 : ℝ)*base63 + (42174246394747/100000000000000000000000000 : ℝ)*base64 + (907800142331954433/125000000000000000000000000 : ℝ)*base67 + (62960811093/2000000000000000000000000 : ℝ)*base68 + (1235911994747/100000000000000000000000000 : ℝ)*base70 + (8041219/62500000000000000000 : ℝ)*base73 + (615261740673/2500000000000000000000000 : ℝ)*base75 + (2244849/100000000000000000000 : ℝ)*base77 + (51006839204433/125000000000000000000000000 : ℝ)*base79 + (4071/500000000000 : ℝ)*base81 + (11/12500000000 : ℝ)*base85 + (11/12500000000 : ℝ)*base88 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c326015_s0_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2809226229/10000000000 : ℝ)*x 0 + (-6167736139/10000000000 : ℝ)*x 1 + (377819067/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2809226229/10000000000 : ℝ)^89 ≤ (2658514426007/12500000000000 : ℝ)^73 := by
    have hnat : (2809226229 : ℕ)^89*12500000000000^73 ≤ 2658514426007^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2809226229 10000000000 2658514426007 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6167736139/10000000000 : ℝ)^89 ≤ (55478659411159/100000000000000 : ℝ)^73 := by
    have hnat : (6167736139 : ℕ)^89*100000000000000^73 ≤ 55478659411159^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6167736139 10000000000 55478659411159 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (377819067/1250000000 : ℝ)^89 ≤ (4650645033281/20000000000000 : ℝ)^73 := by
    have hnat : (377819067 : ℕ)^89*20000000000000^73 ≤ 4650645033281^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377819067 1250000000 4650645033281 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2809226229/10000000000 : ℝ), (-6167736139/10000000000 : ℝ), (377819067/1250000000 : ℝ)] ![(2658514426007/12500000000000 : ℝ), (55478659411159/100000000000000 : ℝ), (4650645033281/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2809226229/10000000000 : ℝ)|^89 ≤ (2658514426007/12500000000000 : ℝ)^73
        have hw : |(-2809226229/10000000000 : ℝ)|=(2809226229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6167736139/10000000000 : ℝ)|^89 ≤ (55478659411159/100000000000000 : ℝ)^73
        have hw : |(-6167736139/10000000000 : ℝ)|=(6167736139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(377819067/1250000000 : ℝ)|^89 ≤ (4650645033281/20000000000000 : ℝ)^73
        have hw : |(377819067/1250000000 : ℝ)|=(377819067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s0_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (924758951/2500000000 : ℝ)*x 0 + (-4241159583/10000000000 : ℝ)*x 1 + (-847610463/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (924758951/2500000000 : ℝ)^89 ≤ (2974561882779/10000000000000 : ℝ)^73 := by
    have hnat : (924758951 : ℕ)^89*10000000000000^73 ≤ 2974561882779^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924758951 2500000000 2974561882779 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241159583/10000000000 : ℝ)^89 ≤ (35142884581791/100000000000000 : ℝ)^73 := by
    have hnat : (4241159583 : ℕ)^89*100000000000000^73 ≤ 35142884581791^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241159583 10000000000 35142884581791 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847610463/2000000000 : ℝ)^89 ≤ (17555748286209/50000000000000 : ℝ)^73 := by
    have hnat : (847610463 : ℕ)^89*50000000000000^73 ≤ 17555748286209^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847610463 2000000000 17555748286209 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(924758951/2500000000 : ℝ), (-4241159583/10000000000 : ℝ), (-847610463/2000000000 : ℝ)] ![(2974561882779/10000000000000 : ℝ), (35142884581791/100000000000000 : ℝ), (17555748286209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(924758951/2500000000 : ℝ)|^89 ≤ (2974561882779/10000000000000 : ℝ)^73
        have hw : |(924758951/2500000000 : ℝ)|=(924758951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4241159583/10000000000 : ℝ)|^89 ≤ (35142884581791/100000000000000 : ℝ)^73
        have hw : |(-4241159583/10000000000 : ℝ)|=(4241159583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-847610463/2000000000 : ℝ)|^89 ≤ (17555748286209/50000000000000 : ℝ)^73
        have hw : |(-847610463/2000000000 : ℝ)|=(847610463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s0_7 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2428868673/10000000000 : ℝ)*x 0 + (-1496172783/2000000000 : ℝ)*x 1 + (877834257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2428868673/10000000000 : ℝ)^89 ≤ (17811400462729/100000000000000 : ℝ)^73 := by
    have hnat : (2428868673 : ℕ)^89*100000000000000^73 ≤ 17811400462729^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2428868673 10000000000 17811400462729 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1496172783/2000000000 : ℝ)^89 ≤ (701980004739/1000000000000 : ℝ)^73 := by
    have hnat : (1496172783 : ℕ)^89*1000000000000^73 ≤ 701980004739^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1496172783 2000000000 701980004739 1000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (877834257/5000000000 : ℝ)^89 ≤ (5995299529241/50000000000000 : ℝ)^73 := by
    have hnat : (877834257 : ℕ)^89*50000000000000^73 ≤ 5995299529241^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877834257 5000000000 5995299529241 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2428868673/10000000000 : ℝ), (-1496172783/2000000000 : ℝ), (877834257/5000000000 : ℝ)] ![(17811400462729/100000000000000 : ℝ), (701980004739/1000000000000 : ℝ), (5995299529241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2428868673/10000000000 : ℝ)|^89 ≤ (17811400462729/100000000000000 : ℝ)^73
        have hw : |(-2428868673/10000000000 : ℝ)|=(2428868673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1496172783/2000000000 : ℝ)|^89 ≤ (701980004739/1000000000000 : ℝ)^73
        have hw : |(-1496172783/2000000000 : ℝ)|=(1496172783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(877834257/5000000000 : ℝ)|^89 ≤ (5995299529241/50000000000000 : ℝ)^73
        have hw : |(877834257/5000000000 : ℝ)|=(877834257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s0_8 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2518702927/5000000000 : ℝ)*x 0 + (2092170041/5000000000 : ℝ)*x 1 + (1448737851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2518702927/5000000000 : ℝ)^89 ≤ (10836205686823/25000000000000 : ℝ)^73 := by
    have hnat : (2518702927 : ℕ)^89*25000000000000^73 ≤ 10836205686823^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518702927 5000000000 10836205686823 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2092170041/5000000000 : ℝ)^89 ≤ (17284861533319/50000000000000 : ℝ)^73 := by
    have hnat : (2092170041 : ℕ)^89*50000000000000^73 ≤ 17284861533319^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092170041 5000000000 17284861533319 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1448737851/5000000000 : ℝ)^89 ≤ (22085454179059/100000000000000 : ℝ)^73 := by
    have hnat : (1448737851 : ℕ)^89*100000000000000^73 ≤ 22085454179059^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1448737851 5000000000 22085454179059 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2518702927/5000000000 : ℝ), (2092170041/5000000000 : ℝ), (1448737851/5000000000 : ℝ)] ![(10836205686823/25000000000000 : ℝ), (17284861533319/50000000000000 : ℝ), (22085454179059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2518702927/5000000000 : ℝ)|^89 ≤ (10836205686823/25000000000000 : ℝ)^73
        have hw : |(2518702927/5000000000 : ℝ)|=(2518702927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2092170041/5000000000 : ℝ)|^89 ≤ (17284861533319/50000000000000 : ℝ)^73
        have hw : |(2092170041/5000000000 : ℝ)|=(2092170041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1448737851/5000000000 : ℝ)|^89 ≤ (22085454179059/100000000000000 : ℝ)^73
        have hw : |(1448737851/5000000000 : ℝ)|=(1448737851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s0_9 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (287880023/625000000 : ℝ)*x 0 + (-1031781621/2000000000 : ℝ)*x 1 + (-456549857/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (287880023/625000000 : ℝ)^89 ≤ (19431716336703/50000000000000 : ℝ)^73 := by
    have hnat : (287880023 : ℕ)^89*50000000000000^73 ≤ 19431716336703^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287880023 625000000 19431716336703 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031781621/2000000000 : ℝ)^89 ≤ (22311397020357/50000000000000 : ℝ)^73 := by
    have hnat : (1031781621 : ℕ)^89*50000000000000^73 ≤ 22311397020357^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031781621 2000000000 22311397020357 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (456549857/2000000000 : ℝ)^89 ≤ (3302754653153/20000000000000 : ℝ)^73 := by
    have hnat : (456549857 : ℕ)^89*20000000000000^73 ≤ 3302754653153^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456549857 2000000000 3302754653153 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(287880023/625000000 : ℝ), (-1031781621/2000000000 : ℝ), (-456549857/2000000000 : ℝ)] ![(19431716336703/50000000000000 : ℝ), (22311397020357/50000000000000 : ℝ), (3302754653153/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(287880023/625000000 : ℝ)|^89 ≤ (19431716336703/50000000000000 : ℝ)^73
        have hw : |(287880023/625000000 : ℝ)|=(287880023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1031781621/2000000000 : ℝ)|^89 ≤ (22311397020357/50000000000000 : ℝ)^73
        have hw : |(-1031781621/2000000000 : ℝ)|=(1031781621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-456549857/2000000000 : ℝ)|^89 ≤ (3302754653153/20000000000000 : ℝ)^73
        have hw : |(-456549857/2000000000 : ℝ)|=(456549857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s0_13 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (128645051/1000000000 : ℝ)*x 0 + (1951/500000000 : ℝ)*x 1 + (233042361/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128645051/1000000000 : ℝ)^89 ≤ (8207134816469/100000000000000 : ℝ)^73 := by
    have hnat : (128645051 : ℕ)^89*100000000000000^73 ≤ 8207134816469^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128645051 1000000000 8207134816469 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1951/500000000 : ℝ)^89 ≤ (12728757/50000000000000 : ℝ)^73 := by
    have hnat : (1951 : ℕ)^89*50000000000000^73 ≤ 12728757^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951 500000000 12728757 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233042361/250000000 : ℝ)^89 ≤ (91792839713837/100000000000000 : ℝ)^73 := by
    have hnat : (233042361 : ℕ)^89*100000000000000^73 ≤ 91792839713837^73*250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233042361 250000000 91792839713837 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(128645051/1000000000 : ℝ), (1951/500000000 : ℝ), (233042361/250000000 : ℝ)] ![(8207134816469/100000000000000 : ℝ), (12728757/50000000000000 : ℝ), (91792839713837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(128645051/1000000000 : ℝ)|^89 ≤ (8207134816469/100000000000000 : ℝ)^73
        have hw : |(128645051/1000000000 : ℝ)|=(128645051/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1951/500000000 : ℝ)|^89 ≤ (12728757/50000000000000 : ℝ)^73
        have hw : |(1951/500000000 : ℝ)|=(1951/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(233042361/250000000 : ℝ)|^89 ≤ (91792839713837/100000000000000 : ℝ)^73
        have hw : |(233042361/250000000 : ℝ)|=(233042361/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s0_14 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-189527867/500000000 : ℝ)*x 0 + (-5357274011/10000000000 : ℝ)*x 1 + (1478042333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (189527867/500000000 : ℝ)^89 ≤ (766132747691/2500000000000 : ℝ)^73 := by
    have hnat : (189527867 : ℕ)^89*2500000000000^73 ≤ 766132747691^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189527867 500000000 766132747691 2500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5357274011/10000000000 : ℝ)^89 ≤ (730052884253/1562500000000 : ℝ)^73 := by
    have hnat : (5357274011 : ℕ)^89*1562500000000^73 ≤ 730052884253^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5357274011 10000000000 730052884253 1562500000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1478042333/5000000000 : ℝ)^89 ≤ (22631305488003/100000000000000 : ℝ)^73 := by
    have hnat : (1478042333 : ℕ)^89*100000000000000^73 ≤ 22631305488003^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1478042333 5000000000 22631305488003 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-189527867/500000000 : ℝ), (-5357274011/10000000000 : ℝ), (1478042333/5000000000 : ℝ)] ![(766132747691/2500000000000 : ℝ), (730052884253/1562500000000 : ℝ), (22631305488003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-189527867/500000000 : ℝ)|^89 ≤ (766132747691/2500000000000 : ℝ)^73
        have hw : |(-189527867/500000000 : ℝ)|=(189527867/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5357274011/10000000000 : ℝ)|^89 ≤ (730052884253/1562500000000 : ℝ)^73
        have hw : |(-5357274011/10000000000 : ℝ)|=(5357274011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1478042333/5000000000 : ℝ)|^89 ≤ (22631305488003/100000000000000 : ℝ)^73
        have hw : |(1478042333/5000000000 : ℝ)|=(1478042333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s0_15 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (291742393/400000000 : ℝ)*x 0 + (621581199/2500000000 : ℝ)*x 1 + (487051017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (291742393/400000000 : ℝ)^89 ≤ (68061090448427/100000000000000 : ℝ)^73 := by
    have hnat : (291742393 : ℕ)^89*100000000000000^73 ≤ 68061090448427^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291742393 400000000 68061090448427 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (621581199/2500000000 : ℝ)^89 ≤ (18326409746817/100000000000000 : ℝ)^73 := by
    have hnat : (621581199 : ℕ)^89*100000000000000^73 ≤ 18326409746817^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621581199 2500000000 18326409746817 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (487051017/2500000000 : ℝ)^89 ≤ (13612499789167/100000000000000 : ℝ)^73 := by
    have hnat : (487051017 : ℕ)^89*100000000000000^73 ≤ 13612499789167^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487051017 2500000000 13612499789167 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(291742393/400000000 : ℝ), (621581199/2500000000 : ℝ), (487051017/2500000000 : ℝ)] ![(68061090448427/100000000000000 : ℝ), (18326409746817/100000000000000 : ℝ), (13612499789167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(291742393/400000000 : ℝ)|^89 ≤ (68061090448427/100000000000000 : ℝ)^73
        have hw : |(291742393/400000000 : ℝ)|=(291742393/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(621581199/2500000000 : ℝ)|^89 ≤ (18326409746817/100000000000000 : ℝ)^73
        have hw : |(621581199/2500000000 : ℝ)|=(621581199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(487051017/2500000000 : ℝ)|^89 ≤ (13612499789167/100000000000000 : ℝ)^73
        have hw : |(487051017/2500000000 : ℝ)|=(487051017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s0_16 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1660852331/5000000000 : ℝ)*x 0 + (-3087964967/5000000000 : ℝ)*x 1 + (-38877123/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1660852331/5000000000 : ℝ)^89 ≤ (26088784262999/100000000000000 : ℝ)^73 := by
    have hnat : (1660852331 : ℕ)^89*100000000000000^73 ≤ 26088784262999^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1660852331 5000000000 26088784262999 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3087964967/5000000000 : ℝ)^89 ≤ (55568529591813/100000000000000 : ℝ)^73 := by
    have hnat : (3087964967 : ℕ)^89*100000000000000^73 ≤ 55568529591813^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3087964967 5000000000 55568529591813 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38877123/156250000 : ℝ)^89 ≤ (18342686134039/100000000000000 : ℝ)^73 := by
    have hnat : (38877123 : ℕ)^89*100000000000000^73 ≤ 18342686134039^73*156250000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38877123 156250000 18342686134039 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1660852331/5000000000 : ℝ), (-3087964967/5000000000 : ℝ), (-38877123/156250000 : ℝ)] ![(26088784262999/100000000000000 : ℝ), (55568529591813/100000000000000 : ℝ), (18342686134039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1660852331/5000000000 : ℝ)|^89 ≤ (26088784262999/100000000000000 : ℝ)^73
        have hw : |(1660852331/5000000000 : ℝ)|=(1660852331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3087964967/5000000000 : ℝ)|^89 ≤ (55568529591813/100000000000000 : ℝ)^73
        have hw : |(-3087964967/5000000000 : ℝ)|=(3087964967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38877123/156250000 : ℝ)|^89 ≤ (18342686134039/100000000000000 : ℝ)^73
        have hw : |(-38877123/156250000 : ℝ)|=(38877123/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s0_20 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (830777829/10000000000 : ℝ)*x 0 + (-321/1000000000 : ℝ)*x 1 + (9603260973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (830777829/10000000000 : ℝ)^89 ≤ (963140545481/20000000000000 : ℝ)^73 := by
    have hnat : (830777829 : ℕ)^89*20000000000000^73 ≤ 963140545481^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830777829 10000000000 963140545481 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321/1000000000 : ℝ)^89 ≤ (1211361/100000000000000 : ℝ)^73 := by
    have hnat : (321 : ℕ)^89*100000000000000^73 ≤ 1211361^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321 1000000000 1211361 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9603260973/10000000000 : ℝ)^89 ≤ (95184296056589/100000000000000 : ℝ)^73 := by
    have hnat : (9603260973 : ℕ)^89*100000000000000^73 ≤ 95184296056589^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9603260973 10000000000 95184296056589 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(830777829/10000000000 : ℝ), (-321/1000000000 : ℝ), (9603260973/10000000000 : ℝ)] ![(963140545481/20000000000000 : ℝ), (1211361/100000000000000 : ℝ), (95184296056589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(830777829/10000000000 : ℝ)|^89 ≤ (963140545481/20000000000000 : ℝ)^73
        have hw : |(830777829/10000000000 : ℝ)|=(830777829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-321/1000000000 : ℝ)|^89 ≤ (1211361/100000000000000 : ℝ)^73
        have hw : |(-321/1000000000 : ℝ)|=(321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9603260973/10000000000 : ℝ)|^89 ≤ (95184296056589/100000000000000 : ℝ)^73
        have hw : |(9603260973/10000000000 : ℝ)|=(9603260973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s0_21 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1689490099/10000000000 : ℝ)*x 0 + (-1772933767/2500000000 : ℝ)*x 1 + (2972668331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1689490099/10000000000 : ℝ)^89 ≤ (1430232454129/12500000000000 : ℝ)^73 := by
    have hnat : (1689490099 : ℕ)^89*12500000000000^73 ≤ 1430232454129^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1689490099 10000000000 1430232454129 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1772933767/2500000000 : ℝ)^89 ≤ (32885975361399/50000000000000 : ℝ)^73 := by
    have hnat : (1772933767 : ℕ)^89*50000000000000^73 ≤ 32885975361399^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772933767 2500000000 32885975361399 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2972668331/10000000000 : ℝ)^89 ≤ (22786189622303/100000000000000 : ℝ)^73 := by
    have hnat : (2972668331 : ℕ)^89*100000000000000^73 ≤ 22786189622303^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2972668331 10000000000 22786189622303 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1689490099/10000000000 : ℝ), (-1772933767/2500000000 : ℝ), (2972668331/10000000000 : ℝ)] ![(1430232454129/12500000000000 : ℝ), (32885975361399/50000000000000 : ℝ), (22786189622303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1689490099/10000000000 : ℝ)|^89 ≤ (1430232454129/12500000000000 : ℝ)^73
        have hw : |(-1689490099/10000000000 : ℝ)|=(1689490099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1772933767/2500000000 : ℝ)|^89 ≤ (32885975361399/50000000000000 : ℝ)^73
        have hw : |(-1772933767/2500000000 : ℝ)|=(1772933767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2972668331/10000000000 : ℝ)|^89 ≤ (22786189622303/100000000000000 : ℝ)^73
        have hw : |(2972668331/10000000000 : ℝ)|=(2972668331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s0_22 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1665704373/2500000000 : ℝ)*x 0 + (1249183787/5000000000 : ℝ)*x 1 + (2737785453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1665704373/2500000000 : ℝ)^89 ≤ (15238689020297/25000000000000 : ℝ)^73 := by
    have hnat : (1665704373 : ℕ)^89*25000000000000^73 ≤ 15238689020297^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665704373 2500000000 15238689020297 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249183787/5000000000 : ℝ)^89 ≤ (9217344285799/50000000000000 : ℝ)^73 := by
    have hnat : (1249183787 : ℕ)^89*50000000000000^73 ≤ 9217344285799^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249183787 5000000000 9217344285799 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2737785453/10000000000 : ℝ)^89 ≤ (644079854081/3125000000000 : ℝ)^73 := by
    have hnat : (2737785453 : ℕ)^89*3125000000000^73 ≤ 644079854081^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737785453 10000000000 644079854081 3125000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1665704373/2500000000 : ℝ), (1249183787/5000000000 : ℝ), (2737785453/10000000000 : ℝ)] ![(15238689020297/25000000000000 : ℝ), (9217344285799/50000000000000 : ℝ), (644079854081/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1665704373/2500000000 : ℝ)|^89 ≤ (15238689020297/25000000000000 : ℝ)^73
        have hw : |(1665704373/2500000000 : ℝ)|=(1665704373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1249183787/5000000000 : ℝ)|^89 ≤ (9217344285799/50000000000000 : ℝ)^73
        have hw : |(1249183787/5000000000 : ℝ)|=(1249183787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2737785453/10000000000 : ℝ)|^89 ≤ (644079854081/3125000000000 : ℝ)^73
        have hw : |(2737785453/10000000000 : ℝ)|=(2737785453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s0_23 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1257489679/5000000000 : ℝ)*x 0 + (-4204701793/10000000000 : ℝ)*x 1 + (-5349509659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1257489679/5000000000 : ℝ)^89 ≤ (18584235909397/100000000000000 : ℝ)^73 := by
    have hnat : (1257489679 : ℕ)^89*100000000000000^73 ≤ 18584235909397^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257489679 5000000000 18584235909397 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4204701793/10000000000 : ℝ)^89 ≤ (6954985013143/20000000000000 : ℝ)^73 := by
    have hnat : (4204701793 : ℕ)^89*20000000000000^73 ≤ 6954985013143^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204701793 10000000000 6954985013143 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5349509659/10000000000 : ℝ)^89 ≤ (46640839018961/100000000000000 : ℝ)^73 := by
    have hnat : (5349509659 : ℕ)^89*100000000000000^73 ≤ 46640839018961^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349509659 10000000000 46640839018961 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1257489679/5000000000 : ℝ), (-4204701793/10000000000 : ℝ), (-5349509659/10000000000 : ℝ)] ![(18584235909397/100000000000000 : ℝ), (6954985013143/20000000000000 : ℝ), (46640839018961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1257489679/5000000000 : ℝ)|^89 ≤ (18584235909397/100000000000000 : ℝ)^73
        have hw : |(1257489679/5000000000 : ℝ)|=(1257489679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4204701793/10000000000 : ℝ)|^89 ≤ (6954985013143/20000000000000 : ℝ)^73
        have hw : |(-4204701793/10000000000 : ℝ)|=(4204701793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5349509659/10000000000 : ℝ)|^89 ≤ (46640839018961/100000000000000 : ℝ)^73
        have hw : |(-5349509659/10000000000 : ℝ)|=(5349509659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s1_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1668944459/5000000000 : ℝ)*x 0 + (-176486971/400000000 : ℝ)*x 1 + (110304357/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1668944459/5000000000 : ℝ)^89 ≤ (26243838717281/100000000000000 : ℝ)^73 := by
    have hnat : (1668944459 : ℕ)^89*100000000000000^73 ≤ 26243838717281^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1668944459 5000000000 26243838717281 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176486971/400000000 : ℝ)^89 ≤ (18439040304053/50000000000000 : ℝ)^73 := by
    have hnat : (176486971 : ℕ)^89*50000000000000^73 ≤ 18439040304053^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176486971 400000000 18439040304053 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110304357/250000000 : ℝ)^89 ≤ (36878080659057/100000000000000 : ℝ)^73 := by
    have hnat : (110304357 : ℕ)^89*100000000000000^73 ≤ 36878080659057^73*250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110304357 250000000 36878080659057 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1668944459/5000000000 : ℝ), (-176486971/400000000 : ℝ), (110304357/250000000 : ℝ)] ![(26243838717281/100000000000000 : ℝ), (18439040304053/50000000000000 : ℝ), (36878080659057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1668944459/5000000000 : ℝ)|^89 ≤ (26243838717281/100000000000000 : ℝ)^73
        have hw : |(-1668944459/5000000000 : ℝ)|=(1668944459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-176486971/400000000 : ℝ)|^89 ≤ (18439040304053/50000000000000 : ℝ)^73
        have hw : |(-176486971/400000000 : ℝ)|=(176486971/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110304357/250000000 : ℝ)|^89 ≤ (36878080659057/100000000000000 : ℝ)^73
        have hw : |(110304357/250000000 : ℝ)|=(110304357/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s1_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1281390011/2500000000 : ℝ)*x 0 + (1753012223/5000000000 : ℝ)*x 1 + (3506024451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1281390011/2500000000 : ℝ)^89 ≤ (44271372467877/100000000000000 : ℝ)^73 := by
    have hnat : (1281390011 : ℕ)^89*100000000000000^73 ≤ 44271372467877^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281390011 2500000000 44271372467877 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1753012223/5000000000 : ℝ)^89 ≤ (13932156868771/50000000000000 : ℝ)^73 := by
    have hnat : (1753012223 : ℕ)^89*50000000000000^73 ≤ 13932156868771^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1753012223 5000000000 13932156868771 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3506024451/10000000000 : ℝ)^89 ≤ (2786431378599/10000000000000 : ℝ)^73 := by
    have hnat : (3506024451 : ℕ)^89*10000000000000^73 ≤ 2786431378599^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3506024451 10000000000 2786431378599 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1281390011/2500000000 : ℝ), (1753012223/5000000000 : ℝ), (3506024451/10000000000 : ℝ)] ![(44271372467877/100000000000000 : ℝ), (13932156868771/50000000000000 : ℝ), (2786431378599/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1281390011/2500000000 : ℝ)|^89 ≤ (44271372467877/100000000000000 : ℝ)^73
        have hw : |(1281390011/2500000000 : ℝ)|=(1281390011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1753012223/5000000000 : ℝ)|^89 ≤ (13932156868771/50000000000000 : ℝ)^73
        have hw : |(1753012223/5000000000 : ℝ)|=(1753012223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3506024451/10000000000 : ℝ)|^89 ≤ (2786431378599/10000000000000 : ℝ)^73
        have hw : |(3506024451/10000000000 : ℝ)|=(3506024451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s1_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1668944459/5000000000 : ℝ)*x 0 + (-176486971/400000000 : ℝ)*x 1 + (-110304357/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1668944459/5000000000 : ℝ)^89 ≤ (26243838717281/100000000000000 : ℝ)^73 := by
    have hnat : (1668944459 : ℕ)^89*100000000000000^73 ≤ 26243838717281^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1668944459 5000000000 26243838717281 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176486971/400000000 : ℝ)^89 ≤ (18439040304053/50000000000000 : ℝ)^73 := by
    have hnat : (176486971 : ℕ)^89*50000000000000^73 ≤ 18439040304053^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176486971 400000000 18439040304053 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110304357/250000000 : ℝ)^89 ≤ (36878080659057/100000000000000 : ℝ)^73 := by
    have hnat : (110304357 : ℕ)^89*100000000000000^73 ≤ 36878080659057^73*250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110304357 250000000 36878080659057 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1668944459/5000000000 : ℝ), (-176486971/400000000 : ℝ), (-110304357/250000000 : ℝ)] ![(26243838717281/100000000000000 : ℝ), (18439040304053/50000000000000 : ℝ), (36878080659057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1668944459/5000000000 : ℝ)|^89 ≤ (26243838717281/100000000000000 : ℝ)^73
        have hw : |(1668944459/5000000000 : ℝ)|=(1668944459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-176486971/400000000 : ℝ)|^89 ≤ (18439040304053/50000000000000 : ℝ)^73
        have hw : |(-176486971/400000000 : ℝ)|=(176486971/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-110304357/250000000 : ℝ)|^89 ≤ (36878080659057/100000000000000 : ℝ)^73
        have hw : |(-110304357/250000000 : ℝ)|=(110304357/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326015_s1_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1281390011/2500000000 : ℝ)*x 0 + (-1753012223/5000000000 : ℝ)*x 1 + (3506024451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1281390011/2500000000 : ℝ)^89 ≤ (44271372467877/100000000000000 : ℝ)^73 := by
    have hnat : (1281390011 : ℕ)^89*100000000000000^73 ≤ 44271372467877^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281390011 2500000000 44271372467877 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1753012223/5000000000 : ℝ)^89 ≤ (13932156868771/50000000000000 : ℝ)^73 := by
    have hnat : (1753012223 : ℕ)^89*50000000000000^73 ≤ 13932156868771^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1753012223 5000000000 13932156868771 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3506024451/10000000000 : ℝ)^89 ≤ (2786431378599/10000000000000 : ℝ)^73 := by
    have hnat : (3506024451 : ℕ)^89*10000000000000^73 ≤ 2786431378599^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3506024451 10000000000 2786431378599 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1281390011/2500000000 : ℝ), (-1753012223/5000000000 : ℝ), (3506024451/10000000000 : ℝ)] ![(44271372467877/100000000000000 : ℝ), (13932156868771/50000000000000 : ℝ), (2786431378599/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1281390011/2500000000 : ℝ)|^89 ≤ (44271372467877/100000000000000 : ℝ)^73
        have hw : |(1281390011/2500000000 : ℝ)|=(1281390011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1753012223/5000000000 : ℝ)|^89 ≤ (13932156868771/50000000000000 : ℝ)^73
        have hw : |(-1753012223/5000000000 : ℝ)|=(1753012223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3506024451/10000000000 : ℝ)|^89 ≤ (2786431378599/10000000000000 : ℝ)^73
        have hw : |(3506024451/10000000000 : ℝ)|=(3506024451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326015 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (163929/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(27191371846757/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(27191371846757/200000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2809226229/10000000000 : ℝ)*X 0 0+(-6167736139/10000000000 : ℝ)*X 0 1+(377819067/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((924758951/2500000000 : ℝ)*X 2 0+(-4241159583/10000000000 : ℝ)*X 2 1+(-847610463/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2428868673/10000000000 : ℝ)*X 0 0+(-1496172783/2000000000 : ℝ)*X 0 1+(877834257/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2518702927/5000000000 : ℝ)*X 1 0+(2092170041/5000000000 : ℝ)*X 1 1+(1448737851/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((287880023/625000000 : ℝ)*X 2 0+(-1031781621/2000000000 : ℝ)*X 2 1+(-456549857/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((128645051/1000000000 : ℝ)*X 0 0+(1951/500000000 : ℝ)*X 0 1+(233042361/250000000 : ℝ)*X 0 2+(128645051/1000000000 : ℝ)*X 1 0+(1951/500000000 : ℝ)*X 1 1+(233042361/250000000 : ℝ)*X 1 2+(128645051/1000000000 : ℝ)*X 2 0+(1951/500000000 : ℝ)*X 2 1+(233042361/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-189527867/500000000 : ℝ)*X 0 0+(-5357274011/10000000000 : ℝ)*X 0 1+(1478042333/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((291742393/400000000 : ℝ)*X 1 0+(621581199/2500000000 : ℝ)*X 1 1+(487051017/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1660852331/5000000000 : ℝ)*X 2 0+(-3087964967/5000000000 : ℝ)*X 2 1+(-38877123/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((830777829/10000000000 : ℝ)*X 0 0+(-321/1000000000 : ℝ)*X 0 1+(9603260973/10000000000 : ℝ)*X 0 2+(830777829/10000000000 : ℝ)*X 1 0+(-321/1000000000 : ℝ)*X 1 1+(9603260973/10000000000 : ℝ)*X 1 2+(830777829/10000000000 : ℝ)*X 2 0+(-321/1000000000 : ℝ)*X 2 1+(9603260973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1689490099/10000000000 : ℝ)*X 0 0+(-1772933767/2500000000 : ℝ)*X 0 1+(2972668331/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1665704373/2500000000 : ℝ)*X 1 0+(1249183787/5000000000 : ℝ)*X 1 1+(2737785453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1257489679/5000000000 : ℝ)*X 2 0+(-4204701793/10000000000 : ℝ)*X 2 1+(-5349509659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((57573/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(57573/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23730538745854337403171/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4457436709/7812500000 : ℝ)*(base3) + (921348805409/1000000000000 : ℝ)*(base7) + (1602479/500000000000 : ℝ)*(base40) + (477259827543/1000000000000 : ℝ)*(base50) + (68374760097/62500000000 : ℝ)*(base54) + (2135349113241/1000000000000 : ℝ)*(major_s0_0) + (2135349113241/1000000000000 : ℝ)*(major_s0_1) + (130169118961/125000000000 : ℝ)*(major_s0_2) + (24003/3906250000 : ℝ)*(sp_s0_0) + (2731990798301/1000000000000 : ℝ)*(sp_s0_7) + (3302548841821/1000000000000 : ℝ)*(sp_s0_8) + (409494939183/250000000000 : ℝ)*(sp_s0_9) + (292046236701/1000000000000 : ℝ)*(sp_s0_13) + (4204957/200000000000 : ℝ)*(sp_s0_16) + (258811372899/250000000000 : ℝ)*(f.failure) + (2731996943069/1000000000000 : ℝ)*(f.sum) + (44165392433621/200000000000000000000000000 : ℝ)*base62 + (671146235608717/1250000000000000000000000000 : ℝ)*base64 + (5148028077288877/10000000000000000000000000000 : ℝ)*base66 + (14279225949477/25000000000000000000000000 : ℝ)*base69 + (184146896698943/5000000000000000000000000000 : ℝ)*base70 + (845035057288877/10000000000000000000000000000 : ℝ)*base72 + (48842457270563/200000000000000000000000000 : ℝ)*base75 + (110658427790563/200000000000000000000000000 : ℝ)*base76 + (1164981574711123/5000000000000000000000000000 : ℝ)*base79 + (2553/5000000000000000 : ℝ)*base86 + (2553/5000000000000000 : ℝ)*base88 + (2447/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-21717/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-21717/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19278277902436752674667/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216381092853/500000000000 : ℝ)*(base7) + (235550030229/1000000000000 : ℝ)*(base33) + (169031900341/500000000000 : ℝ)*(base40) + (1195261/500000000000 : ℝ)*(base50) + (30713974393/31250000000 : ℝ)*(base54) + (1969379632471/1000000000000 : ℝ)*(major_s0_0) + (22049296627/10000000000 : ℝ)*(major_s0_1) + (305520620531/250000000000 : ℝ)*(major_s0_2) + (45295319/500000000000 : ℝ)*(sp_s0_9) + (67526551/500000000000 : ℝ)*(sp_s0_13) + (620880690319/200000000000 : ℝ)*(sp_s0_14) + (573770684273/200000000000 : ℝ)*(sp_s0_15) + (1885915650151/1000000000000 : ℝ)*(sp_s0_16) + (518759014253/1000000000000 : ℝ)*(sp_s0_20) + (534489531113/500000000000 : ℝ)*(f.failure) + (620880690319/200000000000 : ℝ)*(f.sum) + (439815752063/3125000000000000000000000 : ℝ)*base62 + (1175181207648993/2500000000000000000000000000 : ℝ)*base65 + (15220286624319/100000000000000000000000000 : ℝ)*base66 + (16396880557967/50000000000000000000000000 : ℝ)*base69 + (2152460203961661/5000000000000000000000000000 : ℝ)*base71 + (948014267210813/10000000000000000000000000000 : ℝ)*base73 + (559176489239/2000000000000000000000000 : ℝ)*base74 + (146828255526547/200000000000000000000000000 : ℝ)*base77 + (5278847754221087/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (4589/10000000000000000 : ℝ)*base87 + (4589/10000000000000000 : ℝ)*base89 + (4589/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(51047/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(51047/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1705851965765605046553/100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2796326141629/1000000000000 : ℝ)*(base3) + (162100488697/125000000000 : ℝ)*(base7) + (999910603379/1000000000000 : ℝ)*(base40) + (418013065687/250000000000 : ℝ)*(base50) + (3092989531943/1000000000000 : ℝ)*(major_s0_0) + (3092989531943/1000000000000 : ℝ)*(major_s0_1) + (3092989531943/1000000000000 : ℝ)*(major_s0_2) + (39260449/1000000000000 : ℝ)*(sp_s0_2) + (5034129/1000000000000 : ℝ)*(sp_s0_7) + (5560021/1000000000000 : ℝ)*(sp_s0_15) + (7964117/500000000000 : ℝ)*(sp_s0_16) + (3977833551213/1000000000000 : ℝ)*(sp_s0_21) + (135483183339/20000000000 : ℝ)*(sp_s0_22) + (1988891698329/500000000000 : ℝ)*(sp_s0_23) + (374880558013/250000000000 : ℝ)*(f.failure) + (1988919292671/500000000000 : ℝ)*(f.sum) + (324610113/1250000000000000000000 : ℝ)*base63 + (1956912193098029/10000000000000000000000000000 : ℝ)*base65 + (1838869865098029/10000000000000000000000000000 : ℝ)*base67 + (58999962041149/200000000000000000000000000 : ℝ)*base68 + (2410307281040579/10000000000000000000000000000 : ℝ)*base71 + (4067424103901971/10000000000000000000000000000 : ℝ)*base72 + (97728478181149/200000000000000000000000000 : ℝ)*base75 + (7231105201149/200000000000000000000000000 : ℝ)*base76 + (1746320773401971/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (4711/5000000000000000 : ℝ)*base86 + (4711/5000000000000000 : ℝ)*base88 + (4711/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (57573/100000 : ℝ) ^ (87/16 : ℝ) ≤ (993619366676966983/20000000000000000000 : ℝ) := by
    have hpowers : (57573/100000 : ℝ)^87 ≤ (993619366676966983/20000000000000000000 : ℝ)^16 := by
      have hnat : (57573 : ℕ)^87*20000000000000000000^16 ≤ 993619366676966983^16*100000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57573 100000 993619366676966983 20000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (57573/100000 : ℝ)) (X := (993619366676966983/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (20993619366676966983/20000000000000000000 : ℝ) ≤ (10089568917297051/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (20993619366676966983/20000000000000000000 : ℝ)^16 ≤ (10089568917297051/10000000000000000 : ℝ)^87 := by
      have hnat : (20993619366676966983 : ℕ)^16*10000000000000000^87 ≤ 10089568917297051^87*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20993619366676966983 20000000000000000000 10089568917297051 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10089568917297051/10000000000000000 : ℝ)) (X := (20993619366676966983/20000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (10993619366676966983/10000000000000000000 : ℝ) ≤ (5087871209692657/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (10993619366676966983/10000000000000000000 : ℝ)^16 ≤ (5087871209692657/5000000000000000 : ℝ)^87 := by
      have hnat : (10993619366676966983 : ℕ)^16*5000000000000000^87 ≤ 5087871209692657^87*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10993619366676966983 10000000000000000000 5087871209692657 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5087871209692657/5000000000000000 : ℝ)) (X := (10993619366676966983/10000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(89568917297051/5757300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(86173502088263/5757300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (57573/100000 : ℝ)) (alpha := (89568917297051/5757300000000000 : ℝ)) (beta := (86173502088263/5757300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (57573/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(89568917297051/5757300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(86173502088263/5757300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (21717/50000 : ℝ) ^ (87/16 : ℝ) ≤ (1073247002939013877/100000000000000000000 : ℝ) := by
    have hpowers : (21717/50000 : ℝ)^87 ≤ (1073247002939013877/100000000000000000000 : ℝ)^16 := by
      have hnat : (21717 : ℕ)^87*100000000000000000000^16 ≤ 1073247002939013877^16*50000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21717 50000 1073247002939013877 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21717/50000 : ℝ)) (X := (1073247002939013877/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (101073247002939013877/100000000000000000000 : ℝ) ≤ (10019651994411513/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (101073247002939013877/100000000000000000000 : ℝ)^16 ≤ (10019651994411513/10000000000000000 : ℝ)^87 := by
      have hnat : (101073247002939013877 : ℕ)^16*10000000000000000^87 ≤ 10019651994411513^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101073247002939013877 100000000000000000000 10019651994411513 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10019651994411513/10000000000000000 : ℝ)) (X := (101073247002939013877/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (51073247002939013877/50000000000000000000 : ℝ) ≤ (5019567211120189/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (51073247002939013877/50000000000000000000 : ℝ)^16 ≤ (5019567211120189/5000000000000000 : ℝ)^87 := by
      have hnat : (51073247002939013877 : ℕ)^16*5000000000000000^87 ≤ 5019567211120189^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51073247002939013877 50000000000000000000 5019567211120189 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5019567211120189/5000000000000000 : ℝ)) (X := (51073247002939013877/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(19651994411513/4343400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(3896485565773/868680000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (21717/50000 : ℝ)) (alpha := (19651994411513/4343400000000000 : ℝ)) (beta := (3896485565773/868680000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (21717/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(19651994411513/4343400000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(3896485565773/868680000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (51047/100000 : ℝ) ^ (87/16 : ℝ) ≤ (80712001010380123/3125000000000000000 : ℝ) := by
    have hpowers : (51047/100000 : ℝ)^87 ≤ (80712001010380123/3125000000000000000 : ℝ)^16 := by
      have hnat : (51047 : ℕ)^87*3125000000000000000^16 ≤ 80712001010380123^16*100000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51047 100000 80712001010380123 3125000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (51047/100000 : ℝ)) (X := (80712001010380123/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (3205712001010380123/3125000000000000000 : ℝ) ≤ (10047006569368077/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3205712001010380123/3125000000000000000 : ℝ)^16 ≤ (10047006569368077/10000000000000000 : ℝ)^87 := by
      have hnat : (3205712001010380123 : ℕ)^16*10000000000000000^87 ≤ 10047006569368077^87*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3205712001010380123 3125000000000000000 10047006569368077 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10047006569368077/10000000000000000 : ℝ)) (X := (3205712001010380123/3125000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1643212001010380123/1562500000000000000 : ℝ) ≤ (252326424989909/250000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (1643212001010380123/1562500000000000000 : ℝ)^16 ≤ (252326424989909/250000000000000 : ℝ)^87 := by
      have hnat : (1643212001010380123 : ℕ)^16*250000000000000^87 ≤ 252326424989909^87*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1643212001010380123 1562500000000000000 252326424989909 250000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (252326424989909/250000000000000 : ℝ)) (X := (1643212001010380123/1562500000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(47006569368077/5104700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(46050430228283/5104700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (51047/100000 : ℝ)) (alpha := (47006569368077/5104700000000000 : ℝ)) (beta := (46050430228283/5104700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (51047/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(47006569368077/5104700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(46050430228283/5104700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1668944459/5000000000 : ℝ)*X 0 0+(-176486971/400000000 : ℝ)*X 0 1+(110304357/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1281390011/2500000000 : ℝ)*X 1 0+(1753012223/5000000000 : ℝ)*X 1 1+(3506024451/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1668944459/5000000000 : ℝ)*X 2 0+(-176486971/400000000 : ℝ)*X 2 1+(-110304357/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1281390011/2500000000 : ℝ)*X 0 0+(-1753012223/5000000000 : ℝ)*X 0 1+(3506024451/10000000000 : ℝ)*X 0 2+(1281390011/2500000000 : ℝ)*X 1 0+(-1753012223/5000000000 : ℝ)*X 1 1+(3506024451/10000000000 : ℝ)*X 1 2+(1281390011/2500000000 : ℝ)*X 2 0+(-1753012223/5000000000 : ℝ)*X 2 1+(3506024451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326015_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-93759/10000 : ℝ) < ((-41253/20000 : ℝ)*P 0+(-41253/20000 : ℝ)*P 1+(-41253/20000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-93759/10000 : ℝ) < (-361827107657942277844474131741699021/39397975058350000000000000000000000 : ℝ) := by norm_num
    linear_combination (1717/500000000000 : ℝ)*(base1) + (48539644309/50000000000 : ℝ)*(base3) + (5171/250000000000 : ℝ)*(base10) + (83702658363/125000000000 : ℝ)*(base40) + (305556166027/1000000000000 : ℝ)*(base49) + (1016519073183/1000000000000 : ℝ)*(base50) + (1949/250000000000 : ℝ)*(base54) + (341551643191/500000000000 : ℝ)*(base59) + (41253/20000 : ℝ)*(major_s1_0) + (41253/20000 : ℝ)*(major_s1_1) + (515662498051/250000000000 : ℝ)*(major_s1_2) + (3061300359413/1000000000000 : ℝ)*(sp_s1_0) + (2016046631421/500000000000 : ℝ)*(sp_s1_1) + (1530650184433/500000000000 : ℝ)*(sp_s1_2) + (2920710259/100000000000 : ℝ)*(sp_s1_6) + (1530650188331/500000000000 : ℝ)*(f.sum) + (87616673852797037/577389426562500000000000000000 : ℝ)*base62 + (122544332829109/2552350000000000000000000000 : ℝ)*base64 + (2014072485947/7239000000000000000000000 : ℝ)*base66 + (178743374285513/1276175000000000000000000000 : ℝ)*base68 + (2947897127269108243/24491074425000000000000000000000 : ℝ)*base71 + (11327600596739/23988750000000000000000000 : ℝ)*base72 + (3941916855643/18097500000000000000000000 : ℝ)*base74 + (7442190663239/19191000000000000000000000 : ℝ)*base77 + (8960046606345721/15435961000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p026_b005 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 14 ≤ c.val) (hhi : c.val < 16)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=14 ∨ c=15 := by omega
  rcases hc with rfl|rfl
  · exact collision_c326014 p hpa (by linarith only [hpb]) X hX
  · exact collision_c326015 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 14 ≤ c.val) (hhi : c.val < 16)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b005 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b034
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:27:27.771638+00:00
-- url     : https://prove2.me/submissions/a075adfd-a2ec-4bd8-9b95-6ee2917cc822

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
theorem collision_support_c329070_s0_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-549273067/2500000000 : ℝ)*x 0 + (-460052161/1250000000 : ℝ)*x 1 + (-1492477149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549273067/2500000000 : ℝ)^95 ≤ (8082054083959/50000000000000 : ℝ)^79 := by
    have hnat : (549273067 : ℕ)^95*50000000000000^79 ≤ 8082054083959^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549273067 2500000000 8082054083959 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (460052161/1250000000 : ℝ)^95 ≤ (3757400533341/12500000000000 : ℝ)^79 := by
    have hnat : (460052161 : ℕ)^95*12500000000000^79 ≤ 3757400533341^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460052161 1250000000 3757400533341 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1492477149/2500000000 : ℝ)^95 ≤ (53776687548097/100000000000000 : ℝ)^79 := by
    have hnat : (1492477149 : ℕ)^95*100000000000000^79 ≤ 53776687548097^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1492477149 2500000000 53776687548097 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549273067/2500000000 : ℝ), (-460052161/1250000000 : ℝ), (-1492477149/2500000000 : ℝ)] ![(8082054083959/50000000000000 : ℝ), (3757400533341/12500000000000 : ℝ), (53776687548097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549273067/2500000000 : ℝ)|^95 ≤ (8082054083959/50000000000000 : ℝ)^79
        have hw : |(-549273067/2500000000 : ℝ)|=(549273067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-460052161/1250000000 : ℝ)|^95 ≤ (3757400533341/12500000000000 : ℝ)^79
        have hw : |(-460052161/1250000000 : ℝ)|=(460052161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1492477149/2500000000 : ℝ)|^95 ≤ (53776687548097/100000000000000 : ℝ)^79
        have hw : |(-1492477149/2500000000 : ℝ)|=(1492477149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329070_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5969908003/10000000000 : ℝ)*x 0 + (736083459/2000000000 : ℝ)*x 1 + (-2197092987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5969908003/10000000000 : ℝ)^95 ≤ (5377668112451/10000000000000 : ℝ)^79 := by
    have hnat : (5969908003 : ℕ)^95*10000000000000^79 ≤ 5377668112451^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5969908003 10000000000 5377668112451 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (736083459/2000000000 : ℝ)^95 ≤ (15029602167739/50000000000000 : ℝ)^79 := by
    have hnat : (736083459 : ℕ)^95*50000000000000^79 ≤ 15029602167739^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736083459 2000000000 15029602167739 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197092987/10000000000 : ℝ)^95 ≤ (16164114528969/100000000000000 : ℝ)^79 := by
    have hnat : (2197092987 : ℕ)^95*100000000000000^79 ≤ 16164114528969^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197092987 10000000000 16164114528969 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5969908003/10000000000 : ℝ), (736083459/2000000000 : ℝ), (-2197092987/10000000000 : ℝ)] ![(5377668112451/10000000000000 : ℝ), (15029602167739/50000000000000 : ℝ), (16164114528969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5969908003/10000000000 : ℝ)|^95 ≤ (5377668112451/10000000000000 : ℝ)^79
        have hw : |(5969908003/10000000000 : ℝ)|=(5969908003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(736083459/2000000000 : ℝ)|^95 ≤ (15029602167739/50000000000000 : ℝ)^79
        have hw : |(736083459/2000000000 : ℝ)|=(736083459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2197092987/10000000000 : ℝ)|^95 ≤ (16164114528969/100000000000000 : ℝ)^79
        have hw : |(-2197092987/10000000000 : ℝ)|=(2197092987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329070_s0_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3508802383/10000000000 : ℝ)*x 0 + (-4979443947/10000000000 : ℝ)*x 1 + (140352141/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3508802383/10000000000 : ℝ)^95 ≤ (3547718949733/12500000000000 : ℝ)^79 := by
    have hnat : (3508802383 : ℕ)^95*12500000000000^79 ≤ 3547718949733^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3508802383 10000000000 3547718949733 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4979443947/10000000000 : ℝ)^95 ≤ (4323648568823/10000000000000 : ℝ)^79 := by
    have hnat : (4979443947 : ℕ)^95*10000000000000^79 ≤ 4323648568823^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4979443947 10000000000 4323648568823 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140352141/400000000 : ℝ)^95 ≤ (7095440676511/25000000000000 : ℝ)^79 := by
    have hnat : (140352141 : ℕ)^95*25000000000000^79 ≤ 7095440676511^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140352141 400000000 7095440676511 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3508802383/10000000000 : ℝ), (-4979443947/10000000000 : ℝ), (140352141/400000000 : ℝ)] ![(3547718949733/12500000000000 : ℝ), (4323648568823/10000000000000 : ℝ), (7095440676511/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3508802383/10000000000 : ℝ)|^95 ≤ (3547718949733/12500000000000 : ℝ)^79
        have hw : |(3508802383/10000000000 : ℝ)|=(3508802383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4979443947/10000000000 : ℝ)|^95 ≤ (4323648568823/10000000000000 : ℝ)^79
        have hw : |(-4979443947/10000000000 : ℝ)|=(4979443947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140352141/400000000 : ℝ)|^95 ≤ (7095440676511/25000000000000 : ℝ)^79
        have hw : |(140352141/400000000 : ℝ)|=(140352141/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329070_s0_3 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9999999999/10000000000 : ℝ)*x 0 + (3/2000000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9999999999/10000000000 : ℝ)^95 ≤ (3999999999519/4000000000000 : ℝ)^79 := by
    have hnat : (9999999999 : ℕ)^95*4000000000000^79 ≤ 3999999999519^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999999 10000000000 3999999999519 4000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3/2000000000 : ℝ)^95 ≤ (2449/100000000000000 : ℝ)^79 := by
    have hnat : (3 : ℕ)^95*100000000000000^79 ≤ 2449^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3 2000000000 2449 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^95 ≤ (0 : ℝ)^79 := by
    have hnat : (0 : ℕ)^95*1^79 ≤ 0^79*1^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9999999999/10000000000 : ℝ), (3/2000000000 : ℝ), (0 : ℝ)] ![(3999999999519/4000000000000 : ℝ), (2449/100000000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9999999999/10000000000 : ℝ)|^95 ≤ (3999999999519/4000000000000 : ℝ)^79
        have hw : |(9999999999/10000000000 : ℝ)|=(9999999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3/2000000000 : ℝ)|^95 ≤ (2449/100000000000000 : ℝ)^79
        have hw : |(3/2000000000 : ℝ)|=(3/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^95 ≤ (0 : ℝ)^79
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329070_s0_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (946771697/2000000000 : ℝ)*x 0 + (-1236197531/5000000000 : ℝ)*x 1 + (-1183464741/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (946771697/2000000000 : ℝ)^95 ≤ (40685165339177/100000000000000 : ℝ)^79 := by
    have hnat : (946771697 : ℕ)^95*100000000000000^79 ≤ 40685165339177^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946771697 2000000000 40685165339177 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1236197531/5000000000 : ℝ)^95 ≤ (18629664361533/100000000000000 : ℝ)^79 := by
    have hnat : (1236197531 : ℕ)^95*100000000000000^79 ≤ 18629664361533^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1236197531 5000000000 18629664361533 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1183464741/2500000000 : ℝ)^95 ≤ (1017129257243/2500000000000 : ℝ)^79 := by
    have hnat : (1183464741 : ℕ)^95*2500000000000^79 ≤ 1017129257243^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183464741 2500000000 1017129257243 2500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(946771697/2000000000 : ℝ), (-1236197531/5000000000 : ℝ), (-1183464741/2500000000 : ℝ)] ![(40685165339177/100000000000000 : ℝ), (18629664361533/100000000000000 : ℝ), (1017129257243/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(946771697/2000000000 : ℝ)|^95 ≤ (40685165339177/100000000000000 : ℝ)^79
        have hw : |(946771697/2000000000 : ℝ)|=(946771697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1236197531/5000000000 : ℝ)|^95 ≤ (18629664361533/100000000000000 : ℝ)^79
        have hw : |(-1236197531/5000000000 : ℝ)|=(1236197531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1183464741/2500000000 : ℝ)|^95 ≤ (1017129257243/2500000000000 : ℝ)^79
        have hw : |(-1183464741/2500000000 : ℝ)|=(1183464741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329070 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]]) : False := by
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
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-549273067/2500000000 : ℝ)*X 0 0+(-460052161/1250000000 : ℝ)*X 0 1+(-1492477149/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329070_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5969908003/10000000000 : ℝ)*X 1 0+(736083459/2000000000 : ℝ)*X 1 1+(-2197092987/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329070_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3508802383/10000000000 : ℝ)*X 2 0+(-4979443947/10000000000 : ℝ)*X 2 1+(140352141/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329070_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((9999999999/10000000000 : ℝ)*X 1 0+(3/2000000000 : ℝ)*X 1 1+(9999999999/10000000000 : ℝ)*X 2 0+(3/2000000000 : ℝ)*X 2 1+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329070_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((946771697/2000000000 : ℝ)*X 0 0+(-1236197531/5000000000 : ℝ)*X 0 1+(-1183464741/2500000000 : ℝ)*X 0 2+(946771697/2000000000 : ℝ)*X 1 0+(-1236197531/5000000000 : ℝ)*X 1 1+(-1183464741/2500000000 : ℝ)*X 1 2+(946771697/2000000000 : ℝ)*X 2 0+(-1236197531/5000000000 : ℝ)*X 2 1+(-1183464741/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329070_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-129267/12500 : ℝ) < ((-55589/25000 : ℝ)*P 0+(-55589/25000 : ℝ)*P 1+(-55589/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-129267/12500 : ℝ) < (-5105088490161225585825243183/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (322271/1000000000000 : ℝ)*(base12) + (222341/500000000000 : ℝ)*(base15) + (279593/500000000000 : ℝ)*(base22) + (49723/100000000000 : ℝ)*(base33) + (410711416841/500000000000 : ℝ)*(base39) + (599994403/1600000000 : ℝ)*(base49) + (108547160851/200000000000 : ℝ)*(base59) + (222356151261/100000000000 : ℝ)*(major_s0_0) + (55589/25000 : ℝ)*(major_s0_1) + (55589/25000 : ℝ)*(major_s0_2) + (3403392004501/1000000000000 : ℝ)*(sp_s0_0) + (3403391384859/1000000000000 : ℝ)*(sp_s0_1) + (680678254071/200000000000 : ℝ)*(sp_s0_2) + (25123/12500000000 : ℝ)*(sp_s0_3) + (1 : ℝ)*(sp_s0_6) + (3403392326771/1000000000000 : ℝ)*(f.sum) + (154422187/2500000000000000000000 : ℝ)*base63 + (34749429/312500000000000000000 : ℝ)*base65 + (1270857919/2500000000000000000000 : ℝ)*base67 + (2112042183/10000000000000000000000 : ℝ)*base69 + (183999357771477/1000000000000000000000000000 : ℝ)*base71 + (381099537681061/1000000000000000000000000000 : ℝ)*base72 + (464597087/2000000000000000000000 : ℝ)*base75 + (190774727228523/1000000000000000000000000000 : ℝ)*base76 + (269703950481061/1000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c329071_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1728438157/5000000000 : ℝ)*x 0 + (2483465531/5000000000 : ℝ)*x 1 + (3573958313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1728438157/5000000000 : ℝ)^95 ≤ (6969357276671/25000000000000 : ℝ)^79 := by
    have hnat : (1728438157 : ℕ)^95*25000000000000^79 ≤ 6969357276671^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728438157 5000000000 6969357276671 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2483465531/5000000000 : ℝ)^95 ≤ (10776466179721/25000000000000 : ℝ)^79 := by
    have hnat : (2483465531 : ℕ)^95*25000000000000^79 ≤ 10776466179721^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2483465531 5000000000 10776466179721 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3573958313/10000000000 : ℝ)^95 ≤ (29016706165971/100000000000000 : ℝ)^79 := by
    have hnat : (3573958313 : ℕ)^95*100000000000000^79 ≤ 29016706165971^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3573958313 10000000000 29016706165971 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1728438157/5000000000 : ℝ), (2483465531/5000000000 : ℝ), (3573958313/10000000000 : ℝ)] ![(6969357276671/25000000000000 : ℝ), (10776466179721/25000000000000 : ℝ), (29016706165971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1728438157/5000000000 : ℝ)|^95 ≤ (6969357276671/25000000000000 : ℝ)^79
        have hw : |(1728438157/5000000000 : ℝ)|=(1728438157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2483465531/5000000000 : ℝ)|^95 ≤ (10776466179721/25000000000000 : ℝ)^79
        have hw : |(2483465531/5000000000 : ℝ)|=(2483465531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3573958313/10000000000 : ℝ)|^95 ≤ (29016706165971/100000000000000 : ℝ)^79
        have hw : |(3573958313/10000000000 : ℝ)|=(3573958313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s0_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (763594723/1250000000 : ℝ)*x 0 + (-3492765063/10000000000 : ℝ)*x 1 + (-2233854849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (763594723/1250000000 : ℝ)^95 ≤ (55284272011769/100000000000000 : ℝ)^79 := by
    have hnat : (763594723 : ℕ)^95*100000000000000^79 ≤ 55284272011769^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      763594723 1250000000 55284272011769 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3492765063/10000000000 : ℝ)^95 ≤ (2822582963553/10000000000000 : ℝ)^79 := by
    have hnat : (3492765063 : ℕ)^95*10000000000000^79 ≤ 2822582963553^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3492765063 10000000000 2822582963553 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2233854849/10000000000 : ℝ)^95 ≤ (515309322941/3125000000000 : ℝ)^79 := by
    have hnat : (2233854849 : ℕ)^95*3125000000000^79 ≤ 515309322941^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233854849 10000000000 515309322941 3125000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(763594723/1250000000 : ℝ), (-3492765063/10000000000 : ℝ), (-2233854849/10000000000 : ℝ)] ![(55284272011769/100000000000000 : ℝ), (2822582963553/10000000000000 : ℝ), (515309322941/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(763594723/1250000000 : ℝ)|^95 ≤ (55284272011769/100000000000000 : ℝ)^79
        have hw : |(763594723/1250000000 : ℝ)|=(763594723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3492765063/10000000000 : ℝ)|^95 ≤ (2822582963553/10000000000000 : ℝ)^79
        have hw : |(-3492765063/10000000000 : ℝ)|=(3492765063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2233854849/10000000000 : ℝ)|^95 ≤ (515309322941/3125000000000 : ℝ)^79
        have hw : |(-2233854849/10000000000 : ℝ)|=(2233854849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s0_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2279/5000000000 : ℝ)*x 0 + (-384199871/2000000000 : ℝ)*x 1 + (8842258721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2279/5000000000 : ℝ)^95 ≤ (2313/97656250000 : ℝ)^79 := by
    have hnat : (2279 : ℕ)^95*97656250000^79 ≤ 2313^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279 5000000000 2313 97656250000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (384199871/2000000000 : ℝ)^95 ≤ (343841914571/2500000000000 : ℝ)^79 := by
    have hnat : (384199871 : ℕ)^95*2500000000000^79 ≤ 343841914571^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384199871 2000000000 343841914571 2500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8842258721/10000000000 : ℝ)^95 ≤ (8624632103359/10000000000000 : ℝ)^79 := by
    have hnat : (8842258721 : ℕ)^95*10000000000000^79 ≤ 8624632103359^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8842258721 10000000000 8624632103359 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2279/5000000000 : ℝ), (-384199871/2000000000 : ℝ), (8842258721/10000000000 : ℝ)] ![(2313/97656250000 : ℝ), (343841914571/2500000000000 : ℝ), (8624632103359/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2279/5000000000 : ℝ)|^95 ≤ (2313/97656250000 : ℝ)^79
        have hw : |(-2279/5000000000 : ℝ)|=(2279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-384199871/2000000000 : ℝ)|^95 ≤ (343841914571/2500000000000 : ℝ)^79
        have hw : |(-384199871/2000000000 : ℝ)|=(384199871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8842258721/10000000000 : ℝ)|^95 ≤ (8624632103359/10000000000000 : ℝ)^79
        have hw : |(8842258721/10000000000 : ℝ)|=(8842258721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s0_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3541494263/10000000000 : ℝ)*x 0 + (-4268075867/10000000000 : ℝ)*x 1 + (4214547103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3541494263/10000000000 : ℝ)^95 ≤ (28700043252127/100000000000000 : ℝ)^79 := by
    have hnat : (3541494263 : ℕ)^95*100000000000000^79 ≤ 28700043252127^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3541494263 10000000000 28700043252127 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4268075867/10000000000 : ℝ)^95 ≤ (35920505151303/100000000000000 : ℝ)^79 := by
    have hnat : (4268075867 : ℕ)^95*100000000000000^79 ≤ 35920505151303^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268075867 10000000000 35920505151303 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4214547103/10000000000 : ℝ)^95 ≤ (35379451589869/100000000000000 : ℝ)^79 := by
    have hnat : (4214547103 : ℕ)^95*100000000000000^79 ≤ 35379451589869^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214547103 10000000000 35379451589869 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3541494263/10000000000 : ℝ), (-4268075867/10000000000 : ℝ), (4214547103/10000000000 : ℝ)] ![(28700043252127/100000000000000 : ℝ), (35920505151303/100000000000000 : ℝ), (35379451589869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3541494263/10000000000 : ℝ)|^95 ≤ (28700043252127/100000000000000 : ℝ)^79
        have hw : |(-3541494263/10000000000 : ℝ)|=(3541494263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4268075867/10000000000 : ℝ)|^95 ≤ (35920505151303/100000000000000 : ℝ)^79
        have hw : |(-4268075867/10000000000 : ℝ)|=(4268075867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4214547103/10000000000 : ℝ)|^95 ≤ (35379451589869/100000000000000 : ℝ)^79
        have hw : |(4214547103/10000000000 : ℝ)|=(4214547103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s0_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3420564113/10000000000 : ℝ)*x 0 + (2465779307/5000000000 : ℝ)*x 1 + (182380919/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3420564113/10000000000 : ℝ)^95 ≤ (5505132525619/20000000000000 : ℝ)^79 := by
    have hnat : (3420564113 : ℕ)^95*20000000000000^79 ≤ 5505132525619^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3420564113 10000000000 5505132525619 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2465779307/5000000000 : ℝ)^95 ≤ (5342121938841/12500000000000 : ℝ)^79 := by
    have hnat : (2465779307 : ℕ)^95*12500000000000^79 ≤ 5342121938841^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2465779307 5000000000 5342121938841 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182380919/500000000 : ℝ)^95 ≤ (29737361853973/100000000000000 : ℝ)^79 := by
    have hnat : (182380919 : ℕ)^95*100000000000000^79 ≤ 29737361853973^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182380919 500000000 29737361853973 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3420564113/10000000000 : ℝ), (2465779307/5000000000 : ℝ), (182380919/500000000 : ℝ)] ![(5505132525619/20000000000000 : ℝ), (5342121938841/12500000000000 : ℝ), (29737361853973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3420564113/10000000000 : ℝ)|^95 ≤ (5505132525619/20000000000000 : ℝ)^79
        have hw : |(3420564113/10000000000 : ℝ)|=(3420564113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2465779307/5000000000 : ℝ)|^95 ≤ (5342121938841/12500000000000 : ℝ)^79
        have hw : |(2465779307/5000000000 : ℝ)|=(2465779307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(182380919/500000000 : ℝ)|^95 ≤ (29737361853973/100000000000000 : ℝ)^79
        have hw : |(182380919/500000000 : ℝ)|=(182380919/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s0_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (374713621/625000000 : ℝ)*x 0 + (-3574099671/10000000000 : ℝ)*x 1 + (-2283186299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (374713621/625000000 : ℝ)^95 ≤ (27026566602429/50000000000000 : ℝ)^79 := by
    have hnat : (374713621 : ℕ)^95*50000000000000^79 ≤ 27026566602429^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374713621 625000000 27026566602429 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3574099671/10000000000 : ℝ)^95 ≤ (14509043143661/50000000000000 : ℝ)^79 := by
    have hnat : (3574099671 : ℕ)^95*50000000000000^79 ≤ 14509043143661^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3574099671 10000000000 14509043143661 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2283186299/10000000000 : ℝ)^95 ≤ (2116097561071/12500000000000 : ℝ)^79 := by
    have hnat : (2283186299 : ℕ)^95*12500000000000^79 ≤ 2116097561071^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283186299 10000000000 2116097561071 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(374713621/625000000 : ℝ), (-3574099671/10000000000 : ℝ), (-2283186299/10000000000 : ℝ)] ![(27026566602429/50000000000000 : ℝ), (14509043143661/50000000000000 : ℝ), (2116097561071/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(374713621/625000000 : ℝ)|^95 ≤ (27026566602429/50000000000000 : ℝ)^79
        have hw : |(374713621/625000000 : ℝ)|=(374713621/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3574099671/10000000000 : ℝ)|^95 ≤ (14509043143661/50000000000000 : ℝ)^79
        have hw : |(-3574099671/10000000000 : ℝ)|=(3574099671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2283186299/10000000000 : ℝ)|^95 ≤ (2116097561071/12500000000000 : ℝ)^79
        have hw : |(-2283186299/10000000000 : ℝ)|=(2283186299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s0_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-24549/10000000000 : ℝ)*x 0 + (-70214089/400000000 : ℝ)*x 1 + (8962595161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24549/10000000000 : ℝ)^95 ≤ (2242581/12500000000000 : ℝ)^79 := by
    have hnat : (24549 : ℕ)^95*12500000000000^79 ≤ 2242581^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24549 10000000000 2242581 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70214089/400000000 : ℝ)^95 ≤ (12340254800767/100000000000000 : ℝ)^79 := by
    have hnat : (70214089 : ℕ)^95*100000000000000^79 ≤ 12340254800767^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70214089 400000000 12340254800767 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8962595161/10000000000 : ℝ)^95 ≤ (87659727246899/100000000000000 : ℝ)^79 := by
    have hnat : (8962595161 : ℕ)^95*100000000000000^79 ≤ 87659727246899^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8962595161 10000000000 87659727246899 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24549/10000000000 : ℝ), (-70214089/400000000 : ℝ), (8962595161/10000000000 : ℝ)] ![(2242581/12500000000000 : ℝ), (12340254800767/100000000000000 : ℝ), (87659727246899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24549/10000000000 : ℝ)|^95 ≤ (2242581/12500000000000 : ℝ)^79
        have hw : |(-24549/10000000000 : ℝ)|=(24549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70214089/400000000 : ℝ)|^95 ≤ (12340254800767/100000000000000 : ℝ)^79
        have hw : |(-70214089/400000000 : ℝ)|=(70214089/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8962595161/10000000000 : ℝ)|^95 ≤ (87659727246899/100000000000000 : ℝ)^79
        have hw : |(8962595161/10000000000 : ℝ)|=(8962595161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s0_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3134619309/10000000000 : ℝ)*x 0 + (-341284103/1000000000 : ℝ)*x 1 + (5409606923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3134619309/10000000000 : ℝ)^95 ≤ (4956513341801/20000000000000 : ℝ)^79 := by
    have hnat : (3134619309 : ℕ)^95*20000000000000^79 ≤ 4956513341801^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3134619309 10000000000 4956513341801 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341284103/1000000000 : ℝ)^95 ≤ (27450944171077/100000000000000 : ℝ)^79 := by
    have hnat : (341284103 : ℕ)^95*100000000000000^79 ≤ 27450944171077^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341284103 1000000000 27450944171077 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409606923/10000000000 : ℝ)^95 ≤ (47766489096593/100000000000000 : ℝ)^79 := by
    have hnat : (5409606923 : ℕ)^95*100000000000000^79 ≤ 47766489096593^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409606923 10000000000 47766489096593 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3134619309/10000000000 : ℝ), (-341284103/1000000000 : ℝ), (5409606923/10000000000 : ℝ)] ![(4956513341801/20000000000000 : ℝ), (27450944171077/100000000000000 : ℝ), (47766489096593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3134619309/10000000000 : ℝ)|^95 ≤ (4956513341801/20000000000000 : ℝ)^79
        have hw : |(-3134619309/10000000000 : ℝ)|=(3134619309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-341284103/1000000000 : ℝ)|^95 ≤ (27450944171077/100000000000000 : ℝ)^79
        have hw : |(-341284103/1000000000 : ℝ)|=(341284103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409606923/10000000000 : ℝ)|^95 ≤ (47766489096593/100000000000000 : ℝ)^79
        have hw : |(5409606923/10000000000 : ℝ)|=(5409606923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s0_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1024589219/2500000000 : ℝ)*x 0 + (4849181449/10000000000 : ℝ)*x 1 + (1521292817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1024589219/2500000000 : ℝ)^95 ≤ (8552459015711/25000000000000 : ℝ)^79 := by
    have hnat : (1024589219 : ℕ)^95*25000000000000^79 ≤ 8552459015711^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024589219 2500000000 8552459015711 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4849181449/10000000000 : ℝ)^95 ≤ (20939984230933/50000000000000 : ℝ)^79 := by
    have hnat : (4849181449 : ℕ)^95*50000000000000^79 ≤ 20939984230933^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4849181449 10000000000 20939984230933 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1521292817/5000000000 : ℝ)^95 ≤ (23910195459603/100000000000000 : ℝ)^79 := by
    have hnat : (1521292817 : ℕ)^95*100000000000000^79 ≤ 23910195459603^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521292817 5000000000 23910195459603 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1024589219/2500000000 : ℝ), (4849181449/10000000000 : ℝ), (1521292817/5000000000 : ℝ)] ![(8552459015711/25000000000000 : ℝ), (20939984230933/50000000000000 : ℝ), (23910195459603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1024589219/2500000000 : ℝ)|^95 ≤ (8552459015711/25000000000000 : ℝ)^79
        have hw : |(1024589219/2500000000 : ℝ)|=(1024589219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4849181449/10000000000 : ℝ)|^95 ≤ (20939984230933/50000000000000 : ℝ)^79
        have hw : |(4849181449/10000000000 : ℝ)|=(4849181449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1521292817/5000000000 : ℝ)|^95 ≤ (23910195459603/100000000000000 : ℝ)^79
        have hw : |(1521292817/5000000000 : ℝ)|=(1521292817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s0_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (20887213/31250000 : ℝ)*x 0 + (-130350531/400000000 : ℝ)*x 1 + (-353207523/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20887213/31250000 : ℝ)^95 ≤ (61601829134309/100000000000000 : ℝ)^79 := by
    have hnat : (20887213 : ℕ)^95*100000000000000^79 ≤ 61601829134309^79*31250000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20887213 31250000 61601829134309 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130350531/400000000 : ℝ)^95 ≤ (6491881846561/25000000000000 : ℝ)^79 := by
    have hnat : (130350531 : ℕ)^95*25000000000000^79 ≤ 6491881846561^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130350531 400000000 6491881846561 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (353207523/2000000000 : ℝ)^95 ≤ (12430643460329/100000000000000 : ℝ)^79 := by
    have hnat : (353207523 : ℕ)^95*100000000000000^79 ≤ 12430643460329^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353207523 2000000000 12430643460329 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20887213/31250000 : ℝ), (-130350531/400000000 : ℝ), (-353207523/2000000000 : ℝ)] ![(61601829134309/100000000000000 : ℝ), (6491881846561/25000000000000 : ℝ), (12430643460329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20887213/31250000 : ℝ)|^95 ≤ (61601829134309/100000000000000 : ℝ)^79
        have hw : |(20887213/31250000 : ℝ)|=(20887213/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130350531/400000000 : ℝ)|^95 ≤ (6491881846561/25000000000000 : ℝ)^79
        have hw : |(-130350531/400000000 : ℝ)|=(130350531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-353207523/2000000000 : ℝ)|^95 ≤ (12430643460329/100000000000000 : ℝ)^79
        have hw : |(-353207523/2000000000 : ℝ)|=(353207523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s0_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-223/10000000000 : ℝ)*x 0 + (-1854349769/10000000000 : ℝ)*x 1 + (2222745279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223/10000000000 : ℝ)^95 ≤ (15723/25000000000000 : ℝ)^79 := by
    have hnat : (223 : ℕ)^95*25000000000000^79 ≤ 15723^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223 10000000000 15723 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1854349769/10000000000 : ℝ)^95 ≤ (13181878552433/100000000000000 : ℝ)^79 := by
    have hnat : (1854349769 : ℕ)^95*100000000000000^79 ≤ 13181878552433^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854349769 10000000000 13181878552433 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2222745279/2500000000 : ℝ)^95 ≤ (86818121380529/100000000000000 : ℝ)^79 := by
    have hnat : (2222745279 : ℕ)^95*100000000000000^79 ≤ 86818121380529^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222745279 2500000000 86818121380529 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-223/10000000000 : ℝ), (-1854349769/10000000000 : ℝ), (2222745279/2500000000 : ℝ)] ![(15723/25000000000000 : ℝ), (13181878552433/100000000000000 : ℝ), (86818121380529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-223/10000000000 : ℝ)|^95 ≤ (15723/25000000000000 : ℝ)^79
        have hw : |(-223/10000000000 : ℝ)|=(223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1854349769/10000000000 : ℝ)|^95 ≤ (13181878552433/100000000000000 : ℝ)^79
        have hw : |(-1854349769/10000000000 : ℝ)|=(1854349769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2222745279/2500000000 : ℝ)|^95 ≤ (86818121380529/100000000000000 : ℝ)^79
        have hw : |(2222745279/2500000000 : ℝ)|=(2222745279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s0_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-783378979/2500000000 : ℝ)*x 0 + (-4117295269/10000000000 : ℝ)*x 1 + (2373832443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (783378979/2500000000 : ℝ)^95 ≤ (24772076775497/100000000000000 : ℝ)^79 := by
    have hnat : (783378979 : ℕ)^95*100000000000000^79 ≤ 24772076775497^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783378979 2500000000 24772076775497 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4117295269/10000000000 : ℝ)^95 ≤ (34400024359343/100000000000000 : ℝ)^79 := by
    have hnat : (4117295269 : ℕ)^95*100000000000000^79 ≤ 34400024359343^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4117295269 10000000000 34400024359343 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2373832443/5000000000 : ℝ)^95 ≤ (10206974713421/25000000000000 : ℝ)^79 := by
    have hnat : (2373832443 : ℕ)^95*25000000000000^79 ≤ 10206974713421^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2373832443 5000000000 10206974713421 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-783378979/2500000000 : ℝ), (-4117295269/10000000000 : ℝ), (2373832443/5000000000 : ℝ)] ![(24772076775497/100000000000000 : ℝ), (34400024359343/100000000000000 : ℝ), (10206974713421/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-783378979/2500000000 : ℝ)|^95 ≤ (24772076775497/100000000000000 : ℝ)^79
        have hw : |(-783378979/2500000000 : ℝ)|=(783378979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4117295269/10000000000 : ℝ)|^95 ≤ (34400024359343/100000000000000 : ℝ)^79
        have hw : |(-4117295269/10000000000 : ℝ)|=(4117295269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2373832443/5000000000 : ℝ)|^95 ≤ (10206974713421/25000000000000 : ℝ)^79
        have hw : |(2373832443/5000000000 : ℝ)|=(2373832443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s0_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2892862/9765625 : ℝ)*x 0 + (649860527/1250000000 : ℝ)*x 1 + (380719593/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2892862/9765625 : ℝ)^95 ≤ (2894180210203/12500000000000 : ℝ)^79 := by
    have hnat : (2892862 : ℕ)^95*12500000000000^79 ≤ 2894180210203^79*9765625^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2892862 9765625 2894180210203 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649860527/1250000000 : ℝ)^95 ≤ (22768947934013/50000000000000 : ℝ)^79 := by
    have hnat : (649860527 : ℕ)^95*50000000000000^79 ≤ 22768947934013^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649860527 1250000000 22768947934013 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (380719593/1000000000 : ℝ)^95 ≤ (31308662432723/100000000000000 : ℝ)^79 := by
    have hnat : (380719593 : ℕ)^95*100000000000000^79 ≤ 31308662432723^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380719593 1000000000 31308662432723 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2892862/9765625 : ℝ), (649860527/1250000000 : ℝ), (380719593/1000000000 : ℝ)] ![(2894180210203/12500000000000 : ℝ), (22768947934013/50000000000000 : ℝ), (31308662432723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2892862/9765625 : ℝ)|^95 ≤ (2894180210203/12500000000000 : ℝ)^79
        have hw : |(2892862/9765625 : ℝ)|=(2892862/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(649860527/1250000000 : ℝ)|^95 ≤ (22768947934013/50000000000000 : ℝ)^79
        have hw : |(649860527/1250000000 : ℝ)|=(649860527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(380719593/1000000000 : ℝ)|^95 ≤ (31308662432723/100000000000000 : ℝ)^79
        have hw : |(380719593/1000000000 : ℝ)|=(380719593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s0_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1358090741/2000000000 : ℝ)*x 0 + (-2974174901/10000000000 : ℝ)*x 1 + (-1943801871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1358090741/2000000000 : ℝ)^95 ≤ (62784577857931/100000000000000 : ℝ)^79 := by
    have hnat : (1358090741 : ℕ)^95*100000000000000^79 ≤ 62784577857931^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358090741 2000000000 62784577857931 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2974174901/10000000000 : ℝ)^95 ≤ (11632593718783/50000000000000 : ℝ)^79 := by
    have hnat : (2974174901 : ℕ)^95*50000000000000^79 ≤ 11632593718783^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2974174901 10000000000 11632593718783 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1943801871/10000000000 : ℝ)^95 ≤ (1395023468967/10000000000000 : ℝ)^79 := by
    have hnat : (1943801871 : ℕ)^95*10000000000000^79 ≤ 1395023468967^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943801871 10000000000 1395023468967 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1358090741/2000000000 : ℝ), (-2974174901/10000000000 : ℝ), (-1943801871/10000000000 : ℝ)] ![(62784577857931/100000000000000 : ℝ), (11632593718783/50000000000000 : ℝ), (1395023468967/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1358090741/2000000000 : ℝ)|^95 ≤ (62784577857931/100000000000000 : ℝ)^79
        have hw : |(1358090741/2000000000 : ℝ)|=(1358090741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2974174901/10000000000 : ℝ)|^95 ≤ (11632593718783/50000000000000 : ℝ)^79
        have hw : |(-2974174901/10000000000 : ℝ)|=(2974174901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1943801871/10000000000 : ℝ)|^95 ≤ (1395023468967/10000000000000 : ℝ)^79
        have hw : |(-1943801871/10000000000 : ℝ)|=(1943801871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s1_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3321025401/10000000000 : ℝ)*x 0 + (-3682200541/10000000000 : ℝ)*x 1 + (199643089/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3321025401/10000000000 : ℝ)^95 ≤ (26565296510093/100000000000000 : ℝ)^79 := by
    have hnat : (3321025401 : ℕ)^95*100000000000000^79 ≤ 26565296510093^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3321025401 10000000000 26565296510093 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3682200541/10000000000 : ℝ)^95 ≤ (15038359654719/50000000000000 : ℝ)^79 := by
    have hnat : (3682200541 : ℕ)^95*50000000000000^79 ≤ 15038359654719^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3682200541 10000000000 15038359654719 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199643089/400000000 : ℝ)^95 ≤ (43357984164191/100000000000000 : ℝ)^79 := by
    have hnat : (199643089 : ℕ)^95*100000000000000^79 ≤ 43357984164191^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199643089 400000000 43357984164191 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3321025401/10000000000 : ℝ), (-3682200541/10000000000 : ℝ), (199643089/400000000 : ℝ)] ![(26565296510093/100000000000000 : ℝ), (15038359654719/50000000000000 : ℝ), (43357984164191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3321025401/10000000000 : ℝ)|^95 ≤ (26565296510093/100000000000000 : ℝ)^79
        have hw : |(-3321025401/10000000000 : ℝ)|=(3321025401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3682200541/10000000000 : ℝ)|^95 ≤ (15038359654719/50000000000000 : ℝ)^79
        have hw : |(-3682200541/10000000000 : ℝ)|=(3682200541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(199643089/400000000 : ℝ)|^95 ≤ (43357984164191/100000000000000 : ℝ)^79
        have hw : |(199643089/400000000 : ℝ)|=(199643089/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s1_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4050571677/10000000000 : ℝ)*x 0 + (900455199/2000000000 : ℝ)*x 1 + (1732978619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4050571677/10000000000 : ℝ)^95 ≤ (33730746785831/100000000000000 : ℝ)^79 := by
    have hnat : (4050571677 : ℕ)^95*100000000000000^79 ≤ 33730746785831^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4050571677 10000000000 33730746785831 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900455199/2000000000 : ℝ)^95 ≤ (38303737287901/100000000000000 : ℝ)^79 := by
    have hnat : (900455199 : ℕ)^95*100000000000000^79 ≤ 38303737287901^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900455199 2000000000 38303737287901 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1732978619/5000000000 : ℝ)^95 ≤ (873922372303/3125000000000 : ℝ)^79 := by
    have hnat : (1732978619 : ℕ)^95*3125000000000^79 ≤ 873922372303^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732978619 5000000000 873922372303 3125000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4050571677/10000000000 : ℝ), (900455199/2000000000 : ℝ), (1732978619/5000000000 : ℝ)] ![(33730746785831/100000000000000 : ℝ), (38303737287901/100000000000000 : ℝ), (873922372303/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4050571677/10000000000 : ℝ)|^95 ≤ (33730746785831/100000000000000 : ℝ)^79
        have hw : |(4050571677/10000000000 : ℝ)|=(4050571677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900455199/2000000000 : ℝ)|^95 ≤ (38303737287901/100000000000000 : ℝ)^79
        have hw : |(900455199/2000000000 : ℝ)|=(900455199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1732978619/5000000000 : ℝ)|^95 ≤ (873922372303/3125000000000 : ℝ)^79
        have hw : |(1732978619/5000000000 : ℝ)|=(1732978619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s1_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (489818421/1000000000 : ℝ)*x 0 + (-125768489/312500000 : ℝ)*x 1 + (-1533433011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (489818421/1000000000 : ℝ)^95 ≤ (2649338391413/6250000000000 : ℝ)^79 := by
    have hnat : (489818421 : ℕ)^95*6250000000000^79 ≤ 2649338391413^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489818421 1000000000 2649338391413 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125768489/312500000 : ℝ)^95 ≤ (33470752904681/100000000000000 : ℝ)^79 := by
    have hnat : (125768489 : ℕ)^95*100000000000000^79 ≤ 33470752904681^79*312500000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125768489 312500000 33470752904681 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1533433011/5000000000 : ℝ)^95 ≤ (965593312489/4000000000000 : ℝ)^79 := by
    have hnat : (1533433011 : ℕ)^95*4000000000000^79 ≤ 965593312489^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1533433011 5000000000 965593312489 4000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(489818421/1000000000 : ℝ), (-125768489/312500000 : ℝ), (-1533433011/5000000000 : ℝ)] ![(2649338391413/6250000000000 : ℝ), (33470752904681/100000000000000 : ℝ), (965593312489/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(489818421/1000000000 : ℝ)|^95 ≤ (2649338391413/6250000000000 : ℝ)^79
        have hw : |(489818421/1000000000 : ℝ)|=(489818421/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-125768489/312500000 : ℝ)|^95 ≤ (33470752904681/100000000000000 : ℝ)^79
        have hw : |(-125768489/312500000 : ℝ)|=(125768489/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1533433011/5000000000 : ℝ)|^95 ≤ (965593312489/4000000000000 : ℝ)^79
        have hw : |(-1533433011/5000000000 : ℝ)|=(1533433011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329071_s1_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2948923487/10000000000 : ℝ)*x 0 + (-96211127/312500000 : ℝ)*x 1 + (734021347/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2948923487/10000000000 : ℝ)^95 ≤ (23027860045287/100000000000000 : ℝ)^79 := by
    have hnat : (2948923487 : ℕ)^95*100000000000000^79 ≤ 23027860045287^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2948923487 10000000000 23027860045287 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96211127/312500000 : ℝ)^95 ≤ (24252420176537/100000000000000 : ℝ)^79 := by
    have hnat : (96211127 : ℕ)^95*100000000000000^79 ≤ 24252420176537^79*312500000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96211127 312500000 24252420176537 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (734021347/1250000000 : ℝ)^95 ≤ (52719719759149/100000000000000 : ℝ)^79 := by
    have hnat : (734021347 : ℕ)^95*100000000000000^79 ≤ 52719719759149^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734021347 1250000000 52719719759149 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2948923487/10000000000 : ℝ), (-96211127/312500000 : ℝ), (734021347/1250000000 : ℝ)] ![(23027860045287/100000000000000 : ℝ), (24252420176537/100000000000000 : ℝ), (52719719759149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2948923487/10000000000 : ℝ)|^95 ≤ (23027860045287/100000000000000 : ℝ)^79
        have hw : |(2948923487/10000000000 : ℝ)|=(2948923487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-96211127/312500000 : ℝ)|^95 ≤ (24252420176537/100000000000000 : ℝ)^79
        have hw : |(-96211127/312500000 : ℝ)|=(96211127/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(734021347/1250000000 : ℝ)|^95 ≤ (52719719759149/100000000000000 : ℝ)^79
        have hw : |(734021347/1250000000 : ℝ)|=(734021347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329071 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]]) : False := by
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
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (160257/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((1728438157/5000000000 : ℝ)*X 1 0+(2483465531/5000000000 : ℝ)*X 1 1+(3573958313/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((763594723/1250000000 : ℝ)*X 2 0+(-3492765063/10000000000 : ℝ)*X 2 1+(-2233854849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((-2279/5000000000 : ℝ)*X 0 0+(-384199871/2000000000 : ℝ)*X 0 1+(8842258721/10000000000 : ℝ)*X 0 2+(-2279/5000000000 : ℝ)*X 1 0+(-384199871/2000000000 : ℝ)*X 1 1+(8842258721/10000000000 : ℝ)*X 1 2+(-2279/5000000000 : ℝ)*X 2 0+(-384199871/2000000000 : ℝ)*X 2 1+(8842258721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-3541494263/10000000000 : ℝ)*X 0 0+(-4268075867/10000000000 : ℝ)*X 0 1+(4214547103/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3420564113/10000000000 : ℝ)*X 1 0+(2465779307/5000000000 : ℝ)*X 1 1+(182380919/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((374713621/625000000 : ℝ)*X 2 0+(-3574099671/10000000000 : ℝ)*X 2 1+(-2283186299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-24549/10000000000 : ℝ)*X 0 0+(-70214089/400000000 : ℝ)*X 0 1+(8962595161/10000000000 : ℝ)*X 0 2+(-24549/10000000000 : ℝ)*X 1 0+(-70214089/400000000 : ℝ)*X 1 1+(8962595161/10000000000 : ℝ)*X 1 2+(-24549/10000000000 : ℝ)*X 2 0+(-70214089/400000000 : ℝ)*X 2 1+(8962595161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-3134619309/10000000000 : ℝ)*X 0 0+(-341284103/1000000000 : ℝ)*X 0 1+(5409606923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1024589219/2500000000 : ℝ)*X 1 0+(4849181449/10000000000 : ℝ)*X 1 1+(1521292817/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((20887213/31250000 : ℝ)*X 2 0+(-130350531/400000000 : ℝ)*X 2 1+(-353207523/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-223/10000000000 : ℝ)*X 0 0+(-1854349769/10000000000 : ℝ)*X 0 1+(2222745279/2500000000 : ℝ)*X 0 2+(-223/10000000000 : ℝ)*X 1 0+(-1854349769/10000000000 : ℝ)*X 1 1+(2222745279/2500000000 : ℝ)*X 1 2+(-223/10000000000 : ℝ)*X 2 0+(-1854349769/10000000000 : ℝ)*X 2 1+(2222745279/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-783378979/2500000000 : ℝ)*X 0 0+(-4117295269/10000000000 : ℝ)*X 0 1+(2373832443/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2892862/9765625 : ℝ)*X 1 0+(649860527/1250000000 : ℝ)*X 1 1+(380719593/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1358090741/2000000000 : ℝ)*X 2 0+(-2974174901/10000000000 : ℝ)*X 2 1+(-1943801871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((18799/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18799/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (44457647238660865453707/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (303725837131/1000000000000 : ℝ)*(base1) + (153025674833/200000000000 : ℝ)*(base7) + (164540276721/500000000000 : ℝ)*(base40) + (334381/50000000000 : ℝ)*(base54) + (219527819787/125000000000 : ℝ)*(base60) + (5259607211497/1000000000000 : ℝ)*(major_s0_0) + (5259607211497/1000000000000 : ℝ)*(major_s0_1) + (5259600523877/1000000000000 : ℝ)*(major_s0_2) + (87737319/250000000000 : ℝ)*(sp_s0_1) + (804881409527/100000000000 : ℝ)*(sp_s0_7) + (121011520451/15625000000 : ℝ)*(sp_s0_8) + (193627039263/25000000000 : ℝ)*(sp_s0_9) + (141283543503/50000000000 : ℝ)*(sp_s0_13) + (281063541/250000000000 : ℝ)*(sp_s0_20) + (236539927481/100000000000 : ℝ)*(f.failure) + (387254412907/50000000000 : ℝ)*(f.sum) + (402441196484477/2500000000000000000000000000 : ℝ)*base63 + (5902512754577523/10000000000000000000000000000 : ℝ)*base64 + (3434936443914529/10000000000000000000000000000 : ℝ)*base67 + (2676089340911811/10000000000000000000000000000 : ℝ)*base69 + (1756670757331497/5000000000000000000000000000 : ℝ)*base70 + (1267191531026097/10000000000000000000000000000 : ℝ)*base72 + (919127931026097/10000000000000000000000000000 : ℝ)*base75 + (183543526085471/10000000000000000000000000000 : ℝ)*base76 + (197971974680527/625000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1191/2500000000000000 : ℝ)*base86 + (1191/2500000000000000 : ℝ)*base88 + (1191/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-6729/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-6729/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12061312558639064511957/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1311300060787/1000000000000 : ℝ)*(base1) + (387488205253/250000000000 : ℝ)*(base7) + (102743343437/100000000000 : ℝ)*(base40) + (729712050933/500000000000 : ℝ)*(base60) + (2353222996289/500000000000 : ℝ)*(major_s0_0) + (2353222996289/500000000000 : ℝ)*(major_s0_1) + (2353222996289/500000000000 : ℝ)*(major_s0_2) + (2138037/200000000000 : ℝ)*(sp_s0_2) + (158018703/500000000000 : ℝ)*(sp_s0_13) + (972449130577/125000000000 : ℝ)*(sp_s0_14) + (646829298383/100000000000 : ℝ)*(sp_s0_15) + (3234072270309/500000000000 : ℝ)*(sp_s0_16) + (1177481605167/500000000000 : ℝ)*(sp_s0_20) + (137753027/1000000000000 : ℝ)*(sp_s0_23) + (423325297503/200000000000 : ℝ)*(f.failure) + (646829298383/100000000000 : ℝ)*(f.sum) + (76271146691399/312500000000000000000000000 : ℝ)*base62 + (286982709756489/5000000000000000000000000000 : ℝ)*base65 + (1019620260181127/5000000000000000000000000000 : ℝ)*base66 + (1201005930818873/5000000000000000000000000000 : ℝ)*base68 + (634620606787681/2500000000000000000000000000 : ℝ)*base71 + (3252436536756489/5000000000000000000000000000 : ℝ)*base72 + (994896917743511/5000000000000000000000000000 : ℝ)*base74 + (1664454142818873/5000000000000000000000000000 : ℝ)*base77 + (171527407621101/312500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (4267/5000000000000000 : ℝ)*base87 + (4267/5000000000000000 : ℝ)*base89 + (4267/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(33393/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(33393/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18677318296931186921943/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1434685074667/500000000000 : ℝ)*(base1) + (258910654993/200000000000 : ℝ)*(base7) + (1649319405363/1000000000000 : ℝ)*(base40) + (81868757537/125000000000 : ℝ)*(base60) + (3501705523067/1000000000000 : ℝ)*(major_s0_0) + (3501705523067/1000000000000 : ℝ)*(major_s0_1) + (3501705523067/1000000000000 : ℝ)*(major_s0_2) + (44115693/1000000000000 : ℝ)*(sp_s0_1) + (1284853/500000000000 : ℝ)*(sp_s0_6) + (1364097/1000000000000 : ℝ)*(sp_s0_7) + (95929883/1000000000000 : ℝ)*(sp_s0_16) + (1901605120757/250000000000 : ℝ)*(sp_s0_21) + (4737007582097/1000000000000 : ℝ)*(sp_s0_22) + (1184238941977/250000000000 : ℝ)*(sp_s0_23) + (62992777763/40000000000 : ℝ)*(f.failure) + (473705169779/100000000000 : ℝ)*(f.sum) + (11804639478897/625000000000000000000000000 : ℝ)*base62 + (9480296906363667/10000000000000000000000000000 : ℝ)*base65 + (8749262840973981/10000000000000000000000000000 : ℝ)*base66 + (4627047374026019/10000000000000000000000000000 : ℝ)*base68 + (1304038670694843/5000000000000000000000000000 : ℝ)*base71 + (2405892790363667/10000000000000000000000000000 : ℝ)*base72 + (7510908826636333/10000000000000000000000000000 : ℝ)*base74 + (3212622547026019/10000000000000000000000000000 : ℝ)*base77 + (34433889103897/625000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (407/1000000000000000 : ℝ)*base87 + (407/1000000000000000 : ℝ)*base89 + (407/1000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (18799/100000 : ℝ) ^ (93/16 : ℝ) ≤ (1509552531206139/25000000000000000000 : ℝ) := by
    have hpowers : (18799/100000 : ℝ)^93 ≤ (1509552531206139/25000000000000000000 : ℝ)^16 := by
      have hnat : (18799 : ℕ)^93*25000000000000000000^16 ≤ 1509552531206139^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18799 100000 1509552531206139 25000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18799/100000 : ℝ)) (X := (1509552531206139/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (25001509552531206139/25000000000000000000 : ℝ) ≤ (10000103880588283/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (25001509552531206139/25000000000000000000 : ℝ)^16 ≤ (10000103880588283/10000000000000000 : ℝ)^93 := by
      have hnat : (25001509552531206139 : ℕ)^16*10000000000000000^93 ≤ 10000103880588283^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001509552531206139 25000000000000000000 10000103880588283 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000103880588283/10000000000000000 : ℝ)) (X := (25001509552531206139/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (12501509552531206139/12500000000000000000 : ℝ) ≤ (1250025969497953/1250000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (12501509552531206139/12500000000000000000 : ℝ)^16 ≤ (1250025969497953/1250000000000000 : ℝ)^93 := by
      have hnat : (12501509552531206139 : ℕ)^16*1250000000000000^93 ≤ 1250025969497953^93*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501509552531206139 12500000000000000000 1250025969497953 1250000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250025969497953/1250000000000000 : ℝ)) (X := (12501509552531206139/12500000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(103880588283/1879900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(103875395341/1879900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (18799/100000 : ℝ)) (alpha := (103880588283/1879900000000000 : ℝ)) (beta := (103875395341/1879900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (18799/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(103880588283/1879900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(103875395341/1879900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (6729/12500 : ℝ) ^ (93/16 : ℝ) ≤ (341651245391784423/12500000000000000000 : ℝ) := by
    have hpowers : (6729/12500 : ℝ)^93 ≤ (341651245391784423/12500000000000000000 : ℝ)^16 := by
      have hnat : (6729 : ℕ)^93*12500000000000000000^16 ≤ 341651245391784423^16*12500^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6729 12500 341651245391784423 12500000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6729/12500 : ℝ)) (X := (341651245391784423/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (12841651245391784423/12500000000000000000 : ℝ) ≤ (10046499600064409/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (12841651245391784423/12500000000000000000 : ℝ)^16 ≤ (10046499600064409/10000000000000000 : ℝ)^93 := by
      have hnat : (12841651245391784423 : ℕ)^16*10000000000000000^93 ≤ 10046499600064409^93*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12841651245391784423 12500000000000000000 10046499600064409 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10046499600064409/10000000000000000 : ℝ)) (X := (12841651245391784423/12500000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (6591651245391784423/6250000000000000000 : ℝ) ≤ (630749121926063/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (6591651245391784423/6250000000000000000 : ℝ)^16 ≤ (630749121926063/625000000000000 : ℝ)^93 := by
      have hnat : (6591651245391784423 : ℕ)^16*625000000000000^93 ≤ 630749121926063^93*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6591651245391784423 6250000000000000000 630749121926063 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (630749121926063/625000000000000 : ℝ)) (X := (6591651245391784423/6250000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(46499600064409/5383200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(15162116917533/1794400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (6729/12500 : ℝ)) (alpha := (46499600064409/5383200000000000 : ℝ)) (beta := (15162116917533/1794400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (6729/12500 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(46499600064409/5383200000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(15162116917533/1794400000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (33393/100000 : ℝ) ^ (93/16 : ℝ) ≤ (21289097124793057/12500000000000000000 : ℝ) := by
    have hpowers : (33393/100000 : ℝ)^93 ≤ (21289097124793057/12500000000000000000 : ℝ)^16 := by
      have hnat : (33393 : ℕ)^93*12500000000000000000^16 ≤ 21289097124793057^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33393 100000 21289097124793057 12500000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33393/100000 : ℝ)) (X := (21289097124793057/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (12521289097124793057/12500000000000000000 : ℝ) ≤ (5001464024266923/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (12521289097124793057/12500000000000000000 : ℝ)^16 ≤ (5001464024266923/5000000000000000 : ℝ)^93 := by
      have hnat : (12521289097124793057 : ℕ)^16*5000000000000000^93 ≤ 5001464024266923^93*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12521289097124793057 12500000000000000000 5001464024266923 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001464024266923/5000000000000000 : ℝ)) (X := (12521289097124793057/12500000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (6271289097124793057/6250000000000000000 : ℝ) ≤ (1250731497261893/1250000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (6271289097124793057/6250000000000000000 : ℝ)^16 ≤ (1250731497261893/1250000000000000 : ℝ)^93 := by
      have hnat : (6271289097124793057 : ℕ)^16*1250000000000000^93 ≤ 1250731497261893^93*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6271289097124793057 6250000000000000000 1250731497261893 1250000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250731497261893/1250000000000000 : ℝ)) (X := (6271289097124793057/6250000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1464024266923/1669650000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1461964780649/1669650000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (33393/100000 : ℝ)) (alpha := (1464024266923/1669650000000000 : ℝ)) (beta := (1461964780649/1669650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (33393/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1464024266923/1669650000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1461964780649/1669650000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3321025401/10000000000 : ℝ)*X 0 0+(-3682200541/10000000000 : ℝ)*X 0 1+(199643089/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4050571677/10000000000 : ℝ)*X 1 0+(900455199/2000000000 : ℝ)*X 1 1+(1732978619/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((489818421/1000000000 : ℝ)*X 2 0+(-125768489/312500000 : ℝ)*X 2 1+(-1533433011/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2948923487/10000000000 : ℝ)*X 0 0+(-96211127/312500000 : ℝ)*X 0 1+(734021347/1250000000 : ℝ)*X 0 2+(2948923487/10000000000 : ℝ)*X 1 0+(-96211127/312500000 : ℝ)*X 1 1+(734021347/1250000000 : ℝ)*X 1 2+(2948923487/10000000000 : ℝ)*X 2 0+(-96211127/312500000 : ℝ)*X 2 1+(734021347/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329071_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-129267/12500 : ℝ) < ((-55589/25000 : ℝ)*P 0+(-55589/25000 : ℝ)*P 1+(-55589/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-129267/12500 : ℝ) < (-23755802889403254298050487637642619/2346757467835000000000000000000000 : ℝ) := by norm_num
    linear_combination (324324288351/1000000000000 : ℝ)*(base1) + (83/100000000000 : ℝ)*(base10) + (121/500000000000 : ℝ)*(base19) + (1759/250000000000 : ℝ)*(base24) + (328702933013/500000000000 : ℝ)*(base40) + (352738824171/1000000000000 : ℝ)*(base49) + (1043/1000000000000 : ℝ)*(base50) + (10243517449/15625000000 : ℝ)*(base60) + (55589/25000 : ℝ)*(major_s1_0) + (55589/25000 : ℝ)*(major_s1_1) + (55589/25000 : ℝ)*(major_s1_2) + (739719508797/200000000000 : ℝ)*(sp_s1_0) + (3374273256221/1000000000000 : ℝ)*(sp_s1_1) + (1687136624713/500000000000 : ℝ)*(sp_s1_2) + (675675711649/1000000000000 : ℝ)*(sp_s1_6) + (3374273256463/1000000000000 : ℝ)*(f.sum) + (396827356413299039/374502495000000000000000000000 : ℝ)*base63 + (65220937663453/333930000000000000000000000 : ℝ)*base65 + (11062949394521/67290000000000000000000000 : ℝ)*base66 + (3927681006419/8348250000000000000000000 : ℝ)*base69 + (3793250945016722513/6277550070000000000000000000000 : ℝ)*base70 + (6026713863189/93995000000000000000000000 : ℝ)*base72 + (16025216117911/22430000000000000000000000 : ℝ)*base75 + (2520301725137/5874687500000000000000000 : ℝ)*base76 + (76580656680075173/316246177500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p029_b034 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=70 ∨ c=71 := by omega
  rcases hc with rfl|rfl
  · exact collision_c329070 p hpa (by linarith only [hpb]) X hX
  · exact collision_c329071 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b034 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

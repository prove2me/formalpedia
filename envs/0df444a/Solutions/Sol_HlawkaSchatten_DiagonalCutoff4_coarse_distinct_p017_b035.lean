-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017_b035
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:14:20.833812+00:00
-- url     : https://prove2.me/submissions/66356bc9-be32-445e-910c-90a575d7f28b

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
theorem collision_support_c317081_s0_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-269449241/625000000 : ℝ)*x 0 + (2597058139/10000000000 : ℝ)*x 1 + (43871201/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269449241/625000000 : ℝ)^39 ≤ (3469759593733/10000000000000 : ℝ)^31 := by
    have hnat : (269449241 : ℕ)^39*10000000000000^31 ≤ 3469759593733^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269449241 625000000 3469759593733 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2597058139/10000000000 : ℝ)^39 ≤ (9169595382491/50000000000000 : ℝ)^31 := by
    have hnat : (2597058139 : ℕ)^39*50000000000000^31 ≤ 9169595382491^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597058139 10000000000 9169595382491 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43871201/80000000 : ℝ)^39 ≤ (11740803318727/25000000000000 : ℝ)^31 := by
    have hnat : (43871201 : ℕ)^39*25000000000000^31 ≤ 11740803318727^31*80000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43871201 80000000 11740803318727 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269449241/625000000 : ℝ), (2597058139/10000000000 : ℝ), (43871201/80000000 : ℝ)] ![(3469759593733/10000000000000 : ℝ), (9169595382491/50000000000000 : ℝ), (11740803318727/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269449241/625000000 : ℝ)|^39 ≤ (3469759593733/10000000000000 : ℝ)^31
        have hw : |(-269449241/625000000 : ℝ)|=(269449241/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2597058139/10000000000 : ℝ)|^39 ≤ (9169595382491/50000000000000 : ℝ)^31
        have hw : |(2597058139/10000000000 : ℝ)|=(2597058139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43871201/80000000 : ℝ)|^39 ≤ (11740803318727/25000000000000 : ℝ)^31
        have hw : |(43871201/80000000 : ℝ)|=(43871201/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s0_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3922430291/10000000000 : ℝ)*x 0 + (3467930079/5000000000 : ℝ)*x 1 + (-540090443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3922430291/10000000000 : ℝ)^39 ≤ (30808195550719/100000000000000 : ℝ)^31 := by
    have hnat : (3922430291 : ℕ)^39*100000000000000^31 ≤ 30808195550719^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3922430291 10000000000 30808195550719 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3467930079/5000000000 : ℝ)^39 ≤ (63109386936729/100000000000000 : ℝ)^31 := by
    have hnat : (3467930079 : ℕ)^39*100000000000000^31 ≤ 63109386936729^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3467930079 5000000000 63109386936729 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540090443/5000000000 : ℝ)^39 ≤ (3041208749621/50000000000000 : ℝ)^31 := by
    have hnat : (540090443 : ℕ)^39*50000000000000^31 ≤ 3041208749621^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540090443 5000000000 3041208749621 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3922430291/10000000000 : ℝ), (3467930079/5000000000 : ℝ), (-540090443/5000000000 : ℝ)] ![(30808195550719/100000000000000 : ℝ), (63109386936729/100000000000000 : ℝ), (3041208749621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3922430291/10000000000 : ℝ)|^39 ≤ (30808195550719/100000000000000 : ℝ)^31
        have hw : |(3922430291/10000000000 : ℝ)|=(3922430291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3467930079/5000000000 : ℝ)|^39 ≤ (63109386936729/100000000000000 : ℝ)^31
        have hw : |(3467930079/5000000000 : ℝ)|=(3467930079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-540090443/5000000000 : ℝ)|^39 ≤ (3041208749621/50000000000000 : ℝ)^31
        have hw : |(-540090443/5000000000 : ℝ)|=(540090443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s0_7 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1134539723/2500000000 : ℝ)*x 0 + (1152522651/5000000000 : ℝ)*x 1 + (5506341837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1134539723/2500000000 : ℝ)^39 ≤ (37011145151767/100000000000000 : ℝ)^31 := by
    have hnat : (1134539723 : ℕ)^39*100000000000000^31 ≤ 37011145151767^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134539723 2500000000 37011145151767 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1152522651/5000000000 : ℝ)^39 ≤ (3945932559687/25000000000000 : ℝ)^31 := by
    have hnat : (1152522651 : ℕ)^39*25000000000000^31 ≤ 3945932559687^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152522651 5000000000 3945932559687 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5506341837/10000000000 : ℝ)^39 ≤ (590064057477/1250000000000 : ℝ)^31 := by
    have hnat : (5506341837 : ℕ)^39*1250000000000^31 ≤ 590064057477^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506341837 10000000000 590064057477 1250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1134539723/2500000000 : ℝ), (1152522651/5000000000 : ℝ), (5506341837/10000000000 : ℝ)] ![(37011145151767/100000000000000 : ℝ), (3945932559687/25000000000000 : ℝ), (590064057477/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1134539723/2500000000 : ℝ)|^39 ≤ (37011145151767/100000000000000 : ℝ)^31
        have hw : |(-1134539723/2500000000 : ℝ)|=(1134539723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1152522651/5000000000 : ℝ)|^39 ≤ (3945932559687/25000000000000 : ℝ)^31
        have hw : |(1152522651/5000000000 : ℝ)|=(1152522651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5506341837/10000000000 : ℝ)|^39 ≤ (590064057477/1250000000000 : ℝ)^31
        have hw : |(5506341837/10000000000 : ℝ)|=(5506341837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s0_8 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4806242237/10000000000 : ℝ)*x 0 + (-2441211591/10000000000 : ℝ)*x 1 + (5136554869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4806242237/10000000000 : ℝ)^39 ≤ (9945600146521/25000000000000 : ℝ)^31 := by
    have hnat : (4806242237 : ℕ)^39*25000000000000^31 ≤ 9945600146521^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4806242237 10000000000 9945600146521 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2441211591/10000000000 : ℝ)^39 ≤ (4241389158223/25000000000000 : ℝ)^31 := by
    have hnat : (2441211591 : ℕ)^39*25000000000000^31 ≤ 4241389158223^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2441211591 10000000000 4241389158223 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5136554869/10000000000 : ℝ)^39 ≤ (10813010689959/25000000000000 : ℝ)^31 := by
    have hnat : (5136554869 : ℕ)^39*25000000000000^31 ≤ 10813010689959^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136554869 10000000000 10813010689959 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4806242237/10000000000 : ℝ), (-2441211591/10000000000 : ℝ), (5136554869/10000000000 : ℝ)] ![(9945600146521/25000000000000 : ℝ), (4241389158223/25000000000000 : ℝ), (10813010689959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4806242237/10000000000 : ℝ)|^39 ≤ (9945600146521/25000000000000 : ℝ)^31
        have hw : |(4806242237/10000000000 : ℝ)|=(4806242237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2441211591/10000000000 : ℝ)|^39 ≤ (4241389158223/25000000000000 : ℝ)^31
        have hw : |(-2441211591/10000000000 : ℝ)|=(2441211591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5136554869/10000000000 : ℝ)|^39 ≤ (10813010689959/25000000000000 : ℝ)^31
        have hw : |(5136554869/10000000000 : ℝ)|=(5136554869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s0_9 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (679133749/2000000000 : ℝ)*x 0 + (379469767/500000000 : ℝ)*x 1 + (-715729987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (679133749/2000000000 : ℝ)^39 ≤ (513929777619/2000000000000 : ℝ)^31 := by
    have hnat : (679133749 : ℕ)^39*2000000000000^31 ≤ 513929777619^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679133749 2000000000 513929777619 2000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (379469767/500000000 : ℝ)^39 ≤ (1413588146803/2000000000000 : ℝ)^31 := by
    have hnat : (379469767 : ℕ)^39*2000000000000^31 ≤ 1413588146803^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379469767 500000000 1413588146803 2000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (715729987/10000000000 : ℝ)^39 ≤ (1812051879503/50000000000000 : ℝ)^31 := by
    have hnat : (715729987 : ℕ)^39*50000000000000^31 ≤ 1812051879503^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715729987 10000000000 1812051879503 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(679133749/2000000000 : ℝ), (379469767/500000000 : ℝ), (-715729987/10000000000 : ℝ)] ![(513929777619/2000000000000 : ℝ), (1413588146803/2000000000000 : ℝ), (1812051879503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(679133749/2000000000 : ℝ)|^39 ≤ (513929777619/2000000000000 : ℝ)^31
        have hw : |(679133749/2000000000 : ℝ)|=(679133749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(379469767/500000000 : ℝ)|^39 ≤ (1413588146803/2000000000000 : ℝ)^31
        have hw : |(379469767/500000000 : ℝ)|=(379469767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-715729987/10000000000 : ℝ)|^39 ≤ (1812051879503/50000000000000 : ℝ)^31
        have hw : |(-715729987/10000000000 : ℝ)|=(715729987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s0_12 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (880024689/5000000000 : ℝ)*x 0 + (786749919/2000000000 : ℝ)*x 1 + (1294264113/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (880024689/5000000000 : ℝ)^39 ≤ (1405178839311/12500000000000 : ℝ)^31 := by
    have hnat : (880024689 : ℕ)^39*12500000000000^31 ≤ 1405178839311^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880024689 5000000000 1405178839311 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (786749919/2000000000 : ℝ)^39 ≤ (966252705341/3125000000000 : ℝ)^31 := by
    have hnat : (786749919 : ℕ)^39*3125000000000^31 ≤ 966252705341^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786749919 2000000000 966252705341 3125000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294264113/2000000000 : ℝ)^39 ≤ (57838482698163/100000000000000 : ℝ)^31 := by
    have hnat : (1294264113 : ℕ)^39*100000000000000^31 ≤ 57838482698163^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294264113 2000000000 57838482698163 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(880024689/5000000000 : ℝ), (786749919/2000000000 : ℝ), (1294264113/2000000000 : ℝ)] ![(1405178839311/12500000000000 : ℝ), (966252705341/3125000000000 : ℝ), (57838482698163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(880024689/5000000000 : ℝ)|^39 ≤ (1405178839311/12500000000000 : ℝ)^31
        have hw : |(880024689/5000000000 : ℝ)|=(880024689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(786749919/2000000000 : ℝ)|^39 ≤ (966252705341/3125000000000 : ℝ)^31
        have hw : |(786749919/2000000000 : ℝ)|=(786749919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294264113/2000000000 : ℝ)|^39 ≤ (57838482698163/100000000000000 : ℝ)^31
        have hw : |(1294264113/2000000000 : ℝ)|=(1294264113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s0_13 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-250147063/625000000 : ℝ)*x 0 + (1064698387/5000000000 : ℝ)*x 1 + (6137858209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (250147063/625000000 : ℝ)^39 ≤ (31600001597347/100000000000000 : ℝ)^31 := by
    have hnat : (250147063 : ℕ)^39*100000000000000^31 ≤ 31600001597347^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250147063 625000000 31600001597347 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064698387/5000000000 : ℝ)^39 ≤ (14285763435887/100000000000000 : ℝ)^31 := by
    have hnat : (1064698387 : ℕ)^39*100000000000000^31 ≤ 14285763435887^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064698387 5000000000 14285763435887 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6137858209/10000000000 : ℝ)^39 ≤ (54114234951399/100000000000000 : ℝ)^31 := by
    have hnat : (6137858209 : ℕ)^39*100000000000000^31 ≤ 54114234951399^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6137858209 10000000000 54114234951399 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-250147063/625000000 : ℝ), (1064698387/5000000000 : ℝ), (6137858209/10000000000 : ℝ)] ![(31600001597347/100000000000000 : ℝ), (14285763435887/100000000000000 : ℝ), (54114234951399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-250147063/625000000 : ℝ)|^39 ≤ (31600001597347/100000000000000 : ℝ)^31
        have hw : |(-250147063/625000000 : ℝ)|=(250147063/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1064698387/5000000000 : ℝ)|^39 ≤ (14285763435887/100000000000000 : ℝ)^31
        have hw : |(1064698387/5000000000 : ℝ)|=(1064698387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6137858209/10000000000 : ℝ)|^39 ≤ (54114234951399/100000000000000 : ℝ)^31
        have hw : |(6137858209/10000000000 : ℝ)|=(6137858209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s0_14 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5200462589/10000000000 : ℝ)*x 0 + (-1467849593/5000000000 : ℝ)*x 1 + (2154387673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5200462589/10000000000 : ℝ)^39 ≤ (43930129809577/100000000000000 : ℝ)^31 := by
    have hnat : (5200462589 : ℕ)^39*100000000000000^31 ≤ 43930129809577^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200462589 10000000000 43930129809577 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1467849593/5000000000 : ℝ)^39 ≤ (2139669971479/10000000000000 : ℝ)^31 := by
    have hnat : (1467849593 : ℕ)^39*10000000000000^31 ≤ 2139669971479^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1467849593 5000000000 2139669971479 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2154387673/5000000000 : ℝ)^39 ≤ (6934634091439/20000000000000 : ℝ)^31 := by
    have hnat : (2154387673 : ℕ)^39*20000000000000^31 ≤ 6934634091439^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154387673 5000000000 6934634091439 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5200462589/10000000000 : ℝ), (-1467849593/5000000000 : ℝ), (2154387673/5000000000 : ℝ)] ![(43930129809577/100000000000000 : ℝ), (2139669971479/10000000000000 : ℝ), (6934634091439/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5200462589/10000000000 : ℝ)|^39 ≤ (43930129809577/100000000000000 : ℝ)^31
        have hw : |(5200462589/10000000000 : ℝ)|=(5200462589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1467849593/5000000000 : ℝ)|^39 ≤ (2139669971479/10000000000000 : ℝ)^31
        have hw : |(-1467849593/5000000000 : ℝ)|=(1467849593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2154387673/5000000000 : ℝ)|^39 ≤ (6934634091439/20000000000000 : ℝ)^31
        have hw : |(2154387673/5000000000 : ℝ)|=(2154387673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s0_15 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3995604581/10000000000 : ℝ)*x 0 + (1424010583/2000000000 : ℝ)*x 1 + (-65506481/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3995604581/10000000000 : ℝ)^39 ≤ (15766492479047/50000000000000 : ℝ)^31 := by
    have hnat : (3995604581 : ℕ)^39*50000000000000^31 ≤ 15766492479047^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3995604581 10000000000 15766492479047 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1424010583/2000000000 : ℝ)^39 ≤ (65225043155841/100000000000000 : ℝ)^31 := by
    have hnat : (1424010583 : ℕ)^39*100000000000000^31 ≤ 65225043155841^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424010583 2000000000 65225043155841 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65506481/1000000000 : ℝ)^39 ≤ (810492968309/25000000000000 : ℝ)^31 := by
    have hnat : (65506481 : ℕ)^39*25000000000000^31 ≤ 810492968309^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65506481 1000000000 810492968309 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3995604581/10000000000 : ℝ), (1424010583/2000000000 : ℝ), (-65506481/1000000000 : ℝ)] ![(15766492479047/50000000000000 : ℝ), (65225043155841/100000000000000 : ℝ), (810492968309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3995604581/10000000000 : ℝ)|^39 ≤ (15766492479047/50000000000000 : ℝ)^31
        have hw : |(3995604581/10000000000 : ℝ)|=(3995604581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1424010583/2000000000 : ℝ)|^39 ≤ (65225043155841/100000000000000 : ℝ)^31
        have hw : |(1424010583/2000000000 : ℝ)|=(1424010583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65506481/1000000000 : ℝ)|^39 ≤ (810492968309/25000000000000 : ℝ)^31
        have hw : |(-65506481/1000000000 : ℝ)|=(65506481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s0_18 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-27/5000000000 : ℝ)*x 0 + (0 : ℝ)*x 1 + (9999999999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27/5000000000 : ℝ)^39 ≤ (3971/100000000000000 : ℝ)^31 := by
    have hnat : (27 : ℕ)^39*100000000000000^31 ≤ 3971^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27 5000000000 3971 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^39 ≤ (0 : ℝ)^31 := by
    have hnat : (0 : ℕ)^39*1^31 ≤ 0^31*1^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9999999999/10000000000 : ℝ)^39 ≤ (4999999999371/5000000000000 : ℝ)^31 := by
    have hnat : (9999999999 : ℕ)^39*5000000000000^31 ≤ 4999999999371^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999999 10000000000 4999999999371 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27/5000000000 : ℝ), (0 : ℝ), (9999999999/10000000000 : ℝ)] ![(3971/100000000000000 : ℝ), (0 : ℝ), (4999999999371/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27/5000000000 : ℝ)|^39 ≤ (3971/100000000000000 : ℝ)^31
        have hw : |(-27/5000000000 : ℝ)|=(27/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^39 ≤ (0 : ℝ)^31
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9999999999/10000000000 : ℝ)|^39 ≤ (4999999999371/5000000000000 : ℝ)^31
        have hw : |(9999999999/10000000000 : ℝ)|=(9999999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s0_19 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1692937501/10000000000 : ℝ)*x 0 + (3200884617/10000000000 : ℝ)*x 1 + (7138624037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1692937501/10000000000 : ℝ)^39 ≤ (535242417167/5000000000000 : ℝ)^31 := by
    have hnat : (1692937501 : ℕ)^39*5000000000000^31 ≤ 535242417167^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692937501 10000000000 535242417167 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3200884617/10000000000 : ℝ)^39 ≤ (11928003848647/50000000000000 : ℝ)^31 := by
    have hnat : (3200884617 : ℕ)^39*50000000000000^31 ≤ 11928003848647^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3200884617 10000000000 11928003848647 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7138624037/10000000000 : ℝ)^39 ≤ (32719571969127/50000000000000 : ℝ)^31 := by
    have hnat : (7138624037 : ℕ)^39*50000000000000^31 ≤ 32719571969127^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7138624037 10000000000 32719571969127 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1692937501/10000000000 : ℝ), (3200884617/10000000000 : ℝ), (7138624037/10000000000 : ℝ)] ![(535242417167/5000000000000 : ℝ), (11928003848647/50000000000000 : ℝ), (32719571969127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1692937501/10000000000 : ℝ)|^39 ≤ (535242417167/5000000000000 : ℝ)^31
        have hw : |(1692937501/10000000000 : ℝ)|=(1692937501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3200884617/10000000000 : ℝ)|^39 ≤ (11928003848647/50000000000000 : ℝ)^31
        have hw : |(3200884617/10000000000 : ℝ)|=(3200884617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7138624037/10000000000 : ℝ)|^39 ≤ (32719571969127/50000000000000 : ℝ)^31
        have hw : |(7138624037/10000000000 : ℝ)|=(7138624037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s0_20 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4632614881/10000000000 : ℝ)*x 0 + (2419938963/10000000000 : ℝ)*x 1 + (332693587/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4632614881/10000000000 : ℝ)^39 ≤ (9495717942801/25000000000000 : ℝ)^31 := by
    have hnat : (4632614881 : ℕ)^39*25000000000000^31 ≤ 9495717942801^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4632614881 10000000000 9495717942801 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2419938963/10000000000 : ℝ)^39 ≤ (16779777426517/100000000000000 : ℝ)^31 := by
    have hnat : (2419938963 : ℕ)^39*100000000000000^31 ≤ 16779777426517^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2419938963 10000000000 16779777426517 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (332693587/625000000 : ℝ)^39 ≤ (9047470158391/20000000000000 : ℝ)^31 := by
    have hnat : (332693587 : ℕ)^39*20000000000000^31 ≤ 9047470158391^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332693587 625000000 9047470158391 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4632614881/10000000000 : ℝ), (2419938963/10000000000 : ℝ), (332693587/625000000 : ℝ)] ![(9495717942801/25000000000000 : ℝ), (16779777426517/100000000000000 : ℝ), (9047470158391/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4632614881/10000000000 : ℝ)|^39 ≤ (9495717942801/25000000000000 : ℝ)^31
        have hw : |(-4632614881/10000000000 : ℝ)|=(4632614881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2419938963/10000000000 : ℝ)|^39 ≤ (16779777426517/100000000000000 : ℝ)^31
        have hw : |(2419938963/10000000000 : ℝ)|=(2419938963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(332693587/625000000 : ℝ)|^39 ≤ (9047470158391/20000000000000 : ℝ)^31
        have hw : |(332693587/625000000 : ℝ)|=(332693587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s0_21 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (421511551/1000000000 : ℝ)*x 0 + (-3377680427/10000000000 : ℝ)*x 1 + (4898645163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421511551/1000000000 : ℝ)^39 ≤ (33727652958327/100000000000000 : ℝ)^31 := by
    have hnat : (421511551 : ℕ)^39*100000000000000^31 ≤ 33727652958327^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421511551 1000000000 33727652958327 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3377680427/10000000000 : ℝ)^39 ≤ (12762675807469/50000000000000 : ℝ)^31 := by
    have hnat : (3377680427 : ℕ)^39*50000000000000^31 ≤ 12762675807469^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3377680427 10000000000 12762675807469 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4898645163/10000000000 : ℝ)^39 ≤ (2037349770839/5000000000000 : ℝ)^31 := by
    have hnat : (4898645163 : ℕ)^39*5000000000000^31 ≤ 2037349770839^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4898645163 10000000000 2037349770839 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(421511551/1000000000 : ℝ), (-3377680427/10000000000 : ℝ), (4898645163/10000000000 : ℝ)] ![(33727652958327/100000000000000 : ℝ), (12762675807469/50000000000000 : ℝ), (2037349770839/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(421511551/1000000000 : ℝ)|^39 ≤ (33727652958327/100000000000000 : ℝ)^31
        have hw : |(421511551/1000000000 : ℝ)|=(421511551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3377680427/10000000000 : ℝ)|^39 ≤ (12762675807469/50000000000000 : ℝ)^31
        have hw : |(-3377680427/10000000000 : ℝ)|=(3377680427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4898645163/10000000000 : ℝ)|^39 ≤ (2037349770839/5000000000000 : ℝ)^31
        have hw : |(4898645163/10000000000 : ℝ)|=(4898645163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s0_22 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (548792031/1250000000 : ℝ)*x 0 + (3316842631/5000000000 : ℝ)*x 1 + (-112396519/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548792031/1250000000 : ℝ)^39 ≤ (7100176462149/20000000000000 : ℝ)^31 := by
    have hnat : (548792031 : ℕ)^39*20000000000000^31 ≤ 7100176462149^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548792031 1250000000 7100176462149 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3316842631/5000000000 : ℝ)^39 ≤ (11934002180533/20000000000000 : ℝ)^31 := by
    have hnat : (3316842631 : ℕ)^39*20000000000000^31 ≤ 11934002180533^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3316842631 5000000000 11934002180533 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112396519/1250000000 : ℝ)^39 ≤ (4829106783203/100000000000000 : ℝ)^31 := by
    have hnat : (112396519 : ℕ)^39*100000000000000^31 ≤ 4829106783203^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112396519 1250000000 4829106783203 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(548792031/1250000000 : ℝ), (3316842631/5000000000 : ℝ), (-112396519/1250000000 : ℝ)] ![(7100176462149/20000000000000 : ℝ), (11934002180533/20000000000000 : ℝ), (4829106783203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(548792031/1250000000 : ℝ)|^39 ≤ (7100176462149/20000000000000 : ℝ)^31
        have hw : |(548792031/1250000000 : ℝ)|=(548792031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3316842631/5000000000 : ℝ)|^39 ≤ (11934002180533/20000000000000 : ℝ)^31
        have hw : |(3316842631/5000000000 : ℝ)|=(3316842631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-112396519/1250000000 : ℝ)|^39 ≤ (4829106783203/100000000000000 : ℝ)^31
        have hw : |(-112396519/1250000000 : ℝ)|=(112396519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s0_26 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1589963053/10000000000 : ℝ)*x 0 + (3685318049/10000000000 : ℝ)*x 1 + (1701446121/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1589963053/10000000000 : ℝ)^39 ≤ (9892210821439/100000000000000 : ℝ)^31 := by
    have hnat : (1589963053 : ℕ)^39*100000000000000^31 ≤ 9892210821439^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1589963053 10000000000 9892210821439 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3685318049/10000000000 : ℝ)^39 ≤ (14241887552251/50000000000000 : ℝ)^31 := by
    have hnat : (3685318049 : ℕ)^39*50000000000000^31 ≤ 14241887552251^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3685318049 10000000000 14241887552251 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1701446121/2500000000 : ℝ)^39 ≤ (61624014057889/100000000000000 : ℝ)^31 := by
    have hnat : (1701446121 : ℕ)^39*100000000000000^31 ≤ 61624014057889^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1701446121 2500000000 61624014057889 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1589963053/10000000000 : ℝ), (3685318049/10000000000 : ℝ), (1701446121/2500000000 : ℝ)] ![(9892210821439/100000000000000 : ℝ), (14241887552251/50000000000000 : ℝ), (61624014057889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1589963053/10000000000 : ℝ)|^39 ≤ (9892210821439/100000000000000 : ℝ)^31
        have hw : |(1589963053/10000000000 : ℝ)|=(1589963053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3685318049/10000000000 : ℝ)|^39 ≤ (14241887552251/50000000000000 : ℝ)^31
        have hw : |(3685318049/10000000000 : ℝ)|=(3685318049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1701446121/2500000000 : ℝ)|^39 ≤ (61624014057889/100000000000000 : ℝ)^31
        have hw : |(1701446121/2500000000 : ℝ)|=(1701446121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s1_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4281934079/10000000000 : ℝ)*x 0 + (416439153/1250000000 : ℝ)*x 1 + (1219023377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4281934079/10000000000 : ℝ)^39 ≤ (34401654184373/100000000000000 : ℝ)^31 := by
    have hnat : (4281934079 : ℕ)^39*100000000000000^31 ≤ 34401654184373^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4281934079 10000000000 34401654184373 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416439153/1250000000 : ℝ)^39 ≤ (12543602014769/50000000000000 : ℝ)^31 := by
    have hnat : (416439153 : ℕ)^39*50000000000000^31 ≤ 12543602014769^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416439153 1250000000 12543602014769 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1219023377/2500000000 : ℝ)^39 ≤ (5063892721643/12500000000000 : ℝ)^31 := by
    have hnat : (1219023377 : ℕ)^39*12500000000000^31 ≤ 5063892721643^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1219023377 2500000000 5063892721643 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4281934079/10000000000 : ℝ), (416439153/1250000000 : ℝ), (1219023377/2500000000 : ℝ)] ![(34401654184373/100000000000000 : ℝ), (12543602014769/50000000000000 : ℝ), (5063892721643/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4281934079/10000000000 : ℝ)|^39 ≤ (34401654184373/100000000000000 : ℝ)^31
        have hw : |(-4281934079/10000000000 : ℝ)|=(4281934079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(416439153/1250000000 : ℝ)|^39 ≤ (12543602014769/50000000000000 : ℝ)^31
        have hw : |(416439153/1250000000 : ℝ)|=(416439153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1219023377/2500000000 : ℝ)|^39 ≤ (5063892721643/12500000000000 : ℝ)^31
        have hw : |(1219023377/2500000000 : ℝ)|=(1219023377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s1_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (277006573/625000000 : ℝ)*x 0 + (-3448352241/10000000000 : ℝ)*x 1 + (231105923/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277006573/625000000 : ℝ)^39 ≤ (35926313263251/100000000000000 : ℝ)^31 := by
    have hnat : (277006573 : ℕ)^39*100000000000000^31 ≤ 35926313263251^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277006573 625000000 35926313263251 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3448352241/10000000000 : ℝ)^39 ≤ (26199052697211/100000000000000 : ℝ)^31 := by
    have hnat : (3448352241 : ℕ)^39*100000000000000^31 ≤ 26199052697211^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3448352241 10000000000 26199052697211 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (231105923/500000000 : ℝ)^39 ≤ (37874634036267/100000000000000 : ℝ)^31 := by
    have hnat : (231105923 : ℕ)^39*100000000000000^31 ≤ 37874634036267^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231105923 500000000 37874634036267 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(277006573/625000000 : ℝ), (-3448352241/10000000000 : ℝ), (231105923/500000000 : ℝ)] ![(35926313263251/100000000000000 : ℝ), (26199052697211/100000000000000 : ℝ), (37874634036267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(277006573/625000000 : ℝ)|^39 ≤ (35926313263251/100000000000000 : ℝ)^31
        have hw : |(277006573/625000000 : ℝ)|=(277006573/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3448352241/10000000000 : ℝ)|^39 ≤ (26199052697211/100000000000000 : ℝ)^31
        have hw : |(-3448352241/10000000000 : ℝ)|=(3448352241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(231105923/500000000 : ℝ)|^39 ≤ (37874634036267/100000000000000 : ℝ)^31
        have hw : |(231105923/500000000 : ℝ)|=(231105923/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s1_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2105714257/5000000000 : ℝ)*x 0 + (5733449399/10000000000 : ℝ)*x 1 + (-2404134357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105714257/5000000000 : ℝ)^39 ≤ (16845270956417/50000000000000 : ℝ)^31 := by
    have hnat : (2105714257 : ℕ)^39*50000000000000^31 ≤ 16845270956417^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105714257 5000000000 16845270956417 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5733449399/10000000000 : ℝ)^39 ≤ (49667433818523/100000000000000 : ℝ)^31 := by
    have hnat : (5733449399 : ℕ)^39*100000000000000^31 ≤ 49667433818523^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5733449399 10000000000 49667433818523 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2404134357/10000000000 : ℝ)^39 ≤ (3328404848929/20000000000000 : ℝ)^31 := by
    have hnat : (2404134357 : ℕ)^39*20000000000000^31 ≤ 3328404848929^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2404134357 10000000000 3328404848929 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2105714257/5000000000 : ℝ), (5733449399/10000000000 : ℝ), (-2404134357/10000000000 : ℝ)] ![(16845270956417/50000000000000 : ℝ), (49667433818523/100000000000000 : ℝ), (3328404848929/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2105714257/5000000000 : ℝ)|^39 ≤ (16845270956417/50000000000000 : ℝ)^31
        have hw : |(2105714257/5000000000 : ℝ)|=(2105714257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5733449399/10000000000 : ℝ)|^39 ≤ (49667433818523/100000000000000 : ℝ)^31
        have hw : |(5733449399/10000000000 : ℝ)|=(5733449399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2404134357/10000000000 : ℝ)|^39 ≤ (3328404848929/20000000000000 : ℝ)^31
        have hw : |(-2404134357/10000000000 : ℝ)|=(2404134357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317081_s1_6 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (583309499/2000000000 : ℝ)*x 0 + (794119023/2000000000 : ℝ)*x 1 + (1106619711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (583309499/2000000000 : ℝ)^39 ≤ (1061061968949/5000000000000 : ℝ)^31 := by
    have hnat : (583309499 : ℕ)^39*5000000000000^31 ≤ 1061061968949^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583309499 2000000000 1061061968949 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (794119023/2000000000 : ℝ)^39 ≤ (15642439135107/50000000000000 : ℝ)^31 := by
    have hnat : (794119023 : ℕ)^39*50000000000000^31 ≤ 15642439135107^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794119023 2000000000 15642439135107 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106619711/2000000000 : ℝ)^39 ≤ (47493882332129/100000000000000 : ℝ)^31 := by
    have hnat : (1106619711 : ℕ)^39*100000000000000^31 ≤ 47493882332129^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106619711 2000000000 47493882332129 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(583309499/2000000000 : ℝ), (794119023/2000000000 : ℝ), (1106619711/2000000000 : ℝ)] ![(1061061968949/5000000000000 : ℝ), (15642439135107/50000000000000 : ℝ), (47493882332129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(583309499/2000000000 : ℝ)|^39 ≤ (1061061968949/5000000000000 : ℝ)^31
        have hw : |(583309499/2000000000 : ℝ)|=(583309499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(794119023/2000000000 : ℝ)|^39 ≤ (15642439135107/50000000000000 : ℝ)^31
        have hw : |(794119023/2000000000 : ℝ)|=(794119023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1106619711/2000000000 : ℝ)|^39 ≤ (47493882332129/100000000000000 : ℝ)^31
        have hw : |(1106619711/2000000000 : ℝ)|=(1106619711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317081 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-269449241/625000000 : ℝ)*X 0 0+(2597058139/10000000000 : ℝ)*X 0 1+(43871201/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3922430291/10000000000 : ℝ)*X 2 0+(3467930079/5000000000 : ℝ)*X 2 1+(-540090443/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1134539723/2500000000 : ℝ)*X 0 0+(1152522651/5000000000 : ℝ)*X 0 1+(5506341837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4806242237/10000000000 : ℝ)*X 1 0+(-2441211591/10000000000 : ℝ)*X 1 1+(5136554869/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((679133749/2000000000 : ℝ)*X 2 0+(379469767/500000000 : ℝ)*X 2 1+(-715729987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((880024689/5000000000 : ℝ)*X 0 0+(786749919/2000000000 : ℝ)*X 0 1+(1294264113/2000000000 : ℝ)*X 0 2+(880024689/5000000000 : ℝ)*X 1 0+(786749919/2000000000 : ℝ)*X 1 1+(1294264113/2000000000 : ℝ)*X 1 2+(880024689/5000000000 : ℝ)*X 2 0+(786749919/2000000000 : ℝ)*X 2 1+(1294264113/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-250147063/625000000 : ℝ)*X 0 0+(1064698387/5000000000 : ℝ)*X 0 1+(6137858209/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((5200462589/10000000000 : ℝ)*X 1 0+(-1467849593/5000000000 : ℝ)*X 1 1+(2154387673/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3995604581/10000000000 : ℝ)*X 2 0+(1424010583/2000000000 : ℝ)*X 2 1+(-65506481/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_18 : ((-27/5000000000 : ℝ)*X 0 0+(9999999999/10000000000 : ℝ)*X 0 2+(-27/5000000000 : ℝ)*X 1 0+(9999999999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s0_18 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((1692937501/10000000000 : ℝ)*X 0 0+(3200884617/10000000000 : ℝ)*X 0 1+(7138624037/10000000000 : ℝ)*X 0 2+(1692937501/10000000000 : ℝ)*X 1 0+(3200884617/10000000000 : ℝ)*X 1 1+(7138624037/10000000000 : ℝ)*X 1 2+(1692937501/10000000000 : ℝ)*X 2 0+(3200884617/10000000000 : ℝ)*X 2 1+(7138624037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-4632614881/10000000000 : ℝ)*X 0 0+(2419938963/10000000000 : ℝ)*X 0 1+(332693587/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((421511551/1000000000 : ℝ)*X 1 0+(-3377680427/10000000000 : ℝ)*X 1 1+(4898645163/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((548792031/1250000000 : ℝ)*X 2 0+(3316842631/5000000000 : ℝ)*X 2 1+(-112396519/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_26 : ((1589963053/10000000000 : ℝ)*X 0 0+(3685318049/10000000000 : ℝ)*X 0 1+(1701446121/2500000000 : ℝ)*X 0 2+(1589963053/10000000000 : ℝ)*X 1 0+(3685318049/10000000000 : ℝ)*X 1 1+(1701446121/2500000000 : ℝ)*X 1 2+(1589963053/10000000000 : ℝ)*X 2 0+(3685318049/10000000000 : ℝ)*X 2 1+(1701446121/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s0_26 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((19553/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19553/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4593004185667772679117/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (349447622227/200000000000 : ℝ)*(base49) + (577420340527/250000000000 : ℝ)*(base59) + (68770655817/500000000000 : ℝ)*(base60) + (6261296329239/1000000000000 : ℝ)*(major_s0_0) + (6261296329239/1000000000000 : ℝ)*(major_s0_1) + (6261296329239/1000000000000 : ℝ)*(major_s0_2) + (294689327/1000000000000 : ℝ)*(sp_s0_0) + (47730007/1000000000000 : ℝ)*(sp_s0_2) + (4520557533531/500000000000 : ℝ)*(sp_s0_7) + (9041422741191/1000000000000 : ℝ)*(sp_s0_8) + (565085938199/62500000000 : ℝ)*(sp_s0_9) + (348112125629/100000000000 : ℝ)*(sp_s0_12) + (6492401/500000000000 : ℝ)*(sp_s0_13) + (45598987/1000000000000 : ℝ)*(sp_s0_26) + (3481166855277/1000000000000 : ℝ)*(f.failure) + (9041422741191/1000000000000 : ℝ)*(f.sum) + (2619743149063799/2500000000000000000000000000 : ℝ)*base63 + (8830753517407207/10000000000000000000000000000 : ℝ)*base64 + (324344480337597/10000000000000000000000000000 : ℝ)*base67 + (3200456376662403/10000000000000000000000000000 : ℝ)*base69 + (712041028606961/1000000000000000000000000000 : ℝ)*base70 + (733950142407207/10000000000000000000000000000 : ℝ)*base73 + (3826818272592793/10000000000000000000000000000 : ℝ)*base75 + (757418153662403/10000000000000000000000000000 : ℝ)*base76 + (677356089186201/2500000000000000000000000000 : ℝ)*base79 + (34113/50000000000000000 : ℝ)*base86 + (34113/50000000000000000 : ℝ)*base88 + (34113/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((24351/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(24351/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (72963051478252209808359/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (321265072717/500000000000 : ℝ)*(base40) + (354473753747/200000000000 : ℝ)*(base49) + (2975904256903/1000000000000 : ℝ)*(base59) + (3897351056277/500000000000 : ℝ)*(major_s0_0) + (3897351056277/500000000000 : ℝ)*(major_s0_1) + (1558947350463/200000000000 : ℝ)*(major_s0_2) + (1594597/40000000000 : ℝ)*(sp_s0_7) + (58623249/1000000000000 : ℝ)*(sp_s0_8) + (11255646920471/1000000000000 : ℝ)*(sp_s0_13) + (11255628162147/1000000000000 : ℝ)*(sp_s0_14) + (11255545224771/1000000000000 : ℝ)*(sp_s0_15) + (432997/12500000000 : ℝ)*(sp_s0_18) + (866742515101/200000000000 : ℝ)*(sp_s0_19) + (226497/1600000000 : ℝ)*(sp_s0_22) + (866742515101/200000000000 : ℝ)*(f.failure) + (2813921696349/250000000000 : ℝ)*(f.sum) + (1874753075230547/10000000000000000000000000000 : ℝ)*base62 + (545337219776719/2000000000000000000000000000 : ℝ)*base64 + (1240462958793671/5000000000000000000000000000 : ℝ)*base67 + (1183977015327349/2000000000000000000000000000 : ℝ)*base68 + (2396461812703747/10000000000000000000000000000 : ℝ)*base71 + (1036096647296901/5000000000000000000000000000 : ℝ)*base73 + (3598684209296901/5000000000000000000000000000 : ℝ)*base74 + (2882854646706329/5000000000000000000000000000 : ℝ)*base76 + (409772775727357/1250000000000000000000000000 : ℝ)*base78 + (8031/10000000000000000 : ℝ)*base87 + (8031/10000000000000000 : ℝ)*base89 + (1969/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1063/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1063/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (41424947666066866665489/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53338766221/1000000000000 : ℝ)*(base40) + (1189835300707/1000000000000 : ℝ)*(base49) + (2325099081973/1000000000000 : ℝ)*(base59) + (3378158613421/500000000000 : ℝ)*(major_s0_0) + (3378158613421/500000000000 : ℝ)*(major_s0_1) + (3378158613421/500000000000 : ℝ)*(major_s0_2) + (34511303/500000000000 : ℝ)*(sp_s0_0) + (241483893/1000000000000 : ℝ)*(sp_s0_12) + (3507183/40000000000 : ℝ)*(sp_s0_14) + (74350293/1000000000000 : ℝ)*(sp_s0_15) + (4878085219341/500000000000 : ℝ)*(sp_s0_20) + (9756151781713/1000000000000 : ℝ)*(sp_s0_21) + (1951233022199/200000000000 : ℝ)*(sp_s0_22) + (234759249073/62500000000 : ℝ)*(sp_s0_26) + (187819473453/50000000000 : ℝ)*(f.failure) + (1219529932661/125000000000 : ℝ)*(f.sum) + (488510145064739/1250000000000000000000000000 : ℝ)*base62 + (1420496105978627/5000000000000000000000000000 : ℝ)*base65 + (696099054237583/5000000000000000000000000000 : ℝ)*base67 + (1385755588762417/5000000000000000000000000000 : ℝ)*base69 + (43632033621621/500000000000000000000000000 : ℝ)*base71 + (127837402478627/5000000000000000000000000000 : ℝ)*base72 + (509957163978627/5000000000000000000000000000 : ℝ)*base75 + (2201676853737583/5000000000000000000000000000 : ℝ)*base77 + (480109750810261/1250000000000000000000000000 : ℝ)*base78 + (3257/2500000000000000 : ℝ)*base86 + (3257/2500000000000000 : ℝ)*base88 + (3257/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (19553/100000 : ℝ) ^ (77/16 : ℝ) ≤ (155247451677941/400000000000000000 : ℝ) := by
    have hpowers : (19553/100000 : ℝ)^77 ≤ (155247451677941/400000000000000000 : ℝ)^16 := by
      have hnat : (19553 : ℕ)^77*400000000000000000^16 ≤ 155247451677941^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19553 100000 155247451677941 400000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19553/100000 : ℝ)) (X := (155247451677941/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (400155247451677941/400000000000000000 : ℝ) ≤ (1000080635631271/1000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (400155247451677941/400000000000000000 : ℝ)^16 ≤ (1000080635631271/1000000000000000 : ℝ)^77 := by
      have hnat : (400155247451677941 : ℕ)^16*1000000000000000^77 ≤ 1000080635631271^77*400000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400155247451677941 400000000000000000 1000080635631271 1000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000080635631271/1000000000000000 : ℝ)) (X := (400155247451677941/400000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (200155247451677941/200000000000000000 : ℝ) ≤ (10001612464828821/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (200155247451677941/200000000000000000 : ℝ)^16 ≤ (10001612464828821/10000000000000000 : ℝ)^77 := by
      have hnat : (200155247451677941 : ℕ)^16*10000000000000000^77 ≤ 10001612464828821^77*200000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200155247451677941 200000000000000000 10001612464828821 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001612464828821/10000000000000000 : ℝ)) (X := (200155247451677941/200000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(80635631271/195530000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(806108516111/1955300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (19553/100000 : ℝ)) (alpha := (80635631271/195530000000000 : ℝ)) (beta := (806108516111/1955300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (19553/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(80635631271/195530000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(806108516111/1955300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (24351/100000 : ℝ) ^ (77/16 : ℝ) ≤ (55793307490306773/50000000000000000000 : ℝ) := by
    have hpowers : (24351/100000 : ℝ)^77 ≤ (55793307490306773/50000000000000000000 : ℝ)^16 := by
      have hnat : (24351 : ℕ)^77*50000000000000000000^16 ≤ 55793307490306773^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24351 100000 55793307490306773 50000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24351/100000 : ℝ)) (X := (55793307490306773/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50055793307490306773/50000000000000000000 : ℝ) ≤ (625144853670999/625000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (50055793307490306773/50000000000000000000 : ℝ)^16 ≤ (625144853670999/625000000000000 : ℝ)^77 := by
      have hnat : (50055793307490306773 : ℕ)^16*625000000000000^77 ≤ 625144853670999^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50055793307490306773 50000000000000000000 625144853670999 625000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625144853670999/625000000000000 : ℝ)) (X := (50055793307490306773/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25055793307490306773/25000000000000000000 : ℝ) ≤ (5002316635926473/5000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (25055793307490306773/25000000000000000000 : ℝ)^16 ≤ (5002316635926473/5000000000000000 : ℝ)^77 := by
      have hnat : (25055793307490306773 : ℕ)^16*5000000000000000^77 ≤ 5002316635926473^77*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25055793307490306773 25000000000000000000 5002316635926473 5000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002316635926473/5000000000000000 : ℝ)) (X := (25055793307490306773/25000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(144853670999/152193750000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1157806558481/1217550000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (24351/100000 : ℝ)) (alpha := (144853670999/152193750000000 : ℝ)) (beta := (1157806558481/1217550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (24351/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(144853670999/152193750000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1157806558481/1217550000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1063/20000 : ℝ) ^ (77/16 : ℝ) ≤ (2941334877509/4000000000000000000 : ℝ) := by
    have hpowers : (1063/20000 : ℝ)^77 ≤ (2941334877509/4000000000000000000 : ℝ)^16 := by
      have hnat : (1063 : ℕ)^77*4000000000000000000^16 ≤ 2941334877509^16*20000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1063 20000 2941334877509 4000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1063/20000 : ℝ)) (X := (2941334877509/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (4000002941334877509/4000000000000000000 : ℝ) ≤ (5000000763982863/5000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (4000002941334877509/4000000000000000000 : ℝ)^16 ≤ (5000000763982863/5000000000000000 : ℝ)^77 := by
      have hnat : (4000002941334877509 : ℕ)^16*5000000000000000^77 ≤ 5000000763982863^77*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4000002941334877509 4000000000000000000 5000000763982863 5000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000763982863/5000000000000000 : ℝ)) (X := (4000002941334877509/4000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (2000002941334877509/2000000000000000000 : ℝ) ≤ (10000003055930561/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2000002941334877509/2000000000000000000 : ℝ)^16 ≤ (10000003055930561/10000000000000000 : ℝ)^77 := by
      have hnat : (2000002941334877509 : ℕ)^16*10000000000000000^77 ≤ 10000003055930561^77*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000002941334877509 2000000000000000000 10000003055930561 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000003055930561/10000000000000000 : ℝ)) (X := (2000002941334877509/2000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(763982863/265750000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(305592967/106300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1063/20000 : ℝ)) (alpha := (763982863/265750000000000 : ℝ)) (beta := (305592967/106300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1063/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(763982863/265750000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(305592967/106300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-4281934079/10000000000 : ℝ)*X 0 0+(416439153/1250000000 : ℝ)*X 0 1+(1219023377/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((277006573/625000000 : ℝ)*X 1 0+(-3448352241/10000000000 : ℝ)*X 1 1+(231105923/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2105714257/5000000000 : ℝ)*X 2 0+(5733449399/10000000000 : ℝ)*X 2 1+(-2404134357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((583309499/2000000000 : ℝ)*X 0 0+(794119023/2000000000 : ℝ)*X 0 1+(1106619711/2000000000 : ℝ)*X 0 2+(583309499/2000000000 : ℝ)*X 1 0+(794119023/2000000000 : ℝ)*X 1 1+(1106619711/2000000000 : ℝ)*X 1 2+(583309499/2000000000 : ℝ)*X 2 0+(794119023/2000000000 : ℝ)*X 2 1+(1106619711/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317081_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-194793/25000 : ℝ) < ((-89931/50000 : ℝ)*P 0+(-89931/50000 : ℝ)*P 1+(-89931/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-194793/25000 : ℝ) < (-129439123623895947333845560014147/16871053816300000000000000000000 : ℝ) := by norm_num
    linear_combination (2731/40000000000 : ℝ)*(base23) + (24351/1000000000000 : ℝ)*(base24) + (2421/200000000000 : ℝ)*(base39) + (63981739639/1000000000000 : ℝ)*(base40) + (428215676513/1000000000000 : ℝ)*(base49) + (221/50000000000 : ℝ)*(base50) + (923031914559/1000000000000 : ℝ)*(base59) + (74696906493/200000000000 : ℝ)*(base60) + (89931/50000 : ℝ)*(major_s1_0) + (89931/50000 : ℝ)*(major_s1_1) + (89931/50000 : ℝ)*(major_s1_2) + (159838765153/62500000000 : ℝ)*(sp_s1_0) + (159838765153/62500000000 : ℝ)*(sp_s1_1) + (1278710074911/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (159838765153/62500000000 : ℝ)*(f.sum) + (3742272112347277/5392731875000000000000000000 : ℝ)*base63 + (1599548223/20761718750000000000000 : ℝ)*base64 + (290970195323/1268281250000000000000000 : ℝ)*base67 + (445835267/2595214843750000000000 : ℝ)*base68 + (519056940087553/12990524375000000000000000000 : ℝ)*base70 + (268370396143/611031250000000000000000 : ℝ)*base73 + (12190121367141/20292500000000000000000000 : ℝ)*base75 + (21383645745417/97765000000000000000000000 : ℝ)*base76 + (1023623052066273127/793558505000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p017_b035 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 81 ≤ c.val) (hhi : c.val < 82)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=81 := by omega
  rcases hc with rfl
  · exact collision_c317081 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 81 ≤ c.val) (hhi : c.val < 82)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017_b035 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

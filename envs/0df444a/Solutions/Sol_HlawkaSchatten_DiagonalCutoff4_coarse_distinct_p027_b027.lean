-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b027
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:15:38.395174+00:00
-- url     : https://prove2.me/submissions/8fdcaf4d-2644-4f5d-a435-4138aac87454

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
theorem collision_support_c327057_s0_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-290972801/1000000000 : ℝ)*x 0 + (45464499/156250000 : ℝ)*x 1 + (6135206363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (290972801/1000000000 : ℝ)^91 ≤ (4472025122341/20000000000000 : ℝ)^75 := by
    have hnat : (290972801 : ℕ)^91*20000000000000^75 ≤ 4472025122341^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290972801 1000000000 4472025122341 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45464499/156250000 : ℝ)^91 ≤ (2236012492173/10000000000000 : ℝ)^75 := by
    have hnat : (45464499 : ℕ)^91*10000000000000^75 ≤ 2236012492173^75*156250000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45464499 156250000 2236012492173 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6135206363/10000000000 : ℝ)^91 ≤ (55279749438889/100000000000000 : ℝ)^75 := by
    have hnat : (6135206363 : ℕ)^91*100000000000000^75 ≤ 55279749438889^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6135206363 10000000000 55279749438889 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-290972801/1000000000 : ℝ), (45464499/156250000 : ℝ), (6135206363/10000000000 : ℝ)] ![(4472025122341/20000000000000 : ℝ), (2236012492173/10000000000000 : ℝ), (55279749438889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-290972801/1000000000 : ℝ)|^91 ≤ (4472025122341/20000000000000 : ℝ)^75
        have hw : |(-290972801/1000000000 : ℝ)|=(290972801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45464499/156250000 : ℝ)|^91 ≤ (2236012492173/10000000000000 : ℝ)^75
        have hw : |(45464499/156250000 : ℝ)|=(45464499/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6135206363/10000000000 : ℝ)|^91 ≤ (55279749438889/100000000000000 : ℝ)^75
        have hw : |(6135206363/10000000000 : ℝ)|=(6135206363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s0_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (363716001/1250000000 : ℝ)*x 0 + (-1454863967/5000000000 : ℝ)*x 1 + (6135206367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (363716001/1250000000 : ℝ)^91 ≤ (22360125593057/100000000000000 : ℝ)^75 := by
    have hnat : (363716001 : ℕ)^91*100000000000000^75 ≤ 22360125593057^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363716001 1250000000 22360125593057 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1454863967/5000000000 : ℝ)^91 ≤ (11180062451541/50000000000000 : ℝ)^75 := by
    have hnat : (1454863967 : ℕ)^91*50000000000000^75 ≤ 11180062451541^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1454863967 5000000000 11180062451541 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6135206367/10000000000 : ℝ)^91 ≤ (55279749482619/100000000000000 : ℝ)^75 := by
    have hnat : (6135206367 : ℕ)^91*100000000000000^75 ≤ 55279749482619^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6135206367 10000000000 55279749482619 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(363716001/1250000000 : ℝ), (-1454863967/5000000000 : ℝ), (6135206367/10000000000 : ℝ)] ![(22360125593057/100000000000000 : ℝ), (11180062451541/50000000000000 : ℝ), (55279749482619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(363716001/1250000000 : ℝ)|^91 ≤ (22360125593057/100000000000000 : ℝ)^75
        have hw : |(363716001/1250000000 : ℝ)|=(363716001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1454863967/5000000000 : ℝ)|^91 ≤ (11180062451541/50000000000000 : ℝ)^75
        have hw : |(-1454863967/5000000000 : ℝ)|=(1454863967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6135206367/10000000000 : ℝ)|^91 ≤ (55279749482619/100000000000000 : ℝ)^75
        have hw : |(6135206367/10000000000 : ℝ)|=(6135206367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s0_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5648047599/10000000000 : ℝ)*x 0 + (5648047677/10000000000 : ℝ)*x 1 + (-287/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5648047599/10000000000 : ℝ)^91 ≤ (49999999002611/100000000000000 : ℝ)^75 := by
    have hnat : (5648047599 : ℕ)^91*100000000000000^75 ≤ 49999999002611^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5648047599 10000000000 49999999002611 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5648047677/10000000000 : ℝ)^91 ≤ (24999999920211/50000000000000 : ℝ)^75 := by
    have hnat : (5648047677 : ℕ)^91*50000000000000^75 ≤ 24999999920211^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5648047677 10000000000 24999999920211 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (287/1000000000 : ℝ)^91 ≤ (230813/20000000000000 : ℝ)^75 := by
    have hnat : (287 : ℕ)^91*20000000000000^75 ≤ 230813^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287 1000000000 230813 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5648047599/10000000000 : ℝ), (5648047677/10000000000 : ℝ), (-287/1000000000 : ℝ)] ![(49999999002611/100000000000000 : ℝ), (24999999920211/50000000000000 : ℝ), (230813/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5648047599/10000000000 : ℝ)|^91 ≤ (49999999002611/100000000000000 : ℝ)^75
        have hw : |(5648047599/10000000000 : ℝ)|=(5648047599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5648047677/10000000000 : ℝ)|^91 ≤ (24999999920211/50000000000000 : ℝ)^75
        have hw : |(5648047677/10000000000 : ℝ)|=(5648047677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-287/1000000000 : ℝ)|^91 ≤ (230813/20000000000000 : ℝ)^75
        have hw : |(-287/1000000000 : ℝ)|=(287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s0_7 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2359235223/10000000000 : ℝ)*x 0 + (678161049/10000000000 : ℝ)*x 1 + (1027610703/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2359235223/10000000000 : ℝ)^91 ≤ (17336540646553/100000000000000 : ℝ)^75 := by
    have hnat : (2359235223 : ℕ)^91*100000000000000^75 ≤ 17336540646553^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2359235223 10000000000 17336540646553 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678161049/10000000000 : ℝ)^91 ≤ (3819593816033/100000000000000 : ℝ)^75 := by
    have hnat : (678161049 : ℕ)^91*100000000000000^75 ≤ 3819593816033^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678161049 10000000000 3819593816033 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027610703/1250000000 : ℝ)^91 ≤ (7884386553131/10000000000000 : ℝ)^75 := by
    have hnat : (1027610703 : ℕ)^91*10000000000000^75 ≤ 7884386553131^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027610703 1250000000 7884386553131 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2359235223/10000000000 : ℝ), (678161049/10000000000 : ℝ), (1027610703/1250000000 : ℝ)] ![(17336540646553/100000000000000 : ℝ), (3819593816033/100000000000000 : ℝ), (7884386553131/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2359235223/10000000000 : ℝ)|^91 ≤ (17336540646553/100000000000000 : ℝ)^75
        have hw : |(-2359235223/10000000000 : ℝ)|=(2359235223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678161049/10000000000 : ℝ)|^91 ≤ (3819593816033/100000000000000 : ℝ)^75
        have hw : |(678161049/10000000000 : ℝ)|=(678161049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027610703/1250000000 : ℝ)|^91 ≤ (7884386553131/10000000000000 : ℝ)^75
        have hw : |(1027610703/1250000000 : ℝ)|=(1027610703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s0_8 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (883691201/5000000000 : ℝ)*x 0 + (-1367452513/10000000000 : ℝ)*x 1 + (1644177107/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (883691201/5000000000 : ℝ)^91 ≤ (1221127575691/10000000000000 : ℝ)^75 := by
    have hnat : (883691201 : ℕ)^91*10000000000000^75 ≤ 1221127575691^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883691201 5000000000 1221127575691 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367452513/10000000000 : ℝ)^91 ≤ (2236214932323/25000000000000 : ℝ)^75 := by
    have hnat : (1367452513 : ℕ)^91*25000000000000^75 ≤ 2236214932323^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367452513 10000000000 2236214932323 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1644177107/2000000000 : ℝ)^91 ≤ (15768772899129/20000000000000 : ℝ)^75 := by
    have hnat : (1644177107 : ℕ)^91*20000000000000^75 ≤ 15768772899129^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1644177107 2000000000 15768772899129 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(883691201/5000000000 : ℝ), (-1367452513/10000000000 : ℝ), (1644177107/2000000000 : ℝ)] ![(1221127575691/10000000000000 : ℝ), (2236214932323/25000000000000 : ℝ), (15768772899129/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(883691201/5000000000 : ℝ)|^91 ≤ (1221127575691/10000000000000 : ℝ)^75
        have hw : |(883691201/5000000000 : ℝ)|=(883691201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1367452513/10000000000 : ℝ)|^91 ≤ (2236214932323/25000000000000 : ℝ)^75
        have hw : |(-1367452513/10000000000 : ℝ)|=(1367452513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1644177107/2000000000 : ℝ)|^91 ≤ (15768772899129/20000000000000 : ℝ)^75
        have hw : |(1644177107/2000000000 : ℝ)|=(1644177107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s0_9 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1803076139/5000000000 : ℝ)*x 0 + (3769860123/5000000000 : ℝ)*x 1 + (-800127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1803076139/5000000000 : ℝ)^91 ≤ (29009937626749/100000000000000 : ℝ)^75 := by
    have hnat : (1803076139 : ℕ)^91*100000000000000^75 ≤ 29009937626749^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803076139 5000000000 29009937626749 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3769860123/5000000000 : ℝ)^91 ≤ (70988992888667/100000000000000 : ℝ)^75 := by
    have hnat : (3769860123 : ℕ)^91*100000000000000^75 ≤ 70988992888667^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3769860123 5000000000 70988992888667 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (800127/10000000000 : ℝ)^91 ≤ (66841499/6250000000000 : ℝ)^75 := by
    have hnat : (800127 : ℕ)^91*6250000000000^75 ≤ 66841499^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800127 10000000000 66841499 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1803076139/5000000000 : ℝ), (3769860123/5000000000 : ℝ), (-800127/10000000000 : ℝ)] ![(29009937626749/100000000000000 : ℝ), (70988992888667/100000000000000 : ℝ), (66841499/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1803076139/5000000000 : ℝ)|^91 ≤ (29009937626749/100000000000000 : ℝ)^75
        have hw : |(1803076139/5000000000 : ℝ)|=(1803076139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3769860123/5000000000 : ℝ)|^91 ≤ (70988992888667/100000000000000 : ℝ)^75
        have hw : |(3769860123/5000000000 : ℝ)|=(3769860123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-800127/10000000000 : ℝ)|^91 ≤ (66841499/6250000000000 : ℝ)^75
        have hw : |(-800127/10000000000 : ℝ)|=(800127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s0_13 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1226216349/5000000000 : ℝ)*x 0 + (3769860123/5000000000 : ℝ)*x 1 + (1602123909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1226216349/5000000000 : ℝ)^91 ≤ (18170957478849/100000000000000 : ℝ)^75 := by
    have hnat : (1226216349 : ℕ)^91*100000000000000^75 ≤ 18170957478849^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226216349 5000000000 18170957478849 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3769860123/5000000000 : ℝ)^91 ≤ (70988992888667/100000000000000 : ℝ)^75 := by
    have hnat : (3769860123 : ℕ)^91*100000000000000^75 ≤ 70988992888667^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3769860123 5000000000 70988992888667 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1602123909/10000000000 : ℝ)^91 ≤ (5420024806791/50000000000000 : ℝ)^75 := by
    have hnat : (1602123909 : ℕ)^91*50000000000000^75 ≤ 5420024806791^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602123909 10000000000 5420024806791 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1226216349/5000000000 : ℝ), (3769860123/5000000000 : ℝ), (1602123909/10000000000 : ℝ)] ![(18170957478849/100000000000000 : ℝ), (70988992888667/100000000000000 : ℝ), (5420024806791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1226216349/5000000000 : ℝ)|^91 ≤ (18170957478849/100000000000000 : ℝ)^75
        have hw : |(1226216349/5000000000 : ℝ)|=(1226216349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3769860123/5000000000 : ℝ)|^91 ≤ (70988992888667/100000000000000 : ℝ)^75
        have hw : |(3769860123/5000000000 : ℝ)|=(3769860123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1602123909/10000000000 : ℝ)|^91 ≤ (5420024806791/50000000000000 : ℝ)^75
        have hw : |(1602123909/10000000000 : ℝ)|=(1602123909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s0_14 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1203779431/10000000000 : ℝ)*x 0 + (37536329/200000000 : ℝ)*x 1 + (412584137/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1203779431/10000000000 : ℝ)^91 ≤ (3831483254553/50000000000000 : ℝ)^75 := by
    have hnat : (1203779431 : ℕ)^91*50000000000000^75 ≤ 3831483254553^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203779431 10000000000 3831483254553 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37536329/200000000 : ℝ)^91 ≤ (2626929683399/20000000000000 : ℝ)^75 := by
    have hnat : (37536329 : ℕ)^91*20000000000000^75 ≤ 2626929683399^75*200000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37536329 200000000 2626929683399 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412584137/500000000 : ℝ)^91 ≤ (79202385060589/100000000000000 : ℝ)^75 := by
    have hnat : (412584137 : ℕ)^91*100000000000000^75 ≤ 79202385060589^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412584137 500000000 79202385060589 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1203779431/10000000000 : ℝ), (37536329/200000000 : ℝ), (412584137/500000000 : ℝ)] ![(3831483254553/50000000000000 : ℝ), (2626929683399/20000000000000 : ℝ), (79202385060589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1203779431/10000000000 : ℝ)|^91 ≤ (3831483254553/50000000000000 : ℝ)^75
        have hw : |(-1203779431/10000000000 : ℝ)|=(1203779431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(37536329/200000000 : ℝ)|^91 ≤ (2626929683399/20000000000000 : ℝ)^75
        have hw : |(37536329/200000000 : ℝ)|=(37536329/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(412584137/500000000 : ℝ)|^91 ≤ (79202385060589/100000000000000 : ℝ)^75
        have hw : |(412584137/500000000 : ℝ)|=(412584137/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s0_15 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (389909607/5000000000 : ℝ)*x 0 + (-55981181/250000000 : ℝ)*x 1 + (1031460341/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (389909607/5000000000 : ℝ)^91 ≤ (2262503751513/50000000000000 : ℝ)^75 := by
    have hnat : (389909607 : ℕ)^91*50000000000000^75 ≤ 2262503751513^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389909607 5000000000 2262503751513 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55981181/250000000 : ℝ)^91 ≤ (813630378417/5000000000000 : ℝ)^75 := by
    have hnat : (55981181 : ℕ)^91*5000000000000^75 ≤ 813630378417^75*250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55981181 250000000 813630378417 5000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031460341/1250000000 : ℝ)^91 ≤ (79202384920837/100000000000000 : ℝ)^75 := by
    have hnat : (1031460341 : ℕ)^91*100000000000000^75 ≤ 79202384920837^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031460341 1250000000 79202384920837 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(389909607/5000000000 : ℝ), (-55981181/250000000 : ℝ), (1031460341/1250000000 : ℝ)] ![(2262503751513/50000000000000 : ℝ), (813630378417/5000000000000 : ℝ), (79202384920837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(389909607/5000000000 : ℝ)|^91 ≤ (2262503751513/50000000000000 : ℝ)^75
        have hw : |(389909607/5000000000 : ℝ)|=(389909607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55981181/250000000 : ℝ)|^91 ≤ (813630378417/5000000000000 : ℝ)^75
        have hw : |(-55981181/250000000 : ℝ)|=(55981181/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1031460341/1250000000 : ℝ)|^91 ≤ (79202384920837/100000000000000 : ℝ)^75
        have hw : |(1031460341/1250000000 : ℝ)|=(1031460341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s0_16 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3934193543/5000000000 : ℝ)*x 0 + (643010301/2000000000 : ℝ)*x 1 + (-50737/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3934193543/5000000000 : ℝ)^91 ≤ (74760925637921/100000000000000 : ℝ)^75 := by
    have hnat : (3934193543 : ℕ)^91*100000000000000^75 ≤ 74760925637921^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3934193543 5000000000 74760925637921 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643010301/2000000000 : ℝ)^91 ≤ (25237985941507/100000000000000 : ℝ)^75 := by
    have hnat : (643010301 : ℕ)^91*100000000000000^75 ≤ 25237985941507^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643010301 2000000000 25237985941507 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50737/625000000 : ℝ)^91 ≤ (217682231/20000000000000 : ℝ)^75 := by
    have hnat : (50737 : ℕ)^91*20000000000000^75 ≤ 217682231^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50737 625000000 217682231 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3934193543/5000000000 : ℝ), (643010301/2000000000 : ℝ), (-50737/625000000 : ℝ)] ![(74760925637921/100000000000000 : ℝ), (25237985941507/100000000000000 : ℝ), (217682231/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3934193543/5000000000 : ℝ)|^91 ≤ (74760925637921/100000000000000 : ℝ)^75
        have hw : |(3934193543/5000000000 : ℝ)|=(3934193543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643010301/2000000000 : ℝ)|^91 ≤ (25237985941507/100000000000000 : ℝ)^75
        have hw : |(643010301/2000000000 : ℝ)|=(643010301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50737/625000000 : ℝ)|^91 ≤ (217682231/20000000000000 : ℝ)^75
        have hw : |(-50737/625000000 : ℝ)|=(50737/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s0_20 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7191442307/10000000000 : ℝ)*x 0 + (2882719193/10000000000 : ℝ)*x 1 + (1604714601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7191442307/10000000000 : ℝ)^91 ≤ (33515066479231/50000000000000 : ℝ)^75 := by
    have hnat : (7191442307 : ℕ)^91*50000000000000^75 ≤ 33515066479231^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7191442307 10000000000 33515066479231 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2882719193/10000000000 : ℝ)^91 ≤ (22108545519119/100000000000000 : ℝ)^75 := by
    have hnat : (2882719193 : ℕ)^91*100000000000000^75 ≤ 22108545519119^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2882719193 10000000000 22108545519119 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1604714601/10000000000 : ℝ)^91 ≤ (10861321497379/100000000000000 : ℝ)^75 := by
    have hnat : (1604714601 : ℕ)^91*100000000000000^75 ≤ 10861321497379^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1604714601 10000000000 10861321497379 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7191442307/10000000000 : ℝ), (2882719193/10000000000 : ℝ), (1604714601/10000000000 : ℝ)] ![(33515066479231/50000000000000 : ℝ), (22108545519119/100000000000000 : ℝ), (10861321497379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7191442307/10000000000 : ℝ)|^91 ≤ (33515066479231/50000000000000 : ℝ)^75
        have hw : |(7191442307/10000000000 : ℝ)|=(7191442307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2882719193/10000000000 : ℝ)|^91 ≤ (22108545519119/100000000000000 : ℝ)^75
        have hw : |(2882719193/10000000000 : ℝ)|=(2882719193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1604714601/10000000000 : ℝ)|^91 ≤ (10861321497379/100000000000000 : ℝ)^75
        have hw : |(1604714601/10000000000 : ℝ)|=(1604714601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s0_21 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1192540031/2500000000 : ℝ)*x 0 + (385653883/2000000000 : ℝ)*x 1 + (5243973189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1192540031/2500000000 : ℝ)^91 ≤ (40733649480959/100000000000000 : ℝ)^75 := by
    have hnat : (1192540031 : ℕ)^91*100000000000000^75 ≤ 40733649480959^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192540031 2500000000 40733649480959 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (385653883/2000000000 : ℝ)^91 ≤ (542912885747/4000000000000 : ℝ)^75 := by
    have hnat : (385653883 : ℕ)^91*4000000000000^75 ≤ 542912885747^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385653883 2000000000 542912885747 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243973189/10000000000 : ℝ)^91 ≤ (45693528353749/100000000000000 : ℝ)^75 := by
    have hnat : (5243973189 : ℕ)^91*100000000000000^75 ≤ 45693528353749^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243973189 10000000000 45693528353749 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1192540031/2500000000 : ℝ), (385653883/2000000000 : ℝ), (5243973189/10000000000 : ℝ)] ![(40733649480959/100000000000000 : ℝ), (542912885747/4000000000000 : ℝ), (45693528353749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1192540031/2500000000 : ℝ)|^91 ≤ (40733649480959/100000000000000 : ℝ)^75
        have hw : |(-1192540031/2500000000 : ℝ)|=(1192540031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(385653883/2000000000 : ℝ)|^91 ≤ (542912885747/4000000000000 : ℝ)^75
        have hw : |(385653883/2000000000 : ℝ)|=(385653883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243973189/10000000000 : ℝ)|^91 ≤ (45693528353749/100000000000000 : ℝ)^75
        have hw : |(5243973189/10000000000 : ℝ)|=(5243973189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s0_22 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (218064667/5000000000 : ℝ)*x 0 + (-283879937/625000000 : ℝ)*x 1 + (6508032329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218064667/5000000000 : ℝ)^91 ≤ (2235629827069/100000000000000 : ℝ)^75 := by
    have hnat : (218064667 : ℕ)^91*100000000000000^75 ≤ 2235629827069^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218064667 5000000000 2235629827069 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283879937/625000000 : ℝ)^91 ≤ (38382714164399/100000000000000 : ℝ)^75 := by
    have hnat : (283879937 : ℕ)^91*100000000000000^75 ≤ 38382714164399^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283879937 625000000 38382714164399 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6508032329/10000000000 : ℝ)^91 ≤ (14845413996493/25000000000000 : ℝ)^75 := by
    have hnat : (6508032329 : ℕ)^91*25000000000000^75 ≤ 14845413996493^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6508032329 10000000000 14845413996493 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218064667/5000000000 : ℝ), (-283879937/625000000 : ℝ), (6508032329/10000000000 : ℝ)] ![(2235629827069/100000000000000 : ℝ), (38382714164399/100000000000000 : ℝ), (14845413996493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218064667/5000000000 : ℝ)|^91 ≤ (2235629827069/100000000000000 : ℝ)^75
        have hw : |(218064667/5000000000 : ℝ)|=(218064667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-283879937/625000000 : ℝ)|^91 ≤ (38382714164399/100000000000000 : ℝ)^75
        have hw : |(-283879937/625000000 : ℝ)|=(283879937/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6508032329/10000000000 : ℝ)|^91 ≤ (14845413996493/25000000000000 : ℝ)^75
        have hw : |(6508032329/10000000000 : ℝ)|=(6508032329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s0_23 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1208255583/2000000000 : ℝ)*x 0 + (656107429/1250000000 : ℝ)*x 1 + (117111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1208255583/2000000000 : ℝ)^91 ≤ (54254566205549/100000000000000 : ℝ)^75 := by
    have hnat : (1208255583 : ℕ)^91*100000000000000^75 ≤ 54254566205549^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208255583 2000000000 54254566205549 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656107429/1250000000 : ℝ)^91 ≤ (45745192894601/100000000000000 : ℝ)^75 := by
    have hnat : (656107429 : ℕ)^91*100000000000000^75 ≤ 45745192894601^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656107429 1250000000 45745192894601 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117111/5000000000 : ℝ)^91 ≤ (240887867/100000000000000 : ℝ)^75 := by
    have hnat : (117111 : ℕ)^91*100000000000000^75 ≤ 240887867^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117111 5000000000 240887867 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1208255583/2000000000 : ℝ), (656107429/1250000000 : ℝ), (117111/5000000000 : ℝ)] ![(54254566205549/100000000000000 : ℝ), (45745192894601/100000000000000 : ℝ), (240887867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1208255583/2000000000 : ℝ)|^91 ≤ (54254566205549/100000000000000 : ℝ)^75
        have hw : |(1208255583/2000000000 : ℝ)|=(1208255583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656107429/1250000000 : ℝ)|^91 ≤ (45745192894601/100000000000000 : ℝ)^75
        have hw : |(656107429/1250000000 : ℝ)|=(656107429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(117111/5000000000 : ℝ)|^91 ≤ (240887867/100000000000000 : ℝ)^75
        have hw : |(117111/5000000000 : ℝ)|=(117111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s0_27 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (947483697/5000000000 : ℝ)*x 0 + (656107429/1250000000 : ℝ)*x 1 + (599070289/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (947483697/5000000000 : ℝ)^91 ≤ (830558315109/6250000000000 : ℝ)^75 := by
    have hnat : (947483697 : ℕ)^91*6250000000000^75 ≤ 830558315109^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947483697 5000000000 830558315109 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656107429/1250000000 : ℝ)^91 ≤ (45745192894601/100000000000000 : ℝ)^75 := by
    have hnat : (656107429 : ℕ)^91*100000000000000^75 ≤ 45745192894601^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656107429 1250000000 45745192894601 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (599070289/1250000000 : ℝ)^91 ≤ (10241468512391/25000000000000 : ℝ)^75 := by
    have hnat : (599070289 : ℕ)^91*25000000000000^75 ≤ 10241468512391^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599070289 1250000000 10241468512391 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(947483697/5000000000 : ℝ), (656107429/1250000000 : ℝ), (599070289/1250000000 : ℝ)] ![(830558315109/6250000000000 : ℝ), (45745192894601/100000000000000 : ℝ), (10241468512391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(947483697/5000000000 : ℝ)|^91 ≤ (830558315109/6250000000000 : ℝ)^75
        have hw : |(947483697/5000000000 : ℝ)|=(947483697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656107429/1250000000 : ℝ)|^91 ≤ (45745192894601/100000000000000 : ℝ)^75
        have hw : |(656107429/1250000000 : ℝ)|=(656107429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(599070289/1250000000 : ℝ)|^91 ≤ (10241468512391/25000000000000 : ℝ)^75
        have hw : |(599070289/1250000000 : ℝ)|=(599070289/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s1_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3221979621/10000000000 : ℝ)*x 0 + (1610193673/5000000000 : ℝ)*x 1 + (5592799903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3221979621/10000000000 : ℝ)^91 ≤ (12651994327941/50000000000000 : ℝ)^75 := by
    have hnat : (3221979621 : ℕ)^91*50000000000000^75 ≤ 12651994327941^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3221979621 10000000000 12651994327941 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1610193673/5000000000 : ℝ)^91 ≤ (5057763340473/20000000000000 : ℝ)^75 := by
    have hnat : (1610193673 : ℕ)^91*20000000000000^75 ≤ 5057763340473^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1610193673 5000000000 5057763340473 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5592799903/10000000000 : ℝ)^91 ≤ (24703597309577/50000000000000 : ℝ)^75 := by
    have hnat : (5592799903 : ℕ)^91*50000000000000^75 ≤ 24703597309577^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5592799903 10000000000 24703597309577 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3221979621/10000000000 : ℝ), (1610193673/5000000000 : ℝ), (5592799903/10000000000 : ℝ)] ![(12651994327941/50000000000000 : ℝ), (5057763340473/20000000000000 : ℝ), (24703597309577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3221979621/10000000000 : ℝ)|^91 ≤ (12651994327941/50000000000000 : ℝ)^75
        have hw : |(-3221979621/10000000000 : ℝ)|=(3221979621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1610193673/5000000000 : ℝ)|^91 ≤ (5057763340473/20000000000000 : ℝ)^75
        have hw : |(1610193673/5000000000 : ℝ)|=(1610193673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5592799903/10000000000 : ℝ)|^91 ≤ (24703597309577/50000000000000 : ℝ)^75
        have hw : |(5592799903/10000000000 : ℝ)|=(5592799903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s1_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (16102087/50000000 : ℝ)*x 0 + (-3218825897/10000000000 : ℝ)*x 1 + (5595576431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16102087/50000000 : ℝ)^91 ≤ (6322275764089/25000000000000 : ℝ)^75 := by
    have hnat : (16102087 : ℕ)^91*25000000000000^75 ≤ 6322275764089^75*50000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16102087 50000000 6322275764089 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3218825897/10000000000 : ℝ)^91 ≤ (25273940027711/100000000000000 : ℝ)^75 := by
    have hnat : (3218825897 : ℕ)^91*100000000000000^75 ≤ 25273940027711^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3218825897 10000000000 25273940027711 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5595576431/10000000000 : ℝ)^91 ≤ (3089809805751/6250000000000 : ℝ)^75 := by
    have hnat : (5595576431 : ℕ)^91*6250000000000^75 ≤ 3089809805751^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595576431 10000000000 3089809805751 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16102087/50000000 : ℝ), (-3218825897/10000000000 : ℝ), (5595576431/10000000000 : ℝ)] ![(6322275764089/25000000000000 : ℝ), (25273940027711/100000000000000 : ℝ), (3089809805751/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16102087/50000000 : ℝ)|^91 ≤ (6322275764089/25000000000000 : ℝ)^75
        have hw : |(16102087/50000000 : ℝ)|=(16102087/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3218825897/10000000000 : ℝ)|^91 ≤ (25273940027711/100000000000000 : ℝ)^75
        have hw : |(-3218825897/10000000000 : ℝ)|=(3218825897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5595576431/10000000000 : ℝ)|^91 ≤ (3089809805751/6250000000000 : ℝ)^75
        have hw : |(5595576431/10000000000 : ℝ)|=(5595576431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s1_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2705025941/5000000000 : ℝ)*x 0 + (5412610747/10000000000 : ℝ)*x 1 + (-34214503/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2705025941/5000000000 : ℝ)^91 ≤ (47455264866441/100000000000000 : ℝ)^75 := by
    have hnat : (2705025941 : ℕ)^91*100000000000000^75 ≤ 47455264866441^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705025941 5000000000 47455264866441 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412610747/10000000000 : ℝ)^91 ≤ (47482500180167/100000000000000 : ℝ)^75 := by
    have hnat : (5412610747 : ℕ)^91*100000000000000^75 ≤ 47482500180167^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412610747 10000000000 47482500180167 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34214503/400000000 : ℝ)^91 ≤ (2531117467689/50000000000000 : ℝ)^75 := by
    have hnat : (34214503 : ℕ)^91*50000000000000^75 ≤ 2531117467689^75*400000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34214503 400000000 2531117467689 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2705025941/5000000000 : ℝ), (5412610747/10000000000 : ℝ), (-34214503/400000000 : ℝ)] ![(47455264866441/100000000000000 : ℝ), (47482500180167/100000000000000 : ℝ), (2531117467689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2705025941/5000000000 : ℝ)|^91 ≤ (47455264866441/100000000000000 : ℝ)^75
        have hw : |(2705025941/5000000000 : ℝ)|=(2705025941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412610747/10000000000 : ℝ)|^91 ≤ (47482500180167/100000000000000 : ℝ)^75
        have hw : |(5412610747/10000000000 : ℝ)|=(5412610747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34214503/400000000 : ℝ)|^91 ≤ (2531117467689/50000000000000 : ℝ)^75
        have hw : |(-34214503/400000000 : ℝ)|=(34214503/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327057_s1_6 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2122758919/5000000000 : ℝ)*x 0 + (4247525897/10000000000 : ℝ)*x 1 + (3630995151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122758919/5000000000 : ℝ)^91 ≤ (2210221997123/6250000000000 : ℝ)^75 := by
    have hnat : (2122758919 : ℕ)^91*6250000000000^75 ≤ 2210221997123^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122758919 5000000000 2210221997123 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4247525897/10000000000 : ℝ)^91 ≤ (1415353905561/4000000000000 : ℝ)^75 := by
    have hnat : (4247525897 : ℕ)^91*4000000000000^75 ≤ 1415353905561^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247525897 10000000000 1415353905561 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3630995151/10000000000 : ℝ)^91 ≤ (117010401523/400000000000 : ℝ)^75 := by
    have hnat : (3630995151 : ℕ)^91*400000000000^75 ≤ 117010401523^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3630995151 10000000000 117010401523 400000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2122758919/5000000000 : ℝ), (4247525897/10000000000 : ℝ), (3630995151/10000000000 : ℝ)] ![(2210221997123/6250000000000 : ℝ), (1415353905561/4000000000000 : ℝ), (117010401523/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2122758919/5000000000 : ℝ)|^91 ≤ (2210221997123/6250000000000 : ℝ)^75
        have hw : |(2122758919/5000000000 : ℝ)|=(2122758919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4247525897/10000000000 : ℝ)|^91 ≤ (1415353905561/4000000000000 : ℝ)^75
        have hw : |(4247525897/10000000000 : ℝ)|=(4247525897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3630995151/10000000000 : ℝ)|^91 ≤ (117010401523/400000000000 : ℝ)^75
        have hw : |(3630995151/10000000000 : ℝ)|=(3630995151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c327057 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (32523/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-290972801/1000000000 : ℝ)*X 0 0+(45464499/156250000 : ℝ)*X 0 1+(6135206363/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((363716001/1250000000 : ℝ)*X 1 0+(-1454863967/5000000000 : ℝ)*X 1 1+(6135206367/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5648047599/10000000000 : ℝ)*X 2 0+(5648047677/10000000000 : ℝ)*X 2 1+(-287/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2359235223/10000000000 : ℝ)*X 0 0+(678161049/10000000000 : ℝ)*X 0 1+(1027610703/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((883691201/5000000000 : ℝ)*X 1 0+(-1367452513/10000000000 : ℝ)*X 1 1+(1644177107/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1803076139/5000000000 : ℝ)*X 2 0+(3769860123/5000000000 : ℝ)*X 2 1+(-800127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1226216349/5000000000 : ℝ)*X 0 0+(3769860123/5000000000 : ℝ)*X 0 1+(1602123909/10000000000 : ℝ)*X 0 2+(1226216349/5000000000 : ℝ)*X 1 0+(3769860123/5000000000 : ℝ)*X 1 1+(1602123909/10000000000 : ℝ)*X 1 2+(1226216349/5000000000 : ℝ)*X 2 0+(3769860123/5000000000 : ℝ)*X 2 1+(1602123909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1203779431/10000000000 : ℝ)*X 0 0+(37536329/200000000 : ℝ)*X 0 1+(412584137/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((389909607/5000000000 : ℝ)*X 1 0+(-55981181/250000000 : ℝ)*X 1 1+(1031460341/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3934193543/5000000000 : ℝ)*X 2 0+(643010301/2000000000 : ℝ)*X 2 1+(-50737/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((7191442307/10000000000 : ℝ)*X 0 0+(2882719193/10000000000 : ℝ)*X 0 1+(1604714601/10000000000 : ℝ)*X 0 2+(7191442307/10000000000 : ℝ)*X 1 0+(2882719193/10000000000 : ℝ)*X 1 1+(1604714601/10000000000 : ℝ)*X 1 2+(7191442307/10000000000 : ℝ)*X 2 0+(2882719193/10000000000 : ℝ)*X 2 1+(1604714601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1192540031/2500000000 : ℝ)*X 0 0+(385653883/2000000000 : ℝ)*X 0 1+(5243973189/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((218064667/5000000000 : ℝ)*X 1 0+(-283879937/625000000 : ℝ)*X 1 1+(6508032329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1208255583/2000000000 : ℝ)*X 2 0+(656107429/1250000000 : ℝ)*X 2 1+(117111/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((947483697/5000000000 : ℝ)*X 0 0+(656107429/1250000000 : ℝ)*X 0 1+(599070289/1250000000 : ℝ)*X 0 2+(947483697/5000000000 : ℝ)*X 1 0+(656107429/1250000000 : ℝ)*X 1 1+(599070289/1250000000 : ℝ)*X 1 2+(947483697/5000000000 : ℝ)*X 2 0+(656107429/1250000000 : ℝ)*X 2 1+(599070289/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((63829/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63829/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6189280290198058808433/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (264048077647/1000000000000 : ℝ)*(base5) + (299398816831/250000000000 : ℝ)*(base7) + (504838247/10000000000 : ℝ)*(base59) + (390751783103/250000000000 : ℝ)*(major_s0_0) + (390751783103/250000000000 : ℝ)*(major_s0_1) + (390751783103/250000000000 : ℝ)*(major_s0_2) + (4324469/500000000000 : ℝ)*(sp_s0_0) + (376651/40000000000 : ℝ)*(sp_s0_1) + (3394943651/1953125000 : ℝ)*(sp_s0_7) + (869076696209/500000000000 : ℝ)*(sp_s0_8) + (400455281487/200000000000 : ℝ)*(sp_s0_9) + (418042502039/250000000000 : ℝ)*(sp_s0_13) + (4265769/500000000000 : ℝ)*(sp_s0_14) + (8190137/125000000000 : ℝ)*(sp_s0_15) + (738622818479/1000000000000 : ℝ)*(f.failure) + (434557082447/250000000000 : ℝ)*(f.sum) + (701960027/5000000000000000000000 : ℝ)*base62 + (206229488981741/1250000000000000000000000000 : ℝ)*base65 + (371352281268259/1250000000000000000000000000 : ℝ)*base67 + (22053320977811/625000000000000000000000000 : ℝ)*base69 + (161328598526119/1250000000000000000000000000 : ℝ)*base71 + (501371361356741/1250000000000000000000000000 : ℝ)*base72 + (250530836147189/625000000000000000000000000 : ℝ)*base75 + (281138113147189/625000000000000000000000000 : ℝ)*base77 + (9041072080759/625000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (40331/100000000000000000 : ℝ)*base86 + (40331/100000000000000000 : ℝ)*base88 + (40331/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63513/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63513/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (39879200382031980522441/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (275383651753/1000000000000 : ℝ)*(base5) + (298787246683/250000000000 : ℝ)*(base7) + (56923/500000000000 : ℝ)*(base40) + (19697864719/1000000000000 : ℝ)*(base60) + (1544368846533/1000000000000 : ℝ)*(major_s0_0) + (1544368846533/1000000000000 : ℝ)*(major_s0_1) + (1544368846533/1000000000000 : ℝ)*(major_s0_2) + (1363409/200000000000 : ℝ)*(sp_s0_0) + (8072617/1000000000000 : ℝ)*(sp_s0_1) + (49987401/1000000000000 : ℝ)*(sp_s0_7) + (855515025213/500000000000 : ℝ)*(sp_s0_14) + (855539391127/500000000000 : ℝ)*(sp_s0_15) + (15891764053/8000000000 : ℝ)*(sp_s0_16) + (1649580347683/1000000000000 : ℝ)*(sp_s0_20) + (22806719147/31250000000 : ℝ)*(f.failure) + (213885856859/125000000000 : ℝ)*(f.sum) + (1828340601/5000000000000000000000 : ℝ)*base62 + (444665570941951/5000000000000000000000000000 : ℝ)*base65 + (2976289355941951/5000000000000000000000000000 : ℝ)*base66 + (1583837741745279/2500000000000000000000000000 : ℝ)*base68 + (3596727421432509/5000000000000000000000000000 : ℝ)*base71 + (2048656131941951/5000000000000000000000000000 : ℝ)*base72 + (1864382109254721/2500000000000000000000000000 : ℝ)*base74 + (87589862504721/2500000000000000000000000000 : ℝ)*base76 + (1367740085691951/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (3/48828125000000 : ℝ)*base87 + (3/48828125000000 : ℝ)*base89 + (3/48828125000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(6543/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(6543/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25359038688506293507593/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1007075768371/1000000000000 : ℝ)*(base5) + (426964654393/1000000000000 : ℝ)*(base7) + (5668097/1000000000000 : ℝ)*(base40) + (52417816471/250000000000 : ℝ)*(base50) + (80917153199/100000000000 : ℝ)*(base59) + (1237439971947/1000000000000 : ℝ)*(major_s0_0) + (1237439971947/1000000000000 : ℝ)*(major_s0_1) + (1237439971947/1000000000000 : ℝ)*(major_s0_2) + (84863/1000000000000 : ℝ)*(sp_s0_0) + (126920067/1000000000000 : ℝ)*(sp_s0_2) + (829334593567/500000000000 : ℝ)*(sp_s0_21) + (1658669271997/1000000000000 : ℝ)*(sp_s0_22) + (2665618120301/1000000000000 : ℝ)*(sp_s0_23) + (2329992899/500000000000 : ℝ)*(sp_s0_27) + (4568524217/7812500000 : ℝ)*(f.failure) + (1658669271997/1000000000000 : ℝ)*(f.sum) + (682156583/5000000000000000000000 : ℝ)*base62 + (1091419602729391/5000000000000000000000000000 : ℝ)*base64 + (684212739770609/5000000000000000000000000000 : ℝ)*base66 + (667819325240961/2500000000000000000000000000 : ℝ)*base68 + (193982956247469/5000000000000000000000000000 : ℝ)*base70 + (1800741448770609/5000000000000000000000000000 : ℝ)*base72 + (1250011267259039/2500000000000000000000000000 : ℝ)*base74 + (943790809009039/2500000000000000000000000000 : ℝ)*base76 + (93828168729391/2500000000000000000000000000 : ℝ)*base79 + (27/3125000000000000 : ℝ)*base86 + (27/3125000000000000 : ℝ)*base88 + (27/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (63829/100000 : ℝ) ^ (89/16 : ℝ) ≤ (8230246637808313787/100000000000000000000 : ℝ) := by
    have hpowers : (63829/100000 : ℝ)^89 ≤ (8230246637808313787/100000000000000000000 : ℝ)^16 := by
      have hnat : (63829 : ℕ)^89*100000000000000000000^16 ≤ 8230246637808313787^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63829 100000 8230246637808313787 100000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63829/100000 : ℝ)) (X := (8230246637808313787/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (108230246637808313787/100000000000000000000 : ℝ) ≤ (2535800286294827/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (108230246637808313787/100000000000000000000 : ℝ)^16 ≤ (2535800286294827/2500000000000000 : ℝ)^89 := by
      have hnat : (108230246637808313787 : ℕ)^16*2500000000000000^89 ≤ 2535800286294827^89*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108230246637808313787 100000000000000000000 2535800286294827 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2535800286294827/2500000000000000 : ℝ)) (X := (108230246637808313787/100000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (58230246637808313787/50000000000000000000 : ℝ) ≤ (10277731811168953/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (58230246637808313787/50000000000000000000 : ℝ)^16 ≤ (10277731811168953/10000000000000000 : ℝ)^89 := by
      have hnat : (58230246637808313787 : ℕ)^16*10000000000000000^89 ≤ 10277731811168953^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58230246637808313787 50000000000000000000 10277731811168953 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10277731811168953/10000000000000000 : ℝ)) (X := (58230246637808313787/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(35800286294827/1595725000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(26906133197929/1276580000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (63829/100000 : ℝ)) (alpha := (35800286294827/1595725000000000 : ℝ)) (beta := (26906133197929/1276580000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (63829/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(35800286294827/1595725000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(26906133197929/1276580000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (63513/100000 : ℝ) ^ (89/16 : ℝ) ≤ (2001535837970243939/25000000000000000000 : ℝ) := by
    have hpowers : (63513/100000 : ℝ)^89 ≤ (2001535837970243939/25000000000000000000 : ℝ)^16 := by
      have hnat : (63513 : ℕ)^89*25000000000000000000^16 ≤ 2001535837970243939^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63513 100000 2001535837970243939 25000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63513/100000 : ℝ)) (X := (2001535837970243939/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (27001535837970243939/25000000000000000000 : ℝ) ≤ (5069711086503881/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (27001535837970243939/25000000000000000000 : ℝ)^16 ≤ (5069711086503881/5000000000000000 : ℝ)^89 := by
      have hnat : (27001535837970243939 : ℕ)^16*5000000000000000^89 ≤ 5069711086503881^89*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27001535837970243939 25000000000000000000 5069711086503881 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5069711086503881/5000000000000000 : ℝ)) (X := (27001535837970243939/25000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (14501535837970243939/12500000000000000000 : ℝ) ≤ (1027060962402301/1000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (14501535837970243939/12500000000000000000 : ℝ)^16 ≤ (1027060962402301/1000000000000000 : ℝ)^89 := by
      have hnat : (14501535837970243939 : ℕ)^16*1000000000000000^89 ≤ 1027060962402301^89*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14501535837970243939 12500000000000000000 1027060962402301 1000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1027060962402301/1000000000000000 : ℝ)) (X := (14501535837970243939/12500000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(7745676278209/352850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(2733071896151/132318750000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (63513/100000 : ℝ)) (alpha := (7745676278209/352850000000000 : ℝ)) (beta := (2733071896151/132318750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (63513/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(7745676278209/352850000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(2733071896151/132318750000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (6543/25000 : ℝ) ^ (89/16 : ℝ) ≤ (14443013912612453/25000000000000000000 : ℝ) := by
    have hpowers : (6543/25000 : ℝ)^89 ≤ (14443013912612453/25000000000000000000 : ℝ)^16 := by
      have hnat : (6543 : ℕ)^89*25000000000000000000^16 ≤ 14443013912612453^16*25000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6543 25000 14443013912612453 25000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6543/25000 : ℝ)) (X := (14443013912612453/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25014443013912612453/25000000000000000000 : ℝ) ≤ (2500259588190983/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (25014443013912612453/25000000000000000000 : ℝ)^16 ≤ (2500259588190983/2500000000000000 : ℝ)^89 := by
      have hnat : (25014443013912612453 : ℕ)^16*2500000000000000^89 ≤ 2500259588190983^89*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014443013912612453 25000000000000000000 2500259588190983 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500259588190983/2500000000000000 : ℝ)) (X := (25014443013912612453/25000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12514443013912612453/12500000000000000000 : ℝ) ≤ (2500519053473449/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (12514443013912612453/12500000000000000000 : ℝ)^16 ≤ (2500519053473449/2500000000000000 : ℝ)^89 := by
      have hnat : (12514443013912612453 : ℕ)^16*2500000000000000^89 ≤ 2500519053473449^89*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12514443013912612453 12500000000000000000 2500519053473449 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500519053473449/2500000000000000 : ℝ)) (X := (12514443013912612453/12500000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(259588190983/654300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(129732641233/327150000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (6543/25000 : ℝ)) (alpha := (259588190983/654300000000000 : ℝ)) (beta := (129732641233/327150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (6543/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(259588190983/654300000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(129732641233/327150000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3221979621/10000000000 : ℝ)*X 0 0+(1610193673/5000000000 : ℝ)*X 0 1+(5592799903/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((16102087/50000000 : ℝ)*X 1 0+(-3218825897/10000000000 : ℝ)*X 1 1+(5595576431/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2705025941/5000000000 : ℝ)*X 2 0+(5412610747/10000000000 : ℝ)*X 2 1+(-34214503/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2122758919/5000000000 : ℝ)*X 0 0+(4247525897/10000000000 : ℝ)*X 0 1+(3630995151/10000000000 : ℝ)*X 0 2+(2122758919/5000000000 : ℝ)*X 1 0+(4247525897/10000000000 : ℝ)*X 1 1+(3630995151/10000000000 : ℝ)*X 1 2+(2122758919/5000000000 : ℝ)*X 2 0+(4247525897/10000000000 : ℝ)*X 2 1+(3630995151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327057_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-484833/50000 : ℝ) < ((-211611/100000 : ℝ)*P 0+(-211611/100000 : ℝ)*P 1+(-211611/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-484833/50000 : ℝ) < (-15780283893569368324327822295823981/1637353954655000000000000000000000 : ℝ) := by norm_num
    linear_combination (3983/1000000000000 : ℝ)*(base7) + (2091/62500000000 : ℝ)*(base8) + (471407/1000000000000 : ℝ)*(base11) + (487081/1000000000000 : ℝ)*(base15) + (1649/62500000000 : ℝ)*(base40) + (8119/250000000000 : ℝ)*(base50) + (164011296163/125000000000 : ℝ)*(base59) + (656140550639/1000000000000 : ℝ)*(base60) + (211611/100000 : ℝ)*(major_s1_0) + (211611/100000 : ℝ)*(major_s1_1) + (211611/100000 : ℝ)*(major_s1_2) + (3212557545089/1000000000000 : ℝ)*(sp_s1_0) + (401569695359/125000000000 : ℝ)*(sp_s1_1) + (100392439061/31250000000 : ℝ)*(sp_s1_2) + (1000000003983/1000000000000 : ℝ)*(sp_s1_6) + (100392439061/31250000000 : ℝ)*(f.sum) + (10919077627704451/30782634000000000000000000000 : ℝ)*base63 + (1160922948071/4362000000000000000000000 : ℝ)*base65 + (11868896669/44106250000000000000000 : ℝ)*base67 + (1190273845363/10905000000000000000000000 : ℝ)*base69 + (828249331895136217/1392110490000000000000000000000 : ℝ)*base71 + (52336180767737/127658000000000000000000000 : ℝ)*base72 + (15388137522087/35285000000000000000000000 : ℝ)*base75 + (86745225264809/127658000000000000000000000 : ℝ)*base77 + (987597226503581349/4504412530000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p027_b027 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (c : Fin 88) (hlo : 57 ≤ c.val) (hhi : c.val < 58)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=57 := by omega
  rcases hc with rfl
  · exact collision_c327057 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (c : Fin 88) (hlo : 57 ≤ c.val) (hhi : c.val < 58)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b027 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

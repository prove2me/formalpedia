-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b023
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:38:45.465964+00:00
-- url     : https://prove2.me/submissions/7dcb441e-2f9a-4772-8cc9-26b6718eeae2

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
theorem collision_support_c320044_s0_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-738309611/10000000000 : ℝ)*x 0 + (-1637311123/2500000000 : ℝ)*x 1 + (-4489101/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (738309611/10000000000 : ℝ)^41 ≤ (1962646604733/50000000000000 : ℝ)^33 := by
    have hnat : (738309611 : ℕ)^41*50000000000000^33 ≤ 1962646604733^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738309611 10000000000 1962646604733 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1637311123/2500000000 : ℝ)^41 ≤ (7388248738227/12500000000000 : ℝ)^33 := by
    have hnat : (1637311123 : ℕ)^41*12500000000000^33 ≤ 7388248738227^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1637311123 2500000000 7388248738227 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489101/10000000 : ℝ)^41 ≤ (18484358433827/50000000000000 : ℝ)^33 := by
    have hnat : (4489101 : ℕ)^41*50000000000000^33 ≤ 18484358433827^33*10000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489101 10000000 18484358433827 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-738309611/10000000000 : ℝ), (-1637311123/2500000000 : ℝ), (-4489101/10000000 : ℝ)] ![(1962646604733/50000000000000 : ℝ), (7388248738227/12500000000000 : ℝ), (18484358433827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-738309611/10000000000 : ℝ)|^41 ≤ (1962646604733/50000000000000 : ℝ)^33
        have hw : |(-738309611/10000000000 : ℝ)|=(738309611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1637311123/2500000000 : ℝ)|^41 ≤ (7388248738227/12500000000000 : ℝ)^33
        have hw : |(-1637311123/2500000000 : ℝ)|=(1637311123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4489101/10000000 : ℝ)|^41 ≤ (18484358433827/50000000000000 : ℝ)^33
        have hw : |(-4489101/10000000 : ℝ)|=(4489101/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s0_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5036231133/10000000000 : ℝ)*x 0 + (-1531249949/5000000000 : ℝ)*x 1 + (4232887491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5036231133/10000000000 : ℝ)^41 ≤ (21323517477599/50000000000000 : ℝ)^33 := by
    have hnat : (5036231133 : ℕ)^41*50000000000000^33 ≤ 21323517477599^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5036231133 10000000000 21323517477599 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1531249949/5000000000 : ℝ)^41 ≤ (22987326620779/100000000000000 : ℝ)^33 := by
    have hnat : (1531249949 : ℕ)^41*100000000000000^33 ≤ 22987326620779^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1531249949 5000000000 22987326620779 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232887491/10000000000 : ℝ)^41 ≤ (34365638406233/100000000000000 : ℝ)^33 := by
    have hnat : (4232887491 : ℕ)^41*100000000000000^33 ≤ 34365638406233^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232887491 10000000000 34365638406233 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5036231133/10000000000 : ℝ), (-1531249949/5000000000 : ℝ), (4232887491/10000000000 : ℝ)] ![(21323517477599/50000000000000 : ℝ), (22987326620779/100000000000000 : ℝ), (34365638406233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5036231133/10000000000 : ℝ)|^41 ≤ (21323517477599/50000000000000 : ℝ)^33
        have hw : |(5036231133/10000000000 : ℝ)|=(5036231133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1531249949/5000000000 : ℝ)|^41 ≤ (22987326620779/100000000000000 : ℝ)^33
        have hw : |(-1531249949/5000000000 : ℝ)|=(1531249949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232887491/10000000000 : ℝ)|^41 ≤ (34365638406233/100000000000000 : ℝ)^33
        have hw : |(4232887491/10000000000 : ℝ)|=(4232887491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s0_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3812976163/5000000000 : ℝ)*x 0 + (-1234459719/5000000000 : ℝ)*x 1 + (-105768199/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3812976163/5000000000 : ℝ)^41 ≤ (71410046995497/100000000000000 : ℝ)^33 := by
    have hnat : (3812976163 : ℕ)^41*100000000000000^33 ≤ 71410046995497^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3812976163 5000000000 71410046995497 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1234459719/5000000000 : ℝ)^41 ≤ (17588786163227/100000000000000 : ℝ)^33 := by
    have hnat : (1234459719 : ℕ)^41*100000000000000^33 ≤ 17588786163227^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1234459719 5000000000 17588786163227 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105768199/625000000 : ℝ)^41 ≤ (5500583414449/50000000000000 : ℝ)^33 := by
    have hnat : (105768199 : ℕ)^41*50000000000000^33 ≤ 5500583414449^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105768199 625000000 5500583414449 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3812976163/5000000000 : ℝ), (-1234459719/5000000000 : ℝ), (-105768199/625000000 : ℝ)] ![(71410046995497/100000000000000 : ℝ), (17588786163227/100000000000000 : ℝ), (5500583414449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3812976163/5000000000 : ℝ)|^41 ≤ (71410046995497/100000000000000 : ℝ)^33
        have hw : |(3812976163/5000000000 : ℝ)|=(3812976163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1234459719/5000000000 : ℝ)|^41 ≤ (17588786163227/100000000000000 : ℝ)^33
        have hw : |(-1234459719/5000000000 : ℝ)|=(1234459719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105768199/625000000 : ℝ)|^41 ≤ (5500583414449/50000000000000 : ℝ)^33
        have hw : |(-105768199/625000000 : ℝ)|=(105768199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s0_7 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-389272549/5000000000 : ℝ)*x 0 + (-2616963/3906250 : ℝ)*x 1 + (-1074227957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (389272549/5000000000 : ℝ)^41 ≤ (4192799390487/100000000000000 : ℝ)^33 := by
    have hnat : (389272549 : ℕ)^41*100000000000000^33 ≤ 4192799390487^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389272549 5000000000 4192799390487 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616963/3906250 : ℝ)^41 ≤ (30397287866993/50000000000000 : ℝ)^33 := by
    have hnat : (2616963 : ℕ)^41*50000000000000^33 ≤ 30397287866993^33*3906250^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616963 3906250 30397287866993 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1074227957/2500000000 : ℝ)^41 ≤ (35012624853379/100000000000000 : ℝ)^33 := by
    have hnat : (1074227957 : ℕ)^41*100000000000000^33 ≤ 35012624853379^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074227957 2500000000 35012624853379 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-389272549/5000000000 : ℝ), (-2616963/3906250 : ℝ), (-1074227957/2500000000 : ℝ)] ![(4192799390487/100000000000000 : ℝ), (30397287866993/50000000000000 : ℝ), (35012624853379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-389272549/5000000000 : ℝ)|^41 ≤ (4192799390487/100000000000000 : ℝ)^33
        have hw : |(-389272549/5000000000 : ℝ)|=(389272549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2616963/3906250 : ℝ)|^41 ≤ (30397287866993/50000000000000 : ℝ)^33
        have hw : |(-2616963/3906250 : ℝ)|=(2616963/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1074227957/2500000000 : ℝ)|^41 ≤ (35012624853379/100000000000000 : ℝ)^33
        have hw : |(-1074227957/2500000000 : ℝ)|=(1074227957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s0_8 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4929996399/10000000000 : ℝ)*x 0 + (53524997/156250000 : ℝ)*x 1 + (-1000366589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4929996399/10000000000 : ℝ)^41 ≤ (8306444505069/20000000000000 : ℝ)^33 := by
    have hnat : (4929996399 : ℕ)^41*20000000000000^33 ≤ 8306444505069^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4929996399 10000000000 8306444505069 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53524997/156250000 : ℝ)^41 ≤ (1056830883021/4000000000000 : ℝ)^33 := by
    have hnat : (53524997 : ℕ)^41*4000000000000^33 ≤ 1056830883021^33*156250000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53524997 156250000 1056830883021 4000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000366589/2500000000 : ℝ)^41 ≤ (32047005382469/100000000000000 : ℝ)^33 := by
    have hnat : (1000366589 : ℕ)^41*100000000000000^33 ≤ 32047005382469^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000366589 2500000000 32047005382469 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4929996399/10000000000 : ℝ), (53524997/156250000 : ℝ), (-1000366589/2500000000 : ℝ)] ![(8306444505069/20000000000000 : ℝ), (1056830883021/4000000000000 : ℝ), (32047005382469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4929996399/10000000000 : ℝ)|^41 ≤ (8306444505069/20000000000000 : ℝ)^33
        have hw : |(4929996399/10000000000 : ℝ)|=(4929996399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53524997/156250000 : ℝ)|^41 ≤ (1056830883021/4000000000000 : ℝ)^33
        have hw : |(53524997/156250000 : ℝ)|=(53524997/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1000366589/2500000000 : ℝ)|^41 ≤ (32047005382469/100000000000000 : ℝ)^33
        have hw : |(-1000366589/2500000000 : ℝ)|=(1000366589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s0_9 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2464998147/5000000000 : ℝ)*x 0 + (-1364186611/5000000000 : ℝ)*x 1 + (4643405233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2464998147/5000000000 : ℝ)^41 ≤ (8306444285269/20000000000000 : ℝ)^33 := by
    have hnat : (2464998147 : ℕ)^41*20000000000000^33 ≤ 8306444285269^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2464998147 5000000000 8306444285269 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364186611/5000000000 : ℝ)^41 ≤ (19913755898377/100000000000000 : ℝ)^33 := by
    have hnat : (1364186611 : ℕ)^41*100000000000000^33 ≤ 19913755898377^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364186611 5000000000 19913755898377 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4643405233/10000000000 : ℝ)^41 ≤ (38554022666331/100000000000000 : ℝ)^33 := by
    have hnat : (4643405233 : ℕ)^41*100000000000000^33 ≤ 38554022666331^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4643405233 10000000000 38554022666331 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2464998147/5000000000 : ℝ), (-1364186611/5000000000 : ℝ), (4643405233/10000000000 : ℝ)] ![(8306444285269/20000000000000 : ℝ), (19913755898377/100000000000000 : ℝ), (38554022666331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2464998147/5000000000 : ℝ)|^41 ≤ (8306444285269/20000000000000 : ℝ)^33
        have hw : |(2464998147/5000000000 : ℝ)|=(2464998147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1364186611/5000000000 : ℝ)|^41 ≤ (19913755898377/100000000000000 : ℝ)^33
        have hw : |(-1364186611/5000000000 : ℝ)|=(1364186611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4643405233/10000000000 : ℝ)|^41 ≤ (38554022666331/100000000000000 : ℝ)^33
        have hw : |(4643405233/10000000000 : ℝ)|=(4643405233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s0_13 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7727155653/10000000000 : ℝ)*x 0 + (-2140597791/10000000000 : ℝ)*x 1 + (-948577753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7727155653/10000000000 : ℝ)^41 ≤ (14517870137689/20000000000000 : ℝ)^33 := by
    have hnat : (7727155653 : ℕ)^41*20000000000000^33 ≤ 14517870137689^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7727155653 10000000000 14517870137689 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2140597791/10000000000 : ℝ)^41 ≤ (14731282063649/100000000000000 : ℝ)^33 := by
    have hnat : (2140597791 : ℕ)^41*100000000000000^33 ≤ 14731282063649^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140597791 10000000000 14731282063649 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (948577753/5000000000 : ℝ)^41 ≤ (253587344611/2000000000000 : ℝ)^33 := by
    have hnat : (948577753 : ℕ)^41*2000000000000^33 ≤ 253587344611^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948577753 5000000000 253587344611 2000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7727155653/10000000000 : ℝ), (-2140597791/10000000000 : ℝ), (-948577753/5000000000 : ℝ)] ![(14517870137689/20000000000000 : ℝ), (14731282063649/100000000000000 : ℝ), (253587344611/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7727155653/10000000000 : ℝ)|^41 ≤ (14517870137689/20000000000000 : ℝ)^33
        have hw : |(7727155653/10000000000 : ℝ)|=(7727155653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2140597791/10000000000 : ℝ)|^41 ≤ (14731282063649/100000000000000 : ℝ)^33
        have hw : |(-2140597791/10000000000 : ℝ)|=(2140597791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-948577753/5000000000 : ℝ)|^41 ≤ (253587344611/2000000000000 : ℝ)^33
        have hw : |(-948577753/5000000000 : ℝ)|=(948577753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s0_14 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-124102379/10000000000 : ℝ)*x 0 + (-6605160391/10000000000 : ℝ)*x 1 + (-4767489999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (124102379/10000000000 : ℝ)^41 ≤ (428219256769/100000000000000 : ℝ)^33 := by
    have hnat : (124102379 : ℕ)^41*100000000000000^33 ≤ 428219256769^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124102379 10000000000 428219256769 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6605160391/10000000000 : ℝ)^41 ≤ (29866802779323/50000000000000 : ℝ)^33 := by
    have hnat : (6605160391 : ℕ)^41*50000000000000^33 ≤ 29866802779323^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6605160391 10000000000 29866802779323 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4767489999/10000000000 : ℝ)^41 ≤ (3983817517151/10000000000000 : ℝ)^33 := by
    have hnat : (4767489999 : ℕ)^41*10000000000000^33 ≤ 3983817517151^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4767489999 10000000000 3983817517151 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-124102379/10000000000 : ℝ), (-6605160391/10000000000 : ℝ), (-4767489999/10000000000 : ℝ)] ![(428219256769/100000000000000 : ℝ), (29866802779323/50000000000000 : ℝ), (3983817517151/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-124102379/10000000000 : ℝ)|^41 ≤ (428219256769/100000000000000 : ℝ)^33
        have hw : |(-124102379/10000000000 : ℝ)|=(124102379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6605160391/10000000000 : ℝ)|^41 ≤ (29866802779323/50000000000000 : ℝ)^33
        have hw : |(-6605160391/10000000000 : ℝ)|=(6605160391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4767489999/10000000000 : ℝ)|^41 ≤ (3983817517151/10000000000000 : ℝ)^33
        have hw : |(-4767489999/10000000000 : ℝ)|=(4767489999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s0_15 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4634902107/10000000000 : ℝ)*x 0 + (625733787/2000000000 : ℝ)*x 1 + (-2291295129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4634902107/10000000000 : ℝ)^41 ≤ (38466325575061/100000000000000 : ℝ)^33 := by
    have hnat : (4634902107 : ℕ)^41*100000000000000^33 ≤ 38466325575061^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4634902107 10000000000 38466325575061 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625733787/2000000000 : ℝ)^41 ≤ (1475375485807/6250000000000 : ℝ)^33 := by
    have hnat : (625733787 : ℕ)^41*6250000000000^33 ≤ 1475375485807^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625733787 2000000000 1475375485807 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2291295129/5000000000 : ℝ)^41 ≤ (37927666634767/100000000000000 : ℝ)^33 := by
    have hnat : (2291295129 : ℕ)^41*100000000000000^33 ≤ 37927666634767^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291295129 5000000000 37927666634767 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4634902107/10000000000 : ℝ), (625733787/2000000000 : ℝ), (-2291295129/5000000000 : ℝ)] ![(38466325575061/100000000000000 : ℝ), (1475375485807/6250000000000 : ℝ), (37927666634767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4634902107/10000000000 : ℝ)|^41 ≤ (38466325575061/100000000000000 : ℝ)^33
        have hw : |(4634902107/10000000000 : ℝ)|=(4634902107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(625733787/2000000000 : ℝ)|^41 ≤ (1475375485807/6250000000000 : ℝ)^33
        have hw : |(625733787/2000000000 : ℝ)|=(625733787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2291295129/5000000000 : ℝ)|^41 ≤ (37927666634767/100000000000000 : ℝ)^33
        have hw : |(-2291295129/5000000000 : ℝ)|=(2291295129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s0_16 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5677754281/10000000000 : ℝ)*x 0 + (-1334354661/5000000000 : ℝ)*x 1 + (3908883169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5677754281/10000000000 : ℝ)^41 ≤ (1546796077167/3125000000000 : ℝ)^33 := by
    have hnat : (5677754281 : ℕ)^41*3125000000000^33 ≤ 1546796077167^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5677754281 10000000000 1546796077167 3125000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1334354661/5000000000 : ℝ)^41 ≤ (19374156042769/100000000000000 : ℝ)^33 := by
    have hnat : (1334354661 : ℕ)^41*100000000000000^33 ≤ 19374156042769^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334354661 5000000000 19374156042769 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3908883169/10000000000 : ℝ)^41 ≤ (31128369475301/100000000000000 : ℝ)^33 := by
    have hnat : (3908883169 : ℕ)^41*100000000000000^33 ≤ 31128369475301^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3908883169 10000000000 31128369475301 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5677754281/10000000000 : ℝ), (-1334354661/5000000000 : ℝ), (3908883169/10000000000 : ℝ)] ![(1546796077167/3125000000000 : ℝ), (19374156042769/100000000000000 : ℝ), (31128369475301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5677754281/10000000000 : ℝ)|^41 ≤ (1546796077167/3125000000000 : ℝ)^33
        have hw : |(5677754281/10000000000 : ℝ)|=(5677754281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1334354661/5000000000 : ℝ)|^41 ≤ (19374156042769/100000000000000 : ℝ)^33
        have hw : |(-1334354661/5000000000 : ℝ)|=(1334354661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3908883169/10000000000 : ℝ)|^41 ≤ (31128369475301/100000000000000 : ℝ)^33
        have hw : |(3908883169/10000000000 : ℝ)|=(3908883169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s0_19 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8796990541/10000000000 : ℝ)*x 0 + (-354508941/2500000000 : ℝ)*x 1 + (-511756787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8796990541/10000000000 : ℝ)^41 ≤ (10659807950773/12500000000000 : ℝ)^33 := by
    have hnat : (8796990541 : ℕ)^41*12500000000000^33 ≤ 10659807950773^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8796990541 10000000000 10659807950773 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (354508941/2500000000 : ℝ)^41 ≤ (1766304552139/20000000000000 : ℝ)^33 := by
    have hnat : (354508941 : ℕ)^41*20000000000000^33 ≤ 1766304552139^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354508941 2500000000 1766304552139 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511756787/5000000000 : ℝ)^41 ≤ (1472503405717/25000000000000 : ℝ)^33 := by
    have hnat : (511756787 : ℕ)^41*25000000000000^33 ≤ 1472503405717^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511756787 5000000000 1472503405717 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8796990541/10000000000 : ℝ), (-354508941/2500000000 : ℝ), (-511756787/5000000000 : ℝ)] ![(10659807950773/12500000000000 : ℝ), (1766304552139/20000000000000 : ℝ), (1472503405717/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8796990541/10000000000 : ℝ)|^41 ≤ (10659807950773/12500000000000 : ℝ)^33
        have hw : |(8796990541/10000000000 : ℝ)|=(8796990541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-354508941/2500000000 : ℝ)|^41 ≤ (1766304552139/20000000000000 : ℝ)^33
        have hw : |(-354508941/2500000000 : ℝ)|=(354508941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-511756787/5000000000 : ℝ)|^41 ≤ (1472503405717/25000000000000 : ℝ)^33
        have hw : |(-511756787/5000000000 : ℝ)|=(511756787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s0_20 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-23470547/2000000000 : ℝ)*x 0 + (-3462368041/5000000000 : ℝ)*x 1 + (-4419253151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23470547/2000000000 : ℝ)^41 ≤ (399476807937/100000000000000 : ℝ)^33 := by
    have hnat : (23470547 : ℕ)^41*100000000000000^33 ≤ 399476807937^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23470547 2000000000 399476807937 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3462368041/5000000000 : ℝ)^41 ≤ (6334511064327/10000000000000 : ℝ)^33 := by
    have hnat : (3462368041 : ℕ)^41*10000000000000^33 ≤ 6334511064327^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3462368041 5000000000 6334511064327 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4419253151/10000000000 : ℝ)^41 ≤ (906385313539/2500000000000 : ℝ)^33 := by
    have hnat : (4419253151 : ℕ)^41*2500000000000^33 ≤ 906385313539^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419253151 10000000000 906385313539 2500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23470547/2000000000 : ℝ), (-3462368041/5000000000 : ℝ), (-4419253151/10000000000 : ℝ)] ![(399476807937/100000000000000 : ℝ), (6334511064327/10000000000000 : ℝ), (906385313539/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23470547/2000000000 : ℝ)|^41 ≤ (399476807937/100000000000000 : ℝ)^33
        have hw : |(-23470547/2000000000 : ℝ)|=(23470547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3462368041/5000000000 : ℝ)|^41 ≤ (6334511064327/10000000000000 : ℝ)^33
        have hw : |(-3462368041/5000000000 : ℝ)|=(3462368041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4419253151/10000000000 : ℝ)|^41 ≤ (906385313539/2500000000000 : ℝ)^33
        have hw : |(-4419253151/10000000000 : ℝ)|=(4419253151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s0_21 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5684503619/10000000000 : ℝ)*x 0 + (2833667137/10000000000 : ℝ)*x 1 + (-3749204713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5684503619/10000000000 : ℝ)^41 ≤ (24785294196859/50000000000000 : ℝ)^33 := by
    have hnat : (5684503619 : ℕ)^41*50000000000000^33 ≤ 24785294196859^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5684503619 10000000000 24785294196859 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2833667137/10000000000 : ℝ)^41 ≤ (4174600396903/20000000000000 : ℝ)^33 := by
    have hnat : (2833667137 : ℕ)^41*20000000000000^33 ≤ 4174600396903^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2833667137 10000000000 4174600396903 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3749204713/10000000000 : ℝ)^41 ≤ (5911281920761/20000000000000 : ℝ)^33 := by
    have hnat : (3749204713 : ℕ)^41*20000000000000^33 ≤ 5911281920761^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3749204713 10000000000 5911281920761 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5684503619/10000000000 : ℝ), (2833667137/10000000000 : ℝ), (-3749204713/10000000000 : ℝ)] ![(24785294196859/50000000000000 : ℝ), (4174600396903/20000000000000 : ℝ), (5911281920761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5684503619/10000000000 : ℝ)|^41 ≤ (24785294196859/50000000000000 : ℝ)^33
        have hw : |(5684503619/10000000000 : ℝ)|=(5684503619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2833667137/10000000000 : ℝ)|^41 ≤ (4174600396903/20000000000000 : ℝ)^33
        have hw : |(2833667137/10000000000 : ℝ)|=(2833667137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3749204713/10000000000 : ℝ)|^41 ≤ (5911281920761/20000000000000 : ℝ)^33
        have hw : |(-3749204713/10000000000 : ℝ)|=(3749204713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s0_22 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4647444299/10000000000 : ℝ)*x 0 + (-1660152291/5000000000 : ℝ)*x 1 + (878614247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4647444299/10000000000 : ℝ)^41 ≤ (3859569326659/10000000000000 : ℝ)^33 := by
    have hnat : (4647444299 : ℕ)^41*10000000000000^33 ≤ 3859569326659^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4647444299 10000000000 3859569326659 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1660152291/5000000000 : ℝ)^41 ≤ (25415569515669/100000000000000 : ℝ)^33 := by
    have hnat : (1660152291 : ℕ)^41*100000000000000^33 ≤ 25415569515669^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1660152291 5000000000 25415569515669 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (878614247/2000000000 : ℝ)^41 ≤ (17994368601197/50000000000000 : ℝ)^33 := by
    have hnat : (878614247 : ℕ)^41*50000000000000^33 ≤ 17994368601197^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878614247 2000000000 17994368601197 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4647444299/10000000000 : ℝ), (-1660152291/5000000000 : ℝ), (878614247/2000000000 : ℝ)] ![(3859569326659/10000000000000 : ℝ), (25415569515669/100000000000000 : ℝ), (17994368601197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4647444299/10000000000 : ℝ)|^41 ≤ (3859569326659/10000000000000 : ℝ)^33
        have hw : |(4647444299/10000000000 : ℝ)|=(4647444299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1660152291/5000000000 : ℝ)|^41 ≤ (25415569515669/100000000000000 : ℝ)^33
        have hw : |(-1660152291/5000000000 : ℝ)|=(1660152291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(878614247/2000000000 : ℝ)|^41 ≤ (17994368601197/50000000000000 : ℝ)^33
        have hw : |(878614247/2000000000 : ℝ)|=(878614247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s0_25 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8762439993/10000000000 : ℝ)*x 0 + (-1520005943/10000000000 : ℝ)*x 1 + (-970042897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8762439993/10000000000 : ℝ)^41 ≤ (84862530880729/100000000000000 : ℝ)^33 := by
    have hnat : (8762439993 : ℕ)^41*100000000000000^33 ≤ 84862530880729^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8762439993 10000000000 84862530880729 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1520005943/10000000000 : ℝ)^41 ≤ (1925461081779/20000000000000 : ℝ)^33 := by
    have hnat : (1520005943 : ℕ)^41*20000000000000^33 ≤ 1925461081779^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1520005943 10000000000 1925461081779 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (970042897/10000000000 : ℝ)^41 ≤ (5510163697121/100000000000000 : ℝ)^33 := by
    have hnat : (970042897 : ℕ)^41*100000000000000^33 ≤ 5510163697121^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970042897 10000000000 5510163697121 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8762439993/10000000000 : ℝ), (-1520005943/10000000000 : ℝ), (-970042897/10000000000 : ℝ)] ![(84862530880729/100000000000000 : ℝ), (1925461081779/20000000000000 : ℝ), (5510163697121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8762439993/10000000000 : ℝ)|^41 ≤ (84862530880729/100000000000000 : ℝ)^33
        have hw : |(8762439993/10000000000 : ℝ)|=(8762439993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1520005943/10000000000 : ℝ)|^41 ≤ (1925461081779/20000000000000 : ℝ)^33
        have hw : |(-1520005943/10000000000 : ℝ)|=(1520005943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-970042897/10000000000 : ℝ)|^41 ≤ (5510163697121/100000000000000 : ℝ)^33
        have hw : |(-970042897/10000000000 : ℝ)|=(970042897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s1_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2171610769/10000000000 : ℝ)*x 0 + (-2819455879/5000000000 : ℝ)*x 1 + (-4386903743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171610769/10000000000 : ℝ)^41 ≤ (2999382531977/20000000000000 : ℝ)^33 := by
    have hnat : (2171610769 : ℕ)^41*20000000000000^33 ≤ 2999382531977^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171610769 10000000000 2999382531977 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2819455879/5000000000 : ℝ)^41 ≤ (24538556505631/50000000000000 : ℝ)^33 := by
    have hnat : (2819455879 : ℕ)^41*50000000000000^33 ≤ 24538556505631^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2819455879 5000000000 24538556505631 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4386903743/10000000000 : ℝ)^41 ≤ (17962987155893/50000000000000 : ℝ)^33 := by
    have hnat : (4386903743 : ℕ)^41*50000000000000^33 ≤ 17962987155893^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386903743 10000000000 17962987155893 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2171610769/10000000000 : ℝ), (-2819455879/5000000000 : ℝ), (-4386903743/10000000000 : ℝ)] ![(2999382531977/20000000000000 : ℝ), (24538556505631/50000000000000 : ℝ), (17962987155893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2171610769/10000000000 : ℝ)|^41 ≤ (2999382531977/20000000000000 : ℝ)^33
        have hw : |(-2171610769/10000000000 : ℝ)|=(2171610769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2819455879/5000000000 : ℝ)|^41 ≤ (24538556505631/50000000000000 : ℝ)^33
        have hw : |(-2819455879/5000000000 : ℝ)|=(2819455879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4386903743/10000000000 : ℝ)|^41 ≤ (17962987155893/50000000000000 : ℝ)^33
        have hw : |(-4386903743/10000000000 : ℝ)|=(4386903743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s1_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (471364271/1000000000 : ℝ)*x 0 + (3442061577/10000000000 : ℝ)*x 1 + (-842130299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (471364271/1000000000 : ℝ)^41 ≤ (39279902048261/100000000000000 : ℝ)^33 := by
    have hnat : (471364271 : ℕ)^41*100000000000000^33 ≤ 39279902048261^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471364271 1000000000 39279902048261 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3442061577/10000000000 : ℝ)^41 ≤ (6488918149/24414062500 : ℝ)^33 := by
    have hnat : (3442061577 : ℕ)^41*24414062500^33 ≤ 6488918149^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3442061577 10000000000 6488918149 24414062500 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (842130299/2000000000 : ℝ)^41 ≤ (3414148920067/10000000000000 : ℝ)^33 := by
    have hnat : (842130299 : ℕ)^41*10000000000000^33 ≤ 3414148920067^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842130299 2000000000 3414148920067 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(471364271/1000000000 : ℝ), (3442061577/10000000000 : ℝ), (-842130299/2000000000 : ℝ)] ![(39279902048261/100000000000000 : ℝ), (6488918149/24414062500 : ℝ), (3414148920067/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(471364271/1000000000 : ℝ)|^41 ≤ (39279902048261/100000000000000 : ℝ)^33
        have hw : |(471364271/1000000000 : ℝ)|=(471364271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3442061577/10000000000 : ℝ)|^41 ≤ (6488918149/24414062500 : ℝ)^33
        have hw : |(3442061577/10000000000 : ℝ)|=(3442061577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-842130299/2000000000 : ℝ)|^41 ≤ (3414148920067/10000000000000 : ℝ)^33
        have hw : |(-842130299/2000000000 : ℝ)|=(842130299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s1_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4712822649/10000000000 : ℝ)*x 0 + (-3442448951/10000000000 : ℝ)*x 1 + (4211125367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4712822649/10000000000 : ℝ)^41 ≤ (7854282358973/20000000000000 : ℝ)^33 := by
    have hnat : (4712822649 : ℕ)^41*20000000000000^33 ≤ 7854282358973^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4712822649 10000000000 7854282358973 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3442448951/10000000000 : ℝ)^41 ≤ (26582325116623/100000000000000 : ℝ)^33 := by
    have hnat : (3442448951 : ℕ)^41*100000000000000^33 ≤ 26582325116623^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3442448951 10000000000 26582325116623 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4211125367/10000000000 : ℝ)^41 ≤ (1365850522591/4000000000000 : ℝ)^33 := by
    have hnat : (4211125367 : ℕ)^41*4000000000000^33 ≤ 1365850522591^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211125367 10000000000 1365850522591 4000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4712822649/10000000000 : ℝ), (-3442448951/10000000000 : ℝ), (4211125367/10000000000 : ℝ)] ![(7854282358973/20000000000000 : ℝ), (26582325116623/100000000000000 : ℝ), (1365850522591/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4712822649/10000000000 : ℝ)|^41 ≤ (7854282358973/20000000000000 : ℝ)^33
        have hw : |(4712822649/10000000000 : ℝ)|=(4712822649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3442448951/10000000000 : ℝ)|^41 ≤ (26582325116623/100000000000000 : ℝ)^33
        have hw : |(-3442448951/10000000000 : ℝ)|=(3442448951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4211125367/10000000000 : ℝ)|^41 ≤ (1365850522591/4000000000000 : ℝ)^33
        have hw : |(4211125367/10000000000 : ℝ)|=(4211125367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320044_s1_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3004618349/5000000000 : ℝ)*x 0 + (-3493253327/10000000000 : ℝ)*x 1 + (-2717646019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3004618349/5000000000 : ℝ)^41 ≤ (6639108447849/12500000000000 : ℝ)^33 := by
    have hnat : (3004618349 : ℕ)^41*12500000000000^33 ≤ 6639108447849^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3004618349 5000000000 6639108447849 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3493253327/10000000000 : ℝ)^41 ≤ (6767651529717/25000000000000 : ℝ)^33 := by
    have hnat : (3493253327 : ℕ)^41*25000000000000^33 ≤ 6767651529717^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3493253327 10000000000 6767651529717 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717646019/10000000000 : ℝ)^41 ≤ (9908263139133/50000000000000 : ℝ)^33 := by
    have hnat : (2717646019 : ℕ)^41*50000000000000^33 ≤ 9908263139133^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717646019 10000000000 9908263139133 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3004618349/5000000000 : ℝ), (-3493253327/10000000000 : ℝ), (-2717646019/10000000000 : ℝ)] ![(6639108447849/12500000000000 : ℝ), (6767651529717/25000000000000 : ℝ), (9908263139133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3004618349/5000000000 : ℝ)|^41 ≤ (6639108447849/12500000000000 : ℝ)^33
        have hw : |(3004618349/5000000000 : ℝ)|=(3004618349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3493253327/10000000000 : ℝ)|^41 ≤ (6767651529717/25000000000000 : ℝ)^33
        have hw : |(-3493253327/10000000000 : ℝ)|=(3493253327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2717646019/10000000000 : ℝ)|^41 ≤ (9908263139133/50000000000000 : ℝ)^33
        have hw : |(-2717646019/10000000000 : ℝ)|=(2717646019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320044 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]]) : False := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 0 (by
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 1 (by
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-738309611/10000000000 : ℝ)*X 0 0+(-1637311123/2500000000 : ℝ)*X 0 1+(-4489101/10000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5036231133/10000000000 : ℝ)*X 2 0+(-1531249949/5000000000 : ℝ)*X 2 1+(4232887491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((3812976163/5000000000 : ℝ)*X 0 0+(-1234459719/5000000000 : ℝ)*X 0 1+(-105768199/625000000 : ℝ)*X 0 2+(3812976163/5000000000 : ℝ)*X 1 0+(-1234459719/5000000000 : ℝ)*X 1 1+(-105768199/625000000 : ℝ)*X 1 2+(3812976163/5000000000 : ℝ)*X 2 0+(-1234459719/5000000000 : ℝ)*X 2 1+(-105768199/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-389272549/5000000000 : ℝ)*X 0 0+(-2616963/3906250 : ℝ)*X 0 1+(-1074227957/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4929996399/10000000000 : ℝ)*X 1 0+(53524997/156250000 : ℝ)*X 1 1+(-1000366589/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2464998147/5000000000 : ℝ)*X 2 0+(-1364186611/5000000000 : ℝ)*X 2 1+(4643405233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((7727155653/10000000000 : ℝ)*X 0 0+(-2140597791/10000000000 : ℝ)*X 0 1+(-948577753/5000000000 : ℝ)*X 0 2+(7727155653/10000000000 : ℝ)*X 1 0+(-2140597791/10000000000 : ℝ)*X 1 1+(-948577753/5000000000 : ℝ)*X 1 2+(7727155653/10000000000 : ℝ)*X 2 0+(-2140597791/10000000000 : ℝ)*X 2 1+(-948577753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-124102379/10000000000 : ℝ)*X 0 0+(-6605160391/10000000000 : ℝ)*X 0 1+(-4767489999/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4634902107/10000000000 : ℝ)*X 1 0+(625733787/2000000000 : ℝ)*X 1 1+(-2291295129/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((5677754281/10000000000 : ℝ)*X 2 0+(-1334354661/5000000000 : ℝ)*X 2 1+(3908883169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((8796990541/10000000000 : ℝ)*X 0 0+(-354508941/2500000000 : ℝ)*X 0 1+(-511756787/5000000000 : ℝ)*X 0 2+(8796990541/10000000000 : ℝ)*X 1 0+(-354508941/2500000000 : ℝ)*X 1 1+(-511756787/5000000000 : ℝ)*X 1 2+(8796990541/10000000000 : ℝ)*X 2 0+(-354508941/2500000000 : ℝ)*X 2 1+(-511756787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-23470547/2000000000 : ℝ)*X 0 0+(-3462368041/5000000000 : ℝ)*X 0 1+(-4419253151/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((5684503619/10000000000 : ℝ)*X 1 0+(2833667137/10000000000 : ℝ)*X 1 1+(-3749204713/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4647444299/10000000000 : ℝ)*X 2 0+(-1660152291/5000000000 : ℝ)*X 2 1+(878614247/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((8762439993/10000000000 : ℝ)*X 0 0+(-1520005943/10000000000 : ℝ)*X 0 1+(-970042897/10000000000 : ℝ)*X 0 2+(8762439993/10000000000 : ℝ)*X 1 0+(-1520005943/10000000000 : ℝ)*X 1 1+(-970042897/10000000000 : ℝ)*X 1 2+(8762439993/10000000000 : ℝ)*X 2 0+(-1520005943/10000000000 : ℝ)*X 2 1+(-970042897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((127/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(127/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13551870059967564206031/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (159356777083/250000000000 : ℝ)*(base39) + (508766897237/1000000000000 : ℝ)*(base49) + (2967917145501/1000000000000 : ℝ)*(major_s0_0) + (2967917145501/1000000000000 : ℝ)*(major_s0_1) + (2967917145501/1000000000000 : ℝ)*(major_s0_2) + (5408963/50000000000 : ℝ)*(sp_s0_0) + (43726557/500000000000 : ℝ)*(sp_s0_6) + (34837484429/8000000000 : ℝ)*(sp_s0_7) + (4354755867873/1000000000000 : ℝ)*(sp_s0_8) + (4354755597321/1000000000000 : ℝ)*(sp_s0_9) + (98809163199/62500000000 : ℝ)*(sp_s0_13) + (10637977/250000000000 : ℝ)*(sp_s0_15) + (292931/62500000000 : ℝ)*(sp_s0_20) + (42822459/1000000000000 : ℝ)*(sp_s0_22) + (1581034064299/1000000000000 : ℝ)*(f.failure) + (4354798419781/1000000000000 : ℝ)*(f.sum) + (1862804280040851/5000000000000000000000000000 : ℝ)*base63 + (4440312439068677/10000000000000000000000000000 : ℝ)*base65 + (4457041304931323/10000000000000000000000000000 : ℝ)*base67 + (870992695959149/10000000000000000000000000000 : ℝ)*base68 + (323344776736309/1250000000000000000000000000 : ℝ)*base70 + (4755488560931323/10000000000000000000000000000 : ℝ)*base73 + (3949827172040851/10000000000000000000000000000 : ℝ)*base75 + (516197020959149/10000000000000000000000000000 : ℝ)*base76 + (1894908639931323/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (2707/2500000000000000 : ℝ)*base87 + (2707/2500000000000000 : ℝ)*base89 + (2707/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6839/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-6839/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3307918484146310328093/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1659666332097/500000000000 : ℝ)*(base39) + (542205237089/250000000000 : ℝ)*(base40) + (973210032947/1000000000000 : ℝ)*(base49) + (408458443677/62500000000 : ℝ)*(major_s0_0) + (408458443677/62500000000 : ℝ)*(major_s0_1) + (408458443677/62500000000 : ℝ)*(major_s0_2) + (114309983/500000000000 : ℝ)*(sp_s0_0) + (39525741/250000000000 : ℝ)*(sp_s0_9) + (21059993/1000000000000 : ℝ)*(sp_s0_13) + (2397252717773/250000000000 : ℝ)*(sp_s0_14) + (9589200402411/1000000000000 : ℝ)*(sp_s0_15) + (4794540694047/500000000000 : ℝ)*(sp_s0_16) + (3481406118161/1000000000000 : ℝ)*(sp_s0_19) + (39088647/1000000000000 : ℝ)*(sp_s0_21) + (696285435631/200000000000 : ℝ)*(f.failure) + (4794619745529/500000000000 : ℝ)*(f.sum) + (181891939795627/312500000000000000000000000 : ℝ)*base63 + (122501320776671/625000000000000000000000000 : ℝ)*base64 + (188794663964171/625000000000000000000000000 : ℝ)*base67 + (369347765920627/625000000000000000000000000 : ℝ)*base69 + (8101531964011/156250000000000000000000000 : ℝ)*base70 + (29534683473329/625000000000000000000000000 : ℝ)*base72 + (407081993420627/625000000000000000000000000 : ℝ)*base75 + (81356812641873/625000000000000000000000000 : ℝ)*base76 + (156005939401671/312500000000000000000000000 : ℝ)*base79 + (283/500000000000000 : ℝ)*base87 + (283/500000000000000 : ℝ)*base89 + (283/500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17281/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-17281/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (810348300742193322729/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6390891/1000000000000 : ℝ)*(base10) + (1747198899089/500000000000 : ℝ)*(base39) + (372152783689/200000000000 : ℝ)*(base40) + (987530522417/1000000000000 : ℝ)*(base49) + (1314356691023/200000000000 : ℝ)*(major_s0_0) + (1314356691023/200000000000 : ℝ)*(major_s0_1) + (1314356691023/200000000000 : ℝ)*(major_s0_2) + (3794717/62500000000 : ℝ)*(sp_s0_2) + (48721261/500000000000 : ℝ)*(sp_s0_7) + (33900507/500000000000 : ℝ)*(sp_s0_8) + (9642618206567/1000000000000 : ℝ)*(sp_s0_20) + (4821327119483/500000000000 : ℝ)*(sp_s0_21) + (2410665331127/250000000000 : ℝ)*(sp_s0_22) + (700168703933/200000000000 : ℝ)*(sp_s0_25) + (700168703933/200000000000 : ℝ)*(f.failure) + (482136101999/50000000000 : ℝ)*(f.sum) + (156259326540927/1000000000000000000000000000 : ℝ)*base62 + (835352013143929/2000000000000000000000000000 : ℝ)*base64 + (1217840369456071/2000000000000000000000000000 : ℝ)*base66 + (611444340859073/2000000000000000000000000000 : ℝ)*base69 + (74072044610607/250000000000000000000000000 : ℝ)*base70 + (914867412343929/2000000000000000000000000000 : ℝ)*base73 + (601763715259073/2000000000000000000000000000 : ℝ)*base75 + (1586552560740927/2000000000000000000000000000 : ℝ)*base76 + (1024305300243929/1000000000000000000000000000 : ℝ)*base79 + (69/500000000000000 : ℝ)*base87 + (69/500000000000000 : ℝ)*base89 + (69/500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (127/3125 : ℝ) ^ (5 : ℝ) ≤ (11085837196581/100000000000000000000 : ℝ) := by
    have hpowers : (127/3125 : ℝ)^5 ≤ (11085837196581/100000000000000000000 : ℝ)^1 := by
      have hnat : (127 : ℕ)^5*100000000000000000000^1 ≤ 11085837196581^1*3125^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127 3125 11085837196581 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (127/3125 : ℝ)) (X := (11085837196581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0a : (100000011085837196581/100000000000000000000 : ℝ) ≤ (2000000044343347/2000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (100000011085837196581/100000000000000000000 : ℝ)^1 ≤ (2000000044343347/2000000000000000 : ℝ)^5 := by
      have hnat : (100000011085837196581 : ℕ)^1*2000000000000000^5 ≤ 2000000044343347^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100000011085837196581 100000000000000000000 2000000044343347 2000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000044343347/2000000000000000 : ℝ)) (X := (100000011085837196581/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0b : (50000011085837196581/50000000000000000000 : ℝ) ≤ (10000000443433449/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (50000011085837196581/50000000000000000000 : ℝ)^1 ≤ (10000000443433449/10000000000000000 : ℝ)^5 := by
      have hnat : (50000011085837196581 : ℕ)^1*10000000000000000^5 ≤ 10000000443433449^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000011085837196581 50000000000000000000 10000000443433449 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000443433449/10000000000000000 : ℝ)) (X := (50000011085837196581/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(44343347/81280000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(110858357/203200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (127/3125 : ℝ)) (alpha := (44343347/81280000000000 : ℝ)) (beta := (110858357/203200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (127/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(44343347/81280000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(110858357/203200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (6839/20000 : ℝ) ^ (5 : ℝ) ≤ (467533829080400569/100000000000000000000 : ℝ) := by
    have hpowers : (6839/20000 : ℝ)^5 ≤ (467533829080400569/100000000000000000000 : ℝ)^1 := by
      have hnat : (6839 : ℕ)^5*100000000000000000000^1 ≤ 467533829080400569^1*20000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6839 20000 467533829080400569 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6839/20000 : ℝ)) (X := (467533829080400569/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1a : (100467533829080400569/100000000000000000000 : ℝ) ≤ (10009333238445797/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (100467533829080400569/100000000000000000000 : ℝ)^1 ≤ (10009333238445797/10000000000000000 : ℝ)^5 := by
      have hnat : (100467533829080400569 : ℕ)^1*10000000000000000^5 ≤ 10009333238445797^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100467533829080400569 100000000000000000000 10009333238445797 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009333238445797/10000000000000000 : ℝ)) (X := (100467533829080400569/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1b : (50467533829080400569/50000000000000000000 : ℝ) ≤ (500931589746399/500000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (50467533829080400569/50000000000000000000 : ℝ)^1 ≤ (500931589746399/500000000000000 : ℝ)^5 := by
      have hnat : (50467533829080400569 : ℕ)^1*500000000000000^5 ≤ 500931589746399^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50467533829080400569 50000000000000000000 500931589746399 500000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500931589746399/500000000000000 : ℝ)) (X := (50467533829080400569/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1333319777971/488500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(9298556482183/3419500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (6839/20000 : ℝ)) (alpha := (1333319777971/488500000000000 : ℝ)) (beta := (9298556482183/3419500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (6839/20000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1333319777971/488500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(9298556482183/3419500000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (17281/50000 : ℝ) ^ (5 : ℝ) ≤ (493167364506188541/100000000000000000000 : ℝ) := by
    have hpowers : (17281/50000 : ℝ)^5 ≤ (493167364506188541/100000000000000000000 : ℝ)^1 := by
      have hnat : (17281 : ℕ)^5*100000000000000000000^1 ≤ 493167364506188541^1*50000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17281 50000 493167364506188541 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17281/50000 : ℝ)) (X := (493167364506188541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2a : (100493167364506188541/100000000000000000000 : ℝ) ≤ (1000984394754187/1000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (100493167364506188541/100000000000000000000 : ℝ)^1 ≤ (1000984394754187/1000000000000000 : ℝ)^5 := by
      have hnat : (100493167364506188541 : ℕ)^1*1000000000000000^5 ≤ 1000984394754187^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100493167364506188541 100000000000000000000 1000984394754187 1000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000984394754187/1000000000000000 : ℝ)) (X := (100493167364506188541/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2b : (50493167364506188541/50000000000000000000 : ℝ) ≤ (2504912330879427/2500000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (50493167364506188541/50000000000000000000 : ℝ)^1 ≤ (2504912330879427/2500000000000000 : ℝ)^5 := by
      have hnat : (50493167364506188541 : ℕ)^1*2500000000000000^5 ≤ 2504912330879427^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50493167364506188541 50000000000000000000 2504912330879427 2500000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504912330879427/2500000000000000 : ℝ)) (X := (50493167364506188541/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(984394754187/345620000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(4902687987919/1728100000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (17281/50000 : ℝ)) (alpha := (984394754187/345620000000000 : ℝ)) (beta := (4902687987919/1728100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (17281/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(984394754187/345620000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(4902687987919/1728100000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2171610769/10000000000 : ℝ)*X 0 0+(-2819455879/5000000000 : ℝ)*X 0 1+(-4386903743/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((471364271/1000000000 : ℝ)*X 1 0+(3442061577/10000000000 : ℝ)*X 1 1+(-842130299/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4712822649/10000000000 : ℝ)*X 2 0+(-3442448951/10000000000 : ℝ)*X 2 1+(4211125367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3004618349/5000000000 : ℝ)*X 0 0+(-3493253327/10000000000 : ℝ)*X 0 1+(-2717646019/10000000000 : ℝ)*X 0 2+(3004618349/5000000000 : ℝ)*X 1 0+(-3493253327/10000000000 : ℝ)*X 1 1+(-2717646019/10000000000 : ℝ)*X 1 2+(3004618349/5000000000 : ℝ)*X 2 0+(-3493253327/10000000000 : ℝ)*X 2 1+(-2717646019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320044_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-10329/1250 : ℝ) < ((-4693/2500 : ℝ)*P 0+(-4693/2500 : ℝ)*P 1+(-4693/2500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-10329/1250 : ℝ) < (-9794449994422220764491120365448339/1200757151440000000000000000000000 : ℝ) := by norm_num
    linear_combination (49/10000000000 : ℝ)*(base8) + (663/125000000000 : ℝ)*(base10) + (4099/250000000000 : ℝ)*(base15) + (3843/250000000000 : ℝ)*(base33) + (1052456812597/1000000000000 : ℝ)*(base39) + (73985478531/125000000000 : ℝ)*(base40) + (407547009657/1000000000000 : ℝ)*(base49) + (5427/500000000000 : ℝ)*(base59) + (469299996157/250000000000 : ℝ)*(major_s1_0) + (4693/2500 : ℝ)*(major_s1_1) + (4693/2500 : ℝ)*(major_s1_2) + (1359482493457/500000000000 : ℝ)*(sp_s1_0) + (54379299307/20000000000 : ℝ)*(sp_s1_1) + (1359482490873/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1359482498559/500000000000 : ℝ)*(f.sum) + (7288238094622479/84417685000000000000000000000 : ℝ)*base62 + (7988822071543/43202500000000000000000000 : ℝ)*base65 + (8151147019289/34195000000000000000000000 : ℝ)*base67 + (65957335643/345620000000000000000000 : ℝ)*base69 + (253143248182160199/351149920000000000000000000000 : ℝ)*base71 + (9994381555951/50800000000000000000000000 : ℝ)*base72 + (1461263622271/4885000000000000000000000 : ℝ)*base75 + (5392444559751/20320000000000000000000000 : ℝ)*base77 + (89303186039223271/347421200000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p020_b023 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 44 ≤ c.val) (hhi : c.val < 45)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=44 := by omega
  rcases hc with rfl
  · exact collision_c320044 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 44 ≤ c.val) (hhi : c.val < 45)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b023 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

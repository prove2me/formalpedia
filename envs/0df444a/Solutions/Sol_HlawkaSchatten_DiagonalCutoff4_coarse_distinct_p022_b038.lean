-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p022_b038
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:45:08.1397+00:00
-- url     : https://prove2.me/submissions/69298dbd-2e82-4cb2-a7b2-52eecd9cb6ac

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
theorem collision_support_c322068_s0_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3735895591/5000000000 : ℝ)*x 0 + (2588866117/10000000000 : ℝ)*x 1 + (-1751934501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3735895591/5000000000 : ℝ)^83 ≤ (69694385753669/100000000000000 : ℝ)^67 := by
    have hnat : (3735895591 : ℕ)^83*100000000000000^67 ≤ 69694385753669^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3735895591 5000000000 69694385753669 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588866117/10000000000 : ℝ)^83 ≤ (468701849027/2500000000000 : ℝ)^67 := by
    have hnat : (2588866117 : ℕ)^83*2500000000000^67 ≤ 468701849027^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588866117 10000000000 468701849027 2500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1751934501/10000000000 : ℝ)^83 ≤ (11557540267549/100000000000000 : ℝ)^67 := by
    have hnat : (1751934501 : ℕ)^83*100000000000000^67 ≤ 11557540267549^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751934501 10000000000 11557540267549 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3735895591/5000000000 : ℝ), (2588866117/10000000000 : ℝ), (-1751934501/10000000000 : ℝ)] ![(69694385753669/100000000000000 : ℝ), (468701849027/2500000000000 : ℝ), (11557540267549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3735895591/5000000000 : ℝ)|^83 ≤ (69694385753669/100000000000000 : ℝ)^67
        have hw : |(3735895591/5000000000 : ℝ)|=(3735895591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588866117/10000000000 : ℝ)|^83 ≤ (468701849027/2500000000000 : ℝ)^67
        have hw : |(2588866117/10000000000 : ℝ)|=(2588866117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1751934501/10000000000 : ℝ)|^83 ≤ (11557540267549/100000000000000 : ℝ)^67
        have hw : |(-1751934501/10000000000 : ℝ)|=(1751934501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s0_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1954772861/5000000000 : ℝ)*x 0 + (-2226709001/5000000000 : ℝ)*x 1 + (1995429297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1954772861/5000000000 : ℝ)^83 ≤ (15620453035461/50000000000000 : ℝ)^67 := by
    have hnat : (1954772861 : ℕ)^83*50000000000000^67 ≤ 15620453035461^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954772861 5000000000 15620453035461 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2226709001/5000000000 : ℝ)^83 ≤ (1468450639183/4000000000000 : ℝ)^67 := by
    have hnat : (2226709001 : ℕ)^83*4000000000000^67 ≤ 1468450639183^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226709001 5000000000 1468450639183 4000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1995429297/5000000000 : ℝ)^83 ≤ (32047827933781/100000000000000 : ℝ)^67 := by
    have hnat : (1995429297 : ℕ)^83*100000000000000^67 ≤ 32047827933781^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995429297 5000000000 32047827933781 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1954772861/5000000000 : ℝ), (-2226709001/5000000000 : ℝ), (1995429297/5000000000 : ℝ)] ![(15620453035461/50000000000000 : ℝ), (1468450639183/4000000000000 : ℝ), (32047827933781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1954772861/5000000000 : ℝ)|^83 ≤ (15620453035461/50000000000000 : ℝ)^67
        have hw : |(1954772861/5000000000 : ℝ)|=(1954772861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2226709001/5000000000 : ℝ)|^83 ≤ (1468450639183/4000000000000 : ℝ)^67
        have hw : |(-2226709001/5000000000 : ℝ)|=(2226709001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1995429297/5000000000 : ℝ)|^83 ≤ (32047827933781/100000000000000 : ℝ)^67
        have hw : |(1995429297/5000000000 : ℝ)|=(1995429297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s0_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-586828273/10000000000 : ℝ)*x 0 + (-135716369/250000000 : ℝ)*x 1 + (-5724105547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (586828273/10000000000 : ℝ)^83 ≤ (298142652817/10000000000000 : ℝ)^67 := by
    have hnat : (586828273 : ℕ)^83*10000000000000^67 ≤ 298142652817^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586828273 10000000000 298142652817 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135716369/250000000 : ℝ)^83 ≤ (46917530195287/100000000000000 : ℝ)^67 := by
    have hnat : (135716369 : ℕ)^83*100000000000000^67 ≤ 46917530195287^67*250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135716369 250000000 46917530195287 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5724105547/10000000000 : ℝ)^83 ≤ (313131520431/625000000000 : ℝ)^67 := by
    have hnat : (5724105547 : ℕ)^83*625000000000^67 ≤ 313131520431^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5724105547 10000000000 313131520431 625000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-586828273/10000000000 : ℝ), (-135716369/250000000 : ℝ), (-5724105547/10000000000 : ℝ)] ![(298142652817/10000000000000 : ℝ), (46917530195287/100000000000000 : ℝ), (313131520431/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-586828273/10000000000 : ℝ)|^83 ≤ (298142652817/10000000000000 : ℝ)^67
        have hw : |(-586828273/10000000000 : ℝ)|=(586828273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-135716369/250000000 : ℝ)|^83 ≤ (46917530195287/100000000000000 : ℝ)^67
        have hw : |(-135716369/250000000 : ℝ)|=(135716369/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5724105547/10000000000 : ℝ)|^83 ≤ (313131520431/625000000000 : ℝ)^67
        have hw : |(-5724105547/10000000000 : ℝ)|=(5724105547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s0_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3748298581/5000000000 : ℝ)*x 0 + (293648829/1000000000 : ℝ)*x 1 + (-164426767/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3748298581/5000000000 : ℝ)^83 ≤ (34990568306633/50000000000000 : ℝ)^67 := by
    have hnat : (3748298581 : ℕ)^83*50000000000000^67 ≤ 34990568306633^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3748298581 5000000000 34990568306633 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (293648829/1000000000 : ℝ)^83 ≤ (5478762777491/25000000000000 : ℝ)^67 := by
    have hnat : (293648829 : ℕ)^83*25000000000000^67 ≤ 5478762777491^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293648829 1000000000 5478762777491 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164426767/1250000000 : ℝ)^83 ≤ (8103812264169/100000000000000 : ℝ)^67 := by
    have hnat : (164426767 : ℕ)^83*100000000000000^67 ≤ 8103812264169^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164426767 1250000000 8103812264169 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3748298581/5000000000 : ℝ), (293648829/1000000000 : ℝ), (-164426767/1250000000 : ℝ)] ![(34990568306633/50000000000000 : ℝ), (5478762777491/25000000000000 : ℝ), (8103812264169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3748298581/5000000000 : ℝ)|^83 ≤ (34990568306633/50000000000000 : ℝ)^67
        have hw : |(3748298581/5000000000 : ℝ)|=(3748298581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(293648829/1000000000 : ℝ)|^83 ≤ (5478762777491/25000000000000 : ℝ)^67
        have hw : |(293648829/1000000000 : ℝ)|=(293648829/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-164426767/1250000000 : ℝ)|^83 ≤ (8103812264169/100000000000000 : ℝ)^67
        have hw : |(-164426767/1250000000 : ℝ)|=(164426767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s0_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (463495741/1000000000 : ℝ)*x 0 + (-808335189/2500000000 : ℝ)*x 1 + (4455653507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (463495741/1000000000 : ℝ)^83 ≤ (7714814255683/20000000000000 : ℝ)^67 := by
    have hnat : (463495741 : ℕ)^83*20000000000000^67 ≤ 7714814255683^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463495741 1000000000 7714814255683 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (808335189/2500000000 : ℝ)^83 ≤ (24691832469881/100000000000000 : ℝ)^67 := by
    have hnat : (808335189 : ℕ)^83*100000000000000^67 ≤ 24691832469881^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808335189 2500000000 24691832469881 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4455653507/10000000000 : ℝ)^83 ≤ (7346819247969/20000000000000 : ℝ)^67 := by
    have hnat : (4455653507 : ℕ)^83*20000000000000^67 ≤ 7346819247969^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4455653507 10000000000 7346819247969 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(463495741/1000000000 : ℝ), (-808335189/2500000000 : ℝ), (4455653507/10000000000 : ℝ)] ![(7714814255683/20000000000000 : ℝ), (24691832469881/100000000000000 : ℝ), (7346819247969/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(463495741/1000000000 : ℝ)|^83 ≤ (7714814255683/20000000000000 : ℝ)^67
        have hw : |(463495741/1000000000 : ℝ)|=(463495741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-808335189/2500000000 : ℝ)|^83 ≤ (24691832469881/100000000000000 : ℝ)^67
        have hw : |(-808335189/2500000000 : ℝ)|=(808335189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4455653507/10000000000 : ℝ)|^83 ≤ (7346819247969/20000000000000 : ℝ)^67
        have hw : |(4455653507/10000000000 : ℝ)|=(4455653507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s0_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (852883889/2500000000 : ℝ)*x 0 + (-1346604547/5000000000 : ℝ)*x 1 + (-6074061333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852883889/2500000000 : ℝ)^83 ≤ (6597137849151/25000000000000 : ℝ)^67 := by
    have hnat : (852883889 : ℕ)^83*25000000000000^67 ≤ 6597137849151^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852883889 2500000000 6597137849151 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346604547/5000000000 : ℝ)^83 ≤ (15381730379/78125000000 : ℝ)^67 := by
    have hnat : (1346604547 : ℕ)^83*78125000000^67 ≤ 15381730379^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346604547 5000000000 15381730379 78125000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6074061333/10000000000 : ℝ)^83 ≤ (26961416849199/50000000000000 : ℝ)^67 := by
    have hnat : (6074061333 : ℕ)^83*50000000000000^67 ≤ 26961416849199^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6074061333 10000000000 26961416849199 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852883889/2500000000 : ℝ), (-1346604547/5000000000 : ℝ), (-6074061333/10000000000 : ℝ)] ![(6597137849151/25000000000000 : ℝ), (15381730379/78125000000 : ℝ), (26961416849199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852883889/2500000000 : ℝ)|^83 ≤ (6597137849151/25000000000000 : ℝ)^67
        have hw : |(852883889/2500000000 : ℝ)|=(852883889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1346604547/5000000000 : ℝ)|^83 ≤ (15381730379/78125000000 : ℝ)^67
        have hw : |(-1346604547/5000000000 : ℝ)|=(1346604547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6074061333/10000000000 : ℝ)|^83 ≤ (26961416849199/50000000000000 : ℝ)^67
        have hw : |(-6074061333/10000000000 : ℝ)|=(6074061333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s0_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-168903601/5000000000 : ℝ)*x 0 + (-1163674729/2500000000 : ℝ)*x 1 + (-3297890443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168903601/5000000000 : ℝ)^83 ≤ (1504202321957/100000000000000 : ℝ)^67 := by
    have hnat : (168903601 : ℕ)^83*100000000000000^67 ≤ 1504202321957^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168903601 5000000000 1504202321957 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1163674729/2500000000 : ℝ)^83 ≤ (38777706958341/100000000000000 : ℝ)^67 := by
    have hnat : (1163674729 : ℕ)^83*100000000000000^67 ≤ 38777706958341^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163674729 2500000000 38777706958341 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3297890443/5000000000 : ℝ)^83 ≤ (59718090703907/100000000000000 : ℝ)^67 := by
    have hnat : (3297890443 : ℕ)^83*100000000000000^67 ≤ 59718090703907^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3297890443 5000000000 59718090703907 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-168903601/5000000000 : ℝ), (-1163674729/2500000000 : ℝ), (-3297890443/5000000000 : ℝ)] ![(1504202321957/100000000000000 : ℝ), (38777706958341/100000000000000 : ℝ), (59718090703907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-168903601/5000000000 : ℝ)|^83 ≤ (1504202321957/100000000000000 : ℝ)^67
        have hw : |(-168903601/5000000000 : ℝ)|=(168903601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1163674729/2500000000 : ℝ)|^83 ≤ (38777706958341/100000000000000 : ℝ)^67
        have hw : |(-1163674729/2500000000 : ℝ)|=(1163674729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3297890443/5000000000 : ℝ)|^83 ≤ (59718090703907/100000000000000 : ℝ)^67
        have hw : |(-3297890443/5000000000 : ℝ)|=(3297890443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s0_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4069840009/5000000000 : ℝ)*x 0 + (2439274081/10000000000 : ℝ)*x 1 + (-180798247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4069840009/5000000000 : ℝ)^83 ≤ (77492528166437/100000000000000 : ℝ)^67 := by
    have hnat : (4069840009 : ℕ)^83*100000000000000^67 ≤ 77492528166437^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4069840009 5000000000 77492528166437 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2439274081/10000000000 : ℝ)^83 ≤ (8707726479689/50000000000000 : ℝ)^67 := by
    have hnat : (2439274081 : ℕ)^83*50000000000000^67 ≤ 8707726479689^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439274081 10000000000 8707726479689 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180798247/2000000000 : ℝ)^83 ≤ (1018403771707/20000000000000 : ℝ)^67 := by
    have hnat : (180798247 : ℕ)^83*20000000000000^67 ≤ 1018403771707^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180798247 2000000000 1018403771707 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4069840009/5000000000 : ℝ), (2439274081/10000000000 : ℝ), (-180798247/2000000000 : ℝ)] ![(77492528166437/100000000000000 : ℝ), (8707726479689/50000000000000 : ℝ), (1018403771707/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4069840009/5000000000 : ℝ)|^83 ≤ (77492528166437/100000000000000 : ℝ)^67
        have hw : |(4069840009/5000000000 : ℝ)|=(4069840009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2439274081/10000000000 : ℝ)|^83 ≤ (8707726479689/50000000000000 : ℝ)^67
        have hw : |(2439274081/10000000000 : ℝ)|=(2439274081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-180798247/2000000000 : ℝ)|^83 ≤ (1018403771707/20000000000000 : ℝ)^67
        have hw : |(-180798247/2000000000 : ℝ)|=(180798247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s0_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4180544277/10000000000 : ℝ)*x 0 + (-1119596317/2500000000 : ℝ)*x 1 + (922649379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180544277/10000000000 : ℝ)^83 ≤ (16972701359973/50000000000000 : ℝ)^67 := by
    have hnat : (4180544277 : ℕ)^83*50000000000000^67 ≤ 16972701359973^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180544277 10000000000 16972701359973 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119596317/2500000000 : ℝ)^83 ≤ (36966401185533/100000000000000 : ℝ)^67 := by
    have hnat : (1119596317 : ℕ)^83*100000000000000^67 ≤ 36966401185533^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119596317 2500000000 36966401185533 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (922649379/2500000000 : ℝ)^83 ≤ (29088196075107/100000000000000 : ℝ)^67 := by
    have hnat : (922649379 : ℕ)^83*100000000000000^67 ≤ 29088196075107^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922649379 2500000000 29088196075107 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180544277/10000000000 : ℝ), (-1119596317/2500000000 : ℝ), (922649379/2500000000 : ℝ)] ![(16972701359973/50000000000000 : ℝ), (36966401185533/100000000000000 : ℝ), (29088196075107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180544277/10000000000 : ℝ)|^83 ≤ (16972701359973/50000000000000 : ℝ)^67
        have hw : |(4180544277/10000000000 : ℝ)|=(4180544277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1119596317/2500000000 : ℝ)|^83 ≤ (36966401185533/100000000000000 : ℝ)^67
        have hw : |(-1119596317/2500000000 : ℝ)|=(1119596317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(922649379/2500000000 : ℝ)|^83 ≤ (29088196075107/100000000000000 : ℝ)^67
        have hw : |(922649379/2500000000 : ℝ)|=(922649379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s0_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2685195281/10000000000 : ℝ)*x 0 + (-350076169/1250000000 : ℝ)*x 1 + (-3297890443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685195281/10000000000 : ℝ)^83 ≤ (4904016399867/25000000000000 : ℝ)^67 := by
    have hnat : (2685195281 : ℕ)^83*25000000000000^67 ≤ 4904016399867^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685195281 10000000000 4904016399867 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350076169/1250000000 : ℝ)^83 ≤ (258323046013/1250000000000 : ℝ)^67 := by
    have hnat : (350076169 : ℕ)^83*1250000000000^67 ≤ 258323046013^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350076169 1250000000 258323046013 1250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3297890443/5000000000 : ℝ)^83 ≤ (59718090703907/100000000000000 : ℝ)^67 := by
    have hnat : (3297890443 : ℕ)^83*100000000000000^67 ≤ 59718090703907^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3297890443 5000000000 59718090703907 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685195281/10000000000 : ℝ), (-350076169/1250000000 : ℝ), (-3297890443/5000000000 : ℝ)] ![(4904016399867/25000000000000 : ℝ), (258323046013/1250000000000 : ℝ), (59718090703907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685195281/10000000000 : ℝ)|^83 ≤ (4904016399867/25000000000000 : ℝ)^67
        have hw : |(2685195281/10000000000 : ℝ)|=(2685195281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-350076169/1250000000 : ℝ)|^83 ≤ (258323046013/1250000000000 : ℝ)^67
        have hw : |(-350076169/1250000000 : ℝ)|=(350076169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3297890443/5000000000 : ℝ)|^83 ≤ (59718090703907/100000000000000 : ℝ)^67
        have hw : |(-3297890443/5000000000 : ℝ)|=(3297890443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s0_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-309860141/10000000000 : ℝ)*x 0 + (-730863487/1250000000 : ℝ)*x 1 + (-5456183443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (309860141/10000000000 : ℝ)^83 ≤ (675798281519/50000000000000 : ℝ)^67 := by
    have hnat : (309860141 : ℕ)^83*50000000000000^67 ≤ 675798281519^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309860141 10000000000 675798281519 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (730863487/1250000000 : ℝ)^83 ≤ (10287192008373/20000000000000 : ℝ)^67 := by
    have hnat : (730863487 : ℕ)^83*20000000000000^67 ≤ 10287192008373^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730863487 1250000000 10287192008373 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456183443/10000000000 : ℝ)^83 ≤ (47212443379511/100000000000000 : ℝ)^67 := by
    have hnat : (5456183443 : ℕ)^83*100000000000000^67 ≤ 47212443379511^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456183443 10000000000 47212443379511 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-309860141/10000000000 : ℝ), (-730863487/1250000000 : ℝ), (-5456183443/10000000000 : ℝ)] ![(675798281519/50000000000000 : ℝ), (10287192008373/20000000000000 : ℝ), (47212443379511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-309860141/10000000000 : ℝ)|^83 ≤ (675798281519/50000000000000 : ℝ)^67
        have hw : |(-309860141/10000000000 : ℝ)|=(309860141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-730863487/1250000000 : ℝ)|^83 ≤ (10287192008373/20000000000000 : ℝ)^67
        have hw : |(-730863487/1250000000 : ℝ)|=(730863487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5456183443/10000000000 : ℝ)|^83 ≤ (47212443379511/100000000000000 : ℝ)^67
        have hw : |(-5456183443/10000000000 : ℝ)|=(5456183443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s0_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2129150507/2500000000 : ℝ)*x 0 + (117423239/625000000 : ℝ)*x 1 + (-952818571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129150507/2500000000 : ℝ)^83 ≤ (40981093908147/50000000000000 : ℝ)^67 := by
    have hnat : (2129150507 : ℕ)^83*50000000000000^67 ≤ 40981093908147^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129150507 2500000000 40981093908147 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117423239/625000000 : ℝ)^83 ≤ (1260290967637/10000000000000 : ℝ)^67 := by
    have hnat : (117423239 : ℕ)^83*10000000000000^67 ≤ 1260290967637^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117423239 625000000 1260290967637 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (952818571/10000000000 : ℝ)^83 ≤ (1358725622647/25000000000000 : ℝ)^67 := by
    have hnat : (952818571 : ℕ)^83*25000000000000^67 ≤ 1358725622647^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952818571 10000000000 1358725622647 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2129150507/2500000000 : ℝ), (117423239/625000000 : ℝ), (-952818571/10000000000 : ℝ)] ![(40981093908147/50000000000000 : ℝ), (1260290967637/10000000000000 : ℝ), (1358725622647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2129150507/2500000000 : ℝ)|^83 ≤ (40981093908147/50000000000000 : ℝ)^67
        have hw : |(2129150507/2500000000 : ℝ)|=(2129150507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(117423239/625000000 : ℝ)|^83 ≤ (1260290967637/10000000000000 : ℝ)^67
        have hw : |(117423239/625000000 : ℝ)|=(117423239/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-952818571/10000000000 : ℝ)|^83 ≤ (1358725622647/25000000000000 : ℝ)^67
        have hw : |(-952818571/10000000000 : ℝ)|=(952818571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s0_23 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (439501257/1250000000 : ℝ)*x 0 + (-4450926369/10000000000 : ℝ)*x 1 + (2187929401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (439501257/1250000000 : ℝ)^83 ≤ (27393288049569/100000000000000 : ℝ)^67 := by
    have hnat : (439501257 : ℕ)^83*100000000000000^67 ≤ 27393288049569^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439501257 1250000000 27393288049569 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4450926369/10000000000 : ℝ)^83 ≤ (18342911609037/50000000000000 : ℝ)^67 := by
    have hnat : (4450926369 : ℕ)^83*50000000000000^67 ≤ 18342911609037^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4450926369 10000000000 18342911609037 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187929401/5000000000 : ℝ)^83 ≤ (35920888724717/100000000000000 : ℝ)^67 := by
    have hnat : (2187929401 : ℕ)^83*100000000000000^67 ≤ 35920888724717^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187929401 5000000000 35920888724717 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(439501257/1250000000 : ℝ), (-4450926369/10000000000 : ℝ), (2187929401/5000000000 : ℝ)] ![(27393288049569/100000000000000 : ℝ), (18342911609037/50000000000000 : ℝ), (35920888724717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(439501257/1250000000 : ℝ)|^83 ≤ (27393288049569/100000000000000 : ℝ)^67
        have hw : |(439501257/1250000000 : ℝ)|=(439501257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4450926369/10000000000 : ℝ)|^83 ≤ (18342911609037/50000000000000 : ℝ)^67
        have hw : |(-4450926369/10000000000 : ℝ)|=(4450926369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2187929401/5000000000 : ℝ)|^83 ≤ (35920888724717/100000000000000 : ℝ)^67
        have hw : |(2187929401/5000000000 : ℝ)|=(2187929401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s0_27 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1650499491/5000000000 : ℝ)*x 0 + (-943835279/2500000000 : ℝ)*x 1 + (-1306289139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1650499491/5000000000 : ℝ)^83 ≤ (5066698146349/20000000000000 : ℝ)^67 := by
    have hnat : (1650499491 : ℕ)^83*20000000000000^67 ≤ 5066698146349^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1650499491 5000000000 5066698146349 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (943835279/2500000000 : ℝ)^83 ≤ (7479469937287/25000000000000 : ℝ)^67 := by
    have hnat : (943835279 : ℕ)^83*25000000000000^67 ≤ 7479469937287^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943835279 2500000000 7479469937287 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306289139/2500000000 : ℝ)^83 ≤ (699197335961/1562500000000 : ℝ)^67 := by
    have hnat : (1306289139 : ℕ)^83*1562500000000^67 ≤ 699197335961^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306289139 2500000000 699197335961 1562500000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1650499491/5000000000 : ℝ), (-943835279/2500000000 : ℝ), (-1306289139/2500000000 : ℝ)] ![(5066698146349/20000000000000 : ℝ), (7479469937287/25000000000000 : ℝ), (699197335961/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1650499491/5000000000 : ℝ)|^83 ≤ (5066698146349/20000000000000 : ℝ)^67
        have hw : |(1650499491/5000000000 : ℝ)|=(1650499491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-943835279/2500000000 : ℝ)|^83 ≤ (7479469937287/25000000000000 : ℝ)^67
        have hw : |(-943835279/2500000000 : ℝ)|=(943835279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1306289139/2500000000 : ℝ)|^83 ≤ (699197335961/1562500000000 : ℝ)^67
        have hw : |(-1306289139/2500000000 : ℝ)|=(1306289139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139490121/10000000000 : ℝ)*x 0 + (-4762110123/10000000000 : ℝ)*x 1 + (-105553649/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139490121/10000000000 : ℝ)^83 ≤ (3701045226623/25000000000000 : ℝ)^67 := by
    have hnat : (2139490121 : ℕ)^83*25000000000000^67 ≤ 3701045226623^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139490121 10000000000 3701045226623 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4762110123/10000000000 : ℝ)^83 ≤ (498615791143/1250000000000 : ℝ)^67 := by
    have hnat : (4762110123 : ℕ)^83*1250000000000^67 ≤ 498615791143^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4762110123 10000000000 498615791143 1250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105553649/200000000 : ℝ)^83 ≤ (22653277893351/50000000000000 : ℝ)^67 := by
    have hnat : (105553649 : ℕ)^83*50000000000000^67 ≤ 22653277893351^67*200000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105553649 200000000 22653277893351 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139490121/10000000000 : ℝ), (-4762110123/10000000000 : ℝ), (-105553649/200000000 : ℝ)] ![(3701045226623/25000000000000 : ℝ), (498615791143/1250000000000 : ℝ), (22653277893351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139490121/10000000000 : ℝ)|^83 ≤ (3701045226623/25000000000000 : ℝ)^67
        have hw : |(-2139490121/10000000000 : ℝ)|=(2139490121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4762110123/10000000000 : ℝ)|^83 ≤ (498615791143/1250000000000 : ℝ)^67
        have hw : |(-4762110123/10000000000 : ℝ)|=(4762110123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105553649/200000000 : ℝ)|^83 ≤ (22653277893351/50000000000000 : ℝ)^67
        have hw : |(-105553649/200000000 : ℝ)|=(105553649/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6154003703/10000000000 : ℝ)*x 0 + (1575187543/5000000000 : ℝ)*x 1 + (-2868392613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6154003703/10000000000 : ℝ)^83 ≤ (54803382714897/100000000000000 : ℝ)^67 := by
    have hnat : (6154003703 : ℕ)^83*100000000000000^67 ≤ 54803382714897^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6154003703 10000000000 54803382714897 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1575187543/5000000000 : ℝ)^83 ≤ (23909372495547/100000000000000 : ℝ)^67 := by
    have hnat : (1575187543 : ℕ)^83*100000000000000^67 ≤ 23909372495547^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1575187543 5000000000 23909372495547 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2868392613/10000000000 : ℝ)^83 ≤ (21287244774629/100000000000000 : ℝ)^67 := by
    have hnat : (2868392613 : ℕ)^83*100000000000000^67 ≤ 21287244774629^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2868392613 10000000000 21287244774629 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6154003703/10000000000 : ℝ), (1575187543/5000000000 : ℝ), (-2868392613/10000000000 : ℝ)] ![(54803382714897/100000000000000 : ℝ), (23909372495547/100000000000000 : ℝ), (21287244774629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6154003703/10000000000 : ℝ)|^83 ≤ (54803382714897/100000000000000 : ℝ)^67
        have hw : |(6154003703/10000000000 : ℝ)|=(6154003703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1575187543/5000000000 : ℝ)|^83 ≤ (23909372495547/100000000000000 : ℝ)^67
        have hw : |(1575187543/5000000000 : ℝ)|=(1575187543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2868392613/10000000000 : ℝ)|^83 ≤ (21287244774629/100000000000000 : ℝ)^67
        have hw : |(-2868392613/10000000000 : ℝ)|=(2868392613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1012474539/2500000000 : ℝ)*x 0 + (-4347822147/10000000000 : ℝ)*x 1 + (1979329539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1012474539/2500000000 : ℝ)^83 ≤ (16318093389641/50000000000000 : ℝ)^67 := by
    have hnat : (1012474539 : ℕ)^83*50000000000000^67 ≤ 16318093389641^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012474539 2500000000 16318093389641 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4347822147/10000000000 : ℝ)^83 ≤ (17817998333159/50000000000000 : ℝ)^67 := by
    have hnat : (4347822147 : ℕ)^83*50000000000000^67 ≤ 17817998333159^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347822147 10000000000 17817998333159 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1979329539/5000000000 : ℝ)^83 ≤ (31727816540649/100000000000000 : ℝ)^67 := by
    have hnat : (1979329539 : ℕ)^83*100000000000000^67 ≤ 31727816540649^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979329539 5000000000 31727816540649 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1012474539/2500000000 : ℝ), (-4347822147/10000000000 : ℝ), (1979329539/5000000000 : ℝ)] ![(16318093389641/50000000000000 : ℝ), (17817998333159/50000000000000 : ℝ), (31727816540649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1012474539/2500000000 : ℝ)|^83 ≤ (16318093389641/50000000000000 : ℝ)^67
        have hw : |(1012474539/2500000000 : ℝ)|=(1012474539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4347822147/10000000000 : ℝ)|^83 ≤ (17817998333159/50000000000000 : ℝ)^67
        have hw : |(-4347822147/10000000000 : ℝ)|=(4347822147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1979329539/5000000000 : ℝ)|^83 ≤ (31727816540649/100000000000000 : ℝ)^67
        have hw : |(1979329539/5000000000 : ℝ)|=(1979329539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322068_s1_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3815131763/10000000000 : ℝ)*x 0 + (-809851757/2000000000 : ℝ)*x 1 + (-4487653891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3815131763/10000000000 : ℝ)^83 ≤ (30308994009779/100000000000000 : ℝ)^67 := by
    have hnat : (3815131763 : ℕ)^83*100000000000000^67 ≤ 30308994009779^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3815131763 10000000000 30308994009779 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (809851757/2000000000 : ℝ)^83 ≤ (16314902047633/50000000000000 : ℝ)^67 := by
    have hnat : (809851757 : ℕ)^83*50000000000000^67 ≤ 16314902047633^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809851757 2000000000 16314902047633 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487653891/10000000000 : ℝ)^83 ≤ (9265300467931/25000000000000 : ℝ)^67 := by
    have hnat : (4487653891 : ℕ)^83*25000000000000^67 ≤ 9265300467931^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487653891 10000000000 9265300467931 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3815131763/10000000000 : ℝ), (-809851757/2000000000 : ℝ), (-4487653891/10000000000 : ℝ)] ![(30308994009779/100000000000000 : ℝ), (16314902047633/50000000000000 : ℝ), (9265300467931/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3815131763/10000000000 : ℝ)|^83 ≤ (30308994009779/100000000000000 : ℝ)^67
        have hw : |(3815131763/10000000000 : ℝ)|=(3815131763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-809851757/2000000000 : ℝ)|^83 ≤ (16314902047633/50000000000000 : ℝ)^67
        have hw : |(-809851757/2000000000 : ℝ)|=(809851757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4487653891/10000000000 : ℝ)|^83 ≤ (9265300467931/25000000000000 : ℝ)^67
        have hw : |(-4487653891/10000000000 : ℝ)|=(4487653891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322068 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((3735895591/5000000000 : ℝ)*X 1 0+(2588866117/10000000000 : ℝ)*X 1 1+(-1751934501/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1954772861/5000000000 : ℝ)*X 2 0+(-2226709001/5000000000 : ℝ)*X 2 1+(1995429297/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-586828273/10000000000 : ℝ)*X 0 0+(-135716369/250000000 : ℝ)*X 0 1+(-5724105547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3748298581/5000000000 : ℝ)*X 1 0+(293648829/1000000000 : ℝ)*X 1 1+(-164426767/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((463495741/1000000000 : ℝ)*X 2 0+(-808335189/2500000000 : ℝ)*X 2 1+(4455653507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((852883889/2500000000 : ℝ)*X 0 0+(-1346604547/5000000000 : ℝ)*X 0 1+(-6074061333/10000000000 : ℝ)*X 0 2+(852883889/2500000000 : ℝ)*X 1 0+(-1346604547/5000000000 : ℝ)*X 1 1+(-6074061333/10000000000 : ℝ)*X 1 2+(852883889/2500000000 : ℝ)*X 2 0+(-1346604547/5000000000 : ℝ)*X 2 1+(-6074061333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-168903601/5000000000 : ℝ)*X 0 0+(-1163674729/2500000000 : ℝ)*X 0 1+(-3297890443/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4069840009/5000000000 : ℝ)*X 1 0+(2439274081/10000000000 : ℝ)*X 1 1+(-180798247/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4180544277/10000000000 : ℝ)*X 2 0+(-1119596317/2500000000 : ℝ)*X 2 1+(922649379/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2685195281/10000000000 : ℝ)*X 0 0+(-350076169/1250000000 : ℝ)*X 0 1+(-3297890443/5000000000 : ℝ)*X 0 2+(2685195281/10000000000 : ℝ)*X 1 0+(-350076169/1250000000 : ℝ)*X 1 1+(-3297890443/5000000000 : ℝ)*X 1 2+(2685195281/10000000000 : ℝ)*X 2 0+(-350076169/1250000000 : ℝ)*X 2 1+(-3297890443/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-309860141/10000000000 : ℝ)*X 0 0+(-730863487/1250000000 : ℝ)*X 0 1+(-5456183443/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2129150507/2500000000 : ℝ)*X 1 0+(117423239/625000000 : ℝ)*X 1 1+(-952818571/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((439501257/1250000000 : ℝ)*X 2 0+(-4450926369/10000000000 : ℝ)*X 2 1+(2187929401/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1650499491/5000000000 : ℝ)*X 0 0+(-943835279/2500000000 : ℝ)*X 0 1+(-1306289139/2500000000 : ℝ)*X 0 2+(1650499491/5000000000 : ℝ)*X 1 0+(-943835279/2500000000 : ℝ)*X 1 1+(-1306289139/2500000000 : ℝ)*X 1 2+(1650499491/5000000000 : ℝ)*X 2 0+(-943835279/2500000000 : ℝ)*X 2 1+(-1306289139/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((5647/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5647/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20518266385753292844651/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (137791877561/100000000000 : ℝ)*(base1) + (945127341271/500000000000 : ℝ)*(base39) + (93848263589/200000000000 : ℝ)*(base49) + (22663996473/1000000000000 : ℝ)*(base60) + (2659245445049/1000000000000 : ℝ)*(major_s0_0) + (2659245445049/1000000000000 : ℝ)*(major_s0_1) + (2659245445049/1000000000000 : ℝ)*(major_s0_2) + (94951797/1000000000000 : ℝ)*(sp_s0_1) + (5318411899617/1000000000000 : ℝ)*(sp_s0_7) + (78809433823/20000000000 : ℝ)*(sp_s0_8) + (39404715527/10000000000 : ℝ)*(sp_s0_9) + (810873/20000000000 : ℝ)*(sp_s0_14) + (3297529/100000000000 : ℝ)*(sp_s0_21) + (95090247/1000000000000 : ℝ)*(sp_s0_23) + (137791877561/100000000000 : ℝ)*(f.failure) + (3940566642947/1000000000000 : ℝ)*(f.sum) + (1983171302045017/10000000000000000000000000000 : ℝ)*base63 + (1343358754467577/2000000000000000000000000000 : ℝ)*base65 + (618562452573217/2500000000000000000000000000 : ℝ)*base67 + (769313176176783/2500000000000000000000000000 : ℝ)*base69 + (3642220922045017/10000000000000000000000000000 : ℝ)*base71 + (512870216932423/2000000000000000000000000000 : ℝ)*base73 + (536407443932423/2000000000000000000000000000 : ℝ)*base74 + (91571850426783/2500000000000000000000000000 : ℝ)*base77 + (2074960334954983/10000000000000000000000000000 : ℝ)*base79 + (739/1000000000000000 : ℝ)*base87 + (739/1000000000000000 : ℝ)*base89 + (739/1000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-18401/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-18401/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6096019371995900355411/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (362919863163/1000000000000 : ℝ)*(base1) + (108241241821/40000000000 : ℝ)*(base39) + (94135631669/100000000000 : ℝ)*(base49) + (263136488767/250000000000 : ℝ)*(base60) + (717012739311/125000000000 : ℝ)*(major_s0_0) + (717012739311/125000000000 : ℝ)*(major_s0_1) + (717012739311/125000000000 : ℝ)*(major_s0_2) + (66846257/1000000000000 : ℝ)*(sp_s0_8) + (4582453/100000000000 : ℝ)*(sp_s0_9) + (50027829/1000000000000 : ℝ)*(sp_s0_13) + (69241350849/7812500000 : ℝ)*(sp_s0_14) + (2124976549813/250000000000 : ℝ)*(sp_s0_15) + (424996361049/50000000000 : ℝ)*(sp_s0_16) + (2609257641257/1000000000000 : ℝ)*(sp_s0_20) + (2972227532249/1000000000000 : ℝ)*(f.failure) + (8499973045509/1000000000000 : ℝ)*(f.sum) + (167069993589863/1250000000000000000000000000 : ℝ)*base63 + (200045326899297/250000000000000000000000000 : ℝ)*base64 + (212676006646587/312500000000000000000000000 : ℝ)*base66 + (135548751646587/312500000000000000000000000 : ℝ)*base69 + (73488150785137/1250000000000000000000000000 : ℝ)*base70 + (127129501275703/250000000000000000000000000 : ℝ)*base72 + (81869502025703/250000000000000000000000000 : ℝ)*base75 + (2734216447163/312500000000000000000000000 : ℝ)*base76 + (552595372089863/1250000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (6549/10000000000000000 : ℝ)*base86 + (6549/10000000000000000 : ℝ)*base88 + (6549/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5121/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5121/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20372916377788768698843/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13749191/1000000000000 : ℝ)*(base10) + (418156371557/250000000000 : ℝ)*(base39) + (2482683/1000000000000 : ℝ)*(base40) + (417297278711/500000000000 : ℝ)*(base49) + (125804089447/1000000000000 : ℝ)*(base60) + (1952855535457/500000000000 : ℝ)*(major_s0_0) + (1952855535457/500000000000 : ℝ)*(major_s0_1) + (1952855535457/500000000000 : ℝ)*(major_s0_2) + (96593941/500000000000 : ℝ)*(sp_s0_2) + (18144557/1000000000000 : ℝ)*(sp_s0_15) + (1157522721519/200000000000 : ℝ)*(sp_s0_21) + (578760921223/100000000000 : ℝ)*(sp_s0_22) + (1157486833781/200000000000 : ℝ)*(sp_s0_23) + (2023789352253/1000000000000 : ℝ)*(sp_s0_27) + (2023789352253/1000000000000 : ℝ)*(f.failure) + (2893813678393/500000000000 : ℝ)*(f.sum) + (166857325058719/5000000000000000000000000000 : ℝ)*base62 + (1255608727164639/1000000000000000000000000000 : ℝ)*base64 + (978030298441119/1250000000000000000000000000 : ℝ)*base66 + (27819783933881/1250000000000000000000000000 : ℝ)*base68 + (4025039694058719/5000000000000000000000000000 : ℝ)*base70 + (223689363264639/1000000000000000000000000000 : ℝ)*base73 + (424445233035361/1000000000000000000000000000 : ℝ)*base75 + (873980662808881/1250000000000000000000000000 : ℝ)*base76 + (1883845024558719/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (9353/10000000000000000 : ℝ)*base86 + (9353/10000000000000000 : ℝ)*base88 + (9353/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (5647/50000 : ℝ) ^ (41/8 : ℝ) ≤ (279817508685127/20000000000000000000 : ℝ) := by
    have hpowers : (5647/50000 : ℝ)^41 ≤ (279817508685127/20000000000000000000 : ℝ)^8 := by
      have hnat : (5647 : ℕ)^41*20000000000000000000^8 ≤ 279817508685127^8*50000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5647 50000 279817508685127 20000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5647/50000 : ℝ)) (X := (279817508685127/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (20000279817508685127/20000000000000000000 : ℝ) ≤ (5000013649557717/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (20000279817508685127/20000000000000000000 : ℝ)^8 ≤ (5000013649557717/5000000000000000 : ℝ)^41 := by
      have hnat : (20000279817508685127 : ℕ)^8*5000000000000000^41 ≤ 5000013649557717^41*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20000279817508685127 20000000000000000000 5000013649557717 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000013649557717/5000000000000000 : ℝ)) (X := (20000279817508685127/20000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (10000279817508685127/10000000000000000000 : ℝ) ≤ (500002729896173/500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (10000279817508685127/10000000000000000000 : ℝ)^8 ≤ (500002729896173/500000000000000 : ℝ)^41 := by
      have hnat : (10000279817508685127 : ℕ)^8*500000000000000^41 ≤ 500002729896173^41*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000279817508685127 10000000000000000000 500002729896173 500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500002729896173/500000000000000 : ℝ)) (X := (10000279817508685127/10000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(13649557717/564700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(13649404013/564700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (5647/50000 : ℝ)) (alpha := (13649557717/564700000000000 : ℝ)) (beta := (13649404013/564700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5647/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(13649557717/564700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(13649404013/564700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (18401/50000 : ℝ) ^ (41/8 : ℝ) ≤ (595787013526774889/100000000000000000000 : ℝ) := by
    have hpowers : (18401/50000 : ℝ)^41 ≤ (595787013526774889/100000000000000000000 : ℝ)^8 := by
      have hnat : (18401 : ℕ)^41*100000000000000000000^8 ≤ 595787013526774889^8*50000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18401 50000 595787013526774889 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18401/50000 : ℝ)) (X := (595787013526774889/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100595787013526774889/100000000000000000000 : ℝ) ≤ (10011597338659661/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (100595787013526774889/100000000000000000000 : ℝ)^8 ≤ (10011597338659661/10000000000000000 : ℝ)^41 := by
      have hnat : (100595787013526774889 : ℕ)^8*10000000000000000^41 ≤ 10011597338659661^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100595787013526774889 100000000000000000000 10011597338659661 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011597338659661/10000000000000000 : ℝ)) (X := (100595787013526774889/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50595787013526774889/50000000000000000000 : ℝ) ≤ (10023139524401399/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50595787013526774889/50000000000000000000 : ℝ)^8 ≤ (10023139524401399/10000000000000000 : ℝ)^41 := by
      have hnat : (50595787013526774889 : ℕ)^8*10000000000000000^41 ≤ 10023139524401399^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50595787013526774889 50000000000000000000 10023139524401399 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10023139524401399/10000000000000000 : ℝ)) (X := (50595787013526774889/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(11597338659661/3680200000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(5771092870869/1840100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (18401/50000 : ℝ)) (alpha := (11597338659661/3680200000000000 : ℝ)) (beta := (5771092870869/1840100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (18401/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(11597338659661/3680200000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(5771092870869/1840100000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (5121/20000 : ℝ) ^ (41/8 : ℝ) ≤ (23206225445595867/25000000000000000000 : ℝ) := by
    have hpowers : (5121/20000 : ℝ)^41 ≤ (23206225445595867/25000000000000000000 : ℝ)^8 := by
      have hnat : (5121 : ℕ)^41*25000000000000000000^8 ≤ 23206225445595867^8*20000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5121 20000 23206225445595867 25000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5121/20000 : ℝ)) (X := (23206225445595867/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25023206225445595867/25000000000000000000 : ℝ) ≤ (5000905270684173/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (25023206225445595867/25000000000000000000 : ℝ)^8 ≤ (5000905270684173/5000000000000000 : ℝ)^41 := by
      have hnat : (25023206225445595867 : ℕ)^8*5000000000000000^41 ≤ 5000905270684173^41*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25023206225445595867 25000000000000000000 5000905270684173 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000905270684173/5000000000000000 : ℝ)) (X := (25023206225445595867/25000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12523206225445595867/12500000000000000000 : ℝ) ≤ (5001809865895177/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (12523206225445595867/12500000000000000000 : ℝ)^8 ≤ (5001809865895177/5000000000000000 : ℝ)^41 := by
      have hnat : (12523206225445595867 : ℕ)^8*5000000000000000^41 ≤ 5001809865895177^41*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12523206225445595867 12500000000000000000 5001809865895177 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001809865895177/5000000000000000 : ℝ)) (X := (12523206225445595867/12500000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(905270684173/1280250000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(226148802751/320062500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (5121/20000 : ℝ)) (alpha := (905270684173/1280250000000000 : ℝ)) (beta := (226148802751/320062500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (5121/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(905270684173/1280250000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(226148802751/320062500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2139490121/10000000000 : ℝ)*X 0 0+(-4762110123/10000000000 : ℝ)*X 0 1+(-105553649/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((6154003703/10000000000 : ℝ)*X 1 0+(1575187543/5000000000 : ℝ)*X 1 1+(-2868392613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1012474539/2500000000 : ℝ)*X 2 0+(-4347822147/10000000000 : ℝ)*X 2 1+(1979329539/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3815131763/10000000000 : ℝ)*X 0 0+(-809851757/2000000000 : ℝ)*X 0 1+(-4487653891/10000000000 : ℝ)*X 0 2+(3815131763/10000000000 : ℝ)*X 1 0+(-809851757/2000000000 : ℝ)*X 1 1+(-4487653891/10000000000 : ℝ)*X 1 2+(3815131763/10000000000 : ℝ)*X 2 0+(-809851757/2000000000 : ℝ)*X 2 1+(-4487653891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322068_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-42897/5000 : ℝ) < ((-19299/10000 : ℝ)*P 0+(-19299/10000 : ℝ)*P 1+(-19299/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-42897/5000 : ℝ) < (-135816390512008490462399598543/16065715000000000000000000000 : ℝ) := by norm_num
    linear_combination (31/25000000000 : ℝ)*(base8) + (69/1000000000000 : ℝ)*(base12) + (7597917907/7812500000 : ℝ)*(base39) + (299739735871/1000000000000 : ℝ)*(base40) + (401099379861/1000000000000 : ℝ)*(base49) + (184406376289/1000000000000 : ℝ)*(base60) + (19299/10000 : ℝ)*(major_s1_0) + (19299/10000 : ℝ)*(major_s1_1) + (19299/10000 : ℝ)*(major_s1_2) + (704483586713/250000000000 : ℝ)*(sp_s1_0) + (704483586877/250000000000 : ℝ)*(sp_s1_1) + (2817934348889/1000000000000 : ℝ)*(sp_s1_2) + (1000000000653/1000000000000 : ℝ)*(sp_s1_6) + (2817934348161/1000000000000 : ℝ)*(f.sum) + (11853583855511471/314105070000000000000000000000 : ℝ)*base63 + (4533578567507/17070000000000000000000000 : ℝ)*base65 + (41766199441423/184010000000000000000000000 : ℝ)*base67 + (1421655239359/17070000000000000000000000 : ℝ)*base69 + (59232181874756393/96394290000000000000000000000 : ℝ)*base71 + (10820367315131/56470000000000000000000000 : ℝ)*base72 + (133921015547373123/184010000000000000000000000 : ℝ)*base74 + (3843987710417/7058750000000000000000000 : ℝ)*base77 + (153653298074152993/1039104470000000000000000000000 : ℝ)*base78 + (653/1000000000000 : ℝ)*base82 + (91/125000000000 : ℝ)*base85 + (653/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c322069_s0_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-412893821/2000000000 : ℝ)*x 0 + (-6959975037/10000000000 : ℝ)*x 1 + (2946394517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412893821/2000000000 : ℝ)^83 ≤ (14163824612709/100000000000000 : ℝ)^67 := by
    have hnat : (412893821 : ℕ)^83*100000000000000^67 ≤ 14163824612709^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412893821 2000000000 14163824612709 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6959975037/10000000000 : ℝ)^83 ≤ (398934388127/625000000000 : ℝ)^67 := by
    have hnat : (6959975037 : ℕ)^83*625000000000^67 ≤ 398934388127^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6959975037 10000000000 398934388127 625000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2946394517/10000000000 : ℝ)^83 ≤ (4401334654209/20000000000000 : ℝ)^67 := by
    have hnat : (2946394517 : ℕ)^83*20000000000000^67 ≤ 4401334654209^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2946394517 10000000000 4401334654209 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412893821/2000000000 : ℝ), (-6959975037/10000000000 : ℝ), (2946394517/10000000000 : ℝ)] ![(14163824612709/100000000000000 : ℝ), (398934388127/625000000000 : ℝ), (4401334654209/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412893821/2000000000 : ℝ)|^83 ≤ (14163824612709/100000000000000 : ℝ)^67
        have hw : |(-412893821/2000000000 : ℝ)|=(412893821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6959975037/10000000000 : ℝ)|^83 ≤ (398934388127/625000000000 : ℝ)^67
        have hw : |(-6959975037/10000000000 : ℝ)|=(6959975037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2946394517/10000000000 : ℝ)|^83 ≤ (4401334654209/20000000000000 : ℝ)^67
        have hw : |(2946394517/10000000000 : ℝ)|=(2946394517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322069_s0_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2876200701/5000000000 : ℝ)*x 0 + (2536543027/10000000000 : ℝ)*x 1 + (244796361/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2876200701/5000000000 : ℝ)^83 ≤ (50408031120893/100000000000000 : ℝ)^67 := by
    have hnat : (2876200701 : ℕ)^83*100000000000000^67 ≤ 50408031120893^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2876200701 5000000000 50408031120893 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2536543027/10000000000 : ℝ)^83 ≤ (1142488242943/6250000000000 : ℝ)^67 := by
    have hnat : (2536543027 : ℕ)^83*6250000000000^67 ≤ 1142488242943^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536543027 10000000000 1142488242943 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (244796361/625000000 : ℝ)^83 ≤ (15656078490923/50000000000000 : ℝ)^67 := by
    have hnat : (244796361 : ℕ)^83*50000000000000^67 ≤ 15656078490923^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244796361 625000000 15656078490923 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2876200701/5000000000 : ℝ), (2536543027/10000000000 : ℝ), (244796361/625000000 : ℝ)] ![(50408031120893/100000000000000 : ℝ), (1142488242943/6250000000000 : ℝ), (15656078490923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2876200701/5000000000 : ℝ)|^83 ≤ (50408031120893/100000000000000 : ℝ)^67
        have hw : |(2876200701/5000000000 : ℝ)|=(2876200701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2536543027/10000000000 : ℝ)|^83 ≤ (1142488242943/6250000000000 : ℝ)^67
        have hw : |(2536543027/10000000000 : ℝ)|=(2536543027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(244796361/625000000 : ℝ)|^83 ≤ (15656078490923/50000000000000 : ℝ)^67
        have hw : |(244796361/625000000 : ℝ)|=(244796361/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322069_s0_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1872585219/5000000000 : ℝ)*x 0 + (-3197545343/10000000000 : ℝ)*x 1 + (-1336269651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1872585219/5000000000 : ℝ)^83 ≤ (14810989002939/50000000000000 : ℝ)^67 := by
    have hnat : (1872585219 : ℕ)^83*50000000000000^67 ≤ 14810989002939^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872585219 5000000000 14810989002939 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3197545343/10000000000 : ℝ)^83 ≤ (12176822923053/50000000000000 : ℝ)^67 := by
    have hnat : (3197545343 : ℕ)^83*50000000000000^67 ≤ 12176822923053^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3197545343 10000000000 12176822923053 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1336269651/2500000000 : ℝ)^83 ≤ (9204875226797/20000000000000 : ℝ)^67 := by
    have hnat : (1336269651 : ℕ)^83*20000000000000^67 ≤ 9204875226797^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336269651 2500000000 9204875226797 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1872585219/5000000000 : ℝ), (-3197545343/10000000000 : ℝ), (-1336269651/2500000000 : ℝ)] ![(14810989002939/50000000000000 : ℝ), (12176822923053/50000000000000 : ℝ), (9204875226797/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1872585219/5000000000 : ℝ)|^83 ≤ (14810989002939/50000000000000 : ℝ)^67
        have hw : |(1872585219/5000000000 : ℝ)|=(1872585219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3197545343/10000000000 : ℝ)|^83 ≤ (12176822923053/50000000000000 : ℝ)^67
        have hw : |(-3197545343/10000000000 : ℝ)|=(3197545343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1336269651/2500000000 : ℝ)|^83 ≤ (9204875226797/20000000000000 : ℝ)^67
        have hw : |(-1336269651/2500000000 : ℝ)|=(1336269651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322069_s0_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2876200701/5000000000 : ℝ)*x 0 + (-2536543027/10000000000 : ℝ)*x 1 + (244796361/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2876200701/5000000000 : ℝ)^83 ≤ (50408031120893/100000000000000 : ℝ)^67 := by
    have hnat : (2876200701 : ℕ)^83*100000000000000^67 ≤ 50408031120893^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2876200701 5000000000 50408031120893 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2536543027/10000000000 : ℝ)^83 ≤ (1142488242943/6250000000000 : ℝ)^67 := by
    have hnat : (2536543027 : ℕ)^83*6250000000000^67 ≤ 1142488242943^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536543027 10000000000 1142488242943 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (244796361/625000000 : ℝ)^83 ≤ (15656078490923/50000000000000 : ℝ)^67 := by
    have hnat : (244796361 : ℕ)^83*50000000000000^67 ≤ 15656078490923^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244796361 625000000 15656078490923 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2876200701/5000000000 : ℝ), (-2536543027/10000000000 : ℝ), (244796361/625000000 : ℝ)] ![(50408031120893/100000000000000 : ℝ), (1142488242943/6250000000000 : ℝ), (15656078490923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2876200701/5000000000 : ℝ)|^83 ≤ (50408031120893/100000000000000 : ℝ)^67
        have hw : |(2876200701/5000000000 : ℝ)|=(2876200701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2536543027/10000000000 : ℝ)|^83 ≤ (1142488242943/6250000000000 : ℝ)^67
        have hw : |(-2536543027/10000000000 : ℝ)|=(2536543027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(244796361/625000000 : ℝ)|^83 ≤ (15656078490923/50000000000000 : ℝ)^67
        have hw : |(244796361/625000000 : ℝ)|=(244796361/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322069 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-412893821/2000000000 : ℝ)*X 0 0+(-6959975037/10000000000 : ℝ)*X 0 1+(2946394517/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322069_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2876200701/5000000000 : ℝ)*X 1 0+(2536543027/10000000000 : ℝ)*X 1 1+(244796361/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322069_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1872585219/5000000000 : ℝ)*X 2 0+(-3197545343/10000000000 : ℝ)*X 2 1+(-1336269651/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322069_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((2876200701/5000000000 : ℝ)*X 0 0+(-2536543027/10000000000 : ℝ)*X 0 1+(244796361/625000000 : ℝ)*X 0 2+(2876200701/5000000000 : ℝ)*X 1 0+(-2536543027/10000000000 : ℝ)*X 1 1+(244796361/625000000 : ℝ)*X 1 2+(2876200701/5000000000 : ℝ)*X 2 0+(-2536543027/10000000000 : ℝ)*X 2 1+(244796361/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322069_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-42897/5000 : ℝ) < ((-19299/10000 : ℝ)*P 0+(-19299/10000 : ℝ)*P 1+(-19299/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-42897/5000 : ℝ) < (-42612196783023202565880143919/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93872822473/200000000000 : ℝ)*(base3) + (274979/1000000000000 : ℝ)*(base13) + (46531/125000000000 : ℝ)*(base21) + (209467/500000000000 : ℝ)*(base24) + (77019/1000000000000 : ℝ)*(base33) + (12148988543/20000000000 : ℝ)*(base40) + (492192530031/500000000000 : ℝ)*(base49) + (18923684429/31250000000 : ℝ)*(base50) + (1929899922981/1000000000000 : ℝ)*(major_s0_0) + (19299/10000 : ℝ)*(major_s0_1) + (19299/10000 : ℝ)*(major_s0_2) + (2840812843887/1000000000000 : ℝ)*(sp_s0_0) + (827544288553/250000000000 : ℝ)*(sp_s0_1) + (568162450133/200000000000 : ℝ)*(sp_s0_2) + (106127177527/200000000000 : ℝ)*(sp_s0_6) + (1420406559433/500000000000 : ℝ)*(f.sum) + (778134713/2000000000000000000000 : ℝ)*base63 + (72716683/1250000000000000000000 : ℝ)*base65 + (190720539/10000000000000000000000 : ℝ)*base66 + (1471571853/5000000000000000000000 : ℝ)*base69 + (202796006226227/2500000000000000000000000000 : ℝ)*base71 + (242744628928613/2000000000000000000000000000 : ℝ)*base72 + (241915199/250000000000000000000 : ℝ)*base75 + (403488335976227/2500000000000000000000000000 : ℝ)*base77 + (242660834528613/2000000000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p022_b038 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=68 ∨ c=69 := by omega
  rcases hc with rfl|rfl
  · exact collision_c322068 p hpa (by linarith only [hpb]) X hX
  · exact collision_c322069 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p022_b038 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

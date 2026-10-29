-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p021_b030
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:43:45.619977+00:00
-- url     : https://prove2.me/submissions/5680450e-5d35-40c7-b34b-617a06162855

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
theorem collision_support_c321051_s0_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-659209093/2000000000 : ℝ)*x 0 + (659209073/2000000000 : ℝ)*x 1 + (5661877229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659209093/2000000000 : ℝ)^83 ≤ (12643202531633/50000000000000 : ℝ)^67 := by
    have hnat : (659209093 : ℕ)^83*50000000000000^67 ≤ 12643202531633^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659209093 2000000000 12643202531633 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659209073/2000000000 : ℝ)^83 ≤ (12643202056443/50000000000000 : ℝ)^67 := by
    have hnat : (659209073 : ℕ)^83*50000000000000^67 ≤ 12643202056443^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659209073 2000000000 12643202056443 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5661877229/10000000000 : ℝ)^83 ≤ (24713595406007/50000000000000 : ℝ)^67 := by
    have hnat : (5661877229 : ℕ)^83*50000000000000^67 ≤ 24713595406007^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5661877229 10000000000 24713595406007 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-659209093/2000000000 : ℝ), (659209073/2000000000 : ℝ), (5661877229/10000000000 : ℝ)] ![(12643202531633/50000000000000 : ℝ), (12643202056443/50000000000000 : ℝ), (24713595406007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-659209093/2000000000 : ℝ)|^83 ≤ (12643202531633/50000000000000 : ℝ)^67
        have hw : |(-659209093/2000000000 : ℝ)|=(659209093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(659209073/2000000000 : ℝ)|^83 ≤ (12643202056443/50000000000000 : ℝ)^67
        have hw : |(659209073/2000000000 : ℝ)|=(659209073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5661877229/10000000000 : ℝ)|^83 ≤ (24713595406007/50000000000000 : ℝ)^67
        have hw : |(5661877229/10000000000 : ℝ)|=(5661877229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s0_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2367828041/10000000000 : ℝ)*x 0 + (-2367827959/10000000000 : ℝ)*x 1 + (7187852809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2367828041/10000000000 : ℝ)^83 ≤ (16785769000737/100000000000000 : ℝ)^67 := by
    have hnat : (2367828041 : ℕ)^83*100000000000000^67 ≤ 16785769000737^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2367828041 10000000000 16785769000737 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2367827959/10000000000 : ℝ)^83 ≤ (16785768280611/100000000000000 : ℝ)^67 := by
    have hnat : (2367827959 : ℕ)^83*100000000000000^67 ≤ 16785768280611^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2367827959 10000000000 16785768280611 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7187852809/10000000000 : ℝ)^83 ≤ (33214231352103/50000000000000 : ℝ)^67 := by
    have hnat : (7187852809 : ℕ)^83*50000000000000^67 ≤ 33214231352103^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7187852809 10000000000 33214231352103 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2367828041/10000000000 : ℝ), (-2367827959/10000000000 : ℝ), (7187852809/10000000000 : ℝ)] ![(16785769000737/100000000000000 : ℝ), (16785768280611/100000000000000 : ℝ), (33214231352103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2367828041/10000000000 : ℝ)|^83 ≤ (16785769000737/100000000000000 : ℝ)^67
        have hw : |(2367828041/10000000000 : ℝ)|=(2367828041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2367827959/10000000000 : ℝ)|^83 ≤ (16785768280611/100000000000000 : ℝ)^67
        have hw : |(-2367827959/10000000000 : ℝ)|=(2367827959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7187852809/10000000000 : ℝ)|^83 ≤ (33214231352103/50000000000000 : ℝ)^67
        have hw : |(7187852809/10000000000 : ℝ)|=(7187852809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s0_7 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1345417869/5000000000 : ℝ)*x 0 + (26020747/156250000 : ℝ)*x 1 + (3726568223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345417869/5000000000 : ℝ)^83 ≤ (19667123443021/100000000000000 : ℝ)^67 := by
    have hnat : (1345417869 : ℕ)^83*100000000000000^67 ≤ 19667123443021^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345417869 5000000000 19667123443021 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26020747/156250000 : ℝ)^83 ≤ (2713496285779/25000000000000 : ℝ)^67 := by
    have hnat : (26020747 : ℕ)^83*25000000000000^67 ≤ 2713496285779^67*156250000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26020747 156250000 2713496285779 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3726568223/5000000000 : ℝ)^83 ≤ (2779155655987/4000000000000 : ℝ)^67 := by
    have hnat : (3726568223 : ℕ)^83*4000000000000^67 ≤ 2779155655987^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3726568223 5000000000 2779155655987 4000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1345417869/5000000000 : ℝ), (26020747/156250000 : ℝ), (3726568223/5000000000 : ℝ)] ![(19667123443021/100000000000000 : ℝ), (2713496285779/25000000000000 : ℝ), (2779155655987/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1345417869/5000000000 : ℝ)|^83 ≤ (19667123443021/100000000000000 : ℝ)^67
        have hw : |(-1345417869/5000000000 : ℝ)|=(1345417869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26020747/156250000 : ℝ)|^83 ≤ (2713496285779/25000000000000 : ℝ)^67
        have hw : |(26020747/156250000 : ℝ)|=(26020747/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3726568223/5000000000 : ℝ)|^83 ≤ (2779155655987/4000000000000 : ℝ)^67
        have hw : |(3726568223/5000000000 : ℝ)|=(3726568223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s0_8 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (624073461/5000000000 : ℝ)*x 0 + (-691552861/10000000000 : ℝ)*x 1 + (4540873689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (624073461/5000000000 : ℝ)^83 ≤ (1518722971291/20000000000000 : ℝ)^67 := by
    have hnat : (624073461 : ℕ)^83*20000000000000^67 ≤ 1518722971291^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624073461 5000000000 1518722971291 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (691552861/10000000000 : ℝ)^83 ≤ (182700090129/5000000000000 : ℝ)^67 := by
    have hnat : (691552861 : ℕ)^83*5000000000000^67 ≤ 182700090129^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691552861 10000000000 182700090129 5000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4540873689/5000000000 : ℝ)^83 ≤ (44376191664547/50000000000000 : ℝ)^67 := by
    have hnat : (4540873689 : ℕ)^83*50000000000000^67 ≤ 44376191664547^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540873689 5000000000 44376191664547 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(624073461/5000000000 : ℝ), (-691552861/10000000000 : ℝ), (4540873689/5000000000 : ℝ)] ![(1518722971291/20000000000000 : ℝ), (182700090129/5000000000000 : ℝ), (44376191664547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(624073461/5000000000 : ℝ)|^83 ≤ (1518722971291/20000000000000 : ℝ)^67
        have hw : |(624073461/5000000000 : ℝ)|=(624073461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-691552861/10000000000 : ℝ)|^83 ≤ (182700090129/5000000000000 : ℝ)^67
        have hw : |(-691552861/10000000000 : ℝ)|=(691552861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4540873689/5000000000 : ℝ)|^83 ≤ (44376191664547/50000000000000 : ℝ)^67
        have hw : |(4540873689/5000000000 : ℝ)|=(4540873689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s0_9 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1004136703/2500000000 : ℝ)*x 0 + (7236317867/10000000000 : ℝ)*x 1 + (-184834401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1004136703/2500000000 : ℝ)^83 ≤ (6460714055627/20000000000000 : ℝ)^67 := by
    have hnat : (1004136703 : ℕ)^83*20000000000000^67 ≤ 6460714055627^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004136703 2500000000 6460714055627 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7236317867/10000000000 : ℝ)^83 ≤ (66983773303739/100000000000000 : ℝ)^67 := by
    have hnat : (7236317867 : ℕ)^83*100000000000000^67 ≤ 66983773303739^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7236317867 10000000000 66983773303739 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184834401/10000000000 : ℝ)^83 ≤ (712656401421/100000000000000 : ℝ)^67 := by
    have hnat : (184834401 : ℕ)^83*100000000000000^67 ≤ 712656401421^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184834401 10000000000 712656401421 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1004136703/2500000000 : ℝ), (7236317867/10000000000 : ℝ), (-184834401/10000000000 : ℝ)] ![(6460714055627/20000000000000 : ℝ), (66983773303739/100000000000000 : ℝ), (712656401421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1004136703/2500000000 : ℝ)|^83 ≤ (6460714055627/20000000000000 : ℝ)^67
        have hw : |(1004136703/2500000000 : ℝ)|=(1004136703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7236317867/10000000000 : ℝ)|^83 ≤ (66983773303739/100000000000000 : ℝ)^67
        have hw : |(7236317867/10000000000 : ℝ)|=(7236317867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-184834401/10000000000 : ℝ)|^83 ≤ (712656401421/100000000000000 : ℝ)^67
        have hw : |(-184834401/10000000000 : ℝ)|=(184834401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s0_13 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2726723101/10000000000 : ℝ)*x 0 + (4144085683/5000000000 : ℝ)*x 1 + (194645969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2726723101/10000000000 : ℝ)^83 ≤ (19992575648513/100000000000000 : ℝ)^67 := by
    have hnat : (2726723101 : ℕ)^83*100000000000000^67 ≤ 19992575648513^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726723101 10000000000 19992575648513 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4144085683/5000000000 : ℝ)^83 ≤ (79247610836939/100000000000000 : ℝ)^67 := by
    have hnat : (4144085683 : ℕ)^83*100000000000000^67 ≤ 79247610836939^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144085683 5000000000 79247610836939 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194645969/10000000000 : ℝ)^83 ≤ (759813499989/100000000000000 : ℝ)^67 := by
    have hnat : (194645969 : ℕ)^83*100000000000000^67 ≤ 759813499989^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194645969 10000000000 759813499989 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2726723101/10000000000 : ℝ), (4144085683/5000000000 : ℝ), (194645969/10000000000 : ℝ)] ![(19992575648513/100000000000000 : ℝ), (79247610836939/100000000000000 : ℝ), (759813499989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2726723101/10000000000 : ℝ)|^83 ≤ (19992575648513/100000000000000 : ℝ)^67
        have hw : |(2726723101/10000000000 : ℝ)|=(2726723101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4144085683/5000000000 : ℝ)|^83 ≤ (79247610836939/100000000000000 : ℝ)^67
        have hw : |(4144085683/5000000000 : ℝ)|=(4144085683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(194645969/10000000000 : ℝ)|^83 ≤ (759813499989/100000000000000 : ℝ)^67
        have hw : |(194645969/10000000000 : ℝ)|=(194645969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s0_14 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1797529597/10000000000 : ℝ)*x 0 + (689131669/2500000000 : ℝ)*x 1 + (7307853803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1797529597/10000000000 : ℝ)^83 ≤ (5965656528149/50000000000000 : ℝ)^67 := by
    have hnat : (1797529597 : ℕ)^83*50000000000000^67 ≤ 5965656528149^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797529597 10000000000 5965656528149 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (689131669/2500000000 : ℝ)^83 ≤ (5065908723641/25000000000000 : ℝ)^67 := by
    have hnat : (689131669 : ℕ)^83*25000000000000^67 ≤ 5065908723641^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689131669 2500000000 5065908723641 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7307853803/10000000000 : ℝ)^83 ≤ (67805052038331/100000000000000 : ℝ)^67 := by
    have hnat : (7307853803 : ℕ)^83*100000000000000^67 ≤ 67805052038331^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7307853803 10000000000 67805052038331 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1797529597/10000000000 : ℝ), (689131669/2500000000 : ℝ), (7307853803/10000000000 : ℝ)] ![(5965656528149/50000000000000 : ℝ), (5065908723641/25000000000000 : ℝ), (67805052038331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1797529597/10000000000 : ℝ)|^83 ≤ (5965656528149/50000000000000 : ℝ)^67
        have hw : |(-1797529597/10000000000 : ℝ)|=(1797529597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(689131669/2500000000 : ℝ)|^83 ≤ (5065908723641/25000000000000 : ℝ)^67
        have hw : |(689131669/2500000000 : ℝ)|=(689131669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7307853803/10000000000 : ℝ)|^83 ≤ (67805052038331/100000000000000 : ℝ)^67
        have hw : |(7307853803/10000000000 : ℝ)|=(7307853803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s0_15 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (897833503/10000000000 : ℝ)*x 0 + (-690354133/5000000000 : ℝ)*x 1 + (8882441399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897833503/10000000000 : ℝ)^83 ≤ (2524542700161/50000000000000 : ℝ)^67 := by
    have hnat : (897833503 : ℕ)^83*50000000000000^67 ≤ 2524542700161^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897833503 10000000000 2524542700161 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (690354133/5000000000 : ℝ)^83 ≤ (430252235159/5000000000000 : ℝ)^67 := by
    have hnat : (690354133 : ℕ)^83*5000000000000^67 ≤ 430252235159^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690354133 5000000000 430252235159 5000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8882441399/10000000000 : ℝ)^83 ≤ (4317293493923/5000000000000 : ℝ)^67 := by
    have hnat : (8882441399 : ℕ)^83*5000000000000^67 ≤ 4317293493923^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8882441399 10000000000 4317293493923 5000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(897833503/10000000000 : ℝ), (-690354133/5000000000 : ℝ), (8882441399/10000000000 : ℝ)] ![(2524542700161/50000000000000 : ℝ), (430252235159/5000000000000 : ℝ), (4317293493923/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(897833503/10000000000 : ℝ)|^83 ≤ (2524542700161/50000000000000 : ℝ)^67
        have hw : |(897833503/10000000000 : ℝ)|=(897833503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-690354133/5000000000 : ℝ)|^83 ≤ (430252235159/5000000000000 : ℝ)^67
        have hw : |(-690354133/5000000000 : ℝ)|=(690354133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8882441399/10000000000 : ℝ)|^83 ≤ (4317293493923/5000000000000 : ℝ)^67
        have hw : |(8882441399/10000000000 : ℝ)|=(8882441399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s0_16 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3807252619/5000000000 : ℝ)*x 0 + (3601139471/10000000000 : ℝ)*x 1 + (-62100867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3807252619/5000000000 : ℝ)^83 ≤ (71347213904079/100000000000000 : ℝ)^67 := by
    have hnat : (3807252619 : ℕ)^83*100000000000000^67 ≤ 71347213904079^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3807252619 5000000000 71347213904079 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3601139471/10000000000 : ℝ)^83 ≤ (14108640132309/50000000000000 : ℝ)^67 := by
    have hnat : (3601139471 : ℕ)^83*50000000000000^67 ≤ 14108640132309^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3601139471 10000000000 14108640132309 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62100867/5000000000 : ℝ)^83 ≤ (435505822609/100000000000000 : ℝ)^67 := by
    have hnat : (62100867 : ℕ)^83*100000000000000^67 ≤ 435505822609^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62100867 5000000000 435505822609 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3807252619/5000000000 : ℝ), (3601139471/10000000000 : ℝ), (-62100867/5000000000 : ℝ)] ![(71347213904079/100000000000000 : ℝ), (14108640132309/50000000000000 : ℝ), (435505822609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3807252619/5000000000 : ℝ)|^83 ≤ (71347213904079/100000000000000 : ℝ)^67
        have hw : |(3807252619/5000000000 : ℝ)|=(3807252619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3601139471/10000000000 : ℝ)|^83 ≤ (14108640132309/50000000000000 : ℝ)^67
        have hw : |(3601139471/10000000000 : ℝ)|=(3601139471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62100867/5000000000 : ℝ)|^83 ≤ (435505822609/100000000000000 : ℝ)^67
        have hw : |(-62100867/5000000000 : ℝ)|=(62100867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s0_20 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7558977893/10000000000 : ℝ)*x 0 + (3632734541/10000000000 : ℝ)*x 1 + (39451723/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7558977893/10000000000 : ℝ)^83 ≤ (35351621304449/50000000000000 : ℝ)^67 := by
    have hnat : (7558977893 : ℕ)^83*50000000000000^67 ≤ 35351621304449^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7558977893 10000000000 35351621304449 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3632734541/10000000000 : ℝ)^83 ≤ (28524289571711/100000000000000 : ℝ)^67 := by
    have hnat : (3632734541 : ℕ)^83*100000000000000^67 ≤ 28524289571711^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3632734541 10000000000 28524289571711 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39451723/2000000000 : ℝ)^83 ≤ (772467813237/100000000000000 : ℝ)^67 := by
    have hnat : (39451723 : ℕ)^83*100000000000000^67 ≤ 772467813237^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39451723 2000000000 772467813237 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7558977893/10000000000 : ℝ), (3632734541/10000000000 : ℝ), (39451723/2000000000 : ℝ)] ![(35351621304449/50000000000000 : ℝ), (28524289571711/100000000000000 : ℝ), (772467813237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7558977893/10000000000 : ℝ)|^83 ≤ (35351621304449/50000000000000 : ℝ)^67
        have hw : |(7558977893/10000000000 : ℝ)|=(7558977893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3632734541/10000000000 : ℝ)|^83 ≤ (28524289571711/100000000000000 : ℝ)^67
        have hw : |(3632734541/10000000000 : ℝ)|=(3632734541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(39451723/2000000000 : ℝ)|^83 ≤ (772467813237/100000000000000 : ℝ)^67
        have hw : |(39451723/2000000000 : ℝ)|=(39451723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s0_21 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1284987867/2500000000 : ℝ)*x 0 + (2106246617/5000000000 : ℝ)*x 1 + (586679847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1284987867/2500000000 : ℝ)^83 ≤ (2192321841613/5000000000000 : ℝ)^67 := by
    have hnat : (1284987867 : ℕ)^83*5000000000000^67 ≤ 2192321841613^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284987867 2500000000 2192321841613 5000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106246617/5000000000 : ℝ)^83 ≤ (27413653973/80000000000 : ℝ)^67 := by
    have hnat : (2106246617 : ℕ)^83*80000000000^67 ≤ 27413653973^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106246617 5000000000 27413653973 80000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (586679847/2000000000 : ℝ)^83 ≤ (5471623922087/25000000000000 : ℝ)^67 := by
    have hnat : (586679847 : ℕ)^83*25000000000000^67 ≤ 5471623922087^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586679847 2000000000 5471623922087 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1284987867/2500000000 : ℝ), (2106246617/5000000000 : ℝ), (586679847/2000000000 : ℝ)] ![(2192321841613/5000000000000 : ℝ), (27413653973/80000000000 : ℝ), (5471623922087/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1284987867/2500000000 : ℝ)|^83 ≤ (2192321841613/5000000000000 : ℝ)^67
        have hw : |(-1284987867/2500000000 : ℝ)|=(1284987867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2106246617/5000000000 : ℝ)|^83 ≤ (27413653973/80000000000 : ℝ)^67
        have hw : |(2106246617/5000000000 : ℝ)|=(2106246617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(586679847/2000000000 : ℝ)|^83 ≤ (5471623922087/25000000000000 : ℝ)^67
        have hw : |(586679847/2000000000 : ℝ)|=(586679847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s0_22 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (211403987/2500000000 : ℝ)*x 0 + (-221634147/1250000000 : ℝ)*x 1 + (4326088839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211403987/2500000000 : ℝ)^83 ≤ (117196791067/2500000000000 : ℝ)^67 := by
    have hnat : (211403987 : ℕ)^83*2500000000000^67 ≤ 117196791067^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211403987 2500000000 117196791067 2500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221634147/1250000000 : ℝ)^83 ≤ (2346108518417/20000000000000 : ℝ)^67 := by
    have hnat : (221634147 : ℕ)^83*20000000000000^67 ≤ 2346108518417^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221634147 1250000000 2346108518417 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4326088839/5000000000 : ℝ)^83 ≤ (83581585751529/100000000000000 : ℝ)^67 := by
    have hnat : (4326088839 : ℕ)^83*100000000000000^67 ≤ 83581585751529^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326088839 5000000000 83581585751529 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211403987/2500000000 : ℝ), (-221634147/1250000000 : ℝ), (4326088839/5000000000 : ℝ)] ![(117196791067/2500000000000 : ℝ), (2346108518417/20000000000000 : ℝ), (83581585751529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211403987/2500000000 : ℝ)|^83 ≤ (117196791067/2500000000000 : ℝ)^67
        have hw : |(211403987/2500000000 : ℝ)|=(211403987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-221634147/1250000000 : ℝ)|^83 ≤ (2346108518417/20000000000000 : ℝ)^67
        have hw : |(-221634147/1250000000 : ℝ)|=(221634147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4326088839/5000000000 : ℝ)|^83 ≤ (83581585751529/100000000000000 : ℝ)^67
        have hw : |(4326088839/5000000000 : ℝ)|=(4326088839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s0_23 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3423084321/5000000000 : ℝ)*x 0 + (2248231659/5000000000 : ℝ)*x 1 + (-94290439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3423084321/5000000000 : ℝ)^83 ≤ (3908692568273/6250000000000 : ℝ)^67 := by
    have hnat : (3423084321 : ℕ)^83*6250000000000^67 ≤ 3908692568273^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3423084321 5000000000 3908692568273 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248231659/5000000000 : ℝ)^83 ≤ (9287837298339/25000000000000 : ℝ)^67 := by
    have hnat : (2248231659 : ℕ)^83*25000000000000^67 ≤ 9287837298339^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248231659 5000000000 9287837298339 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94290439/10000000000 : ℝ)^83 ≤ (61913939341/20000000000000 : ℝ)^67 := by
    have hnat : (94290439 : ℕ)^83*20000000000000^67 ≤ 61913939341^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94290439 10000000000 61913939341 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3423084321/5000000000 : ℝ), (2248231659/5000000000 : ℝ), (-94290439/10000000000 : ℝ)] ![(3908692568273/6250000000000 : ℝ), (9287837298339/25000000000000 : ℝ), (61913939341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3423084321/5000000000 : ℝ)|^83 ≤ (3908692568273/6250000000000 : ℝ)^67
        have hw : |(3423084321/5000000000 : ℝ)|=(3423084321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248231659/5000000000 : ℝ)|^83 ≤ (9287837298339/25000000000000 : ℝ)^67
        have hw : |(2248231659/5000000000 : ℝ)|=(2248231659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94290439/10000000000 : ℝ)|^83 ≤ (61913939341/20000000000000 : ℝ)^67
        have hw : |(-94290439/10000000000 : ℝ)|=(94290439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s0_27 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (524845183/2000000000 : ℝ)*x 0 + (8404231601/10000000000 : ℝ)*x 1 + (94290439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524845183/2000000000 : ℝ)^83 ≤ (19065809204793/100000000000000 : ℝ)^67 := by
    have hnat : (524845183 : ℕ)^83*100000000000000^67 ≤ 19065809204793^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524845183 2000000000 19065809204793 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8404231601/10000000000 : ℝ)^83 ≤ (10078077635213/12500000000000 : ℝ)^67 := by
    have hnat : (8404231601 : ℕ)^83*12500000000000^67 ≤ 10078077635213^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8404231601 10000000000 10078077635213 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94290439/10000000000 : ℝ)^83 ≤ (61913939341/20000000000000 : ℝ)^67 := by
    have hnat : (94290439 : ℕ)^83*20000000000000^67 ≤ 61913939341^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94290439 10000000000 61913939341 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524845183/2000000000 : ℝ), (8404231601/10000000000 : ℝ), (94290439/10000000000 : ℝ)] ![(19065809204793/100000000000000 : ℝ), (10078077635213/12500000000000 : ℝ), (61913939341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524845183/2000000000 : ℝ)|^83 ≤ (19065809204793/100000000000000 : ℝ)^67
        have hw : |(524845183/2000000000 : ℝ)|=(524845183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8404231601/10000000000 : ℝ)|^83 ≤ (10078077635213/12500000000000 : ℝ)^67
        have hw : |(8404231601/10000000000 : ℝ)|=(8404231601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(94290439/10000000000 : ℝ)|^83 ≤ (61913939341/20000000000000 : ℝ)^67
        have hw : |(94290439/10000000000 : ℝ)|=(94290439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s1_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-724426559/2000000000 : ℝ)*x 0 + (904194149/2500000000 : ℝ)*x 1 + (2539804391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (724426559/2000000000 : ℝ)^83 ≤ (28421201033097/100000000000000 : ℝ)^67 := by
    have hnat : (724426559 : ℕ)^83*100000000000000^67 ≤ 28421201033097^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      724426559 2000000000 28421201033097 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904194149/2500000000 : ℝ)^83 ≤ (3546143270861/12500000000000 : ℝ)^67 := by
    have hnat : (904194149 : ℕ)^83*12500000000000^67 ≤ 3546143270861^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904194149 2500000000 3546143270861 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2539804391/5000000000 : ℝ)^83 ≤ (8641930556609/20000000000000 : ℝ)^67 := by
    have hnat : (2539804391 : ℕ)^83*20000000000000^67 ≤ 8641930556609^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539804391 5000000000 8641930556609 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-724426559/2000000000 : ℝ), (904194149/2500000000 : ℝ), (2539804391/5000000000 : ℝ)] ![(28421201033097/100000000000000 : ℝ), (3546143270861/12500000000000 : ℝ), (8641930556609/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-724426559/2000000000 : ℝ)|^83 ≤ (28421201033097/100000000000000 : ℝ)^67
        have hw : |(-724426559/2000000000 : ℝ)|=(724426559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(904194149/2500000000 : ℝ)|^83 ≤ (3546143270861/12500000000000 : ℝ)^67
        have hw : |(904194149/2500000000 : ℝ)|=(904194149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2539804391/5000000000 : ℝ)|^83 ≤ (8641930556609/20000000000000 : ℝ)^67
        have hw : |(2539804391/5000000000 : ℝ)|=(2539804391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s1_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1471417697/5000000000 : ℝ)*x 0 + (-29384837/100000000 : ℝ)*x 1 + (627061693/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1471417697/5000000000 : ℝ)^83 ≤ (5493436663341/25000000000000 : ℝ)^67 := by
    have hnat : (1471417697 : ℕ)^83*25000000000000^67 ≤ 5493436663341^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1471417697 5000000000 5493436663341 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (29384837/100000000 : ℝ)^83 ≤ (5483375155439/25000000000000 : ℝ)^67 := by
    have hnat : (29384837 : ℕ)^83*25000000000000^67 ≤ 5483375155439^67*100000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29384837 100000000 5483375155439 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627061693/1000000000 : ℝ)^83 ≤ (5609275271157/10000000000000 : ℝ)^67 := by
    have hnat : (627061693 : ℕ)^83*10000000000000^67 ≤ 5609275271157^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627061693 1000000000 5609275271157 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1471417697/5000000000 : ℝ), (-29384837/100000000 : ℝ), (627061693/1000000000 : ℝ)] ![(5493436663341/25000000000000 : ℝ), (5483375155439/25000000000000 : ℝ), (5609275271157/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1471417697/5000000000 : ℝ)|^83 ≤ (5493436663341/25000000000000 : ℝ)^67
        have hw : |(1471417697/5000000000 : ℝ)|=(1471417697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-29384837/100000000 : ℝ)|^83 ≤ (5483375155439/25000000000000 : ℝ)^67
        have hw : |(-29384837/100000000 : ℝ)|=(29384837/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627061693/1000000000 : ℝ)|^83 ≤ (5609275271157/10000000000000 : ℝ)^67
        have hw : |(627061693/1000000000 : ℝ)|=(627061693/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s1_2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2633690857/5000000000 : ℝ)*x 0 + (5274625297/10000000000 : ℝ)*x 1 + (-18739777/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633690857/5000000000 : ℝ)^83 ≤ (45197037140531/100000000000000 : ℝ)^67 := by
    have hnat : (2633690857 : ℕ)^83*100000000000000^67 ≤ 45197037140531^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633690857 5000000000 45197037140531 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5274625297/10000000000 : ℝ)^83 ≤ (45274046442203/100000000000000 : ℝ)^67 := by
    have hnat : (5274625297 : ℕ)^83*100000000000000^67 ≤ 45274046442203^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274625297 10000000000 45274046442203 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18739777/125000000 : ℝ)^83 ≤ (1905783282411/20000000000000 : ℝ)^67 := by
    have hnat : (18739777 : ℕ)^83*20000000000000^67 ≤ 1905783282411^67*125000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18739777 125000000 1905783282411 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633690857/5000000000 : ℝ), (5274625297/10000000000 : ℝ), (-18739777/125000000 : ℝ)] ![(45197037140531/100000000000000 : ℝ), (45274046442203/100000000000000 : ℝ), (1905783282411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633690857/5000000000 : ℝ)|^83 ≤ (45197037140531/100000000000000 : ℝ)^67
        have hw : |(2633690857/5000000000 : ℝ)|=(2633690857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5274625297/10000000000 : ℝ)|^83 ≤ (45274046442203/100000000000000 : ℝ)^67
        have hw : |(5274625297/10000000000 : ℝ)|=(5274625297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18739777/125000000 : ℝ)|^83 ≤ (1905783282411/20000000000000 : ℝ)^67
        have hw : |(-18739777/125000000 : ℝ)|=(18739777/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321051_s1_6 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2503710313/5000000000 : ℝ)*x 0 + (1253576679/2500000000 : ℝ)*x 1 + (2165469597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2503710313/5000000000 : ℝ)^83 ≤ (21225118604643/50000000000000 : ℝ)^67 := by
    have hnat : (2503710313 : ℕ)^83*50000000000000^67 ≤ 21225118604643^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503710313 5000000000 21225118604643 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1253576679/2500000000 : ℝ)^83 ≤ (42522566351109/100000000000000 : ℝ)^67 := by
    have hnat : (1253576679 : ℕ)^83*100000000000000^67 ≤ 42522566351109^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253576679 2500000000 42522566351109 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2165469597/10000000000 : ℝ)^83 ≤ (1878399552293/12500000000000 : ℝ)^67 := by
    have hnat : (2165469597 : ℕ)^83*12500000000000^67 ≤ 1878399552293^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165469597 10000000000 1878399552293 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2503710313/5000000000 : ℝ), (1253576679/2500000000 : ℝ), (2165469597/10000000000 : ℝ)] ![(21225118604643/50000000000000 : ℝ), (42522566351109/100000000000000 : ℝ), (1878399552293/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2503710313/5000000000 : ℝ)|^83 ≤ (21225118604643/50000000000000 : ℝ)^67
        have hw : |(2503710313/5000000000 : ℝ)|=(2503710313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1253576679/2500000000 : ℝ)|^83 ≤ (42522566351109/100000000000000 : ℝ)^67
        have hw : |(1253576679/2500000000 : ℝ)|=(1253576679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2165469597/10000000000 : ℝ)|^83 ≤ (1878399552293/12500000000000 : ℝ)^67
        have hw : |(2165469597/10000000000 : ℝ)|=(2165469597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c321051 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80491/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80491/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (168549/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1467340684240883/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1467340684240883/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-659209093/2000000000 : ℝ)*X 0 0+(659209073/2000000000 : ℝ)*X 0 1+(5661877229/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2367828041/10000000000 : ℝ)*X 1 0+(-2367827959/10000000000 : ℝ)*X 1 1+(7187852809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1345417869/5000000000 : ℝ)*X 0 0+(26020747/156250000 : ℝ)*X 0 1+(3726568223/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((624073461/5000000000 : ℝ)*X 1 0+(-691552861/10000000000 : ℝ)*X 1 1+(4540873689/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1004136703/2500000000 : ℝ)*X 2 0+(7236317867/10000000000 : ℝ)*X 2 1+(-184834401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2726723101/10000000000 : ℝ)*X 0 0+(4144085683/5000000000 : ℝ)*X 0 1+(194645969/10000000000 : ℝ)*X 0 2+(2726723101/10000000000 : ℝ)*X 1 0+(4144085683/5000000000 : ℝ)*X 1 1+(194645969/10000000000 : ℝ)*X 1 2+(2726723101/10000000000 : ℝ)*X 2 0+(4144085683/5000000000 : ℝ)*X 2 1+(194645969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1797529597/10000000000 : ℝ)*X 0 0+(689131669/2500000000 : ℝ)*X 0 1+(7307853803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((897833503/10000000000 : ℝ)*X 1 0+(-690354133/5000000000 : ℝ)*X 1 1+(8882441399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3807252619/5000000000 : ℝ)*X 2 0+(3601139471/10000000000 : ℝ)*X 2 1+(-62100867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((7558977893/10000000000 : ℝ)*X 0 0+(3632734541/10000000000 : ℝ)*X 0 1+(39451723/2000000000 : ℝ)*X 0 2+(7558977893/10000000000 : ℝ)*X 1 0+(3632734541/10000000000 : ℝ)*X 1 1+(39451723/2000000000 : ℝ)*X 1 2+(7558977893/10000000000 : ℝ)*X 2 0+(3632734541/10000000000 : ℝ)*X 2 1+(39451723/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1284987867/2500000000 : ℝ)*X 0 0+(2106246617/5000000000 : ℝ)*X 0 1+(586679847/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((211403987/2500000000 : ℝ)*X 1 0+(-221634147/1250000000 : ℝ)*X 1 1+(4326088839/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3423084321/5000000000 : ℝ)*X 2 0+(2248231659/5000000000 : ℝ)*X 2 1+(-94290439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((524845183/2000000000 : ℝ)*X 0 0+(8404231601/10000000000 : ℝ)*X 0 1+(94290439/10000000000 : ℝ)*X 0 2+(524845183/2000000000 : ℝ)*X 1 0+(8404231601/10000000000 : ℝ)*X 1 1+(94290439/10000000000 : ℝ)*X 1 2+(524845183/2000000000 : ℝ)*X 2 0+(8404231601/10000000000 : ℝ)*X 2 1+(94290439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((4211/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4211/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (22969259495141251264239/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (225201174997/250000000000 : ℝ)*(base7) + (3733093/1000000000000 : ℝ)*(base19) + (693463979/250000000000 : ℝ)*(base49) + (29890542899/500000000000 : ℝ)*(base60) + (870782648743/500000000000 : ℝ)*(major_s0_0) + (870782648743/500000000000 : ℝ)*(major_s0_1) + (870782648743/500000000000 : ℝ)*(major_s0_2) + (1804383/1000000000000 : ℝ)*(sp_s0_0) + (2062075764259/1000000000000 : ℝ)*(sp_s0_7) + (2062106386791/1000000000000 : ℝ)*(sp_s0_8) + (412422023977/200000000000 : ℝ)*(sp_s0_9) + (453898778981/250000000000 : ℝ)*(sp_s0_13) + (32551243/1000000000000 : ℝ)*(sp_s0_14) + (6394599/50000000000 : ℝ)*(sp_s0_27) + (914918307917/1000000000000 : ℝ)*(f.failure) + (412422023977/200000000000 : ℝ)*(f.sum) + (478944571/2500000000000000000000 : ℝ)*base63 + (2223398998959259/2500000000000000000000000000 : ℝ)*base65 + (1403202394790741/2500000000000000000000000000 : ℝ)*base67 + (3003638347839931/5000000000000000000000000000 : ℝ)*base69 + (2560978180078587/5000000000000000000000000000 : ℝ)*base71 + (3218955480209259/2500000000000000000000000000 : ℝ)*base73 + (2634607667160069/5000000000000000000000000000 : ℝ)*base75 + (3684408259660069/5000000000000000000000000000 : ℝ)*base77 + (3349074309/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1049/6250000000000000 : ℝ)*base87 + (1049/6250000000000000 : ℝ)*base89 + (1049/6250000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(667/1000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(667/1000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1001738570169995697849/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (260825277713/1000000000000 : ℝ)*(base5) + (880270951431/1000000000000 : ℝ)*(base7) + (9847/31250000000 : ℝ)*(base59) + (191805257607/1000000000000 : ℝ)*(base60) + (59422609367/31250000000 : ℝ)*(major_s0_0) + (59422609367/31250000000 : ℝ)*(major_s0_1) + (59422609367/31250000000 : ℝ)*(major_s0_2) + (1943257/500000000000 : ℝ)*(sp_s0_0) + (1547569/62500000000 : ℝ)*(sp_s0_7) + (461900486533/200000000000 : ℝ)*(sp_s0_14) + (1154759879991/500000000000 : ℝ)*(sp_s0_15) + (514071271599/200000000000 : ℝ)*(sp_s0_16) + (404599206809/250000000000 : ℝ)*(sp_s0_20) + (113203/10000000000 : ℝ)*(sp_s0_22) + (499475576759/500000000000 : ℝ)*(f.failure) + (1154765540141/500000000000 : ℝ)*(f.sum) + (972686019/10000000000000000000000 : ℝ)*base63 + (21841420473079/156250000000000000000000000 : ℝ)*base64 + (17658461612199/39062500000000000000000000 : ℝ)*base66 + (41193286838561/312500000000000000000000000 : ℝ)*base68 + (9664449017403/312500000000000000000000000 : ℝ)*base71 + (39104227964421/156250000000000000000000000 : ℝ)*base73 + (103609421036439/312500000000000000000000000 : ℝ)*base74 + (67131538630189/312500000000000000000000000 : ℝ)*base76 + (6387481/1000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1823/3125000000000000 : ℝ)*base87 + (1823/3125000000000000 : ℝ)*base89 + (1823/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(28473/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(28473/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (44143541210217879/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (20448841577/500000000000 : ℝ)*(base5) + (151227872151/1000000000000 : ℝ)*(base7) + (266327912197/500000000000 : ℝ)*(base39) + (190771/125000000000 : ℝ)*(base44) + (546683380927/1000000000000 : ℝ)*(base49) + (86487361927/50000000000 : ℝ)*(major_s0_0) + (432436428093/250000000000 : ℝ)*(major_s0_1) + (86487361927/50000000000 : ℝ)*(major_s0_2) + (14669159/1000000000000 : ℝ)*(sp_s0_1) + (1896639/200000000000 : ℝ)*(sp_s0_16) + (2465818871203/1000000000000 : ℝ)*(sp_s0_21) + (616450668969/250000000000 : ℝ)*(sp_s0_22) + (1253353535581/500000000000 : ℝ)*(sp_s0_23) + (509519220919/500000000000 : ℝ)*(sp_s0_27) + (90870977901/100000000000 : ℝ)*(f.failure) + (2465818871203/1000000000000 : ℝ)*(f.sum) + (133194711759207/1250000000000000000000000000 : ℝ)*base63 + (109553924306549/250000000000000000000000000 : ℝ)*base64 + (563382194235809/1250000000000000000000000000 : ℝ)*base66 + (169992757911541/500000000000000000000000000 : ℝ)*base68 + (20368380398443/500000000000000000000000000 : ℝ)*base71 + (125204856831549/250000000000000000000000000 : ℝ)*base72 + (1195782575673881/2500000000000000000000000000 : ℝ)*base74 + (231649128888459/500000000000000000000000000 : ℝ)*base76 + (60103660428223/625000000000000000000000000 : ℝ)*base79 + (697/625000000000000 : ℝ)*base87 + (697/625000000000000 : ℝ)*base89 + (697/625000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (4211/6250 : ℝ) ^ (81/16 : ℝ) ≤ (423309210956034443/3125000000000000000 : ℝ) := by
    have hpowers : (4211/6250 : ℝ)^81 ≤ (423309210956034443/3125000000000000000 : ℝ)^16 := by
      have hnat : (4211 : ℕ)^81*3125000000000000000^16 ≤ 423309210956034443^16*6250^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4211 6250 423309210956034443 3125000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4211/6250 : ℝ)) (X := (423309210956034443/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (3548309210956034443/3125000000000000000 : ℝ) ≤ (1281764014542003/1250000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3548309210956034443/3125000000000000000 : ℝ)^16 ≤ (1281764014542003/1250000000000000 : ℝ)^81 := by
      have hnat : (3548309210956034443 : ℕ)^16*1250000000000000^81 ≤ 1281764014542003^81*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3548309210956034443 3125000000000000000 1281764014542003 1250000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1281764014542003/1250000000000000 : ℝ)) (X := (3548309210956034443/3125000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (1985809210956034443/1562500000000000000 : ℝ) ≤ (10484951326681673/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (1985809210956034443/1562500000000000000 : ℝ)^16 ≤ (10484951326681673/10000000000000000 : ℝ)^81 := by
      have hnat : (1985809210956034443 : ℕ)^16*10000000000000000^81 ≤ 10484951326681673^81*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1985809210956034443 1562500000000000000 10484951326681673 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10484951326681673/10000000000000000 : ℝ)) (X := (1985809210956034443/1562500000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(31764014542003/842200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(230839210345649/6737600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (4211/6250 : ℝ)) (alpha := (31764014542003/842200000000000 : ℝ)) (beta := (230839210345649/6737600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (4211/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(31764014542003/842200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(230839210345649/6737600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (667/1000 : ℝ) ^ (81/16 : ℝ) ≤ (6435866672553600869/50000000000000000000 : ℝ) := by
    have hpowers : (667/1000 : ℝ)^81 ≤ (6435866672553600869/50000000000000000000 : ℝ)^16 := by
      have hnat : (667 : ℕ)^81*50000000000000000000^16 ≤ 6435866672553600869^16*1000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        667 1000 6435866672553600869 50000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (667/1000 : ℝ)) (X := (6435866672553600869/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (56435866672553600869/50000000000000000000 : ℝ) ≤ (5121028622936273/5000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (56435866672553600869/50000000000000000000 : ℝ)^16 ≤ (5121028622936273/5000000000000000 : ℝ)^81 := by
      have hnat : (56435866672553600869 : ℕ)^16*5000000000000000^81 ≤ 5121028622936273^81*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56435866672553600869 50000000000000000000 5121028622936273 5000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5121028622936273/5000000000000000 : ℝ)) (X := (56435866672553600869/50000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (31435866672553600869/25000000000000000000 : ℝ) ≤ (261572119547059/250000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (31435866672553600869/25000000000000000000 : ℝ)^16 ≤ (261572119547059/250000000000000 : ℝ)^81 := by
      have hnat : (31435866672553600869 : ℕ)^16*250000000000000^81 ≤ 261572119547059^81*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31435866672553600869 25000000000000000000 261572119547059 250000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (261572119547059/250000000000000 : ℝ)) (X := (31435866672553600869/25000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(121028622936273/3335000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(4800598608909/145000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (667/1000 : ℝ)) (alpha := (121028622936273/3335000000000000 : ℝ)) (beta := (4800598608909/145000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (667/1000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(121028622936273/3335000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(4800598608909/145000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (28473/100000 : ℝ) ^ (81/16 : ℝ) ≤ (173008809358954827/100000000000000000000 : ℝ) := by
    have hpowers : (28473/100000 : ℝ)^81 ≤ (173008809358954827/100000000000000000000 : ℝ)^16 := by
      have hnat : (28473 : ℕ)^81*100000000000000000000^16 ≤ 173008809358954827^16*100000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28473 100000 173008809358954827 100000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28473/100000 : ℝ)) (X := (173008809358954827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100173008809358954827/100000000000000000000 : ℝ) ≤ (5001707544062447/5000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (100173008809358954827/100000000000000000000 : ℝ)^16 ≤ (5001707544062447/5000000000000000 : ℝ)^81 := by
      have hnat : (100173008809358954827 : ℕ)^16*5000000000000000^81 ≤ 5001707544062447^81*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100173008809358954827 100000000000000000000 5001707544062447 5000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001707544062447/5000000000000000 : ℝ)) (X := (100173008809358954827/100000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50173008809358954827/50000000000000000000 : ℝ) ≤ (1250853180800291/1250000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (50173008809358954827/50000000000000000000 : ℝ)^16 ≤ (1250853180800291/1250000000000000 : ℝ)^81 := by
      have hnat : (50173008809358954827 : ℕ)^16*1250000000000000^81 ≤ 1250853180800291^81*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50173008809358954827 50000000000000000000 1250853180800291 1250000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250853180800291/1250000000000000 : ℝ)) (X := (50173008809358954827/50000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(569181354149/474550000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(568393046239/474550000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (28473/100000 : ℝ)) (alpha := (569181354149/474550000000000 : ℝ)) (beta := (568393046239/474550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (28473/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(569181354149/474550000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(568393046239/474550000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-724426559/2000000000 : ℝ)*X 0 0+(904194149/2500000000 : ℝ)*X 0 1+(2539804391/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1471417697/5000000000 : ℝ)*X 1 0+(-29384837/100000000 : ℝ)*X 1 1+(627061693/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2633690857/5000000000 : ℝ)*X 2 0+(5274625297/10000000000 : ℝ)*X 2 1+(-18739777/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2503710313/5000000000 : ℝ)*X 0 0+(1253576679/2500000000 : ℝ)*X 0 1+(2165469597/10000000000 : ℝ)*X 0 2+(2503710313/5000000000 : ℝ)*X 1 0+(1253576679/2500000000 : ℝ)*X 1 1+(2165469597/10000000000 : ℝ)*X 1 2+(2503710313/5000000000 : ℝ)*X 2 0+(1253576679/2500000000 : ℝ)*X 2 1+(2165469597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321051_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-26316/3125 : ℝ) < ((-11897/6250 : ℝ)*P 0+(-11897/6250 : ℝ)*P 1+(-11897/6250 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-26316/3125 : ℝ) < (-353002251866742410880219693/42110000000000000000000000 : ℝ) := by norm_num
    linear_combination (7817/250000000000 : ℝ)*(base11) + (10871/250000000000 : ℝ)*(base15) + (207/100000000000 : ℝ)*(base16) + (709/250000000000 : ℝ)*(base40) + (204563745631/1000000000000 : ℝ)*(base49) + (2251/1000000000000 : ℝ)*(base50) + (92222024531/500000000000 : ℝ)*(base59) + (578182190443/1000000000000 : ℝ)*(base60) + (11897/6250 : ℝ)*(major_s1_0) + (11897/6250 : ℝ)*(major_s1_1) + (11897/6250 : ℝ)*(major_s1_2) + (2794286772073/1000000000000 : ℝ)*(sp_s1_0) + (2794286757787/1000000000000 : ℝ)*(sp_s1_1) + (1397143401671/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1397143401671/500000000000 : ℝ)*(f.sum) + (389950000202921/12660994000000000000000000000 : ℝ)*base62 + (3343684476393/23727500000000000000000000 : ℝ)*base65 + (67114716253/145000000000000000000000 : ℝ)*base67 + (4178064088351/47455000000000000000000000 : ℝ)*base69 + (1774454516898881/3996660100000000000000000000 : ℝ)*base70 + (1264797629501/4211000000000000000000000 : ℝ)*base72 + (375945374651/1667500000000000000000000 : ℝ)*base75 + (8870969210443/21055000000000000000000000 : ℝ)*base77 + (1683332284077/7632437500000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p021_b030 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 51 ≤ c.val) (hhi : c.val < 52)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=51 := by omega
  rcases hc with rfl
  · exact collision_c321051 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 51 ≤ c.val) (hhi : c.val < 52)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p021_b030 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

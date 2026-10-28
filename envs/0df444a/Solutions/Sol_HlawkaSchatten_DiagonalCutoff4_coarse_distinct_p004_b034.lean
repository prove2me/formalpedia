-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p004_b034
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:26:10.631774+00:00
-- url     : https://prove2.me/submissions/9bda9d7d-b150-41f9-b1e6-bc3e2b768035

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
theorem collision_support_c304077_s0_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1115329327/2000000000 : ℝ)*x 0 + (3745606819/10000000000 : ℝ)*x 1 + (3617569377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1115329327/2000000000 : ℝ)^133 ≤ (46346409749579/100000000000000 : ℝ)^101 := by
    have hnat : (1115329327 : ℕ)^133*100000000000000^101 ≤ 46346409749579^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115329327 2000000000 46346409749579 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3745606819/10000000000 : ℝ)^133 ≤ (5488207201471/20000000000000 : ℝ)^101 := by
    have hnat : (3745606819 : ℕ)^133*20000000000000^101 ≤ 5488207201471^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3745606819 10000000000 5488207201471 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3617569377/10000000000 : ℝ)^133 ≤ (26212554227551/100000000000000 : ℝ)^101 := by
    have hnat : (3617569377 : ℕ)^133*100000000000000^101 ≤ 26212554227551^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3617569377 10000000000 26212554227551 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1115329327/2000000000 : ℝ), (3745606819/10000000000 : ℝ), (3617569377/10000000000 : ℝ)] ![(46346409749579/100000000000000 : ℝ), (5488207201471/20000000000000 : ℝ), (26212554227551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1115329327/2000000000 : ℝ)|^133 ≤ (46346409749579/100000000000000 : ℝ)^101
        have hw : |(-1115329327/2000000000 : ℝ)|=(1115329327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3745606819/10000000000 : ℝ)|^133 ≤ (5488207201471/20000000000000 : ℝ)^101
        have hw : |(3745606819/10000000000 : ℝ)|=(3745606819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3617569377/10000000000 : ℝ)|^133 ≤ (26212554227551/100000000000000 : ℝ)^101
        have hw : |(3617569377/10000000000 : ℝ)|=(3617569377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s0_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2254468893/5000000000 : ℝ)*x 0 + (1366825699/2500000000 : ℝ)*x 1 + (-1462473447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2254468893/5000000000 : ℝ)^133 ≤ (17516365854229/50000000000000 : ℝ)^101 := by
    have hnat : (2254468893 : ℕ)^133*50000000000000^101 ≤ 17516365854229^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254468893 5000000000 17516365854229 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366825699/2500000000 : ℝ)^133 ≤ (45153492309103/100000000000000 : ℝ)^101 := by
    have hnat : (1366825699 : ℕ)^133*100000000000000^101 ≤ 45153492309103^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366825699 2500000000 45153492309103 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1462473447/5000000000 : ℝ)^133 ≤ (2476721995169/12500000000000 : ℝ)^101 := by
    have hnat : (1462473447 : ℕ)^133*12500000000000^101 ≤ 2476721995169^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1462473447 5000000000 2476721995169 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2254468893/5000000000 : ℝ), (1366825699/2500000000 : ℝ), (-1462473447/5000000000 : ℝ)] ![(17516365854229/50000000000000 : ℝ), (45153492309103/100000000000000 : ℝ), (2476721995169/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2254468893/5000000000 : ℝ)|^133 ≤ (17516365854229/50000000000000 : ℝ)^101
        have hw : |(2254468893/5000000000 : ℝ)|=(2254468893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366825699/2500000000 : ℝ)|^133 ≤ (45153492309103/100000000000000 : ℝ)^101
        have hw : |(1366825699/2500000000 : ℝ)|=(1366825699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1462473447/5000000000 : ℝ)|^133 ≤ (2476721995169/12500000000000 : ℝ)^101
        have hw : |(-1462473447/5000000000 : ℝ)|=(1462473447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s0_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (422929883/2000000000 : ℝ)*x 0 + (6816562427/10000000000 : ℝ)*x 1 + (3668814473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422929883/2000000000 : ℝ)^133 ≤ (6462826841083/50000000000000 : ℝ)^101 := by
    have hnat : (422929883 : ℕ)^133*50000000000000^101 ≤ 6462826841083^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422929883 2000000000 6462826841083 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6816562427/10000000000 : ℝ)^133 ≤ (30185868200377/50000000000000 : ℝ)^101 := by
    have hnat : (6816562427 : ℕ)^133*50000000000000^101 ≤ 30185868200377^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6816562427 10000000000 30185868200377 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3668814473/10000000000 : ℝ)^133 ≤ (5340521980617/20000000000000 : ℝ)^101 := by
    have hnat : (3668814473 : ℕ)^133*20000000000000^101 ≤ 5340521980617^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3668814473 10000000000 5340521980617 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(422929883/2000000000 : ℝ), (6816562427/10000000000 : ℝ), (3668814473/10000000000 : ℝ)] ![(6462826841083/50000000000000 : ℝ), (30185868200377/50000000000000 : ℝ), (5340521980617/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(422929883/2000000000 : ℝ)|^133 ≤ (6462826841083/50000000000000 : ℝ)^101
        have hw : |(422929883/2000000000 : ℝ)|=(422929883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6816562427/10000000000 : ℝ)|^133 ≤ (30185868200377/50000000000000 : ℝ)^101
        have hw : |(6816562427/10000000000 : ℝ)|=(6816562427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3668814473/10000000000 : ℝ)|^133 ≤ (5340521980617/20000000000000 : ℝ)^101
        have hw : |(3668814473/10000000000 : ℝ)|=(3668814473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s0_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-5705856967/10000000000 : ℝ)*x 0 + (866547031/2500000000 : ℝ)*x 1 + (3747215913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5705856967/10000000000 : ℝ)^133 ≤ (23323067159/48828125000 : ℝ)^101 := by
    have hnat : (5705856967 : ℕ)^133*48828125000^101 ≤ 23323067159^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5705856967 10000000000 23323067159 48828125000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (866547031/2500000000 : ℝ)^133 ≤ (12388898934203/50000000000000 : ℝ)^101 := by
    have hnat : (866547031 : ℕ)^133*50000000000000^101 ≤ 12388898934203^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866547031 2500000000 12388898934203 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3747215913/10000000000 : ℝ)^133 ≤ (3432070072041/12500000000000 : ℝ)^101 := by
    have hnat : (3747215913 : ℕ)^133*12500000000000^101 ≤ 3432070072041^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3747215913 10000000000 3432070072041 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5705856967/10000000000 : ℝ), (866547031/2500000000 : ℝ), (3747215913/10000000000 : ℝ)] ![(23323067159/48828125000 : ℝ), (12388898934203/50000000000000 : ℝ), (3432070072041/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5705856967/10000000000 : ℝ)|^133 ≤ (23323067159/48828125000 : ℝ)^101
        have hw : |(-5705856967/10000000000 : ℝ)|=(5705856967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(866547031/2500000000 : ℝ)|^133 ≤ (12388898934203/50000000000000 : ℝ)^101
        have hw : |(866547031/2500000000 : ℝ)|=(866547031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3747215913/10000000000 : ℝ)|^133 ≤ (3432070072041/12500000000000 : ℝ)^101
        have hw : |(3747215913/10000000000 : ℝ)|=(3747215913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s0_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3781591639/10000000000 : ℝ)*x 0 + (-407552467/2000000000 : ℝ)*x 1 + (6776153031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3781591639/10000000000 : ℝ)^133 ≤ (27788721800637/100000000000000 : ℝ)^101 := by
    have hnat : (3781591639 : ℕ)^133*100000000000000^101 ≤ 27788721800637^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3781591639 10000000000 27788721800637 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (407552467/2000000000 : ℝ)^133 ≤ (12310380622419/100000000000000 : ℝ)^101 := by
    have hnat : (407552467 : ℕ)^133*100000000000000^101 ≤ 12310380622419^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407552467 2000000000 12310380622419 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6776153031/10000000000 : ℝ)^133 ≤ (59900897558153/100000000000000 : ℝ)^101 := by
    have hnat : (6776153031 : ℕ)^133*100000000000000^101 ≤ 59900897558153^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6776153031 10000000000 59900897558153 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3781591639/10000000000 : ℝ), (-407552467/2000000000 : ℝ), (6776153031/10000000000 : ℝ)] ![(27788721800637/100000000000000 : ℝ), (12310380622419/100000000000000 : ℝ), (59900897558153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3781591639/10000000000 : ℝ)|^133 ≤ (27788721800637/100000000000000 : ℝ)^101
        have hw : |(3781591639/10000000000 : ℝ)|=(3781591639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-407552467/2000000000 : ℝ)|^133 ≤ (12310380622419/100000000000000 : ℝ)^101
        have hw : |(-407552467/2000000000 : ℝ)|=(407552467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6776153031/10000000000 : ℝ)|^133 ≤ (59900897558153/100000000000000 : ℝ)^101
        have hw : |(6776153031/10000000000 : ℝ)|=(6776153031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s0_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2131990809/5000000000 : ℝ)*x 0 + (5794233301/10000000000 : ℝ)*x 1 + (-112011639/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131990809/5000000000 : ℝ)^133 ≤ (32548358417383/100000000000000 : ℝ)^101 := by
    have hnat : (2131990809 : ℕ)^133*100000000000000^101 ≤ 32548358417383^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131990809 5000000000 32548358417383 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5794233301/10000000000 : ℝ)^133 ≤ (48742252432337/100000000000000 : ℝ)^101 := by
    have hnat : (5794233301 : ℕ)^133*100000000000000^101 ≤ 48742252432337^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5794233301 10000000000 48742252432337 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112011639/400000000 : ℝ)^133 ≤ (2338673640531/12500000000000 : ℝ)^101 := by
    have hnat : (112011639 : ℕ)^133*12500000000000^101 ≤ 2338673640531^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112011639 400000000 2338673640531 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2131990809/5000000000 : ℝ), (5794233301/10000000000 : ℝ), (-112011639/400000000 : ℝ)] ![(32548358417383/100000000000000 : ℝ), (48742252432337/100000000000000 : ℝ), (2338673640531/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2131990809/5000000000 : ℝ)|^133 ≤ (32548358417383/100000000000000 : ℝ)^101
        have hw : |(2131990809/5000000000 : ℝ)|=(2131990809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5794233301/10000000000 : ℝ)|^133 ≤ (48742252432337/100000000000000 : ℝ)^101
        have hw : |(5794233301/10000000000 : ℝ)|=(5794233301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-112011639/400000000 : ℝ)|^133 ≤ (2338673640531/12500000000000 : ℝ)^101
        have hw : |(-112011639/400000000 : ℝ)|=(112011639/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s0_12 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (226126979/1250000000 : ℝ)*x 0 + (7360222121/10000000000 : ℝ)*x 1 + (810384177/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (226126979/1250000000 : ℝ)^133 ≤ (10523896862431/100000000000000 : ℝ)^101 := by
    have hnat : (226126979 : ℕ)^133*100000000000000^101 ≤ 10523896862431^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226126979 1250000000 10523896862431 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7360222121/10000000000 : ℝ)^133 ≤ (66790969480013/100000000000000 : ℝ)^101 := by
    have hnat : (7360222121 : ℕ)^133*100000000000000^101 ≤ 66790969480013^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7360222121 10000000000 66790969480013 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (810384177/2500000000 : ℝ)^133 ≤ (1134256682167/5000000000000 : ℝ)^101 := by
    have hnat : (810384177 : ℕ)^133*5000000000000^101 ≤ 1134256682167^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810384177 2500000000 1134256682167 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(226126979/1250000000 : ℝ), (7360222121/10000000000 : ℝ), (810384177/2500000000 : ℝ)] ![(10523896862431/100000000000000 : ℝ), (66790969480013/100000000000000 : ℝ), (1134256682167/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(226126979/1250000000 : ℝ)|^133 ≤ (10523896862431/100000000000000 : ℝ)^101
        have hw : |(226126979/1250000000 : ℝ)|=(226126979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7360222121/10000000000 : ℝ)|^133 ≤ (66790969480013/100000000000000 : ℝ)^101
        have hw : |(7360222121/10000000000 : ℝ)|=(7360222121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(810384177/2500000000 : ℝ)|^133 ≤ (1134256682167/5000000000000 : ℝ)^101
        have hw : |(810384177/2500000000 : ℝ)|=(810384177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s0_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-177356577/312500000 : ℝ)*x 0 + (3769020693/10000000000 : ℝ)*x 1 + (3479434401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (177356577/312500000 : ℝ)^133 ≤ (47430294326457/100000000000000 : ℝ)^101 := by
    have hnat : (177356577 : ℕ)^133*100000000000000^101 ≤ 47430294326457^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177356577 312500000 47430294326457 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3769020693/10000000000 : ℝ)^133 ≤ (27667141494979/100000000000000 : ℝ)^101 := by
    have hnat : (3769020693 : ℕ)^133*100000000000000^101 ≤ 27667141494979^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3769020693 10000000000 27667141494979 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3479434401/10000000000 : ℝ)^133 ≤ (12451282083089/50000000000000 : ℝ)^101 := by
    have hnat : (3479434401 : ℕ)^133*50000000000000^101 ≤ 12451282083089^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3479434401 10000000000 12451282083089 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-177356577/312500000 : ℝ), (3769020693/10000000000 : ℝ), (3479434401/10000000000 : ℝ)] ![(47430294326457/100000000000000 : ℝ), (27667141494979/100000000000000 : ℝ), (12451282083089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-177356577/312500000 : ℝ)|^133 ≤ (47430294326457/100000000000000 : ℝ)^101
        have hw : |(-177356577/312500000 : ℝ)|=(177356577/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3769020693/10000000000 : ℝ)|^133 ≤ (27667141494979/100000000000000 : ℝ)^101
        have hw : |(3769020693/10000000000 : ℝ)|=(3769020693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3479434401/10000000000 : ℝ)|^133 ≤ (12451282083089/50000000000000 : ℝ)^101
        have hw : |(3479434401/10000000000 : ℝ)|=(3479434401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s0_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (748695631/2000000000 : ℝ)*x 0 + (-288618033/1250000000 : ℝ)*x 1 + (413630023/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (748695631/2000000000 : ℝ)^133 ≤ (27420501863829/100000000000000 : ℝ)^101 := by
    have hnat : (748695631 : ℕ)^133*100000000000000^101 ≤ 27420501863829^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748695631 2000000000 27420501863829 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (288618033/1250000000 : ℝ)^133 ≤ (14511846009027/100000000000000 : ℝ)^101 := by
    have hnat : (288618033 : ℕ)^133*100000000000000^101 ≤ 14511846009027^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288618033 1250000000 14511846009027 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413630023/625000000 : ℝ)^133 ≤ (14516913028303/25000000000000 : ℝ)^101 := by
    have hnat : (413630023 : ℕ)^133*25000000000000^101 ≤ 14516913028303^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413630023 625000000 14516913028303 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(748695631/2000000000 : ℝ), (-288618033/1250000000 : ℝ), (413630023/625000000 : ℝ)] ![(27420501863829/100000000000000 : ℝ), (14511846009027/100000000000000 : ℝ), (14516913028303/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(748695631/2000000000 : ℝ)|^133 ≤ (27420501863829/100000000000000 : ℝ)^101
        have hw : |(748695631/2000000000 : ℝ)|=(748695631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-288618033/1250000000 : ℝ)|^133 ≤ (14511846009027/100000000000000 : ℝ)^101
        have hw : |(-288618033/1250000000 : ℝ)|=(288618033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(413630023/625000000 : ℝ)|^133 ≤ (14516913028303/25000000000000 : ℝ)^101
        have hw : |(413630023/625000000 : ℝ)|=(413630023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s0_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1097016941/2500000000 : ℝ)*x 0 + (5462231597/10000000000 : ℝ)*x 1 + (-1534036389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097016941/2500000000 : ℝ)^133 ≤ (33801360531859/100000000000000 : ℝ)^101 := by
    have hnat : (1097016941 : ℕ)^133*100000000000000^101 ≤ 33801360531859^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097016941 2500000000 33801360531859 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462231597/10000000000 : ℝ)^133 ≤ (45098348684883/100000000000000 : ℝ)^101 := by
    have hnat : (5462231597 : ℕ)^133*100000000000000^101 ≤ 45098348684883^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462231597 10000000000 45098348684883 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1534036389/5000000000 : ℝ)^133 ≤ (5275072689747/25000000000000 : ℝ)^101 := by
    have hnat : (1534036389 : ℕ)^133*25000000000000^101 ≤ 5275072689747^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1534036389 5000000000 5275072689747 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1097016941/2500000000 : ℝ), (5462231597/10000000000 : ℝ), (-1534036389/5000000000 : ℝ)] ![(33801360531859/100000000000000 : ℝ), (45098348684883/100000000000000 : ℝ), (5275072689747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1097016941/2500000000 : ℝ)|^133 ≤ (33801360531859/100000000000000 : ℝ)^101
        have hw : |(1097016941/2500000000 : ℝ)|=(1097016941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462231597/10000000000 : ℝ)|^133 ≤ (45098348684883/100000000000000 : ℝ)^101
        have hw : |(5462231597/10000000000 : ℝ)|=(5462231597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1534036389/5000000000 : ℝ)|^133 ≤ (5275072689747/25000000000000 : ℝ)^101
        have hw : |(-1534036389/5000000000 : ℝ)|=(1534036389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s0_19 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (564695687/2500000000 : ℝ)*x 0 + (6802609347/10000000000 : ℝ)*x 1 + (3562967601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (564695687/2500000000 : ℝ)^133 ≤ (14098127059127/100000000000000 : ℝ)^101 := by
    have hnat : (564695687 : ℕ)^133*100000000000000^101 ≤ 14098127059127^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564695687 2500000000 14098127059127 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6802609347/10000000000 : ℝ)^133 ≤ (60209058827161/100000000000000 : ℝ)^101 := by
    have hnat : (6802609347 : ℕ)^133*100000000000000^101 ≤ 60209058827161^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6802609347 10000000000 60209058827161 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3562967601/10000000000 : ℝ)^133 ≤ (25692814103389/100000000000000 : ℝ)^101 := by
    have hnat : (3562967601 : ℕ)^133*100000000000000^101 ≤ 25692814103389^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3562967601 10000000000 25692814103389 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(564695687/2500000000 : ℝ), (6802609347/10000000000 : ℝ), (3562967601/10000000000 : ℝ)] ![(14098127059127/100000000000000 : ℝ), (60209058827161/100000000000000 : ℝ), (25692814103389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(564695687/2500000000 : ℝ)|^133 ≤ (14098127059127/100000000000000 : ℝ)^101
        have hw : |(564695687/2500000000 : ℝ)|=(564695687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6802609347/10000000000 : ℝ)|^133 ≤ (60209058827161/100000000000000 : ℝ)^101
        have hw : |(6802609347/10000000000 : ℝ)|=(6802609347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3562967601/10000000000 : ℝ)|^133 ≤ (25692814103389/100000000000000 : ℝ)^101
        have hw : |(3562967601/10000000000 : ℝ)|=(3562967601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s0_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-5606019883/10000000000 : ℝ)*x 0 + (385126927/1000000000 : ℝ)*x 1 + (3475653563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5606019883/10000000000 : ℝ)^133 ≤ (2916758523427/6250000000000 : ℝ)^101 := by
    have hnat : (5606019883 : ℕ)^133*6250000000000^101 ≤ 2916758523427^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5606019883 10000000000 2916758523427 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (385126927/1000000000 : ℝ)^133 ≤ (5692985283929/20000000000000 : ℝ)^101 := by
    have hnat : (385126927 : ℕ)^133*20000000000000^101 ≤ 5692985283929^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385126927 1000000000 5692985283929 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3475653563/10000000000 : ℝ)^133 ≤ (24866937189661/100000000000000 : ℝ)^101 := by
    have hnat : (3475653563 : ℕ)^133*100000000000000^101 ≤ 24866937189661^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3475653563 10000000000 24866937189661 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5606019883/10000000000 : ℝ), (385126927/1000000000 : ℝ), (3475653563/10000000000 : ℝ)] ![(2916758523427/6250000000000 : ℝ), (5692985283929/20000000000000 : ℝ), (24866937189661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5606019883/10000000000 : ℝ)|^133 ≤ (2916758523427/6250000000000 : ℝ)^101
        have hw : |(-5606019883/10000000000 : ℝ)|=(5606019883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(385126927/1000000000 : ℝ)|^133 ≤ (5692985283929/20000000000000 : ℝ)^101
        have hw : |(385126927/1000000000 : ℝ)|=(385126927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3475653563/10000000000 : ℝ)|^133 ≤ (24866937189661/100000000000000 : ℝ)^101
        have hw : |(3475653563/10000000000 : ℝ)|=(3475653563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s0_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1832173559/5000000000 : ℝ)*x 0 + (-560699857/2500000000 : ℝ)*x 1 + (6730780571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1832173559/5000000000 : ℝ)^133 ≤ (6664950477003/25000000000000 : ℝ)^101 := by
    have hnat : (1832173559 : ℕ)^133*25000000000000^101 ≤ 6664950477003^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1832173559 5000000000 6664950477003 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560699857/2500000000 : ℝ)^133 ≤ (13966908177699/100000000000000 : ℝ)^101 := by
    have hnat : (560699857 : ℕ)^133*100000000000000^101 ≤ 13966908177699^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560699857 2500000000 13966908177699 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6730780571/10000000000 : ℝ)^133 ≤ (14843322473309/25000000000000 : ℝ)^101 := by
    have hnat : (6730780571 : ℕ)^133*25000000000000^101 ≤ 14843322473309^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6730780571 10000000000 14843322473309 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1832173559/5000000000 : ℝ), (-560699857/2500000000 : ℝ), (6730780571/10000000000 : ℝ)] ![(6664950477003/25000000000000 : ℝ), (13966908177699/100000000000000 : ℝ), (14843322473309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1832173559/5000000000 : ℝ)|^133 ≤ (6664950477003/25000000000000 : ℝ)^101
        have hw : |(1832173559/5000000000 : ℝ)|=(1832173559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560699857/2500000000 : ℝ)|^133 ≤ (13966908177699/100000000000000 : ℝ)^101
        have hw : |(-560699857/2500000000 : ℝ)|=(560699857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6730780571/10000000000 : ℝ)|^133 ≤ (14843322473309/25000000000000 : ℝ)^101
        have hw : |(6730780571/10000000000 : ℝ)|=(6730780571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s0_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (600660303/1250000000 : ℝ)*x 0 + (5137825761/10000000000 : ℝ)*x 1 + (-2979207589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (600660303/1250000000 : ℝ)^133 ≤ (9523956333039/25000000000000 : ℝ)^101 := by
    have hnat : (600660303 : ℕ)^133*25000000000000^101 ≤ 9523956333039^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600660303 1250000000 9523956333039 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137825761/10000000000 : ℝ)^133 ≤ (41604960456379/100000000000000 : ℝ)^101 := by
    have hnat : (5137825761 : ℕ)^133*100000000000000^101 ≤ 41604960456379^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137825761 10000000000 41604960456379 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2979207589/10000000000 : ℝ)^133 ≤ (20299214183591/100000000000000 : ℝ)^101 := by
    have hnat : (2979207589 : ℕ)^133*100000000000000^101 ≤ 20299214183591^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2979207589 10000000000 20299214183591 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(600660303/1250000000 : ℝ), (5137825761/10000000000 : ℝ), (-2979207589/10000000000 : ℝ)] ![(9523956333039/25000000000000 : ℝ), (41604960456379/100000000000000 : ℝ), (20299214183591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(600660303/1250000000 : ℝ)|^133 ≤ (9523956333039/25000000000000 : ℝ)^101
        have hw : |(600660303/1250000000 : ℝ)|=(600660303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137825761/10000000000 : ℝ)|^133 ≤ (41604960456379/100000000000000 : ℝ)^101
        have hw : |(5137825761/10000000000 : ℝ)|=(5137825761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2979207589/10000000000 : ℝ)|^133 ≤ (20299214183591/100000000000000 : ℝ)^101
        have hw : |(-2979207589/10000000000 : ℝ)|=(2979207589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s0_25 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1712411623/10000000000 : ℝ)*x 0 + (299800631/400000000 : ℝ)*x 1 + (1572704019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1712411623/10000000000 : ℝ)^133 ≤ (9790186217287/100000000000000 : ℝ)^101 := by
    have hnat : (1712411623 : ℕ)^133*100000000000000^101 ≤ 9790186217287^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1712411623 10000000000 9790186217287 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299800631/400000000 : ℝ)^133 ≤ (4275397955649/6250000000000 : ℝ)^101 := by
    have hnat : (299800631 : ℕ)^133*6250000000000^101 ≤ 4275397955649^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299800631 400000000 4275397955649 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1572704019/5000000000 : ℝ)^133 ≤ (2180344648533/10000000000000 : ℝ)^101 := by
    have hnat : (1572704019 : ℕ)^133*10000000000000^101 ≤ 2180344648533^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572704019 5000000000 2180344648533 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1712411623/10000000000 : ℝ), (299800631/400000000 : ℝ), (1572704019/5000000000 : ℝ)] ![(9790186217287/100000000000000 : ℝ), (4275397955649/6250000000000 : ℝ), (2180344648533/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1712411623/10000000000 : ℝ)|^133 ≤ (9790186217287/100000000000000 : ℝ)^101
        have hw : |(1712411623/10000000000 : ℝ)|=(1712411623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(299800631/400000000 : ℝ)|^133 ≤ (4275397955649/6250000000000 : ℝ)^101
        have hw : |(299800631/400000000 : ℝ)|=(299800631/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1572704019/5000000000 : ℝ)|^133 ≤ (2180344648533/10000000000000 : ℝ)^101
        have hw : |(1572704019/5000000000 : ℝ)|=(1572704019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s1_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-4887710969/10000000000 : ℝ)*x 0 + (1015172169/2500000000 : ℝ)*x 1 + (4060719999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4887710969/10000000000 : ℝ)^133 ≤ (38958685392049/100000000000000 : ℝ)^101 := by
    have hnat : (4887710969 : ℕ)^133*100000000000000^101 ≤ 38958685392049^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4887710969 10000000000 38958685392049 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015172169/2500000000 : ℝ)^133 ≤ (244164018331/800000000000 : ℝ)^101 := by
    have hnat : (1015172169 : ℕ)^133*800000000000^101 ≤ 244164018331^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015172169 2500000000 244164018331 800000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4060719999/10000000000 : ℝ)^133 ≤ (30520812308819/100000000000000 : ℝ)^101 := by
    have hnat : (4060719999 : ℕ)^133*100000000000000^101 ≤ 30520812308819^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4060719999 10000000000 30520812308819 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4887710969/10000000000 : ℝ), (1015172169/2500000000 : ℝ), (4060719999/10000000000 : ℝ)] ![(38958685392049/100000000000000 : ℝ), (244164018331/800000000000 : ℝ), (30520812308819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4887710969/10000000000 : ℝ)|^133 ≤ (38958685392049/100000000000000 : ℝ)^101
        have hw : |(-4887710969/10000000000 : ℝ)|=(4887710969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1015172169/2500000000 : ℝ)|^133 ≤ (244164018331/800000000000 : ℝ)^101
        have hw : |(1015172169/2500000000 : ℝ)|=(1015172169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4060719999/10000000000 : ℝ)|^133 ≤ (30520812308819/100000000000000 : ℝ)^101
        have hw : |(4060719999/10000000000 : ℝ)|=(4060719999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s1_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4203451513/10000000000 : ℝ)*x 0 + (-3492208943/10000000000 : ℝ)*x 1 + (5271449011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203451513/10000000000 : ℝ)^133 ≤ (31941294350437/100000000000000 : ℝ)^101 := by
    have hnat : (4203451513 : ℕ)^133*100000000000000^101 ≤ 31941294350437^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203451513 10000000000 31941294350437 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3492208943/10000000000 : ℝ)^133 ≤ (25023029843931/100000000000000 : ℝ)^101 := by
    have hnat : (3492208943 : ℕ)^133*100000000000000^101 ≤ 25023029843931^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3492208943 10000000000 25023029843931 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271449011/10000000000 : ℝ)^133 ≤ (43035675795313/100000000000000 : ℝ)^101 := by
    have hnat : (5271449011 : ℕ)^133*100000000000000^101 ≤ 43035675795313^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271449011 10000000000 43035675795313 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203451513/10000000000 : ℝ), (-3492208943/10000000000 : ℝ), (5271449011/10000000000 : ℝ)] ![(31941294350437/100000000000000 : ℝ), (25023029843931/100000000000000 : ℝ), (43035675795313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203451513/10000000000 : ℝ)|^133 ≤ (31941294350437/100000000000000 : ℝ)^101
        have hw : |(4203451513/10000000000 : ℝ)|=(4203451513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3492208943/10000000000 : ℝ)|^133 ≤ (25023029843931/100000000000000 : ℝ)^101
        have hw : |(-3492208943/10000000000 : ℝ)|=(3492208943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271449011/10000000000 : ℝ)|^133 ≤ (43035675795313/100000000000000 : ℝ)^101
        have hw : |(5271449011/10000000000 : ℝ)|=(5271449011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s1_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2101713609/5000000000 : ℝ)*x 0 + (164733303/312500000 : ℝ)*x 1 + (-3492215697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101713609/5000000000 : ℝ)^133 ≤ (31941051245801/100000000000000 : ℝ)^101 := by
    have hnat : (2101713609 : ℕ)^133*100000000000000^101 ≤ 31941051245801^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101713609 5000000000 31941051245801 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164733303/312500000 : ℝ)^133 ≤ (21517927583793/50000000000000 : ℝ)^101 := by
    have hnat : (164733303 : ℕ)^133*50000000000000^101 ≤ 21517927583793^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164733303 312500000 21517927583793 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3492215697/10000000000 : ℝ)^133 ≤ (5004618714411/20000000000000 : ℝ)^101 := by
    have hnat : (3492215697 : ℕ)^133*20000000000000^101 ≤ 5004618714411^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3492215697 10000000000 5004618714411 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2101713609/5000000000 : ℝ), (164733303/312500000 : ℝ), (-3492215697/10000000000 : ℝ)] ![(31941051245801/100000000000000 : ℝ), (21517927583793/50000000000000 : ℝ), (5004618714411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2101713609/5000000000 : ℝ)|^133 ≤ (31941051245801/100000000000000 : ℝ)^101
        have hw : |(2101713609/5000000000 : ℝ)|=(2101713609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164733303/312500000 : ℝ)|^133 ≤ (21517927583793/50000000000000 : ℝ)^101
        have hw : |(164733303/312500000 : ℝ)|=(164733303/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3492215697/10000000000 : ℝ)|^133 ≤ (5004618714411/20000000000000 : ℝ)^101
        have hw : |(-3492215697/10000000000 : ℝ)|=(3492215697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304077_s1_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3706655247/10000000000 : ℝ)*x 0 + (4648470157/10000000000 : ℝ)*x 1 + (4648428577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3706655247/10000000000 : ℝ)^133 ≤ (27065876619779/100000000000000 : ℝ)^101 := by
    have hnat : (3706655247 : ℕ)^133*100000000000000^101 ≤ 27065876619779^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3706655247 10000000000 27065876619779 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4648470157/10000000000 : ℝ)^133 ≤ (18233638228027/50000000000000 : ℝ)^101 := by
    have hnat : (4648470157 : ℕ)^133*50000000000000^101 ≤ 18233638228027^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4648470157 10000000000 18233638228027 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4648428577/10000000000 : ℝ)^133 ≤ (36466846912289/100000000000000 : ℝ)^101 := by
    have hnat : (4648428577 : ℕ)^133*100000000000000^101 ≤ 36466846912289^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4648428577 10000000000 36466846912289 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3706655247/10000000000 : ℝ), (4648470157/10000000000 : ℝ), (4648428577/10000000000 : ℝ)] ![(27065876619779/100000000000000 : ℝ), (18233638228027/50000000000000 : ℝ), (36466846912289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3706655247/10000000000 : ℝ)|^133 ≤ (27065876619779/100000000000000 : ℝ)^101
        have hw : |(3706655247/10000000000 : ℝ)|=(3706655247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4648470157/10000000000 : ℝ)|^133 ≤ (18233638228027/50000000000000 : ℝ)^101
        have hw : |(4648470157/10000000000 : ℝ)|=(4648470157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4648428577/10000000000 : ℝ)|^133 ≤ (36466846912289/100000000000000 : ℝ)^101
        have hw : |(4648428577/10000000000 : ℝ)|=(4648428577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304077 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1115329327/2000000000 : ℝ)*X 0 0+(3745606819/10000000000 : ℝ)*X 0 1+(3617569377/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2254468893/5000000000 : ℝ)*X 2 0+(1366825699/2500000000 : ℝ)*X 2 1+(-1462473447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((422929883/2000000000 : ℝ)*X 0 0+(6816562427/10000000000 : ℝ)*X 0 1+(3668814473/10000000000 : ℝ)*X 0 2+(422929883/2000000000 : ℝ)*X 1 0+(6816562427/10000000000 : ℝ)*X 1 1+(3668814473/10000000000 : ℝ)*X 1 2+(422929883/2000000000 : ℝ)*X 2 0+(6816562427/10000000000 : ℝ)*X 2 1+(3668814473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-5705856967/10000000000 : ℝ)*X 0 0+(866547031/2500000000 : ℝ)*X 0 1+(3747215913/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3781591639/10000000000 : ℝ)*X 1 0+(-407552467/2000000000 : ℝ)*X 1 1+(6776153031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2131990809/5000000000 : ℝ)*X 2 0+(5794233301/10000000000 : ℝ)*X 2 1+(-112011639/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((226126979/1250000000 : ℝ)*X 0 0+(7360222121/10000000000 : ℝ)*X 0 1+(810384177/2500000000 : ℝ)*X 0 2+(226126979/1250000000 : ℝ)*X 1 0+(7360222121/10000000000 : ℝ)*X 1 1+(810384177/2500000000 : ℝ)*X 1 2+(226126979/1250000000 : ℝ)*X 2 0+(7360222121/10000000000 : ℝ)*X 2 1+(810384177/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-177356577/312500000 : ℝ)*X 0 0+(3769020693/10000000000 : ℝ)*X 0 1+(3479434401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((748695631/2000000000 : ℝ)*X 1 0+(-288618033/1250000000 : ℝ)*X 1 1+(413630023/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1097016941/2500000000 : ℝ)*X 2 0+(5462231597/10000000000 : ℝ)*X 2 1+(-1534036389/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((564695687/2500000000 : ℝ)*X 0 0+(6802609347/10000000000 : ℝ)*X 0 1+(3562967601/10000000000 : ℝ)*X 0 2+(564695687/2500000000 : ℝ)*X 1 0+(6802609347/10000000000 : ℝ)*X 1 1+(3562967601/10000000000 : ℝ)*X 1 2+(564695687/2500000000 : ℝ)*X 2 0+(6802609347/10000000000 : ℝ)*X 2 1+(3562967601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-5606019883/10000000000 : ℝ)*X 0 0+(385126927/1000000000 : ℝ)*X 0 1+(3475653563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((1832173559/5000000000 : ℝ)*X 1 0+(-560699857/2500000000 : ℝ)*X 1 1+(6730780571/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((600660303/1250000000 : ℝ)*X 2 0+(5137825761/10000000000 : ℝ)*X 2 1+(-2979207589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((1712411623/10000000000 : ℝ)*X 0 0+(299800631/400000000 : ℝ)*X 0 1+(1572704019/5000000000 : ℝ)*X 0 2+(1712411623/10000000000 : ℝ)*X 1 0+(299800631/400000000 : ℝ)*X 1 1+(1572704019/5000000000 : ℝ)*X 1 2+(1712411623/10000000000 : ℝ)*X 2 0+(299800631/400000000 : ℝ)*X 2 1+(1572704019/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((11723/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11723/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (226847590673142779427/25000000000000000000000000 : ℝ) := by norm_num
    linear_combination (212700401417/62500000000 : ℝ)*(base49) + (1275587243907/1000000000000 : ℝ)*(base50) + (544171911/250000000 : ℝ)*(base60) + (12639797063607/1000000000000 : ℝ)*(major_s0_0) + (12639797063607/1000000000000 : ℝ)*(major_s0_1) + (12639797063607/1000000000000 : ℝ)*(major_s0_2) + (239383739/1000000000000 : ℝ)*(sp_s0_0) + (93158671/1000000000000 : ℝ)*(sp_s0_6) + (16945712640027/1000000000000 : ℝ)*(sp_s0_7) + (338912020253/20000000000 : ℝ)*(sp_s0_8) + (16945766516419/1000000000000 : ℝ)*(sp_s0_9) + (1041693240017/125000000000 : ℝ)*(sp_s0_12) + (46376837/250000000000 : ℝ)*(sp_s0_15) + (351011117/1000000000000 : ℝ)*(sp_s0_21) + (4166819539403/500000000000 : ℝ)*(f.failure) + (8472976011883/500000000000 : ℝ)*(f.sum) + (258395712536031/2000000000000000000000000000 : ℝ)*base62 + (31011475742691/100000000000000000000000000 : ℝ)*base64 + (96547748610149/2000000000000000000000000000 : ℝ)*base67 + (583083620989851/2000000000000000000000000000 : ℝ)*base68 + (919891965463969/2000000000000000000000000000 : ℝ)*base70 + (53022566402691/100000000000000000000000000 : ℝ)*base72 + (4771725812691/100000000000000000000000000 : ℝ)*base75 + (1523074703210149/2000000000000000000000000000 : ℝ)*base76 + (121473749243671/2000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (2273/6250000000000000 : ℝ)*base86 + (2273/6250000000000000 : ℝ)*base88 + (2273/6250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((467/25000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(467/25000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11206086516077770459191/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2220267/1000000000000 : ℝ)*(base40) + (1215868826037/1000000000000 : ℝ)*(base49) + (718756905867/500000000000 : ℝ)*(base60) + (8648555142851/1000000000000 : ℝ)*(major_s0_0) + (8648555142851/1000000000000 : ℝ)*(major_s0_1) + (8648555142851/1000000000000 : ℝ)*(major_s0_2) + (18433919/250000000000 : ℝ)*(sp_s0_2) + (229757113/1000000000000 : ℝ)*(sp_s0_7) + (11594733257929/1000000000000 : ℝ)*(sp_s0_13) + (5797450380359/500000000000 : ℝ)*(sp_s0_14) + (11594793836413/1000000000000 : ℝ)*(sp_s0_15) + (2851071767647/500000000000 : ℝ)*(sp_s0_19) + (15563581/250000000000 : ℝ)*(sp_s0_21) + (95442953/1000000000000 : ℝ)*(sp_s0_22) + (2851071767647/500000000000 : ℝ)*(f.failure) + (5797481507521/500000000000 : ℝ)*(f.sum) + (1211400007955083/2000000000000000000000000000 : ℝ)*base62 + (12608422196463/100000000000000000000000000 : ℝ)*base64 + (648823952115657/2000000000000000000000000000 : ℝ)*base67 + (194115456284343/2000000000000000000000000000 : ℝ)*base68 + (1608265467844917/2000000000000000000000000000 : ℝ)*base70 + (68970686853537/100000000000000000000000000 : ℝ)*base73 + (66503885406463/100000000000000000000000000 : ℝ)*base75 + (598223787884343/2000000000000000000000000000 : ℝ)*base77 + (202099591813603/2000000000000000000000000000 : ℝ)*base78 + (723/6250000000000000 : ℝ)*base87 + (723/6250000000000000 : ℝ)*base89 + (723/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(307/2500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(307/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (22041998560693759227/3125000000000000000000000 : ℝ) := by norm_num
    linear_combination (2490548442299/1000000000000 : ℝ)*(base49) + (648755347131/500000000000 : ℝ)*(base50) + (2208532567/2000000000 : ℝ)*(base60) + (617897754719/62500000000 : ℝ)*(major_s0_0) + (617897754719/62500000000 : ℝ)*(major_s0_1) + (617897754719/62500000000 : ℝ)*(major_s0_2) + (146740561/500000000000 : ℝ)*(sp_s0_2) + (620528793/1000000000000 : ℝ)*(sp_s0_12) + (13785043/62500000000 : ℝ)*(sp_s0_13) + (275353713/500000000000 : ℝ)*(sp_s0_14) + (13254252644421/1000000000000 : ℝ)*(sp_s0_20) + (13253922497683/1000000000000 : ℝ)*(sp_s0_21) + (13254179723987/1000000000000 : ℝ)*(sp_s0_22) + (3258816032977/500000000000 : ℝ)*(sp_s0_25) + (6518252594747/1000000000000 : ℝ)*(f.failure) + (13254473205109/1000000000000 : ℝ)*(f.sum) + (70511288677773/125000000000000000000000000 : ℝ)*base63 + (580647924759/781250000000000000000000 : ℝ)*base64 + (81086575621167/125000000000000000000000000 : ℝ)*base66 + (62045564808667/125000000000000000000000000 : ℝ)*base68 + (66281246902773/125000000000000000000000000 : ℝ)*base70 + (566684552643/1562500000000000000000000 : ℝ)*base72 + (3244040738697/6250000000000000000000000 : ℝ)*base75 + (64948700991333/125000000000000000000000000 : ℝ)*base76 + (54134792595107/125000000000000000000000000 : ℝ)*base78 + (8373/12500000000000000 : ℝ)*base87 + (8373/12500000000000000 : ℝ)*base89 + (8373/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (11723/50000 : ℝ) ^ (33/8 : ℝ) ≤ (63019310375918519/25000000000000000000 : ℝ) := by
    have hpowers : (11723/50000 : ℝ)^33 ≤ (63019310375918519/25000000000000000000 : ℝ)^8 := by
      have hnat : (11723 : ℕ)^33*25000000000000000000^8 ≤ 63019310375918519^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11723 50000 63019310375918519 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11723/50000 : ℝ)) (X := (63019310375918519/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (25063019310375918519/25000000000000000000 : ℝ) ≤ (10006105137052319/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (25063019310375918519/25000000000000000000 : ℝ)^8 ≤ (10006105137052319/10000000000000000 : ℝ)^33 := by
      have hnat : (25063019310375918519 : ℕ)^8*10000000000000000^33 ≤ 10006105137052319^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25063019310375918519 25000000000000000000 10006105137052319 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006105137052319/10000000000000000 : ℝ)) (X := (25063019310375918519/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (12563019310375918519/12500000000000000000 : ℝ) ≤ (2002439731127671/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (12563019310375918519/12500000000000000000 : ℝ)^8 ≤ (2002439731127671/2000000000000000 : ℝ)^33 := by
      have hnat : (12563019310375918519 : ℕ)^8*2000000000000000^33 ≤ 2002439731127671^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12563019310375918519 12500000000000000000 2002439731127671 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002439731127671/2000000000000000 : ℝ)) (X := (12563019310375918519/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(6105137052319/2344600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1523379646509/586150000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (11723/50000 : ℝ)) (alpha := (6105137052319/2344600000000000 : ℝ)) (beta := (1523379646509/586150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11723/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(6105137052319/2344600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1523379646509/586150000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (467/25000 : ℝ) ^ (33/8 : ℝ) ≤ (7403372417231/100000000000000000000 : ℝ) := by
    have hpowers : (467/25000 : ℝ)^33 ≤ (7403372417231/100000000000000000000 : ℝ)^8 := by
      have hnat : (467 : ℕ)^33*100000000000000000000^8 ≤ 7403372417231^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        467 25000 7403372417231 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (467/25000 : ℝ)) (X := (7403372417231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100000007403372417231/100000000000000000000 : ℝ) ≤ (1000000017947569/1000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (100000007403372417231/100000000000000000000 : ℝ)^8 ≤ (1000000017947569/1000000000000000 : ℝ)^33 := by
      have hnat : (100000007403372417231 : ℕ)^8*1000000000000000^33 ≤ 1000000017947569^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100000007403372417231 100000000000000000000 1000000017947569 1000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000017947569/1000000000000000 : ℝ)) (X := (100000007403372417231/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50000007403372417231/50000000000000000000 : ℝ) ≤ (1000000035895137/1000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50000007403372417231/50000000000000000000 : ℝ)^8 ≤ (1000000035895137/1000000000000000 : ℝ)^33 := by
      have hnat : (50000007403372417231 : ℕ)^8*1000000000000000^33 ≤ 1000000035895137^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000007403372417231 50000000000000000000 1000000035895137 1000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000035895137/1000000000000000 : ℝ)) (X := (50000007403372417231/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(17947569/18680000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1121723/1167500000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (467/25000 : ℝ)) (alpha := (17947569/18680000000000 : ℝ)) (beta := (1121723/1167500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (467/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(17947569/18680000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1121723/1167500000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (307/2500 : ℝ) ^ (33/8 : ℝ) ≤ (17496181007741911/100000000000000000000 : ℝ) := by
    have hpowers : (307/2500 : ℝ)^33 ≤ (17496181007741911/100000000000000000000 : ℝ)^8 := by
      have hnat : (307 : ℕ)^33*100000000000000000000^8 ≤ 17496181007741911^8*2500^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        307 2500 17496181007741911 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (307/2500 : ℝ)) (X := (17496181007741911/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100017496181007741911/100000000000000000000 : ℝ) ≤ (2500106030433909/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (100017496181007741911/100000000000000000000 : ℝ)^8 ≤ (2500106030433909/2500000000000000 : ℝ)^33 := by
      have hnat : (100017496181007741911 : ℕ)^8*2500000000000000^33 ≤ 2500106030433909^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100017496181007741911 100000000000000000000 2500106030433909 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500106030433909/2500000000000000 : ℝ)) (X := (100017496181007741911/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50017496181007741911/50000000000000000000 : ℝ) ≤ (10000848187268839/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50017496181007741911/50000000000000000000 : ℝ)^8 ≤ (10000848187268839/10000000000000000 : ℝ)^33 := by
      have hnat : (50017496181007741911 : ℕ)^8*10000000000000000^33 ≤ 10000848187268839^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017496181007741911 50000000000000000000 10000848187268839 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000848187268839/10000000000000000 : ℝ)) (X := (50017496181007741911/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(106030433909/307000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(424065533203/1228000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (307/2500 : ℝ)) (alpha := (106030433909/307000000000000 : ℝ)) (beta := (424065533203/1228000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (307/2500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(106030433909/307000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(424065533203/1228000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-4887710969/10000000000 : ℝ)*X 0 0+(1015172169/2500000000 : ℝ)*X 0 1+(4060719999/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4203451513/10000000000 : ℝ)*X 1 0+(-3492208943/10000000000 : ℝ)*X 1 1+(5271449011/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2101713609/5000000000 : ℝ)*X 2 0+(164733303/312500000 : ℝ)*X 2 1+(-3492215697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3706655247/10000000000 : ℝ)*X 0 0+(4648470157/10000000000 : ℝ)*X 0 1+(4648428577/10000000000 : ℝ)*X 0 2+(3706655247/10000000000 : ℝ)*X 1 0+(4648470157/10000000000 : ℝ)*X 1 1+(4648428577/10000000000 : ℝ)*X 1 2+(3706655247/10000000000 : ℝ)*X 2 0+(4648470157/10000000000 : ℝ)*X 2 1+(4648428577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304077_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-38127/6250 : ℝ) < ((-18959/12500 : ℝ)*P 0+(-18959/12500 : ℝ)*P 1+(-18959/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-38127/6250 : ℝ) < (-25247288891330648420863701688413/4201786967500000000000000000000 : ℝ) := by norm_num
    linear_combination (92401/1000000000000 : ℝ)*(base11) + (2981/50000000000 : ℝ)*(base19) + (25307/250000000000 : ℝ)*(base23) + (1769/1000000000000 : ℝ)*(base40) + (135675495133/250000000000 : ℝ)*(base49) + (23855374223/100000000000 : ℝ)*(base50) + (8067497659/125000000000 : ℝ)*(base59) + (303620973319/1000000000000 : ℝ)*(base60) + (18959/12500 : ℝ)*(major_s1_0) + (18959/12500 : ℝ)*(major_s1_1) + (18959/12500 : ℝ)*(major_s1_2) + (400580164611/200000000000 : ℝ)*(sp_s1_0) + (500725213959/250000000000 : ℝ)*(sp_s1_1) + (500725203557/250000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (7823831701/3906250000 : ℝ)*(f.sum) + (267204266519229/286738000000000000000000000 : ℝ)*base62 + (201497986513/153500000000000000000000 : ℝ)*base64 + (311230233337/934000000000000000000000 : ℝ)*base67 + (333278079869/767500000000000000000000 : ℝ)*base68 + (5785207322765143/8997402500000000000000000000 : ℝ)*base70 + (19197607947927/29307500000000000000000000 : ℝ)*base72 + (186444068471/583750000000000000000000 : ℝ)*base74 + (2275766183/915859375000000000000000 : ℝ)*base76 + (1890238005913211/13686602500000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p004_b034 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (c : Fin 88) (hlo : 77 ≤ c.val) (hhi : c.val < 78)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=77 := by omega
  rcases hc with rfl
  · exact collision_c304077 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (c : Fin 88) (hlo : 77 ≤ c.val) (hhi : c.val < 78)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p004_b034 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

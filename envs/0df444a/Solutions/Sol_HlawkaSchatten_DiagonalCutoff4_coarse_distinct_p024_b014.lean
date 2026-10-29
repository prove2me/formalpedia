-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b014
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:56:06.447727+00:00
-- url     : https://prove2.me/submissions/be787a38-9c3e-46b3-bcd6-5e01fed437d7

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
theorem collision_support_c324031_s0_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (321728279/500000000 : ℝ)*x 0 + (48067/10000000000 : ℝ)*x 1 + (2459338629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (321728279/500000000 : ℝ)^43 ≤ (29088558697971/50000000000000 : ℝ)^35 := by
    have hnat : (321728279 : ℕ)^43*50000000000000^35 ≤ 29088558697971^35*500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321728279 500000000 29088558697971 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48067/10000000000 : ℝ)^43 ≤ (5851931/20000000000000 : ℝ)^35 := by
    have hnat : (48067 : ℕ)^43*20000000000000^35 ≤ 5851931^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48067 10000000000 5851931 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2459338629/5000000000 : ℝ)^43 ≤ (52278566663/125000000000 : ℝ)^35 := by
    have hnat : (2459338629 : ℕ)^43*125000000000^35 ≤ 52278566663^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2459338629 5000000000 52278566663 125000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(321728279/500000000 : ℝ), (48067/10000000000 : ℝ), (2459338629/5000000000 : ℝ)] ![(29088558697971/50000000000000 : ℝ), (5851931/20000000000000 : ℝ), (52278566663/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(321728279/500000000 : ℝ)|^43 ≤ (29088558697971/50000000000000 : ℝ)^35
        have hw : |(321728279/500000000 : ℝ)|=(321728279/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48067/10000000000 : ℝ)|^43 ≤ (5851931/20000000000000 : ℝ)^35
        have hw : |(48067/10000000000 : ℝ)|=(48067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2459338629/5000000000 : ℝ)|^43 ≤ (52278566663/125000000000 : ℝ)^35
        have hw : |(2459338629/5000000000 : ℝ)|=(2459338629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s0_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1295211261/5000000000 : ℝ)*x 0 + (6326281087/10000000000 : ℝ)*x 1 + (-312984747/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1295211261/5000000000 : ℝ)^43 ≤ (3804642760663/20000000000000 : ℝ)^35 := by
    have hnat : (1295211261 : ℕ)^43*20000000000000^35 ≤ 3804642760663^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295211261 5000000000 3804642760663 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6326281087/10000000000 : ℝ)^43 ≤ (28488311786389/50000000000000 : ℝ)^35 := by
    have hnat : (6326281087 : ℕ)^43*50000000000000^35 ≤ 28488311786389^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6326281087 10000000000 28488311786389 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (312984747/1000000000 : ℝ)^43 ≤ (24000162606227/100000000000000 : ℝ)^35 := by
    have hnat : (312984747 : ℕ)^43*100000000000000^35 ≤ 24000162606227^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312984747 1000000000 24000162606227 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1295211261/5000000000 : ℝ), (6326281087/10000000000 : ℝ), (-312984747/1000000000 : ℝ)] ![(3804642760663/20000000000000 : ℝ), (28488311786389/50000000000000 : ℝ), (24000162606227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1295211261/5000000000 : ℝ)|^43 ≤ (3804642760663/20000000000000 : ℝ)^35
        have hw : |(1295211261/5000000000 : ℝ)|=(1295211261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6326281087/10000000000 : ℝ)|^43 ≤ (28488311786389/50000000000000 : ℝ)^35
        have hw : |(6326281087/10000000000 : ℝ)|=(6326281087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-312984747/1000000000 : ℝ)|^43 ≤ (24000162606227/100000000000000 : ℝ)^35
        have hw : |(-312984747/1000000000 : ℝ)|=(312984747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s0_7 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-166855807/500000000 : ℝ)*x 0 + (440996709/2000000000 : ℝ)*x 1 + (6456907973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166855807/500000000 : ℝ)^43 ≤ (25967349515409/100000000000000 : ℝ)^35 := by
    have hnat : (166855807 : ℕ)^43*100000000000000^35 ≤ 25967349515409^35*500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166855807 500000000 25967349515409 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440996709/2000000000 : ℝ)^43 ≤ (7803628401299/50000000000000 : ℝ)^35 := by
    have hnat : (440996709 : ℕ)^43*50000000000000^35 ≤ 7803628401299^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440996709 2000000000 7803628401299 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6456907973/10000000000 : ℝ)^43 ≤ (58425393669109/100000000000000 : ℝ)^35 := by
    have hnat : (6456907973 : ℕ)^43*100000000000000^35 ≤ 58425393669109^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6456907973 10000000000 58425393669109 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-166855807/500000000 : ℝ), (440996709/2000000000 : ℝ), (6456907973/10000000000 : ℝ)] ![(25967349515409/100000000000000 : ℝ), (7803628401299/50000000000000 : ℝ), (58425393669109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-166855807/500000000 : ℝ)|^43 ≤ (25967349515409/100000000000000 : ℝ)^35
        have hw : |(-166855807/500000000 : ℝ)|=(166855807/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(440996709/2000000000 : ℝ)|^43 ≤ (7803628401299/50000000000000 : ℝ)^35
        have hw : |(440996709/2000000000 : ℝ)|=(440996709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6456907973/10000000000 : ℝ)|^43 ≤ (58425393669109/100000000000000 : ℝ)^35
        have hw : |(6456907973/10000000000 : ℝ)|=(6456907973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s0_8 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2375211879/5000000000 : ℝ)*x 0 + (97701/2000000000 : ℝ)*x 1 + (6591695603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2375211879/5000000000 : ℝ)^43 ≤ (20036073148051/50000000000000 : ℝ)^35 := by
    have hnat : (2375211879 : ℕ)^43*50000000000000^35 ≤ 20036073148051^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2375211879 5000000000 20036073148051 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97701/2000000000 : ℝ)^43 ≤ (252602503/50000000000000 : ℝ)^35 := by
    have hnat : (97701 : ℕ)^43*50000000000000^35 ≤ 252602503^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97701 2000000000 252602503 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6591695603/10000000000 : ℝ)^43 ≤ (29963674241847/50000000000000 : ℝ)^35 := by
    have hnat : (6591695603 : ℕ)^43*50000000000000^35 ≤ 29963674241847^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6591695603 10000000000 29963674241847 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2375211879/5000000000 : ℝ), (97701/2000000000 : ℝ), (6591695603/10000000000 : ℝ)] ![(20036073148051/50000000000000 : ℝ), (252602503/50000000000000 : ℝ), (29963674241847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2375211879/5000000000 : ℝ)|^43 ≤ (20036073148051/50000000000000 : ℝ)^35
        have hw : |(2375211879/5000000000 : ℝ)|=(2375211879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(97701/2000000000 : ℝ)|^43 ≤ (252602503/50000000000000 : ℝ)^35
        have hw : |(97701/2000000000 : ℝ)|=(97701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6591695603/10000000000 : ℝ)|^43 ≤ (29963674241847/50000000000000 : ℝ)^35
        have hw : |(6591695603/10000000000 : ℝ)|=(6591695603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s0_9 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (962928751/10000000000 : ℝ)*x 0 + (1060071713/1250000000 : ℝ)*x 1 + (-1863148321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (962928751/10000000000 : ℝ)^43 ≤ (1409979591077/25000000000000 : ℝ)^35 := by
    have hnat : (962928751 : ℕ)^43*25000000000000^35 ≤ 1409979591077^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962928751 10000000000 1409979591077 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060071713/1250000000 : ℝ)^43 ≤ (81670513491961/100000000000000 : ℝ)^35 := by
    have hnat : (1060071713 : ℕ)^43*100000000000000^35 ≤ 81670513491961^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060071713 1250000000 81670513491961 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1863148321/10000000000 : ℝ)^43 ≤ (6344784066739/50000000000000 : ℝ)^35 := by
    have hnat : (1863148321 : ℕ)^43*50000000000000^35 ≤ 6344784066739^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863148321 10000000000 6344784066739 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(962928751/10000000000 : ℝ), (1060071713/1250000000 : ℝ), (-1863148321/10000000000 : ℝ)] ![(1409979591077/25000000000000 : ℝ), (81670513491961/100000000000000 : ℝ), (6344784066739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(962928751/10000000000 : ℝ)|^43 ≤ (1409979591077/25000000000000 : ℝ)^35
        have hw : |(962928751/10000000000 : ℝ)|=(962928751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060071713/1250000000 : ℝ)|^43 ≤ (81670513491961/100000000000000 : ℝ)^35
        have hw : |(1060071713/1250000000 : ℝ)|=(1060071713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1863148321/10000000000 : ℝ)|^43 ≤ (6344784066739/50000000000000 : ℝ)^35
        have hw : |(-1863148321/10000000000 : ℝ)|=(1863148321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s0_13 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (543141413/2500000000 : ℝ)*x 0 + (3377416611/5000000000 : ℝ)*x 1 + (3014655573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543141413/2500000000 : ℝ)^43 ≤ (7662912457071/50000000000000 : ℝ)^35 := by
    have hnat : (543141413 : ℕ)^43*50000000000000^35 ≤ 7662912457071^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543141413 2500000000 7662912457071 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3377416611/5000000000 : ℝ)^43 ≤ (15438653213053/25000000000000 : ℝ)^35 := by
    have hnat : (3377416611 : ℕ)^43*25000000000000^35 ≤ 15438653213053^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3377416611 5000000000 15438653213053 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3014655573/10000000000 : ℝ)^43 ≤ (22919562223957/100000000000000 : ℝ)^35 := by
    have hnat : (3014655573 : ℕ)^43*100000000000000^35 ≤ 22919562223957^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3014655573 10000000000 22919562223957 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543141413/2500000000 : ℝ), (3377416611/5000000000 : ℝ), (3014655573/10000000000 : ℝ)] ![(7662912457071/50000000000000 : ℝ), (15438653213053/25000000000000 : ℝ), (22919562223957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543141413/2500000000 : ℝ)|^43 ≤ (7662912457071/50000000000000 : ℝ)^35
        have hw : |(543141413/2500000000 : ℝ)|=(543141413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3377416611/5000000000 : ℝ)|^43 ≤ (15438653213053/25000000000000 : ℝ)^35
        have hw : |(3377416611/5000000000 : ℝ)|=(3377416611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3014655573/10000000000 : ℝ)|^43 ≤ (22919562223957/100000000000000 : ℝ)^35
        have hw : |(3014655573/10000000000 : ℝ)|=(3014655573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s0_14 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4724738789/10000000000 : ℝ)*x 0 + (682642563/2500000000 : ℝ)*x 1 + (2366831157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4724738789/10000000000 : ℝ)^43 ≤ (39806122253617/100000000000000 : ℝ)^35 := by
    have hnat : (4724738789 : ℕ)^43*100000000000000^35 ≤ 39806122253617^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4724738789 10000000000 39806122253617 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682642563/2500000000 : ℝ)^43 ≤ (20295370241797/100000000000000 : ℝ)^35 := by
    have hnat : (682642563 : ℕ)^43*100000000000000^35 ≤ 20295370241797^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682642563 2500000000 20295370241797 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2366831157/5000000000 : ℝ)^43 ≤ (39898507497959/100000000000000 : ℝ)^35 := by
    have hnat : (2366831157 : ℕ)^43*100000000000000^35 ≤ 39898507497959^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2366831157 5000000000 39898507497959 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4724738789/10000000000 : ℝ), (682642563/2500000000 : ℝ), (2366831157/5000000000 : ℝ)] ![(39806122253617/100000000000000 : ℝ), (20295370241797/100000000000000 : ℝ), (39898507497959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4724738789/10000000000 : ℝ)|^43 ≤ (39806122253617/100000000000000 : ℝ)^35
        have hw : |(-4724738789/10000000000 : ℝ)|=(4724738789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682642563/2500000000 : ℝ)|^43 ≤ (20295370241797/100000000000000 : ℝ)^35
        have hw : |(682642563/2500000000 : ℝ)|=(682642563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2366831157/5000000000 : ℝ)|^43 ≤ (39898507497959/100000000000000 : ℝ)^35
        have hw : |(2366831157/5000000000 : ℝ)|=(2366831157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s0_15 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8482726411/10000000000 : ℝ)*x 0 + (4087551/10000000000 : ℝ)*x 1 + (501931391/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8482726411/10000000000 : ℝ)^43 ≤ (20423996005541/25000000000000 : ℝ)^35 := by
    have hnat : (8482726411 : ℕ)^43*25000000000000^35 ≤ 20423996005541^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8482726411 10000000000 20423996005541 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4087551/10000000000 : ℝ)^43 ≤ (429358931/6250000000000 : ℝ)^35 := by
    have hnat : (4087551 : ℕ)^43*6250000000000^35 ≤ 429358931^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4087551 10000000000 429358931 6250000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501931391/2000000000 : ℝ)^43 ≤ (9148573112089/50000000000000 : ℝ)^35 := by
    have hnat : (501931391 : ℕ)^43*50000000000000^35 ≤ 9148573112089^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501931391 2000000000 9148573112089 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8482726411/10000000000 : ℝ), (4087551/10000000000 : ℝ), (501931391/2000000000 : ℝ)] ![(20423996005541/25000000000000 : ℝ), (429358931/6250000000000 : ℝ), (9148573112089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8482726411/10000000000 : ℝ)|^43 ≤ (20423996005541/25000000000000 : ℝ)^35
        have hw : |(8482726411/10000000000 : ℝ)|=(8482726411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4087551/10000000000 : ℝ)|^43 ≤ (429358931/6250000000000 : ℝ)^35
        have hw : |(4087551/10000000000 : ℝ)|=(4087551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(501931391/2000000000 : ℝ)|^43 ≤ (9148573112089/50000000000000 : ℝ)^35
        have hw : |(501931391/2000000000 : ℝ)|=(501931391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s0_16 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (348524503/5000000000 : ℝ)*x 0 + (406965689/625000000 : ℝ)*x 1 + (-4469005877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (348524503/5000000000 : ℝ)^43 ≤ (1895991383673/50000000000000 : ℝ)^35 := by
    have hnat : (348524503 : ℕ)^43*50000000000000^35 ≤ 1895991383673^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348524503 5000000000 1895991383673 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (406965689/625000000 : ℝ)^43 ≤ (29516159349383/50000000000000 : ℝ)^35 := by
    have hnat : (406965689 : ℕ)^43*50000000000000^35 ≤ 29516159349383^35*625000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406965689 625000000 29516159349383 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4469005877/10000000000 : ℝ)^43 ≤ (580870289187/1562500000000 : ℝ)^35 := by
    have hnat : (4469005877 : ℕ)^43*1562500000000^35 ≤ 580870289187^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4469005877 10000000000 580870289187 1562500000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(348524503/5000000000 : ℝ), (406965689/625000000 : ℝ), (-4469005877/10000000000 : ℝ)] ![(1895991383673/50000000000000 : ℝ), (29516159349383/50000000000000 : ℝ), (580870289187/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(348524503/5000000000 : ℝ)|^43 ≤ (1895991383673/50000000000000 : ℝ)^35
        have hw : |(348524503/5000000000 : ℝ)|=(348524503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(406965689/625000000 : ℝ)|^43 ≤ (29516159349383/50000000000000 : ℝ)^35
        have hw : |(406965689/625000000 : ℝ)|=(406965689/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4469005877/10000000000 : ℝ)|^43 ≤ (580870289187/1562500000000 : ℝ)^35
        have hw : |(-4469005877/10000000000 : ℝ)|=(4469005877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s0_20 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (17377057/78125000 : ℝ)*x 0 + (539012663/1250000000 : ℝ)*x 1 + (5562537873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17377057/78125000 : ℝ)^43 ≤ (15775081491293/100000000000000 : ℝ)^35 := by
    have hnat : (17377057 : ℕ)^43*100000000000000^35 ≤ 15775081491293^35*78125000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17377057 78125000 15775081491293 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539012663/1250000000 : ℝ)^43 ≤ (7115727093727/20000000000000 : ℝ)^35 := by
    have hnat : (539012663 : ℕ)^43*20000000000000^35 ≤ 7115727093727^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539012663 1250000000 7115727093727 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5562537873/10000000000 : ℝ)^43 ≤ (304039268957/625000000000 : ℝ)^35 := by
    have hnat : (5562537873 : ℕ)^43*625000000000^35 ≤ 304039268957^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5562537873 10000000000 304039268957 625000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17377057/78125000 : ℝ), (539012663/1250000000 : ℝ), (5562537873/10000000000 : ℝ)] ![(15775081491293/100000000000000 : ℝ), (7115727093727/20000000000000 : ℝ), (304039268957/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17377057/78125000 : ℝ)|^43 ≤ (15775081491293/100000000000000 : ℝ)^35
        have hw : |(17377057/78125000 : ℝ)|=(17377057/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539012663/1250000000 : ℝ)|^43 ≤ (7115727093727/20000000000000 : ℝ)^35
        have hw : |(539012663/1250000000 : ℝ)|=(539012663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5562537873/10000000000 : ℝ)|^43 ≤ (304039268957/625000000000 : ℝ)^35
        have hw : |(5562537873/10000000000 : ℝ)|=(5562537873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s0_21 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-886015973/5000000000 : ℝ)*x 0 + (321539953/500000000 : ℝ)*x 1 + (3746396201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (886015973/5000000000 : ℝ)^43 ≤ (11931460695401/100000000000000 : ℝ)^35 := by
    have hnat : (886015973 : ℕ)^43*100000000000000^35 ≤ 11931460695401^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886015973 5000000000 11931460695401 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321539953/500000000 : ℝ)^43 ≤ (58135281931231/100000000000000 : ℝ)^35 := by
    have hnat : (321539953 : ℕ)^43*100000000000000^35 ≤ 58135281931231^35*500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321539953 500000000 58135281931231 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3746396201/10000000000 : ℝ)^43 ≤ (29933257359927/100000000000000 : ℝ)^35 := by
    have hnat : (3746396201 : ℕ)^43*100000000000000^35 ≤ 29933257359927^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3746396201 10000000000 29933257359927 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-886015973/5000000000 : ℝ), (321539953/500000000 : ℝ), (3746396201/10000000000 : ℝ)] ![(11931460695401/100000000000000 : ℝ), (58135281931231/100000000000000 : ℝ), (29933257359927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-886015973/5000000000 : ℝ)|^43 ≤ (11931460695401/100000000000000 : ℝ)^35
        have hw : |(-886015973/5000000000 : ℝ)|=(886015973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321539953/500000000 : ℝ)|^43 ≤ (58135281931231/100000000000000 : ℝ)^35
        have hw : |(321539953/500000000 : ℝ)|=(321539953/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3746396201/10000000000 : ℝ)|^43 ≤ (29933257359927/100000000000000 : ℝ)^35
        have hw : |(3746396201/10000000000 : ℝ)|=(3746396201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s0_22 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4285811443/5000000000 : ℝ)*x 0 + (0 : ℝ)*x 1 + (149513587/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4285811443/5000000000 : ℝ)^43 ≤ (41374540832721/50000000000000 : ℝ)^35 := by
    have hnat : (4285811443 : ℕ)^43*50000000000000^35 ≤ 41374540832721^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285811443 5000000000 41374540832721 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^43 ≤ (0 : ℝ)^35 := by
    have hnat : (0 : ℕ)^43*1^35 ≤ 0^35*1^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149513587/625000000 : ℝ)^43 ≤ (2156364791327/12500000000000 : ℝ)^35 := by
    have hnat : (149513587 : ℕ)^43*12500000000000^35 ≤ 2156364791327^35*625000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149513587 625000000 2156364791327 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4285811443/5000000000 : ℝ), (0 : ℝ), (149513587/625000000 : ℝ)] ![(41374540832721/50000000000000 : ℝ), (0 : ℝ), (2156364791327/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4285811443/5000000000 : ℝ)|^43 ≤ (41374540832721/50000000000000 : ℝ)^35
        have hw : |(4285811443/5000000000 : ℝ)|=(4285811443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^43 ≤ (0 : ℝ)^35
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(149513587/625000000 : ℝ)|^43 ≤ (2156364791327/12500000000000 : ℝ)^35
        have hw : |(149513587/625000000 : ℝ)|=(149513587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s0_23 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (726401593/10000000000 : ℝ)*x 0 + (4116900333/5000000000 : ℝ)*x 1 + (-239214853/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (726401593/10000000000 : ℝ)^43 ≤ (249318414723/6250000000000 : ℝ)^35 := by
    have hnat : (726401593 : ℕ)^43*6250000000000^35 ≤ 249318414723^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726401593 10000000000 249318414723 6250000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4116900333/5000000000 : ℝ)^43 ≤ (39380298555971/50000000000000 : ℝ)^35 := by
    have hnat : (4116900333 : ℕ)^43*50000000000000^35 ≤ 39380298555971^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116900333 5000000000 39380298555971 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239214853/1000000000 : ℝ)^43 ≤ (17250308245837/100000000000000 : ℝ)^35 := by
    have hnat : (239214853 : ℕ)^43*100000000000000^35 ≤ 17250308245837^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239214853 1000000000 17250308245837 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(726401593/10000000000 : ℝ), (4116900333/5000000000 : ℝ), (-239214853/1000000000 : ℝ)] ![(249318414723/6250000000000 : ℝ), (39380298555971/50000000000000 : ℝ), (17250308245837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(726401593/10000000000 : ℝ)|^43 ≤ (249318414723/6250000000000 : ℝ)^35
        have hw : |(726401593/10000000000 : ℝ)|=(726401593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4116900333/5000000000 : ℝ)|^43 ≤ (39380298555971/50000000000000 : ℝ)^35
        have hw : |(4116900333/5000000000 : ℝ)|=(4116900333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-239214853/1000000000 : ℝ)|^43 ≤ (17250308245837/100000000000000 : ℝ)^35
        have hw : |(-239214853/1000000000 : ℝ)|=(239214853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s0_27 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6419012653/10000000000 : ℝ)*x 0 + (3150163853/10000000000 : ℝ)*x 1 + (613612309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6419012653/10000000000 : ℝ)^43 ≤ (58004404227379/100000000000000 : ℝ)^35 := by
    have hnat : (6419012653 : ℕ)^43*100000000000000^35 ≤ 58004404227379^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6419012653 10000000000 58004404227379 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3150163853/10000000000 : ℝ)^43 ≤ (24191702542717/100000000000000 : ℝ)^35 := by
    have hnat : (3150163853 : ℕ)^43*100000000000000^35 ≤ 24191702542717^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3150163853 10000000000 24191702542717 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (613612309/2500000000 : ℝ)^43 ≤ (4450973305387/25000000000000 : ℝ)^35 := by
    have hnat : (613612309 : ℕ)^43*25000000000000^35 ≤ 4450973305387^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613612309 2500000000 4450973305387 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6419012653/10000000000 : ℝ), (3150163853/10000000000 : ℝ), (613612309/2500000000 : ℝ)] ![(58004404227379/100000000000000 : ℝ), (24191702542717/100000000000000 : ℝ), (4450973305387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6419012653/10000000000 : ℝ)|^43 ≤ (58004404227379/100000000000000 : ℝ)^35
        have hw : |(6419012653/10000000000 : ℝ)|=(6419012653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3150163853/10000000000 : ℝ)|^43 ≤ (24191702542717/100000000000000 : ℝ)^35
        have hw : |(3150163853/10000000000 : ℝ)|=(3150163853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(613612309/2500000000 : ℝ)|^43 ≤ (4450973305387/25000000000000 : ℝ)^35
        have hw : |(613612309/2500000000 : ℝ)|=(613612309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s1_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3354966019/10000000000 : ℝ)*x 0 + (5264113297/10000000000 : ℝ)*x 1 + (3589648419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3354966019/10000000000 : ℝ)^43 ≤ (26138098067523/100000000000000 : ℝ)^35 := by
    have hnat : (3354966019 : ℕ)^43*100000000000000^35 ≤ 26138098067523^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3354966019 10000000000 26138098067523 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264113297/10000000000 : ℝ)^43 ≤ (2841241532067/6250000000000 : ℝ)^35 := by
    have hnat : (5264113297 : ℕ)^43*6250000000000^35 ≤ 2841241532067^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264113297 10000000000 2841241532067 6250000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3589648419/10000000000 : ℝ)^43 ≤ (7100509350757/25000000000000 : ℝ)^35 := by
    have hnat : (3589648419 : ℕ)^43*25000000000000^35 ≤ 7100509350757^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3589648419 10000000000 7100509350757 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3354966019/10000000000 : ℝ), (5264113297/10000000000 : ℝ), (3589648419/10000000000 : ℝ)] ![(26138098067523/100000000000000 : ℝ), (2841241532067/6250000000000 : ℝ), (7100509350757/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3354966019/10000000000 : ℝ)|^43 ≤ (26138098067523/100000000000000 : ℝ)^35
        have hw : |(-3354966019/10000000000 : ℝ)|=(3354966019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264113297/10000000000 : ℝ)|^43 ≤ (2841241532067/6250000000000 : ℝ)^35
        have hw : |(5264113297/10000000000 : ℝ)|=(5264113297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3589648419/10000000000 : ℝ)|^43 ≤ (7100509350757/25000000000000 : ℝ)^35
        have hw : |(3589648419/10000000000 : ℝ)|=(3589648419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s1_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1124887933/2000000000 : ℝ)*x 0 + (-92072507/1000000000 : ℝ)*x 1 + (656719671/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1124887933/2000000000 : ℝ)^43 ≤ (6164027041663/12500000000000 : ℝ)^35 := by
    have hnat : (1124887933 : ℕ)^43*12500000000000^35 ≤ 6164027041663^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124887933 2000000000 6164027041663 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92072507/1000000000 : ℝ)^43 ≤ (5337767777047/100000000000000 : ℝ)^35 := by
    have hnat : (92072507 : ℕ)^43*100000000000000^35 ≤ 5337767777047^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92072507 1000000000 5337767777047 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656719671/1250000000 : ℝ)^43 ≤ (11337503968453/25000000000000 : ℝ)^35 := by
    have hnat : (656719671 : ℕ)^43*25000000000000^35 ≤ 11337503968453^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656719671 1250000000 11337503968453 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1124887933/2000000000 : ℝ), (-92072507/1000000000 : ℝ), (656719671/1250000000 : ℝ)] ![(6164027041663/12500000000000 : ℝ), (5337767777047/100000000000000 : ℝ), (11337503968453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1124887933/2000000000 : ℝ)|^43 ≤ (6164027041663/12500000000000 : ℝ)^35
        have hw : |(1124887933/2000000000 : ℝ)|=(1124887933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-92072507/1000000000 : ℝ)|^43 ≤ (5337767777047/100000000000000 : ℝ)^35
        have hw : |(-92072507/1000000000 : ℝ)|=(92072507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656719671/1250000000 : ℝ)|^43 ≤ (11337503968453/25000000000000 : ℝ)^35
        have hw : |(656719671/1250000000 : ℝ)|=(656719671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s1_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3165870811/10000000000 : ℝ)*x 0 + (5615119697/10000000000 : ℝ)*x 1 + (-1693662929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3165870811/10000000000 : ℝ)^43 ≤ (24339979229759/100000000000000 : ℝ)^35 := by
    have hnat : (3165870811 : ℕ)^43*100000000000000^35 ≤ 24339979229759^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3165870811 10000000000 24339979229759 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5615119697/10000000000 : ℝ)^43 ≤ (24605922718293/50000000000000 : ℝ)^35 := by
    have hnat : (5615119697 : ℕ)^43*50000000000000^35 ≤ 24605922718293^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5615119697 10000000000 24605922718293 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1693662929/5000000000 : ℝ)^43 ≤ (26448175322197/100000000000000 : ℝ)^35 := by
    have hnat : (1693662929 : ℕ)^43*100000000000000^35 ≤ 26448175322197^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693662929 5000000000 26448175322197 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3165870811/10000000000 : ℝ), (5615119697/10000000000 : ℝ), (-1693662929/5000000000 : ℝ)] ![(24339979229759/100000000000000 : ℝ), (24605922718293/50000000000000 : ℝ), (26448175322197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3165870811/10000000000 : ℝ)|^43 ≤ (24339979229759/100000000000000 : ℝ)^35
        have hw : |(3165870811/10000000000 : ℝ)|=(3165870811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5615119697/10000000000 : ℝ)|^43 ≤ (24605922718293/50000000000000 : ℝ)^35
        have hw : |(5615119697/10000000000 : ℝ)|=(5615119697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1693662929/5000000000 : ℝ)|^43 ≤ (26448175322197/100000000000000 : ℝ)^35
        have hw : |(-1693662929/5000000000 : ℝ)|=(1693662929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324031_s1_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3825416849/10000000000 : ℝ)*x 0 + (4844182031/10000000000 : ℝ)*x 1 + (3573300303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3825416849/10000000000 : ℝ)^43 ≤ (119964042089/390625000000 : ℝ)^35 := by
    have hnat : (3825416849 : ℕ)^43*390625000000^35 ≤ 119964042089^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3825416849 10000000000 119964042089 390625000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4844182031/10000000000 : ℝ)^43 ≤ (5130750036951/12500000000000 : ℝ)^35 := by
    have hnat : (4844182031 : ℕ)^43*12500000000000^35 ≤ 5130750036951^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4844182031 10000000000 5130750036951 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3573300303/10000000000 : ℝ)^43 ≤ (7060801229149/25000000000000 : ℝ)^35 := by
    have hnat : (3573300303 : ℕ)^43*25000000000000^35 ≤ 7060801229149^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3573300303 10000000000 7060801229149 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3825416849/10000000000 : ℝ), (4844182031/10000000000 : ℝ), (3573300303/10000000000 : ℝ)] ![(119964042089/390625000000 : ℝ), (5130750036951/12500000000000 : ℝ), (7060801229149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3825416849/10000000000 : ℝ)|^43 ≤ (119964042089/390625000000 : ℝ)^35
        have hw : |(3825416849/10000000000 : ℝ)|=(3825416849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4844182031/10000000000 : ℝ)|^43 ≤ (5130750036951/12500000000000 : ℝ)^35
        have hw : |(4844182031/10000000000 : ℝ)|=(4844182031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3573300303/10000000000 : ℝ)|^43 ≤ (7060801229149/25000000000000 : ℝ)^35
        have hw : |(3573300303/10000000000 : ℝ)|=(3573300303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324031 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (83049/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((321728279/500000000 : ℝ)*X 1 0+(48067/10000000000 : ℝ)*X 1 1+(2459338629/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1295211261/5000000000 : ℝ)*X 2 0+(6326281087/10000000000 : ℝ)*X 2 1+(-312984747/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-166855807/500000000 : ℝ)*X 0 0+(440996709/2000000000 : ℝ)*X 0 1+(6456907973/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2375211879/5000000000 : ℝ)*X 1 0+(97701/2000000000 : ℝ)*X 1 1+(6591695603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((962928751/10000000000 : ℝ)*X 2 0+(1060071713/1250000000 : ℝ)*X 2 1+(-1863148321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((543141413/2500000000 : ℝ)*X 0 0+(3377416611/5000000000 : ℝ)*X 0 1+(3014655573/10000000000 : ℝ)*X 0 2+(543141413/2500000000 : ℝ)*X 1 0+(3377416611/5000000000 : ℝ)*X 1 1+(3014655573/10000000000 : ℝ)*X 1 2+(543141413/2500000000 : ℝ)*X 2 0+(3377416611/5000000000 : ℝ)*X 2 1+(3014655573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-4724738789/10000000000 : ℝ)*X 0 0+(682642563/2500000000 : ℝ)*X 0 1+(2366831157/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((8482726411/10000000000 : ℝ)*X 1 0+(4087551/10000000000 : ℝ)*X 1 1+(501931391/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((348524503/5000000000 : ℝ)*X 2 0+(406965689/625000000 : ℝ)*X 2 1+(-4469005877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((17377057/78125000 : ℝ)*X 0 0+(539012663/1250000000 : ℝ)*X 0 1+(5562537873/10000000000 : ℝ)*X 0 2+(17377057/78125000 : ℝ)*X 1 0+(539012663/1250000000 : ℝ)*X 1 1+(5562537873/10000000000 : ℝ)*X 1 2+(17377057/78125000 : ℝ)*X 2 0+(539012663/1250000000 : ℝ)*X 2 1+(5562537873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-886015973/5000000000 : ℝ)*X 0 0+(321539953/500000000 : ℝ)*X 0 1+(3746396201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4285811443/5000000000 : ℝ)*X 1 0+(149513587/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((726401593/10000000000 : ℝ)*X 2 0+(4116900333/5000000000 : ℝ)*X 2 1+(-239214853/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((6419012653/10000000000 : ℝ)*X 0 0+(3150163853/10000000000 : ℝ)*X 0 1+(613612309/2500000000 : ℝ)*X 0 2+(6419012653/10000000000 : ℝ)*X 1 0+(3150163853/10000000000 : ℝ)*X 1 1+(613612309/2500000000 : ℝ)*X 1 2+(6419012653/10000000000 : ℝ)*X 2 0+(3150163853/10000000000 : ℝ)*X 2 1+(613612309/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((15041/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15041/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (71298659850076796727873/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1180046541893/1000000000000 : ℝ)*(base7) + (20027279857/125000000000 : ℝ)*(base49) + (184029033331/1000000000000 : ℝ)*(base50) + (6812641/1000000000000 : ℝ)*(base53) + (28264545651/1000000000000 : ℝ)*(base60) + (404419000817/250000000000 : ℝ)*(major_s0_0) + (404419000817/250000000000 : ℝ)*(major_s0_1) + (1617669190627/1000000000000 : ℝ)*(major_s0_2) + (1766138909033/1000000000000 : ℝ)*(sp_s0_7) + (883078990763/500000000000 : ℝ)*(sp_s0_8) + (1766147674171/1000000000000 : ℝ)*(sp_s0_9) + (199588443263/100000000000 : ℝ)*(sp_s0_13) + (19072493/1000000000000 : ℝ)*(sp_s0_21) + (4279999/250000000000 : ℝ)*(sp_s0_23) + (815837890737/1000000000000 : ℝ)*(f.failure) + (1766164794167/1000000000000 : ℝ)*(f.sum) + (682975001081667/1000000000000000000000000000 : ℝ)*base63 + (3275173347443463/10000000000000000000000000000 : ℝ)*base64 + (699298045959427/2500000000000000000000000000 : ℝ)*base67 + (270736978916151/1000000000000000000000000000 : ℝ)*base69 + (4752344928098623/10000000000000000000000000000 : ℝ)*base70 + (131495301959427/2500000000000000000000000000 : ℝ)*base73 + (48409067666379/250000000000000000000000000 : ℝ)*base75 + (8477052391379/250000000000000000000000000 : ℝ)*base76 + (327761566584427/1250000000000000000000000000 : ℝ)*base79 + (23827/25000000000000000 : ℝ)*base87 + (23827/25000000000000000 : ℝ)*base89 + (23827/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(9277/25000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(9277/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (504940097332769702361/62500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1665713/250000000000 : ℝ)*(base3) + (606304192383/1000000000000 : ℝ)*(base7) + (31302133053/62500000000 : ℝ)*(base40) + (156099/20000000000 : ℝ)*(base54) + (264934502051/1000000000000 : ℝ)*(base60) + (1730095457939/1000000000000 : ℝ)*(major_s0_0) + (1730095457939/1000000000000 : ℝ)*(major_s0_1) + (432521913247/250000000000 : ℝ)*(major_s0_2) + (6306333/500000000000 : ℝ)*(sp_s0_1) + (38312337/1000000000000 : ℝ)*(sp_s0_2) + (2251967772403/1000000000000 : ℝ)*(sp_s0_14) + (2251961822589/1000000000000 : ℝ)*(sp_s0_15) + (562980413779/250000000000 : ℝ)*(sp_s0_16) + (739411897941/500000000000 : ℝ)*(sp_s0_20) + (872534071301/1000000000000 : ℝ)*(f.failure) + (2251967772403/1000000000000 : ℝ)*(f.sum) + (338698792258363/1000000000000000000000000000 : ℝ)*base62 + (1065889280283757/2500000000000000000000000000 : ℝ)*base65 + (4641518782859191/10000000000000000000000000000 : ℝ)*base66 + (56094160384789/250000000000000000000000000 : ℝ)*base68 + (953401174663549/5000000000000000000000000000 : ℝ)*base71 + (6408104563859191/10000000000000000000000000000 : ℝ)*base72 + (171018848480793/1000000000000000000000000000 : ℝ)*base75 + (262645660219207/1000000000000000000000000000 : ℝ)*base77 + (407801686859191/5000000000000000000000000000 : ℝ)*base78 + (13129/25000000000000000 : ℝ)*base86 + (13129/25000000000000000 : ℝ)*base88 + (11871/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(261/400 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(261/400 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24454084142933645580351/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1003307/1000000000000 : ℝ)*(base3) + (1215343662029/1000000000000 : ℝ)*(base7) + (5238041/1000000000000 : ℝ)*(base11) + (256154356489/1000000000000 : ℝ)*(base40) + (72207/200000000000 : ℝ)*(base49) + (1714608754807/1000000000000 : ℝ)*(major_s0_0) + (1714608754807/1000000000000 : ℝ)*(major_s0_1) + (1714608754807/1000000000000 : ℝ)*(major_s0_2) + (12774667/1000000000000 : ℝ)*(sp_s0_2) + (99790449/1000000000000 : ℝ)*(sp_s0_9) + (378319626459/200000000000 : ℝ)*(sp_s0_21) + (1891604373643/1000000000000 : ℝ)*(sp_s0_22) + (94574540261/50000000000 : ℝ)*(sp_s0_23) + (2080066365531/1000000000000 : ℝ)*(sp_s0_27) + (108090463351/125000000000 : ℝ)*(f.failure) + (59112605323/31250000000 : ℝ)*(f.sum) + (2537767673/10000000000000000000000 : ℝ)*base62 + (7827488746639883/10000000000000000000000000000 : ℝ)*base64 + (6087590714639883/10000000000000000000000000000 : ℝ)*base66 + (1015998189129509/1000000000000000000000000000 : ℝ)*base68 + (1700229503065027/10000000000000000000000000000 : ℝ)*base71 + (9455178475639883/10000000000000000000000000000 : ℝ)*base72 + (648400412570491/1000000000000000000000000000 : ℝ)*base74 + (300212803829509/1000000000000000000000000000 : ℝ)*base76 + (2856559652139883/5000000000000000000000000000 : ℝ)*base78 + (273/1562500000000000 : ℝ)*base87 + (273/1562500000000000 : ℝ)*base89 + (273/1562500000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (15041/25000 : ℝ) ^ (21/4 : ℝ) ≤ (1388505755365075343/20000000000000000000 : ℝ) := by
    have hpowers : (15041/25000 : ℝ)^21 ≤ (1388505755365075343/20000000000000000000 : ℝ)^4 := by
      have hnat : (15041 : ℕ)^21*20000000000000000000^4 ≤ 1388505755365075343^4*25000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15041 25000 1388505755365075343 20000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15041/25000 : ℝ)) (X := (1388505755365075343/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (21388505755365075343/20000000000000000000 : ℝ) ≤ (5064335522624911/5000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (21388505755365075343/20000000000000000000 : ℝ)^4 ≤ (5064335522624911/5000000000000000 : ℝ)^21 := by
      have hnat : (21388505755365075343 : ℕ)^4*5000000000000000^21 ≤ 5064335522624911^21*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21388505755365075343 20000000000000000000 5064335522624911 5000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5064335522624911/5000000000000000 : ℝ)) (X := (21388505755365075343/20000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (11388505755365075343/10000000000000000000 : ℝ) ≤ (5125374158757653/5000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (11388505755365075343/10000000000000000000 : ℝ)^4 ≤ (5125374158757653/5000000000000000 : ℝ)^21 := by
      have hnat : (11388505755365075343 : ℕ)^4*5000000000000000^21 ≤ 5125374158757653^21*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11388505755365075343 10000000000000000000 5125374158757653 5000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5125374158757653/5000000000000000 : ℝ)) (X := (11388505755365075343/10000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(64335522624911/3008200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(342913686139/16900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (15041/25000 : ℝ)) (alpha := (64335522624911/3008200000000000 : ℝ)) (beta := (342913686139/16900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (15041/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(64335522624911/3008200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(342913686139/16900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (9277/25000 : ℝ) ^ (21/4 : ℝ) ≤ (17161476433997677/3125000000000000000 : ℝ) := by
    have hpowers : (9277/25000 : ℝ)^21 ≤ (17161476433997677/3125000000000000000 : ℝ)^4 := by
      have hnat : (9277 : ℕ)^21*3125000000000000000^4 ≤ 17161476433997677^4*25000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9277 25000 17161476433997677 3125000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9277/25000 : ℝ)) (X := (17161476433997677/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (3142161476433997677/3125000000000000000 : ℝ) ≤ (10010437153790811/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3142161476433997677/3125000000000000000 : ℝ)^4 ≤ (10010437153790811/10000000000000000 : ℝ)^21 := by
      have hnat : (3142161476433997677 : ℕ)^4*10000000000000000^21 ≤ 10010437153790811^21*3125000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3142161476433997677 3125000000000000000 10010437153790811 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010437153790811/10000000000000000 : ℝ)) (X := (3142161476433997677/3125000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (1579661476433997677/1562500000000000000 : ℝ) ≤ (10020828262722107/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (1579661476433997677/1562500000000000000 : ℝ)^4 ≤ (10020828262722107/10000000000000000 : ℝ)^21 := by
      have hnat : (1579661476433997677 : ℕ)^4*10000000000000000^21 ≤ 10020828262722107^21*1562500000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1579661476433997677 1562500000000000000 10020828262722107 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10020828262722107/10000000000000000 : ℝ)) (X := (1579661476433997677/1562500000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(10437153790811/3710800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(324722154103/115962500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (9277/25000 : ℝ)) (alpha := (10437153790811/3710800000000000 : ℝ)) (beta := (324722154103/115962500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (9277/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(10437153790811/3710800000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(324722154103/115962500000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (261/400 : ℝ) ^ (21/4 : ℝ) ≤ (1328794194643000537/12500000000000000000 : ℝ) := by
    have hpowers : (261/400 : ℝ)^21 ≤ (1328794194643000537/12500000000000000000 : ℝ)^4 := by
      have hnat : (261 : ℕ)^21*12500000000000000000^4 ≤ 1328794194643000537^4*400^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        261 400 1328794194643000537 12500000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (261/400 : ℝ)) (X := (1328794194643000537/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (13828794194643000537/12500000000000000000 : ℝ) ≤ (10194290602181611/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (13828794194643000537/12500000000000000000 : ℝ)^4 ≤ (10194290602181611/10000000000000000 : ℝ)^21 := by
      have hnat : (13828794194643000537 : ℕ)^4*10000000000000000^21 ≤ 10194290602181611^21*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13828794194643000537 12500000000000000000 10194290602181611 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10194290602181611/10000000000000000 : ℝ)) (X := (13828794194643000537/12500000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (7578794194643000537/6250000000000000000 : ℝ) ≤ (2593502635796811/2500000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (7578794194643000537/6250000000000000000 : ℝ)^4 ≤ (2593502635796811/2500000000000000 : ℝ)^21 := by
      have hnat : (7578794194643000537 : ℕ)^4*2500000000000000^21 ≤ 2593502635796811^21*6250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7578794194643000537 6250000000000000000 2593502635796811 2500000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2593502635796811/2500000000000000 : ℝ)) (X := (7578794194643000537/6250000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(64763534060537/2175000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(179719941005633/6525000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (261/400 : ℝ)) (alpha := (64763534060537/2175000000000000 : ℝ)) (beta := (179719941005633/6525000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (261/400 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(64763534060537/2175000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(179719941005633/6525000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3354966019/10000000000 : ℝ)*X 0 0+(5264113297/10000000000 : ℝ)*X 0 1+(3589648419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1124887933/2000000000 : ℝ)*X 1 0+(-92072507/1000000000 : ℝ)*X 1 1+(656719671/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3165870811/10000000000 : ℝ)*X 2 0+(5615119697/10000000000 : ℝ)*X 2 1+(-1693662929/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3825416849/10000000000 : ℝ)*X 0 0+(4844182031/10000000000 : ℝ)*X 0 1+(3573300303/10000000000 : ℝ)*X 0 2+(3825416849/10000000000 : ℝ)*X 1 0+(4844182031/10000000000 : ℝ)*X 1 1+(3573300303/10000000000 : ℝ)*X 1 2+(3825416849/10000000000 : ℝ)*X 2 0+(4844182031/10000000000 : ℝ)*X 2 1+(3573300303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324031_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-111213/12500 : ℝ) < ((-49571/25000 : ℝ)*P 0+(-49571/25000 : ℝ)*P 1+(-49571/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-111213/12500 : ℝ) < (-3018081644646791993746554125113/340999327500000000000000000000 : ℝ) := by norm_num
    linear_combination (7549/500000000000 : ℝ)*(base8) + (102171/250000000000 : ℝ)*(base19) + (877/2500000000 : ℝ)*(base23) + (115762643131/1000000000000 : ℝ)*(base40) + (44341625739/500000000000 : ℝ)*(base49) + (330357993983/500000000000 : ℝ)*(base50) + (741/31250000000 : ℝ)*(base59) + (36759/500000000000 : ℝ)*(base60) + (49571/25000 : ℝ)*(major_s1_0) + (49571/25000 : ℝ)*(major_s1_1) + (49571/25000 : ℝ)*(major_s1_2) + (1475116119887/500000000000 : ℝ)*(sp_s1_0) + (737557961547/250000000000 : ℝ)*(sp_s1_1) + (2950231904071/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (368779031859/125000000000 : ℝ)*(f.sum) + (4220154092168447/4035495000000000000000000000 : ℝ)*base63 + (1137073027579/1305000000000000000000000 : ℝ)*base64 + (27722759726119/46385000000000000000000000 : ℝ)*base67 + (4950527063/43500000000000000000000 : ℝ)*base69 + (993545296441171/981425250000000000000000000 : ℝ)*base70 + (3681639747/52812500000000000000000 : ℝ)*base73 + (37034495643063/92770000000000000000000000 : ℝ)*base75 + (24395214649033/150410000000000000000000000 : ℝ)*base77 + (7026372228411667/7839065000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c324032_s0_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2553255387/10000000000 : ℝ)*x 0 + (-2140563491/5000000000 : ℝ)*x 1 + (-5319353829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2553255387/10000000000 : ℝ)^43 ≤ (4672108855343/25000000000000 : ℝ)^35 := by
    have hnat : (2553255387 : ℕ)^43*25000000000000^35 ≤ 4672108855343^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2553255387 10000000000 4672108855343 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2140563491/5000000000 : ℝ)^43 ≤ (35264913291083/100000000000000 : ℝ)^35 := by
    have hnat : (2140563491 : ℕ)^43*100000000000000^35 ≤ 35264913291083^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140563491 5000000000 35264913291083 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5319353829/10000000000 : ℝ)^43 ≤ (920933025541/2000000000000 : ℝ)^35 := by
    have hnat : (5319353829 : ℕ)^43*2000000000000^35 ≤ 920933025541^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5319353829 10000000000 920933025541 2000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2553255387/10000000000 : ℝ), (-2140563491/5000000000 : ℝ), (-5319353829/10000000000 : ℝ)] ![(4672108855343/25000000000000 : ℝ), (35264913291083/100000000000000 : ℝ), (920933025541/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2553255387/10000000000 : ℝ)|^43 ≤ (4672108855343/25000000000000 : ℝ)^35
        have hw : |(-2553255387/10000000000 : ℝ)|=(2553255387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2140563491/5000000000 : ℝ)|^43 ≤ (35264913291083/100000000000000 : ℝ)^35
        have hw : |(-2140563491/5000000000 : ℝ)|=(2140563491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5319353829/10000000000 : ℝ)|^43 ≤ (920933025541/2000000000000 : ℝ)^35
        have hw : |(-5319353829/10000000000 : ℝ)|=(5319353829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324032_s0_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1420460917/5000000000 : ℝ)*x 0 + (511719377/1000000000 : ℝ)*x 1 + (-84675361/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1420460917/5000000000 : ℝ)^43 ≤ (332932137071/1562500000000 : ℝ)^35 := by
    have hnat : (1420460917 : ℕ)^43*1562500000000^35 ≤ 332932137071^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1420460917 5000000000 332932137071 1562500000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (511719377/1000000000 : ℝ)^43 ≤ (5488262467227/12500000000000 : ℝ)^35 := by
    have hnat : (511719377 : ℕ)^43*12500000000000^35 ≤ 5488262467227^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511719377 1000000000 5488262467227 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84675361/200000000 : ℝ)^43 ≤ (8696560868721/25000000000000 : ℝ)^35 := by
    have hnat : (84675361 : ℕ)^43*25000000000000^35 ≤ 8696560868721^35*200000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84675361 200000000 8696560868721 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1420460917/5000000000 : ℝ), (511719377/1000000000 : ℝ), (-84675361/200000000 : ℝ)] ![(332932137071/1562500000000 : ℝ), (5488262467227/12500000000000 : ℝ), (8696560868721/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1420460917/5000000000 : ℝ)|^43 ≤ (332932137071/1562500000000 : ℝ)^35
        have hw : |(1420460917/5000000000 : ℝ)|=(1420460917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(511719377/1000000000 : ℝ)|^43 ≤ (5488262467227/12500000000000 : ℝ)^35
        have hw : |(511719377/1000000000 : ℝ)|=(511719377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-84675361/200000000 : ℝ)|^43 ≤ (8696560868721/25000000000000 : ℝ)^35
        have hw : |(-84675361/200000000 : ℝ)|=(84675361/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324032_s0_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3443235281/5000000000 : ℝ)*x 0 + (-1377140207/5000000000 : ℝ)*x 1 + (1139392501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3443235281/5000000000 : ℝ)^43 ≤ (15809108395257/25000000000000 : ℝ)^35 := by
    have hnat : (3443235281 : ℕ)^43*25000000000000^35 ≤ 15809108395257^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3443235281 5000000000 15809108395257 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1377140207/5000000000 : ℝ)^43 ≤ (10256047459647/50000000000000 : ℝ)^35 := by
    have hnat : (1377140207 : ℕ)^43*50000000000000^35 ≤ 10256047459647^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377140207 5000000000 10256047459647 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139392501/5000000000 : ℝ)^43 ≤ (8125735742223/50000000000000 : ℝ)^35 := by
    have hnat : (1139392501 : ℕ)^43*50000000000000^35 ≤ 8125735742223^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139392501 5000000000 8125735742223 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3443235281/5000000000 : ℝ), (-1377140207/5000000000 : ℝ), (1139392501/5000000000 : ℝ)] ![(15809108395257/25000000000000 : ℝ), (10256047459647/50000000000000 : ℝ), (8125735742223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3443235281/5000000000 : ℝ)|^43 ≤ (15809108395257/25000000000000 : ℝ)^35
        have hw : |(3443235281/5000000000 : ℝ)|=(3443235281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1377140207/5000000000 : ℝ)|^43 ≤ (10256047459647/50000000000000 : ℝ)^35
        have hw : |(-1377140207/5000000000 : ℝ)|=(1377140207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1139392501/5000000000 : ℝ)|^43 ≤ (8125735742223/50000000000000 : ℝ)^35
        have hw : |(1139392501/5000000000 : ℝ)|=(1139392501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324032_s0_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (140596751/400000000 : ℝ)*x 0 + (-1945878859/5000000000 : ℝ)*x 1 + (-302222353/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140596751/400000000 : ℝ)^43 ≤ (13838674927239/50000000000000 : ℝ)^35 := by
    have hnat : (140596751 : ℕ)^43*50000000000000^35 ≤ 13838674927239^35*400000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140596751 400000000 13838674927239 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1945878859/5000000000 : ℝ)^43 ≤ (7841602849401/25000000000000 : ℝ)^35 := by
    have hnat : (1945878859 : ℕ)^43*25000000000000^35 ≤ 7841602849401^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945878859 5000000000 7841602849401 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (302222353/625000000 : ℝ)^43 ≤ (40956238729679/100000000000000 : ℝ)^35 := by
    have hnat : (302222353 : ℕ)^43*100000000000000^35 ≤ 40956238729679^35*625000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302222353 625000000 40956238729679 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(140596751/400000000 : ℝ), (-1945878859/5000000000 : ℝ), (-302222353/625000000 : ℝ)] ![(13838674927239/50000000000000 : ℝ), (7841602849401/25000000000000 : ℝ), (40956238729679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(140596751/400000000 : ℝ)|^43 ≤ (13838674927239/50000000000000 : ℝ)^35
        have hw : |(140596751/400000000 : ℝ)|=(140596751/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1945878859/5000000000 : ℝ)|^43 ≤ (7841602849401/25000000000000 : ℝ)^35
        have hw : |(-1945878859/5000000000 : ℝ)|=(1945878859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-302222353/625000000 : ℝ)|^43 ≤ (40956238729679/100000000000000 : ℝ)^35
        have hw : |(-302222353/625000000 : ℝ)|=(302222353/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324032 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2553255387/10000000000 : ℝ)*X 0 0+(-2140563491/5000000000 : ℝ)*X 0 1+(-5319353829/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324032_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1420460917/5000000000 : ℝ)*X 1 0+(511719377/1000000000 : ℝ)*X 1 1+(-84675361/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324032_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3443235281/5000000000 : ℝ)*X 2 0+(-1377140207/5000000000 : ℝ)*X 2 1+(1139392501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324032_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((140596751/400000000 : ℝ)*X 0 0+(-1945878859/5000000000 : ℝ)*X 0 1+(-302222353/625000000 : ℝ)*X 0 2+(140596751/400000000 : ℝ)*X 1 0+(-1945878859/5000000000 : ℝ)*X 1 1+(-302222353/625000000 : ℝ)*X 1 2+(140596751/400000000 : ℝ)*X 2 0+(-1945878859/5000000000 : ℝ)*X 2 1+(-302222353/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324032_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-111213/12500 : ℝ) < ((-49571/25000 : ℝ)*P 0+(-49571/25000 : ℝ)*P 1+(-49571/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-111213/12500 : ℝ) < (-44144922690815016385737/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (213899/1000000000000 : ℝ)*(base12) + (114419/1000000000000 : ℝ)*(base22) + (133/1600000000 : ℝ)*(base25) + (574833908211/1000000000000 : ℝ)*(base39) + (62902776203/125000000000 : ℝ)*(base40) + (115477826337/1000000000000 : ℝ)*(base50) + (1679/1000000000000 : ℝ)*(base59) + (257703819341/500000000000 : ℝ)*(base60) + (49571/25000 : ℝ)*(major_s0_0) + (49571/25000 : ℝ)*(major_s0_1) + (49571/25000 : ℝ)*(major_s0_2) + (2942994632151/1000000000000 : ℝ)*(sp_s0_0) + (58859896921/20000000000 : ℝ)*(sp_s0_1) + (1471497324253/500000000000 : ℝ)*(sp_s0_2) + (1 : ℝ)*(sp_s0_6) + (58859896921/20000000000 : ℝ)*(f.sum) + (1624147437/10000000000000000000000 : ℝ)*base63 + (1984900879/5000000000000000000000 : ℝ)*base64 + (2087756139/10000000000000000000000 : ℝ)*base67 + (17989751/100000000000000000000 : ℝ)*base69 + (533116967/500000000000000000000 : ℝ)*base70 + (396965127/500000000000000000000 : ℝ)*base73 + (1204727793/2500000000000000000000 : ℝ)*base74 + (544382671/2500000000000000000000 : ℝ)*base77 + (2066373247/2500000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p024_b014 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 31 ≤ c.val) (hhi : c.val < 33)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=31 ∨ c=32 := by omega
  rcases hc with rfl|rfl
  · exact collision_c324031 p hpa (by linarith only [hpb]) X hX
  · exact collision_c324032 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 31 ≤ c.val) (hhi : c.val < 33)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b014 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

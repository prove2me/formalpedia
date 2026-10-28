-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b008
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:16:21.587227+00:00
-- url     : https://prove2.me/submissions/03652952-7d73-488e-a9a8-8e00c4083280

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
theorem collision_support_c301018_s0_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5507757839/10000000000 : ℝ)*x 0 + (-788598743/5000000000 : ℝ)*x 1 + (-696569431/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5507757839/10000000000 : ℝ)^65 ≤ (9066197758187/20000000000000 : ℝ)^49 := by
    have hnat : (5507757839 : ℕ)^65*20000000000000^49 ≤ 9066197758187^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507757839 10000000000 9066197758187 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (788598743/5000000000 : ℝ)^65 ≤ (2157303927727/25000000000000 : ℝ)^49 := by
    have hnat : (788598743 : ℕ)^65*25000000000000^49 ≤ 2157303927727^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788598743 5000000000 2157303927727 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (696569431/1250000000 : ℝ)^65 ≤ (11509948870761/25000000000000 : ℝ)^49 := by
    have hnat : (696569431 : ℕ)^65*25000000000000^49 ≤ 11509948870761^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696569431 1250000000 11509948870761 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5507757839/10000000000 : ℝ), (-788598743/5000000000 : ℝ), (-696569431/1250000000 : ℝ)] ![(9066197758187/20000000000000 : ℝ), (2157303927727/25000000000000 : ℝ), (11509948870761/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5507757839/10000000000 : ℝ)|^65 ≤ (9066197758187/20000000000000 : ℝ)^49
        have hw : |(5507757839/10000000000 : ℝ)|=(5507757839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-788598743/5000000000 : ℝ)|^65 ≤ (2157303927727/25000000000000 : ℝ)^49
        have hw : |(-788598743/5000000000 : ℝ)|=(788598743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-696569431/1250000000 : ℝ)|^65 ≤ (11509948870761/25000000000000 : ℝ)^49
        have hw : |(-696569431/1250000000 : ℝ)|=(696569431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s0_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4060979917/10000000000 : ℝ)*x 0 + (5667886271/10000000000 : ℝ)*x 1 + (3265045101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4060979917/10000000000 : ℝ)^65 ≤ (30257763978197/100000000000000 : ℝ)^49 := by
    have hnat : (4060979917 : ℕ)^65*100000000000000^49 ≤ 30257763978197^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4060979917 10000000000 30257763978197 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5667886271/10000000000 : ℝ)^65 ≤ (11771873478071/25000000000000 : ℝ)^49 := by
    have hnat : (5667886271 : ℕ)^65*25000000000000^49 ≤ 11771873478071^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5667886271 10000000000 11771873478071 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3265045101/10000000000 : ℝ)^65 ≤ (2265474209883/10000000000000 : ℝ)^49 := by
    have hnat : (3265045101 : ℕ)^65*10000000000000^49 ≤ 2265474209883^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3265045101 10000000000 2265474209883 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4060979917/10000000000 : ℝ), (5667886271/10000000000 : ℝ), (3265045101/10000000000 : ℝ)] ![(30257763978197/100000000000000 : ℝ), (11771873478071/25000000000000 : ℝ), (2265474209883/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4060979917/10000000000 : ℝ)|^65 ≤ (30257763978197/100000000000000 : ℝ)^49
        have hw : |(4060979917/10000000000 : ℝ)|=(4060979917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5667886271/10000000000 : ℝ)|^65 ≤ (11771873478071/25000000000000 : ℝ)^49
        have hw : |(5667886271/10000000000 : ℝ)|=(5667886271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3265045101/10000000000 : ℝ)|^65 ≤ (2265474209883/10000000000000 : ℝ)^49
        have hw : |(3265045101/10000000000 : ℝ)|=(3265045101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s0_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-67330069/2500000000 : ℝ)*x 0 + (337766443/400000000 : ℝ)*x 1 + (-1444898343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67330069/2500000000 : ℝ)^65 ≤ (206844440069/25000000000000 : ℝ)^49 := by
    have hnat : (67330069 : ℕ)^65*25000000000000^49 ≤ 206844440069^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67330069 2500000000 206844440069 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337766443/400000000 : ℝ)^65 ≤ (79905184926693/100000000000000 : ℝ)^49 := by
    have hnat : (337766443 : ℕ)^65*100000000000000^49 ≤ 79905184926693^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337766443 400000000 79905184926693 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1444898343/5000000000 : ℝ)^65 ≤ (9633718650053/50000000000000 : ℝ)^49 := by
    have hnat : (1444898343 : ℕ)^65*50000000000000^49 ≤ 9633718650053^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444898343 5000000000 9633718650053 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67330069/2500000000 : ℝ), (337766443/400000000 : ℝ), (-1444898343/5000000000 : ℝ)] ![(206844440069/25000000000000 : ℝ), (79905184926693/100000000000000 : ℝ), (9633718650053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67330069/2500000000 : ℝ)|^65 ≤ (206844440069/25000000000000 : ℝ)^49
        have hw : |(-67330069/2500000000 : ℝ)|=(67330069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337766443/400000000 : ℝ)|^65 ≤ (79905184926693/100000000000000 : ℝ)^49
        have hw : |(337766443/400000000 : ℝ)|=(337766443/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1444898343/5000000000 : ℝ)|^65 ≤ (9633718650053/50000000000000 : ℝ)^49
        have hw : |(-1444898343/5000000000 : ℝ)|=(1444898343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s0_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2530043191/5000000000 : ℝ)*x 0 + (74437699/400000000 : ℝ)*x 1 + (-1454383603/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2530043191/5000000000 : ℝ)^65 ≤ (20254729295997/50000000000000 : ℝ)^49 := by
    have hnat : (2530043191 : ℕ)^65*50000000000000^49 ≤ 20254729295997^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2530043191 5000000000 20254729295997 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (74437699/400000000 : ℝ)^65 ≤ (5373390528283/50000000000000 : ℝ)^49 := by
    have hnat : (74437699 : ℕ)^65*50000000000000^49 ≤ 5373390528283^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74437699 400000000 5373390528283 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1454383603/2500000000 : ℝ)^65 ≤ (1218594008421/2500000000000 : ℝ)^49 := by
    have hnat : (1454383603 : ℕ)^65*2500000000000^49 ≤ 1218594008421^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1454383603 2500000000 1218594008421 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2530043191/5000000000 : ℝ), (74437699/400000000 : ℝ), (-1454383603/2500000000 : ℝ)] ![(20254729295997/50000000000000 : ℝ), (5373390528283/50000000000000 : ℝ), (1218594008421/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2530043191/5000000000 : ℝ)|^65 ≤ (20254729295997/50000000000000 : ℝ)^49
        have hw : |(-2530043191/5000000000 : ℝ)|=(2530043191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(74437699/400000000 : ℝ)|^65 ≤ (5373390528283/50000000000000 : ℝ)^49
        have hw : |(74437699/400000000 : ℝ)|=(74437699/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1454383603/2500000000 : ℝ)|^65 ≤ (1218594008421/2500000000000 : ℝ)^49
        have hw : |(-1454383603/2500000000 : ℝ)|=(1454383603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s0_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (323360999/500000000 : ℝ)*x 0 + (-37300273/2000000000 : ℝ)*x 1 + (-66622637/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323360999/500000000 : ℝ)^65 ≤ (28046660075093/50000000000000 : ℝ)^49 := by
    have hnat : (323360999 : ℕ)^65*50000000000000^49 ≤ 28046660075093^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323360999 500000000 28046660075093 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37300273/2000000000 : ℝ)^65 ≤ (508167345649/100000000000000 : ℝ)^49 := by
    have hnat : (37300273 : ℕ)^65*100000000000000^49 ≤ 508167345649^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37300273 2000000000 508167345649 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66622637/125000000 : ℝ)^65 ≤ (21699256247199/50000000000000 : ℝ)^49 := by
    have hnat : (66622637 : ℕ)^65*50000000000000^49 ≤ 21699256247199^49*125000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66622637 125000000 21699256247199 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(323360999/500000000 : ℝ), (-37300273/2000000000 : ℝ), (-66622637/125000000 : ℝ)] ![(28046660075093/50000000000000 : ℝ), (508167345649/100000000000000 : ℝ), (21699256247199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(323360999/500000000 : ℝ)|^65 ≤ (28046660075093/50000000000000 : ℝ)^49
        have hw : |(323360999/500000000 : ℝ)|=(323360999/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37300273/2000000000 : ℝ)|^65 ≤ (508167345649/100000000000000 : ℝ)^49
        have hw : |(-37300273/2000000000 : ℝ)|=(37300273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66622637/125000000 : ℝ)|^65 ≤ (21699256247199/50000000000000 : ℝ)^49
        have hw : |(-66622637/125000000 : ℝ)|=(66622637/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s0_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1129458857/5000000000 : ℝ)*x 0 + (1428512419/2000000000 : ℝ)*x 1 + (3205649313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1129458857/5000000000 : ℝ)^65 ≤ (13897257889917/100000000000000 : ℝ)^49 := by
    have hnat : (1129458857 : ℕ)^65*100000000000000^49 ≤ 13897257889917^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129458857 5000000000 13897257889917 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1428512419/2000000000 : ℝ)^65 ≤ (63993061806261/100000000000000 : ℝ)^49 := by
    have hnat : (1428512419 : ℕ)^65*100000000000000^49 ≤ 63993061806261^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428512419 2000000000 63993061806261 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3205649313/10000000000 : ℝ)^65 ≤ (552742007237/2500000000000 : ℝ)^49 := by
    have hnat : (3205649313 : ℕ)^65*2500000000000^49 ≤ 552742007237^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3205649313 10000000000 552742007237 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1129458857/5000000000 : ℝ), (1428512419/2000000000 : ℝ), (3205649313/10000000000 : ℝ)] ![(13897257889917/100000000000000 : ℝ), (63993061806261/100000000000000 : ℝ), (552742007237/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1129458857/5000000000 : ℝ)|^65 ≤ (13897257889917/100000000000000 : ℝ)^49
        have hw : |(1129458857/5000000000 : ℝ)|=(1129458857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1428512419/2000000000 : ℝ)|^65 ≤ (63993061806261/100000000000000 : ℝ)^49
        have hw : |(1428512419/2000000000 : ℝ)|=(1428512419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3205649313/10000000000 : ℝ)|^65 ≤ (552742007237/2500000000000 : ℝ)^49
        have hw : |(3205649313/10000000000 : ℝ)|=(3205649313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s0_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-19616281/500000000 : ℝ)*x 0 + (8876984831/10000000000 : ℝ)*x 1 + (-435927381/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19616281/500000000 : ℝ)^65 ≤ (68139549843/5000000000000 : ℝ)^49 := by
    have hnat : (19616281 : ℕ)^65*5000000000000^49 ≤ 68139549843^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19616281 500000000 68139549843 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8876984831/10000000000 : ℝ)^65 ≤ (85383228552891/100000000000000 : ℝ)^49 := by
    have hnat : (8876984831 : ℕ)^65*100000000000000^49 ≤ 85383228552891^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8876984831 10000000000 85383228552891 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435927381/2000000000 : ℝ)^65 ≤ (13253980428043/100000000000000 : ℝ)^49 := by
    have hnat : (435927381 : ℕ)^65*100000000000000^49 ≤ 13253980428043^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435927381 2000000000 13253980428043 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19616281/500000000 : ℝ), (8876984831/10000000000 : ℝ), (-435927381/2000000000 : ℝ)] ![(68139549843/5000000000000 : ℝ), (85383228552891/100000000000000 : ℝ), (13253980428043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19616281/500000000 : ℝ)|^65 ≤ (68139549843/5000000000000 : ℝ)^49
        have hw : |(-19616281/500000000 : ℝ)|=(19616281/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8876984831/10000000000 : ℝ)|^65 ≤ (85383228552891/100000000000000 : ℝ)^49
        have hw : |(8876984831/10000000000 : ℝ)|=(8876984831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-435927381/2000000000 : ℝ)|^65 ≤ (13253980428043/100000000000000 : ℝ)^49
        have hw : |(-435927381/2000000000 : ℝ)|=(435927381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s0_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5524343549/10000000000 : ℝ)*x 0 + (2199573937/10000000000 : ℝ)*x 1 + (-5113042663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5524343549/10000000000 : ℝ)^65 ≤ (45512158264359/100000000000000 : ℝ)^49 := by
    have hnat : (5524343549 : ℕ)^65*100000000000000^49 ≤ 45512158264359^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524343549 10000000000 45512158264359 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2199573937/10000000000 : ℝ)^65 ≤ (13415040063923/100000000000000 : ℝ)^49 := by
    have hnat : (2199573937 : ℕ)^65*100000000000000^49 ≤ 13415040063923^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199573937 10000000000 13415040063923 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5113042663/10000000000 : ℝ)^65 ≤ (8214560331937/20000000000000 : ℝ)^49 := by
    have hnat : (5113042663 : ℕ)^65*20000000000000^49 ≤ 8214560331937^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5113042663 10000000000 8214560331937 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5524343549/10000000000 : ℝ), (2199573937/10000000000 : ℝ), (-5113042663/10000000000 : ℝ)] ![(45512158264359/100000000000000 : ℝ), (13415040063923/100000000000000 : ℝ), (8214560331937/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5524343549/10000000000 : ℝ)|^65 ≤ (45512158264359/100000000000000 : ℝ)^49
        have hw : |(-5524343549/10000000000 : ℝ)|=(5524343549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2199573937/10000000000 : ℝ)|^65 ≤ (13415040063923/100000000000000 : ℝ)^49
        have hw : |(2199573937/10000000000 : ℝ)|=(2199573937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5113042663/10000000000 : ℝ)|^65 ≤ (8214560331937/20000000000000 : ℝ)^49
        have hw : |(-5113042663/10000000000 : ℝ)|=(5113042663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s0_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (128494801/200000000 : ℝ)*x 0 + (-2991317/2000000000 : ℝ)*x 1 + (-5420154051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128494801/200000000 : ℝ)^65 ≤ (11121017256573/20000000000000 : ℝ)^49 := by
    have hnat : (128494801 : ℕ)^65*20000000000000^49 ≤ 11121017256573^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128494801 200000000 11121017256573 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2991317/2000000000 : ℝ)^65 ≤ (17878404193/100000000000000 : ℝ)^49 := by
    have hnat : (2991317 : ℕ)^65*100000000000000^49 ≤ 17878404193^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2991317 2000000000 17878404193 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420154051/10000000000 : ℝ)^65 ≤ (44377035301529/100000000000000 : ℝ)^49 := by
    have hnat : (5420154051 : ℕ)^65*100000000000000^49 ≤ 44377035301529^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420154051 10000000000 44377035301529 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(128494801/200000000 : ℝ), (-2991317/2000000000 : ℝ), (-5420154051/10000000000 : ℝ)] ![(11121017256573/20000000000000 : ℝ), (17878404193/100000000000000 : ℝ), (44377035301529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(128494801/200000000 : ℝ)|^65 ≤ (11121017256573/20000000000000 : ℝ)^49
        have hw : |(128494801/200000000 : ℝ)|=(128494801/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2991317/2000000000 : ℝ)|^65 ≤ (17878404193/100000000000000 : ℝ)^49
        have hw : |(-2991317/2000000000 : ℝ)|=(2991317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5420154051/10000000000 : ℝ)|^65 ≤ (44377035301529/100000000000000 : ℝ)^49
        have hw : |(-5420154051/10000000000 : ℝ)|=(5420154051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s0_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2640877651/10000000000 : ℝ)*x 0 + (1696069169/2500000000 : ℝ)*x 1 + (3316807531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640877651/10000000000 : ℝ)^65 ≤ (4274363003761/25000000000000 : ℝ)^49 := by
    have hnat : (2640877651 : ℕ)^65*25000000000000^49 ≤ 4274363003761^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640877651 10000000000 4274363003761 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1696069169/2500000000 : ℝ)^65 ≤ (59770144024103/100000000000000 : ℝ)^49 := by
    have hnat : (1696069169 : ℕ)^65*100000000000000^49 ≤ 59770144024103^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696069169 2500000000 59770144024103 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3316807531/10000000000 : ℝ)^65 ≤ (23132403943067/100000000000000 : ℝ)^49 := by
    have hnat : (3316807531 : ℕ)^65*100000000000000^49 ≤ 23132403943067^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3316807531 10000000000 23132403943067 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640877651/10000000000 : ℝ), (1696069169/2500000000 : ℝ), (3316807531/10000000000 : ℝ)] ![(4274363003761/25000000000000 : ℝ), (59770144024103/100000000000000 : ℝ), (23132403943067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640877651/10000000000 : ℝ)|^65 ≤ (4274363003761/25000000000000 : ℝ)^49
        have hw : |(2640877651/10000000000 : ℝ)|=(2640877651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1696069169/2500000000 : ℝ)|^65 ≤ (59770144024103/100000000000000 : ℝ)^49
        have hw : |(1696069169/2500000000 : ℝ)|=(1696069169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3316807531/10000000000 : ℝ)|^65 ≤ (23132403943067/100000000000000 : ℝ)^49
        have hw : |(3316807531/10000000000 : ℝ)|=(3316807531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s0_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-428877699/10000000000 : ℝ)*x 0 + (20562193/31250000 : ℝ)*x 1 + (-5113042663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428877699/10000000000 : ℝ)^65 ≤ (766864223663/50000000000000 : ℝ)^49 := by
    have hnat : (428877699 : ℕ)^65*50000000000000^49 ≤ 766864223663^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428877699 10000000000 766864223663 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20562193/31250000 : ℝ)^65 ≤ (57393469879297/100000000000000 : ℝ)^49 := by
    have hnat : (20562193 : ℕ)^65*100000000000000^49 ≤ 57393469879297^49*31250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20562193 31250000 57393469879297 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5113042663/10000000000 : ℝ)^65 ≤ (8214560331937/20000000000000 : ℝ)^49 := by
    have hnat : (5113042663 : ℕ)^65*20000000000000^49 ≤ 8214560331937^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5113042663 10000000000 8214560331937 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-428877699/10000000000 : ℝ), (20562193/31250000 : ℝ), (-5113042663/10000000000 : ℝ)] ![(766864223663/50000000000000 : ℝ), (57393469879297/100000000000000 : ℝ), (8214560331937/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-428877699/10000000000 : ℝ)|^65 ≤ (766864223663/50000000000000 : ℝ)^49
        have hw : |(-428877699/10000000000 : ℝ)|=(428877699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20562193/31250000 : ℝ)|^65 ≤ (57393469879297/100000000000000 : ℝ)^49
        have hw : |(20562193/31250000 : ℝ)|=(20562193/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5113042663/10000000000 : ℝ)|^65 ≤ (8214560331937/20000000000000 : ℝ)^49
        have hw : |(-5113042663/10000000000 : ℝ)|=(5113042663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s0_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1285824191/2000000000 : ℝ)*x 0 + (667201663/2500000000 : ℝ)*x 1 + (-1863756911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1285824191/2000000000 : ℝ)^65 ≤ (13913847162121/25000000000000 : ℝ)^49 := by
    have hnat : (1285824191 : ℕ)^65*25000000000000^49 ≤ 13913847162121^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285824191 2000000000 13913847162121 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (667201663/2500000000 : ℝ)^65 ≤ (3467544811849/20000000000000 : ℝ)^49 := by
    have hnat : (667201663 : ℕ)^65*20000000000000^49 ≤ 3467544811849^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667201663 2500000000 3467544811849 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1863756911/5000000000 : ℝ)^65 ≤ (6751721822129/25000000000000 : ℝ)^49 := by
    have hnat : (1863756911 : ℕ)^65*25000000000000^49 ≤ 6751721822129^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863756911 5000000000 6751721822129 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1285824191/2000000000 : ℝ), (667201663/2500000000 : ℝ), (-1863756911/5000000000 : ℝ)] ![(13913847162121/25000000000000 : ℝ), (3467544811849/20000000000000 : ℝ), (6751721822129/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1285824191/2000000000 : ℝ)|^65 ≤ (13913847162121/25000000000000 : ℝ)^49
        have hw : |(-1285824191/2000000000 : ℝ)|=(1285824191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(667201663/2500000000 : ℝ)|^65 ≤ (3467544811849/20000000000000 : ℝ)^49
        have hw : |(667201663/2500000000 : ℝ)|=(667201663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1863756911/5000000000 : ℝ)|^65 ≤ (6751721822129/25000000000000 : ℝ)^49
        have hw : |(-1863756911/5000000000 : ℝ)|=(1863756911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s0_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5195571281/10000000000 : ℝ)*x 0 + (-70707409/10000000000 : ℝ)*x 1 + (-1324814327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195571281/10000000000 : ℝ)^65 ≤ (20977265826619/50000000000000 : ℝ)^49 := by
    have hnat : (5195571281 : ℕ)^65*50000000000000^49 ≤ 20977265826619^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195571281 10000000000 20977265826619 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70707409/10000000000 : ℝ)^65 ≤ (35090487089/25000000000000 : ℝ)^49 := by
    have hnat : (70707409 : ℕ)^65*25000000000000^49 ≤ 35090487089^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70707409 10000000000 35090487089 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1324814327/2000000000 : ℝ)^65 ≤ (57905106380187/100000000000000 : ℝ)^49 := by
    have hnat : (1324814327 : ℕ)^65*100000000000000^49 ≤ 57905106380187^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324814327 2000000000 57905106380187 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195571281/10000000000 : ℝ), (-70707409/10000000000 : ℝ), (-1324814327/2000000000 : ℝ)] ![(20977265826619/50000000000000 : ℝ), (35090487089/25000000000000 : ℝ), (57905106380187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195571281/10000000000 : ℝ)|^65 ≤ (20977265826619/50000000000000 : ℝ)^49
        have hw : |(5195571281/10000000000 : ℝ)|=(5195571281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70707409/10000000000 : ℝ)|^65 ≤ (35090487089/25000000000000 : ℝ)^49
        have hw : |(-70707409/10000000000 : ℝ)|=(70707409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1324814327/2000000000 : ℝ)|^65 ≤ (57905106380187/100000000000000 : ℝ)^49
        have hw : |(-1324814327/2000000000 : ℝ)|=(1324814327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s0_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3446487897/5000000000 : ℝ)*x 0 + (185337579/500000000 : ℝ)*x 1 + (2041152959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3446487897/5000000000 : ℝ)^65 ≤ (1526095178691/2500000000000 : ℝ)^49 := by
    have hnat : (3446487897 : ℕ)^65*2500000000000^49 ≤ 1526095178691^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3446487897 5000000000 1526095178691 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (185337579/500000000 : ℝ)^65 ≤ (13403760625363/50000000000000 : ℝ)^49 := by
    have hnat : (185337579 : ℕ)^65*50000000000000^49 ≤ 13403760625363^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185337579 500000000 13403760625363 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2041152959/10000000000 : ℝ)^65 ≤ (6074335793491/50000000000000 : ℝ)^49 := by
    have hnat : (2041152959 : ℕ)^65*50000000000000^49 ≤ 6074335793491^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041152959 10000000000 6074335793491 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3446487897/5000000000 : ℝ), (185337579/500000000 : ℝ), (2041152959/10000000000 : ℝ)] ![(1526095178691/2500000000000 : ℝ), (13403760625363/50000000000000 : ℝ), (6074335793491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3446487897/5000000000 : ℝ)|^65 ≤ (1526095178691/2500000000000 : ℝ)^49
        have hw : |(3446487897/5000000000 : ℝ)|=(3446487897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(185337579/500000000 : ℝ)|^65 ≤ (13403760625363/50000000000000 : ℝ)^49
        have hw : |(185337579/500000000 : ℝ)|=(185337579/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2041152959/10000000000 : ℝ)|^65 ≤ (6074335793491/50000000000000 : ℝ)^49
        have hw : |(2041152959/10000000000 : ℝ)|=(2041152959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s0_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-317632883/10000000000 : ℝ)*x 0 + (4610314269/5000000000 : ℝ)*x 1 + (-33036149/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (317632883/10000000000 : ℝ)^65 ≤ (1029812736101/100000000000000 : ℝ)^49 := by
    have hnat : (317632883 : ℕ)^65*100000000000000^49 ≤ 1029812736101^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317632883 10000000000 1029812736101 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4610314269/5000000000 : ℝ)^65 ≤ (89795331793853/100000000000000 : ℝ)^49 := by
    have hnat : (4610314269 : ℕ)^65*100000000000000^49 ≤ 89795331793853^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4610314269 5000000000 89795331793853 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33036149/200000000 : ℝ)^65 ≤ (9174855464129/100000000000000 : ℝ)^49 := by
    have hnat : (33036149 : ℕ)^65*100000000000000^49 ≤ 9174855464129^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33036149 200000000 9174855464129 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-317632883/10000000000 : ℝ), (4610314269/5000000000 : ℝ), (-33036149/200000000 : ℝ)] ![(1029812736101/100000000000000 : ℝ), (89795331793853/100000000000000 : ℝ), (9174855464129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-317632883/10000000000 : ℝ)|^65 ≤ (1029812736101/100000000000000 : ℝ)^49
        have hw : |(-317632883/10000000000 : ℝ)|=(317632883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4610314269/5000000000 : ℝ)|^65 ≤ (89795331793853/100000000000000 : ℝ)^49
        have hw : |(4610314269/5000000000 : ℝ)|=(4610314269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33036149/200000000 : ℝ)|^65 ≤ (9174855464129/100000000000000 : ℝ)^49
        have hw : |(-33036149/200000000 : ℝ)|=(33036149/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2539817593/5000000000 : ℝ)*x 0 + (3480935619/10000000000 : ℝ)*x 1 + (-224745891/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2539817593/5000000000 : ℝ)^65 ≤ (40717193548849/100000000000000 : ℝ)^49 := by
    have hnat : (2539817593 : ℕ)^65*100000000000000^49 ≤ 40717193548849^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539817593 5000000000 40717193548849 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3480935619/10000000000 : ℝ)^65 ≤ (770718393917/3125000000000 : ℝ)^49 := by
    have hnat : (3480935619 : ℕ)^65*3125000000000^49 ≤ 770718393917^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3480935619 10000000000 770718393917 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224745891/500000000 : ℝ)^65 ≤ (34619817836023/100000000000000 : ℝ)^49 := by
    have hnat : (224745891 : ℕ)^65*100000000000000^49 ≤ 34619817836023^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224745891 500000000 34619817836023 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2539817593/5000000000 : ℝ), (3480935619/10000000000 : ℝ), (-224745891/500000000 : ℝ)] ![(40717193548849/100000000000000 : ℝ), (770718393917/3125000000000 : ℝ), (34619817836023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2539817593/5000000000 : ℝ)|^65 ≤ (40717193548849/100000000000000 : ℝ)^49
        have hw : |(-2539817593/5000000000 : ℝ)|=(2539817593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3480935619/10000000000 : ℝ)|^65 ≤ (770718393917/3125000000000 : ℝ)^49
        have hw : |(3480935619/10000000000 : ℝ)|=(3480935619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224745891/500000000 : ℝ)|^65 ≤ (34619817836023/100000000000000 : ℝ)^49
        have hw : |(-224745891/500000000 : ℝ)|=(224745891/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s1_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2462538609/5000000000 : ℝ)*x 0 + (-2935329899/10000000000 : ℝ)*x 1 + (-5129366441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2462538609/5000000000 : ℝ)^65 ≤ (1954098679517/5000000000000 : ℝ)^49 := by
    have hnat : (2462538609 : ℕ)^65*5000000000000^49 ≤ 1954098679517^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2462538609 5000000000 1954098679517 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2935329899/10000000000 : ℝ)^65 ≤ (4917797191019/25000000000000 : ℝ)^49 := by
    have hnat : (2935329899 : ℕ)^65*25000000000000^49 ≤ 4917797191019^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2935329899 10000000000 4917797191019 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129366441/10000000000 : ℝ)^65 ≤ (41246837629361/100000000000000 : ℝ)^49 := by
    have hnat : (5129366441 : ℕ)^65*100000000000000^49 ≤ 41246837629361^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129366441 10000000000 41246837629361 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2462538609/5000000000 : ℝ), (-2935329899/10000000000 : ℝ), (-5129366441/10000000000 : ℝ)] ![(1954098679517/5000000000000 : ℝ), (4917797191019/25000000000000 : ℝ), (41246837629361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2462538609/5000000000 : ℝ)|^65 ≤ (1954098679517/5000000000000 : ℝ)^49
        have hw : |(2462538609/5000000000 : ℝ)|=(2462538609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2935329899/10000000000 : ℝ)|^65 ≤ (4917797191019/25000000000000 : ℝ)^49
        have hw : |(-2935329899/10000000000 : ℝ)|=(2935329899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5129366441/10000000000 : ℝ)|^65 ≤ (41246837629361/100000000000000 : ℝ)^49
        have hw : |(-5129366441/10000000000 : ℝ)|=(5129366441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4476610769/10000000000 : ℝ)*x 0 + (471227707/1000000000 : ℝ)*x 1 + (1951646673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4476610769/10000000000 : ℝ)^65 ≤ (34432900516461/100000000000000 : ℝ)^49 := by
    have hnat : (4476610769 : ℕ)^65*100000000000000^49 ≤ 34432900516461^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476610769 10000000000 34432900516461 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (471227707/1000000000 : ℝ)^65 ≤ (36857907592413/100000000000000 : ℝ)^49 := by
    have hnat : (471227707 : ℕ)^65*100000000000000^49 ≤ 36857907592413^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471227707 1000000000 36857907592413 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1951646673/5000000000 : ℝ)^65 ≤ (28709191882091/100000000000000 : ℝ)^49 := by
    have hnat : (1951646673 : ℕ)^65*100000000000000^49 ≤ 28709191882091^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951646673 5000000000 28709191882091 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4476610769/10000000000 : ℝ), (471227707/1000000000 : ℝ), (1951646673/5000000000 : ℝ)] ![(34432900516461/100000000000000 : ℝ), (36857907592413/100000000000000 : ℝ), (28709191882091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4476610769/10000000000 : ℝ)|^65 ≤ (34432900516461/100000000000000 : ℝ)^49
        have hw : |(4476610769/10000000000 : ℝ)|=(4476610769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(471227707/1000000000 : ℝ)|^65 ≤ (36857907592413/100000000000000 : ℝ)^49
        have hw : |(471227707/1000000000 : ℝ)|=(471227707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1951646673/5000000000 : ℝ)|^65 ≤ (28709191882091/100000000000000 : ℝ)^49
        have hw : |(1951646673/5000000000 : ℝ)|=(1951646673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301018_s1_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (39468633/312500000 : ℝ)*x 0 + (1955046629/2500000000 : ℝ)*x 1 + (-3128281109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39468633/312500000 : ℝ)^65 ≤ (3213307835187/50000000000000 : ℝ)^49 := by
    have hnat : (39468633 : ℕ)^65*50000000000000^49 ≤ 3213307835187^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39468633 312500000 3213307835187 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1955046629/2500000000 : ℝ)^65 ≤ (36084378838317/50000000000000 : ℝ)^49 := by
    have hnat : (1955046629 : ℕ)^65*50000000000000^49 ≤ 36084378838317^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955046629 2500000000 36084378838317 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3128281109/10000000000 : ℝ)^65 ≤ (428092532777/2000000000000 : ℝ)^49 := by
    have hnat : (3128281109 : ℕ)^65*2000000000000^49 ≤ 428092532777^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3128281109 10000000000 428092532777 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(39468633/312500000 : ℝ), (1955046629/2500000000 : ℝ), (-3128281109/10000000000 : ℝ)] ![(3213307835187/50000000000000 : ℝ), (36084378838317/50000000000000 : ℝ), (428092532777/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(39468633/312500000 : ℝ)|^65 ≤ (3213307835187/50000000000000 : ℝ)^49
        have hw : |(39468633/312500000 : ℝ)|=(39468633/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1955046629/2500000000 : ℝ)|^65 ≤ (36084378838317/50000000000000 : ℝ)^49
        have hw : |(1955046629/2500000000 : ℝ)|=(1955046629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3128281109/10000000000 : ℝ)|^65 ≤ (428092532777/2000000000000 : ℝ)^49
        have hw : |(-3128281109/10000000000 : ℝ)|=(3128281109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301018 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((5507757839/10000000000 : ℝ)*X 1 0+(-788598743/5000000000 : ℝ)*X 1 1+(-696569431/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4060979917/10000000000 : ℝ)*X 2 0+(5667886271/10000000000 : ℝ)*X 2 1+(3265045101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((-67330069/2500000000 : ℝ)*X 0 0+(337766443/400000000 : ℝ)*X 0 1+(-1444898343/5000000000 : ℝ)*X 0 2+(-67330069/2500000000 : ℝ)*X 1 0+(337766443/400000000 : ℝ)*X 1 1+(-1444898343/5000000000 : ℝ)*X 1 2+(-67330069/2500000000 : ℝ)*X 2 0+(337766443/400000000 : ℝ)*X 2 1+(-1444898343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2530043191/5000000000 : ℝ)*X 0 0+(74437699/400000000 : ℝ)*X 0 1+(-1454383603/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((323360999/500000000 : ℝ)*X 1 0+(-37300273/2000000000 : ℝ)*X 1 1+(-66622637/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1129458857/5000000000 : ℝ)*X 2 0+(1428512419/2000000000 : ℝ)*X 2 1+(3205649313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-19616281/500000000 : ℝ)*X 0 0+(8876984831/10000000000 : ℝ)*X 0 1+(-435927381/2000000000 : ℝ)*X 0 2+(-19616281/500000000 : ℝ)*X 1 0+(8876984831/10000000000 : ℝ)*X 1 1+(-435927381/2000000000 : ℝ)*X 1 2+(-19616281/500000000 : ℝ)*X 2 0+(8876984831/10000000000 : ℝ)*X 2 1+(-435927381/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-5524343549/10000000000 : ℝ)*X 0 0+(2199573937/10000000000 : ℝ)*X 0 1+(-5113042663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((128494801/200000000 : ℝ)*X 1 0+(-2991317/2000000000 : ℝ)*X 1 1+(-5420154051/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((2640877651/10000000000 : ℝ)*X 2 0+(1696069169/2500000000 : ℝ)*X 2 1+(3316807531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-428877699/10000000000 : ℝ)*X 0 0+(20562193/31250000 : ℝ)*X 0 1+(-5113042663/10000000000 : ℝ)*X 0 2+(-428877699/10000000000 : ℝ)*X 1 0+(20562193/31250000 : ℝ)*X 1 1+(-5113042663/10000000000 : ℝ)*X 1 2+(-428877699/10000000000 : ℝ)*X 2 0+(20562193/31250000 : ℝ)*X 2 1+(-5113042663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1285824191/2000000000 : ℝ)*X 0 0+(667201663/2500000000 : ℝ)*X 0 1+(-1863756911/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((5195571281/10000000000 : ℝ)*X 1 0+(-70707409/10000000000 : ℝ)*X 1 1+(-1324814327/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3446487897/5000000000 : ℝ)*X 2 0+(185337579/500000000 : ℝ)*X 2 1+(2041152959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((-317632883/10000000000 : ℝ)*X 0 0+(4610314269/5000000000 : ℝ)*X 0 1+(-33036149/200000000 : ℝ)*X 0 2+(-317632883/10000000000 : ℝ)*X 1 0+(4610314269/5000000000 : ℝ)*X 1 1+(-33036149/200000000 : ℝ)*X 1 2+(-317632883/10000000000 : ℝ)*X 2 0+(4610314269/5000000000 : ℝ)*X 2 1+(-33036149/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((91019/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(91019/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3752049294653546419101/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (343786550847/500000000000 : ℝ)*(base7) + (1107759/500000000000 : ℝ)*(base15) + (558112771/2500000000 : ℝ)*(base44) + (251027021407/1000000000000 : ℝ)*(base50) + (303231725513/500000000000 : ℝ)*(base53) + (181623/200000000000 : ℝ)*(base60) + (186251288201/100000000000 : ℝ)*(major_s0_0) + (163926777361/100000000000 : ℝ)*(major_s0_1) + (157006178873/125000000000 : ℝ)*(major_s0_2) + (15604199/500000000000 : ℝ)*(sp_s0_6) + (143595632069/100000000000 : ℝ)*(sp_s0_7) + (303177249193/250000000000 : ℝ)*(sp_s0_8) + (510604942929/250000000000 : ℝ)*(sp_s0_9) + (215424750049/125000000000 : ℝ)*(sp_s0_13) + (157387651937/125000000000 : ℝ)*(f.failure) + (510604942929/250000000000 : ℝ)*(f.sum) + (1096264080885267/5000000000000000000000000000 : ℝ)*base62 + (835610984245339/1250000000000000000000000000 : ℝ)*base65 + (89637300153123/1000000000000000000000000000 : ℝ)*base66 + (1255808784692397/1250000000000000000000000000 : ℝ)*base69 + (2791324075732411/5000000000000000000000000000 : ℝ)*base71 + (356128413376757/1000000000000000000000000000 : ℝ)*base72 + (36080291530971/1000000000000000000000000000 : ℝ)*base74 + (402139212550211/1000000000000000000000000000 : ℝ)*base77 + (12034676421753/25000000000000000000000000 : ℝ)*base79 + (947/3125000000000000 : ℝ)*base87 + (947/3125000000000000 : ℝ)*base89 + (947/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4177/6250 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(4177/6250 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7197577245661932791373/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1783612266573/1000000000000 : ℝ)*(base1) + (471093451987/500000000000 : ℝ)*(base7) + (405574512357/1000000000000 : ℝ)*(base39) + (13723/40000000000 : ℝ)*(base50) + (320175756561/1000000000000 : ℝ)*(base60) + (1795335866573/1000000000000 : ℝ)*(major_s0_0) + (1795335866573/1000000000000 : ℝ)*(major_s0_1) + (1795335866573/1000000000000 : ℝ)*(major_s0_2) + (2338541/100000000000 : ℝ)*(sp_s0_2) + (12836501/500000000000 : ℝ)*(sp_s0_7) + (3580237305977/1000000000000 : ℝ)*(sp_s0_14) + (898325356203/500000000000 : ℝ)*(sp_s0_15) + (449156831749/250000000000 : ℝ)*(sp_s0_16) + (11633208041/31250000000 : ℝ)*(sp_s0_20) + (1213688019911/1000000000000 : ℝ)*(f.failure) + (898325356203/500000000000 : ℝ)*(f.sum) + (419096436372303/5000000000000000000000000000 : ℝ)*base62 + (4827110350436439/10000000000000000000000000000 : ℝ)*base65 + (1133717438436439/10000000000000000000000000000 : ℝ)*base66 + (4026710239127697/10000000000000000000000000000 : ℝ)*base69 + (1966699904154371/5000000000000000000000000000 : ℝ)*base71 + (6259380568563561/10000000000000000000000000000 : ℝ)*base72 + (79406826872303/10000000000000000000000000000 : ℝ)*base74 + (4734994022872303/10000000000000000000000000000 : ℝ)*base77 + (108288143/1000000000000000000000 : ℝ)*base78 + (3691/25000000000000000 : ℝ)*base87 + (3691/25000000000000000 : ℝ)*base89 + (3691/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-89337/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-89337/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1578238896776805840417/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (99843184591/250000000000 : ℝ)*(base1) + (336443400509/500000000000 : ℝ)*(base7) + (89710182387/1000000000000 : ℝ)*(base33) + (1020833412333/1000000000000 : ℝ)*(base44) + (126179849033/500000000000 : ℝ)*(base50) + (304881/250000000000 : ℝ)*(base60) + (1055029527201/500000000000 : ℝ)*(major_s0_0) + (235787164891/200000000000 : ℝ)*(major_s0_1) + (2199769236789/1000000000000 : ℝ)*(major_s0_2) + (6566837/125000000000 : ℝ)*(sp_s0_1) + (2897354898711/1000000000000 : ℝ)*(sp_s0_21) + (1387386030931/1000000000000 : ℝ)*(sp_s0_22) + (60206799449/25000000000 : ℝ)*(sp_s0_23) + (73977485869/100000000000 : ℝ)*(sp_s0_27) + (148709420837/100000000000 : ℝ)*(f.failure) + (2497982160347/1000000000000 : ℝ)*(f.sum) + (1036937144548421/2500000000000000000000000000 : ℝ)*base62 + (3640696095354673/10000000000000000000000000000 : ℝ)*base64 + (241019061965087/2000000000000000000000000000 : ℝ)*base67 + (2374285409775321/10000000000000000000000000000 : ℝ)*base69 + (1371025622403749/10000000000000000000000000000 : ℝ)*base71 + (1189499559999757/5000000000000000000000000000 : ℝ)*base72 + (173718903593801/2000000000000000000000000000 : ℝ)*base74 + (2480808954620789/5000000000000000000000000000 : ℝ)*base76 + (5814022614825921/10000000000000000000000000000 : ℝ)*base79 + (597/2500000000000000 : ℝ)*base87 + (3097/2500000000000000 : ℝ)*base89 + (597/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (91019/100000 : ℝ) ^ (129/32 : ℝ) ≤ (34215360494876116693/50000000000000000000 : ℝ) := by
    have hpowers : (91019/100000 : ℝ)^129 ≤ (34215360494876116693/50000000000000000000 : ℝ)^32 := by
      have hnat : (91019 : ℕ)^129*50000000000000000000^32 ≤ 34215360494876116693^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91019 100000 34215360494876116693 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91019/100000 : ℝ)) (X := (34215360494876116693/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (84215360494876116693/50000000000000000000 : ℝ) ≤ (11380635814458409/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (84215360494876116693/50000000000000000000 : ℝ)^32 ≤ (11380635814458409/10000000000000000 : ℝ)^129 := by
      have hnat : (84215360494876116693 : ℕ)^32*10000000000000000^129 ≤ 11380635814458409^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        84215360494876116693 50000000000000000000 11380635814458409 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11380635814458409/10000000000000000 : ℝ)) (X := (84215360494876116693/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (59215360494876116693/25000000000000000000 : ℝ) ≤ (6192525908452213/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (59215360494876116693/25000000000000000000 : ℝ)^32 ≤ (6192525908452213/5000000000000000 : ℝ)^129 := by
      have hnat : (59215360494876116693 : ℕ)^32*5000000000000000^129 ≤ 6192525908452213^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59215360494876116693 25000000000000000000 6192525908452213 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6192525908452213/5000000000000000 : ℝ)) (X := (59215360494876116693/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1380635814458409/9101900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1004416002446017/9101900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (91019/100000 : ℝ)) (alpha := (1380635814458409/9101900000000000 : ℝ)) (beta := (1004416002446017/9101900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (91019/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1380635814458409/9101900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1004416002446017/9101900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (4177/6250 : ℝ) ^ (129/32 : ℝ) ≤ (19700107498096341229/100000000000000000000 : ℝ) := by
    have hpowers : (4177/6250 : ℝ)^129 ≤ (19700107498096341229/100000000000000000000 : ℝ)^32 := by
      have hnat : (4177 : ℕ)^129*100000000000000000000^32 ≤ 19700107498096341229^32*6250^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4177 6250 19700107498096341229 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4177/6250 : ℝ)) (X := (19700107498096341229/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (119700107498096341229/100000000000000000000 : ℝ) ≤ (1307020207380493/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (119700107498096341229/100000000000000000000 : ℝ)^32 ≤ (1307020207380493/1250000000000000 : ℝ)^129 := by
      have hnat : (119700107498096341229 : ℕ)^32*1250000000000000^129 ≤ 1307020207380493^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        119700107498096341229 100000000000000000000 1307020207380493 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1307020207380493/1250000000000000 : ℝ)) (X := (119700107498096341229/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (69700107498096341229/50000000000000000000 : ℝ) ≤ (5429455586587041/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (69700107498096341229/50000000000000000000 : ℝ)^32 ≤ (5429455586587041/5000000000000000 : ℝ)^129 := by
      have hnat : (69700107498096341229 : ℕ)^32*5000000000000000^129 ≤ 5429455586587041^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69700107498096341229 50000000000000000000 5429455586587041 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5429455586587041/5000000000000000 : ℝ)) (X := (69700107498096341229/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(57020207380493/835400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(201374757065069/3341600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (4177/6250 : ℝ)) (alpha := (57020207380493/835400000000000 : ℝ)) (beta := (201374757065069/3341600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (4177/6250 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(57020207380493/835400000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(201374757065069/3341600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (89337/100000 : ℝ) ^ (129/32 : ℝ) ≤ (495889849100447779/781250000000000000 : ℝ) := by
    have hpowers : (89337/100000 : ℝ)^129 ≤ (495889849100447779/781250000000000000 : ℝ)^32 := by
      have hnat : (89337 : ℕ)^129*781250000000000000^32 ≤ 495889849100447779^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89337 100000 495889849100447779 781250000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89337/100000 : ℝ)) (X := (495889849100447779/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (1277139849100447779/781250000000000000 : ℝ) ≤ (11296618090943353/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (1277139849100447779/781250000000000000 : ℝ)^32 ≤ (11296618090943353/10000000000000000 : ℝ)^129 := by
      have hnat : (1277139849100447779 : ℕ)^32*10000000000000000^129 ≤ 11296618090943353^129*781250000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1277139849100447779 781250000000000000 11296618090943353 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296618090943353/10000000000000000 : ℝ)) (X := (1277139849100447779/781250000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (886514849100447779/390625000000000000 : ℝ) ≤ (61271952556631/50000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (886514849100447779/390625000000000000 : ℝ)^32 ≤ (61271952556631/50000000000000 : ℝ)^129 := by
      have hnat : (886514849100447779 : ℕ)^32*50000000000000^129 ≤ 61271952556631^129*390625000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        886514849100447779 390625000000000000 61271952556631 50000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (61271952556631/50000000000000 : ℝ)) (X := (886514849100447779/390625000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(4455732271283/30700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(319257473460949/2977900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (89337/100000 : ℝ)) (alpha := (4455732271283/30700000000000 : ℝ)) (beta := (319257473460949/2977900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (89337/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(4455732271283/30700000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(319257473460949/2977900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2539817593/5000000000 : ℝ)*X 0 0+(3480935619/10000000000 : ℝ)*X 0 1+(-224745891/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2462538609/5000000000 : ℝ)*X 1 0+(-2935329899/10000000000 : ℝ)*X 1 1+(-5129366441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4476610769/10000000000 : ℝ)*X 2 0+(471227707/1000000000 : ℝ)*X 2 1+(1951646673/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((39468633/312500000 : ℝ)*X 0 0+(1955046629/2500000000 : ℝ)*X 0 1+(-3128281109/10000000000 : ℝ)*X 0 2+(39468633/312500000 : ℝ)*X 1 0+(1955046629/2500000000 : ℝ)*X 1 1+(-3128281109/10000000000 : ℝ)*X 1 2+(39468633/312500000 : ℝ)*X 2 0+(1955046629/2500000000 : ℝ)*X 2 1+(-3128281109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301018_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-73443/12500 : ℝ) < ((-36981/25000 : ℝ)*P 0+(-36981/25000 : ℝ)*P 1+(-36981/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-73443/12500 : ℝ) < (-41516485546012820366312241804479127/7075981064860625000000000000000000 : ℝ) := by norm_num
    linear_combination (3293/250000000000 : ℝ)*(base12) + (4361/1000000000000 : ℝ)*(base16) + (1343/100000000000 : ℝ)*(base23) + (7957/1000000000000 : ℝ)*(base39) + (5007/1000000000000 : ℝ)*(base40) + (376463094981/1000000000000 : ℝ)*(base50) + (719/200000000000 : ℝ)*(base59) + (175026166229/1000000000000 : ℝ)*(base60) + (36981/25000 : ℝ)*(major_s1_0) + (36981/25000 : ℝ)*(major_s1_1) + (36981/25000 : ℝ)*(major_s1_2) + (488936738781/250000000000 : ℝ)*(sp_s1_0) + (391149392787/200000000000 : ℝ)*(sp_s1_1) + (977873477433/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (244468371037/125000000000 : ℝ)*(f.sum) + (195206339712913/1602923750000000000000000000 : ℝ)*base62 + (50039823732981/74447500000000000000000000 : ℝ)*base64 + (26998677917/522125000000000000000000 : ℝ)*base67 + (71988477881/307000000000000000000000 : ℝ)*base68 + (68938108236649087/5420909602000000000000000000000 : ℝ)*base70 + (97933361342727/182038000000000000000000000 : ℝ)*base72 + (281927755929/20885000000000000000000000 : ℝ)*base74 + (1871549992511/45509500000000000000000000 : ℝ)*base77 + (619425768234487467/950465907500000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p001_b008 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 18 ≤ c.val) (hhi : c.val < 19)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=18 := by omega
  rcases hc with rfl
  · exact collision_c301018 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 18 ≤ c.val) (hhi : c.val < 19)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b008 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

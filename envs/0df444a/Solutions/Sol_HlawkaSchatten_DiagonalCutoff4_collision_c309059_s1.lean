-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309059_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:03:57.312551+00:00
-- url     : https://prove2.me/submissions/42666b70-1cca-4d97-88bc-38d3582c4fce

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
theorem collision_support_c309059_s1_s1_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3080773509/10000000000 : ℝ)*x 0 + (153988923/500000000 : ℝ)*x 1 + (3220547123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3080773509/10000000000 : ℝ)^35 ≤ (21734595163573/100000000000000 : ℝ)^27 := by
    have hnat : (3080773509 : ℕ)^35*100000000000000^27 ≤ 21734595163573^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3080773509 10000000000 21734595163573 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153988923/500000000 : ℝ)^35 ≤ (21725495617069/100000000000000 : ℝ)^27 := by
    have hnat : (153988923 : ℕ)^35*100000000000000^27 ≤ 21725495617069^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153988923 500000000 21725495617069 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3220547123/5000000000 : ℝ)^35 ≤ (1130798184177/2000000000000 : ℝ)^27 := by
    have hnat : (3220547123 : ℕ)^35*2000000000000^27 ≤ 1130798184177^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3220547123 5000000000 1130798184177 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3080773509/10000000000 : ℝ), (153988923/500000000 : ℝ), (3220547123/5000000000 : ℝ)] ![(21734595163573/100000000000000 : ℝ), (21725495617069/100000000000000 : ℝ), (1130798184177/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3080773509/10000000000 : ℝ)|^35 ≤ (21734595163573/100000000000000 : ℝ)^27
        have hw : |(-3080773509/10000000000 : ℝ)|=(3080773509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(153988923/500000000 : ℝ)|^35 ≤ (21725495617069/100000000000000 : ℝ)^27
        have hw : |(153988923/500000000 : ℝ)|=(153988923/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3220547123/5000000000 : ℝ)|^35 ≤ (1130798184177/2000000000000 : ℝ)^27
        have hw : |(3220547123/5000000000 : ℝ)|=(3220547123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309059_s1_s1_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (385037139/1250000000 : ℝ)*x 0 + (-3078810773/10000000000 : ℝ)*x 1 + (805281839/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (385037139/1250000000 : ℝ)^35 ≤ (5432559622221/25000000000000 : ℝ)^27 := by
    have hnat : (385037139 : ℕ)^35*25000000000000^27 ≤ 5432559622221^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385037139 1250000000 5432559622221 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3078810773/10000000000 : ℝ)^35 ≤ (10858323563331/50000000000000 : ℝ)^27 := by
    have hnat : (3078810773 : ℕ)^35*50000000000000^27 ≤ 10858323563331^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3078810773 10000000000 10858323563331 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805281839/1250000000 : ℝ)^35 ≤ (11310622874241/20000000000000 : ℝ)^27 := by
    have hnat : (805281839 : ℕ)^35*20000000000000^27 ≤ 11310622874241^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805281839 1250000000 11310622874241 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(385037139/1250000000 : ℝ), (-3078810773/10000000000 : ℝ), (805281839/1250000000 : ℝ)] ![(5432559622221/25000000000000 : ℝ), (10858323563331/50000000000000 : ℝ), (11310622874241/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(385037139/1250000000 : ℝ)|^35 ≤ (5432559622221/25000000000000 : ℝ)^27
        have hw : |(385037139/1250000000 : ℝ)|=(385037139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3078810773/10000000000 : ℝ)|^35 ≤ (10858323563331/50000000000000 : ℝ)^27
        have hw : |(-3078810773/10000000000 : ℝ)|=(3078810773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(805281839/1250000000 : ℝ)|^35 ≤ (11310622874241/20000000000000 : ℝ)^27
        have hw : |(805281839/1250000000 : ℝ)|=(805281839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309059_s1_s1_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-932478877/5000000000 : ℝ)*x 0 + (1193268887/10000000000 : ℝ)*x 1 + (2151285541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (932478877/5000000000 : ℝ)^35 ≤ (708681247807/6250000000000 : ℝ)^27 := by
    have hnat : (932478877 : ℕ)^35*6250000000000^27 ≤ 708681247807^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932478877 5000000000 708681247807 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1193268887/10000000000 : ℝ)^35 ≤ (6355932844963/100000000000000 : ℝ)^27 := by
    have hnat : (1193268887 : ℕ)^35*100000000000000^27 ≤ 6355932844963^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193268887 10000000000 6355932844963 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2151285541/2500000000 : ℝ)^35 ≤ (41152583586501/50000000000000 : ℝ)^27 := by
    have hnat : (2151285541 : ℕ)^35*50000000000000^27 ≤ 41152583586501^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151285541 2500000000 41152583586501 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-932478877/5000000000 : ℝ), (1193268887/10000000000 : ℝ), (2151285541/2500000000 : ℝ)] ![(708681247807/6250000000000 : ℝ), (6355932844963/100000000000000 : ℝ), (41152583586501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-932478877/5000000000 : ℝ)|^35 ≤ (708681247807/6250000000000 : ℝ)^27
        have hw : |(-932478877/5000000000 : ℝ)|=(932478877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1193268887/10000000000 : ℝ)|^35 ≤ (6355932844963/100000000000000 : ℝ)^27
        have hw : |(1193268887/10000000000 : ℝ)|=(1193268887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2151285541/2500000000 : ℝ)|^35 ≤ (41152583586501/50000000000000 : ℝ)^27
        have hw : |(2151285541/2500000000 : ℝ)|=(2151285541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309059_s1_s1_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (875509063/5000000000 : ℝ)*x 0 + (-658737997/5000000000 : ℝ)*x 1 + (4303346659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875509063/5000000000 : ℝ)^35 ≤ (10449137920823/100000000000000 : ℝ)^27 := by
    have hnat : (875509063 : ℕ)^35*100000000000000^27 ≤ 10449137920823^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875509063 5000000000 10449137920823 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658737997/5000000000 : ℝ)^35 ≤ (7226462210379/100000000000000 : ℝ)^27 := by
    have hnat : (658737997 : ℕ)^35*100000000000000^27 ≤ 7226462210379^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658737997 5000000000 7226462210379 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4303346659/5000000000 : ℝ)^35 ≤ (82324399854797/100000000000000 : ℝ)^27 := by
    have hnat : (4303346659 : ℕ)^35*100000000000000^27 ≤ 82324399854797^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303346659 5000000000 82324399854797 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875509063/5000000000 : ℝ), (-658737997/5000000000 : ℝ), (4303346659/5000000000 : ℝ)] ![(10449137920823/100000000000000 : ℝ), (7226462210379/100000000000000 : ℝ), (82324399854797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875509063/5000000000 : ℝ)|^35 ≤ (10449137920823/100000000000000 : ℝ)^27
        have hw : |(875509063/5000000000 : ℝ)|=(875509063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-658737997/5000000000 : ℝ)|^35 ≤ (7226462210379/100000000000000 : ℝ)^27
        have hw : |(-658737997/5000000000 : ℝ)|=(658737997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4303346659/5000000000 : ℝ)|^35 ≤ (82324399854797/100000000000000 : ℝ)^27
        have hw : |(4303346659/5000000000 : ℝ)|=(4303346659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309059_s1_s1_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4110394143/10000000000 : ℝ)*x 0 + (1865358753/2500000000 : ℝ)*x 1 + (-1157347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4110394143/10000000000 : ℝ)^35 ≤ (31584831892421/100000000000000 : ℝ)^27 := by
    have hnat : (4110394143 : ℕ)^35*100000000000000^27 ≤ 31584831892421^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4110394143 10000000000 31584831892421 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1865358753/2500000000 : ℝ)^35 ≤ (2137913446891/3125000000000 : ℝ)^27 := by
    have hnat : (1865358753 : ℕ)^35*3125000000000^27 ≤ 2137913446891^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865358753 2500000000 2137913446891 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1157347/5000000000 : ℝ)^35 ≤ (1937789063/100000000000000 : ℝ)^27 := by
    have hnat : (1157347 : ℕ)^35*100000000000000^27 ≤ 1937789063^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157347 5000000000 1937789063 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4110394143/10000000000 : ℝ), (1865358753/2500000000 : ℝ), (-1157347/5000000000 : ℝ)] ![(31584831892421/100000000000000 : ℝ), (2137913446891/3125000000000 : ℝ), (1937789063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4110394143/10000000000 : ℝ)|^35 ≤ (31584831892421/100000000000000 : ℝ)^27
        have hw : |(4110394143/10000000000 : ℝ)|=(4110394143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1865358753/2500000000 : ℝ)|^35 ≤ (2137913446891/3125000000000 : ℝ)^27
        have hw : |(1865358753/2500000000 : ℝ)|=(1865358753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1157347/5000000000 : ℝ)|^35 ≤ (1937789063/100000000000000 : ℝ)^27
        have hw : |(-1157347/5000000000 : ℝ)|=(1157347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309059_s1_s1_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1960560639/10000000000 : ℝ)*x 0 + (4109026903/5000000000 : ℝ)*x 1 + (1739978747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1960560639/10000000000 : ℝ)^35 ≤ (3024511119879/25000000000000 : ℝ)^27 := by
    have hnat : (1960560639 : ℕ)^35*25000000000000^27 ≤ 3024511119879^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960560639 10000000000 3024511119879 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4109026903/5000000000 : ℝ)^35 ≤ (77538133946117/100000000000000 : ℝ)^27 := by
    have hnat : (4109026903 : ℕ)^35*100000000000000^27 ≤ 77538133946117^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109026903 5000000000 77538133946117 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1739978747/10000000000 : ℝ)^35 ≤ (2590955390219/25000000000000 : ℝ)^27 := by
    have hnat : (1739978747 : ℕ)^35*25000000000000^27 ≤ 2590955390219^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1739978747 10000000000 2590955390219 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1960560639/10000000000 : ℝ), (4109026903/5000000000 : ℝ), (1739978747/10000000000 : ℝ)] ![(3024511119879/25000000000000 : ℝ), (77538133946117/100000000000000 : ℝ), (2590955390219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1960560639/10000000000 : ℝ)|^35 ≤ (3024511119879/25000000000000 : ℝ)^27
        have hw : |(1960560639/10000000000 : ℝ)|=(1960560639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4109026903/5000000000 : ℝ)|^35 ≤ (77538133946117/100000000000000 : ℝ)^27
        have hw : |(4109026903/5000000000 : ℝ)|=(4109026903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1739978747/10000000000 : ℝ)|^35 ≤ (2590955390219/25000000000000 : ℝ)^27
        have hw : |(1739978747/10000000000 : ℝ)|=(1739978747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309059_s1_s1_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-155415963/1000000000 : ℝ)*x 0 + (489456449/2500000000 : ℝ)*x 1 + (8334997619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (155415963/1000000000 : ℝ)^35 ≤ (4476192713081/50000000000000 : ℝ)^27 := by
    have hnat : (155415963 : ℕ)^35*50000000000000^27 ≤ 4476192713081^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155415963 1000000000 4476192713081 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489456449/2500000000 : ℝ)^35 ≤ (2415234563469/20000000000000 : ℝ)^27 := by
    have hnat : (489456449 : ℕ)^35*20000000000000^27 ≤ 2415234563469^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489456449 2500000000 2415234563469 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8334997619/10000000000 : ℝ)^35 ≤ (78971441745127/100000000000000 : ℝ)^27 := by
    have hnat : (8334997619 : ℕ)^35*100000000000000^27 ≤ 78971441745127^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8334997619 10000000000 78971441745127 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-155415963/1000000000 : ℝ), (489456449/2500000000 : ℝ), (8334997619/10000000000 : ℝ)] ![(4476192713081/50000000000000 : ℝ), (2415234563469/20000000000000 : ℝ), (78971441745127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-155415963/1000000000 : ℝ)|^35 ≤ (4476192713081/50000000000000 : ℝ)^27
        have hw : |(-155415963/1000000000 : ℝ)|=(155415963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(489456449/2500000000 : ℝ)|^35 ≤ (2415234563469/20000000000000 : ℝ)^27
        have hw : |(489456449/2500000000 : ℝ)|=(489456449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8334997619/10000000000 : ℝ)|^35 ≤ (78971441745127/100000000000000 : ℝ)^27
        have hw : |(8334997619/10000000000 : ℝ)|=(8334997619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309059_s1_s1_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (733698059/5000000000 : ℝ)*x 0 + (-1017706469/5000000000 : ℝ)*x 1 + (4168250221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (733698059/5000000000 : ℝ)^35 ≤ (1661990101307/20000000000000 : ℝ)^27 := by
    have hnat : (733698059 : ℕ)^35*20000000000000^27 ≤ 1661990101307^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733698059 5000000000 1661990101307 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1017706469/5000000000 : ℝ)^35 ≤ (3175037396069/25000000000000 : ℝ)^27 := by
    have hnat : (1017706469 : ℕ)^35*25000000000000^27 ≤ 3175037396069^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017706469 5000000000 3175037396069 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4168250221/5000000000 : ℝ)^35 ≤ (19747474975153/25000000000000 : ℝ)^27 := by
    have hnat : (4168250221 : ℕ)^35*25000000000000^27 ≤ 19747474975153^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168250221 5000000000 19747474975153 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(733698059/5000000000 : ℝ), (-1017706469/5000000000 : ℝ), (4168250221/5000000000 : ℝ)] ![(1661990101307/20000000000000 : ℝ), (3175037396069/25000000000000 : ℝ), (19747474975153/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(733698059/5000000000 : ℝ)|^35 ≤ (1661990101307/20000000000000 : ℝ)^27
        have hw : |(733698059/5000000000 : ℝ)|=(733698059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1017706469/5000000000 : ℝ)|^35 ≤ (3175037396069/25000000000000 : ℝ)^27
        have hw : |(-1017706469/5000000000 : ℝ)|=(1017706469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4168250221/5000000000 : ℝ)|^35 ≤ (19747474975153/25000000000000 : ℝ)^27
        have hw : |(4168250221/5000000000 : ℝ)|=(4168250221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309059_s1_s1_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (849734547/1000000000 : ℝ)*x 0 + (1390236513/5000000000 : ℝ)*x 1 + (2919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849734547/1000000000 : ℝ)^35 ≤ (40485562356503/50000000000000 : ℝ)^27 := by
    have hnat : (849734547 : ℕ)^35*50000000000000^27 ≤ 40485562356503^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849734547 1000000000 40485562356503 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1390236513/5000000000 : ℝ)^35 ≤ (2378609366983/12500000000000 : ℝ)^27 := by
    have hnat : (1390236513 : ℕ)^35*12500000000000^27 ≤ 2378609366983^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390236513 5000000000 2378609366983 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2919/10000000000 : ℝ)^35 ≤ (338071/100000000000000 : ℝ)^27 := by
    have hnat : (2919 : ℕ)^35*100000000000000^27 ≤ 338071^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2919 10000000000 338071 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849734547/1000000000 : ℝ), (1390236513/5000000000 : ℝ), (2919/10000000000 : ℝ)] ![(40485562356503/50000000000000 : ℝ), (2378609366983/12500000000000 : ℝ), (338071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849734547/1000000000 : ℝ)|^35 ≤ (40485562356503/50000000000000 : ℝ)^27
        have hw : |(849734547/1000000000 : ℝ)|=(849734547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1390236513/5000000000 : ℝ)|^35 ≤ (2378609366983/12500000000000 : ℝ)^27
        have hw : |(1390236513/5000000000 : ℝ)|=(1390236513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2919/10000000000 : ℝ)|^35 ≤ (338071/100000000000000 : ℝ)^27
        have hw : |(2919/10000000000 : ℝ)|=(2919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309059_s1_s1_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6669306943/10000000000 : ℝ)*x 0 + (3793665809/10000000000 : ℝ)*x 1 + (1996107953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6669306943/10000000000 : ℝ)^35 ≤ (11830046883283/20000000000000 : ℝ)^27 := by
    have hnat : (6669306943 : ℕ)^35*20000000000000^27 ≤ 11830046883283^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6669306943 10000000000 11830046883283 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3793665809/10000000000 : ℝ)^35 ≤ (7116653820787/25000000000000 : ℝ)^27 := by
    have hnat : (3793665809 : ℕ)^35*25000000000000^27 ≤ 7116653820787^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3793665809 10000000000 7116653820787 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1996107953/10000000000 : ℝ)^35 ≤ (12383150280523/100000000000000 : ℝ)^27 := by
    have hnat : (1996107953 : ℕ)^35*100000000000000^27 ≤ 12383150280523^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996107953 10000000000 12383150280523 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6669306943/10000000000 : ℝ), (3793665809/10000000000 : ℝ), (1996107953/10000000000 : ℝ)] ![(11830046883283/20000000000000 : ℝ), (7116653820787/25000000000000 : ℝ), (12383150280523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6669306943/10000000000 : ℝ)|^35 ≤ (11830046883283/20000000000000 : ℝ)^27
        have hw : |(6669306943/10000000000 : ℝ)|=(6669306943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3793665809/10000000000 : ℝ)|^35 ≤ (7116653820787/25000000000000 : ℝ)^27
        have hw : |(3793665809/10000000000 : ℝ)|=(3793665809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1996107953/10000000000 : ℝ)|^35 ≤ (12383150280523/100000000000000 : ℝ)^27
        have hw : |(1996107953/10000000000 : ℝ)|=(1996107953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309059_s1_s1_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2890527397/5000000000 : ℝ)*x 0 + (1225556627/5000000000 : ℝ)*x 1 + (4419152687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2890527397/5000000000 : ℝ)^35 ≤ (49146281817531/100000000000000 : ℝ)^27 := by
    have hnat : (2890527397 : ℕ)^35*100000000000000^27 ≤ 49146281817531^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2890527397 5000000000 49146281817531 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1225556627/5000000000 : ℝ)^35 ≤ (16159726604623/100000000000000 : ℝ)^27 := by
    have hnat : (1225556627 : ℕ)^35*100000000000000^27 ≤ 16159726604623^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1225556627 5000000000 16159726604623 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4419152687/10000000000 : ℝ)^35 ≤ (34693991568841/100000000000000 : ℝ)^27 := by
    have hnat : (4419152687 : ℕ)^35*100000000000000^27 ≤ 34693991568841^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419152687 10000000000 34693991568841 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2890527397/5000000000 : ℝ), (1225556627/5000000000 : ℝ), (4419152687/10000000000 : ℝ)] ![(49146281817531/100000000000000 : ℝ), (16159726604623/100000000000000 : ℝ), (34693991568841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2890527397/5000000000 : ℝ)|^35 ≤ (49146281817531/100000000000000 : ℝ)^27
        have hw : |(-2890527397/5000000000 : ℝ)|=(2890527397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1225556627/5000000000 : ℝ)|^35 ≤ (16159726604623/100000000000000 : ℝ)^27
        have hw : |(1225556627/5000000000 : ℝ)|=(1225556627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4419152687/10000000000 : ℝ)|^35 ≤ (34693991568841/100000000000000 : ℝ)^27
        have hw : |(4419152687/10000000000 : ℝ)|=(4419152687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309059_s1_s1_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (452098543/2500000000 : ℝ)*x 0 + (-476638051/2000000000 : ℝ)*x 1 + (7887805209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (452098543/2500000000 : ℝ)^35 ≤ (5447557198949/50000000000000 : ℝ)^27 := by
    have hnat : (452098543 : ℕ)^35*50000000000000^27 ≤ 5447557198949^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452098543 2500000000 5447557198949 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (476638051/2000000000 : ℝ)^35 ≤ (15581639357777/100000000000000 : ℝ)^27 := by
    have hnat : (476638051 : ℕ)^35*100000000000000^27 ≤ 15581639357777^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476638051 2000000000 15581639357777 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7887805209/10000000000 : ℝ)^35 ≤ (36761623117087/50000000000000 : ℝ)^27 := by
    have hnat : (7887805209 : ℕ)^35*50000000000000^27 ≤ 36761623117087^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7887805209 10000000000 36761623117087 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(452098543/2500000000 : ℝ), (-476638051/2000000000 : ℝ), (7887805209/10000000000 : ℝ)] ![(5447557198949/50000000000000 : ℝ), (15581639357777/100000000000000 : ℝ), (36761623117087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(452098543/2500000000 : ℝ)|^35 ≤ (5447557198949/50000000000000 : ℝ)^27
        have hw : |(452098543/2500000000 : ℝ)|=(452098543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-476638051/2000000000 : ℝ)|^35 ≤ (15581639357777/100000000000000 : ℝ)^27
        have hw : |(-476638051/2000000000 : ℝ)|=(476638051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7887805209/10000000000 : ℝ)|^35 ≤ (36761623117087/50000000000000 : ℝ)^27
        have hw : |(7887805209/10000000000 : ℝ)|=(7887805209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309059_s1_s1_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4167386313/5000000000 : ℝ)*x 0 + (600354679/2000000000 : ℝ)*x 1 + (12046831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4167386313/5000000000 : ℝ)^35 ≤ (78968678393591/100000000000000 : ℝ)^27 := by
    have hnat : (4167386313 : ℕ)^35*100000000000000^27 ≤ 78968678393591^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167386313 5000000000 78968678393591 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (600354679/2000000000 : ℝ)^35 ≤ (4202975983431/20000000000000 : ℝ)^27 := by
    have hnat : (600354679 : ℕ)^35*20000000000000^27 ≤ 4202975983431^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600354679 2000000000 4202975983431 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12046831/10000000000 : ℝ)^35 ≤ (16441682043/100000000000000 : ℝ)^27 := by
    have hnat : (12046831 : ℕ)^35*100000000000000^27 ≤ 16441682043^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12046831 10000000000 16441682043 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4167386313/5000000000 : ℝ), (600354679/2000000000 : ℝ), (12046831/10000000000 : ℝ)] ![(78968678393591/100000000000000 : ℝ), (4202975983431/20000000000000 : ℝ), (16441682043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4167386313/5000000000 : ℝ)|^35 ≤ (78968678393591/100000000000000 : ℝ)^27
        have hw : |(4167386313/5000000000 : ℝ)|=(4167386313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(600354679/2000000000 : ℝ)|^35 ≤ (4202975983431/20000000000000 : ℝ)^27
        have hw : |(600354679/2000000000 : ℝ)|=(600354679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12046831/10000000000 : ℝ)|^35 ≤ (16441682043/100000000000000 : ℝ)^27
        have hw : |(12046831/10000000000 : ℝ)|=(12046831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309059_s1_s1_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (485165723/2500000000 : ℝ)*x 0 + (7702163591/10000000000 : ℝ)*x 1 + (2522550613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (485165723/2500000000 : ℝ)^35 ≤ (11939121008873/100000000000000 : ℝ)^27 := by
    have hnat : (485165723 : ℕ)^35*100000000000000^27 ≤ 11939121008873^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485165723 2500000000 11939121008873 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7702163591/10000000000 : ℝ)^35 ≤ (71288013522857/100000000000000 : ℝ)^27 := by
    have hnat : (7702163591 : ℕ)^35*100000000000000^27 ≤ 71288013522857^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7702163591 10000000000 71288013522857 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2522550613/10000000000 : ℝ)^35 ≤ (16772865453649/100000000000000 : ℝ)^27 := by
    have hnat : (2522550613 : ℕ)^35*100000000000000^27 ≤ 16772865453649^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2522550613 10000000000 16772865453649 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(485165723/2500000000 : ℝ), (7702163591/10000000000 : ℝ), (2522550613/10000000000 : ℝ)] ![(11939121008873/100000000000000 : ℝ), (71288013522857/100000000000000 : ℝ), (16772865453649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(485165723/2500000000 : ℝ)|^35 ≤ (11939121008873/100000000000000 : ℝ)^27
        have hw : |(485165723/2500000000 : ℝ)|=(485165723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7702163591/10000000000 : ℝ)|^35 ≤ (71288013522857/100000000000000 : ℝ)^27
        have hw : |(7702163591/10000000000 : ℝ)|=(7702163591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2522550613/10000000000 : ℝ)|^35 ≤ (16772865453649/100000000000000 : ℝ)^27
        have hw : |(2522550613/10000000000 : ℝ)|=(2522550613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309059_s1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((91637/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(91637/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91549/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(91549/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(20621/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(20621/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16149/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16149/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80323/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(80323/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(15581/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(15581/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (91323/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (91637/100000 : ℝ) ^ (69/16 : ℝ) ≤ (8577102678614029739/12500000000000000000 : ℝ) := by
    have hpowers : (91637/100000 : ℝ)^69 ≤ (8577102678614029739/12500000000000000000 : ℝ)^16 := by
      have hnat : (91637 : ℕ)^69*12500000000000000000^16 ≤ 8577102678614029739^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91637 100000 8577102678614029739 12500000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91637/100000 : ℝ)) (X := (8577102678614029739/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (21077102678614029739/12500000000000000000 : ℝ) ≤ (1128794022707117/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (21077102678614029739/12500000000000000000 : ℝ)^16 ≤ (1128794022707117/1000000000000000 : ℝ)^69 := by
      have hnat : (21077102678614029739 : ℕ)^16*1000000000000000^69 ≤ 1128794022707117^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21077102678614029739 12500000000000000000 1128794022707117 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1128794022707117/1000000000000000 : ℝ)) (X := (21077102678614029739/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (14827102678614029739/6250000000000000000 : ℝ) ≤ (12217923392472277/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (14827102678614029739/6250000000000000000 : ℝ)^16 ≤ (12217923392472277/10000000000000000 : ℝ)^69 := by
      have hnat : (14827102678614029739 : ℕ)^16*10000000000000000^69 ≤ 12217923392472277^69*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14827102678614029739 6250000000000000000 12217923392472277 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12217923392472277/10000000000000000 : ℝ)) (X := (14827102678614029739/6250000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(128794022707117/916370000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(929983165401107/9163700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (91637/100000 : ℝ)) (alpha := (128794022707117/916370000000000 : ℝ)) (beta := (929983165401107/9163700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (91637/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(128794022707117/916370000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(929983165401107/9163700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (91549/100000 : ℝ) ^ (69/16 : ℝ) ≤ (34166553728500718971/50000000000000000000 : ℝ) := by
    have hpowers : (91549/100000 : ℝ)^69 ≤ (34166553728500718971/50000000000000000000 : ℝ)^16 := by
      have hnat : (91549 : ℕ)^69*50000000000000000000^16 ≤ 34166553728500718971^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91549 100000 34166553728500718971 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91549/100000 : ℝ)) (X := (34166553728500718971/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (84166553728500718971/50000000000000000000 : ℝ) ≤ (141044164932087/125000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (84166553728500718971/50000000000000000000 : ℝ)^16 ≤ (141044164932087/125000000000000 : ℝ)^69 := by
      have hnat : (84166553728500718971 : ℕ)^16*125000000000000^69 ≤ 141044164932087^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        84166553728500718971 50000000000000000000 141044164932087 125000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (141044164932087/125000000000000 : ℝ)) (X := (84166553728500718971/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (59166553728500718971/25000000000000000000 : ℝ) ≤ (12211140701065363/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (59166553728500718971/25000000000000000000 : ℝ)^16 ≤ (12211140701065363/10000000000000000 : ℝ)^69 := by
      have hnat : (59166553728500718971 : ℕ)^16*10000000000000000^69 ≤ 12211140701065363^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59166553728500718971 25000000000000000000 12211140701065363 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12211140701065363/10000000000000000 : ℝ)) (X := (59166553728500718971/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(16044164932087/114436250000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(927607506498403/9154900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (91549/100000 : ℝ)) (alpha := (16044164932087/114436250000000 : ℝ)) (beta := (927607506498403/9154900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (91549/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(16044164932087/114436250000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(927607506498403/9154900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (20621/25000 : ℝ) ^ (69/16 : ℝ) ≤ (43585736581113747241/100000000000000000000 : ℝ) := by
    have hpowers : (20621/25000 : ℝ)^69 ≤ (43585736581113747241/100000000000000000000 : ℝ)^16 := by
      have hnat : (20621 : ℕ)^69*100000000000000000000^16 ≤ 43585736581113747241^16*25000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20621 25000 43585736581113747241 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20621/25000 : ℝ)) (X := (43585736581113747241/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (143585736581113747241/100000000000000000000 : ℝ) ≤ (10875058601835743/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (143585736581113747241/100000000000000000000 : ℝ)^16 ≤ (10875058601835743/10000000000000000 : ℝ)^69 := by
      have hnat : (143585736581113747241 : ℕ)^16*10000000000000000^69 ≤ 10875058601835743^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        143585736581113747241 100000000000000000000 10875058601835743 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10875058601835743/10000000000000000 : ℝ)) (X := (143585736581113747241/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (93585736581113747241/50000000000000000000 : ℝ) ≤ (11564531322999181/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (93585736581113747241/50000000000000000000 : ℝ)^16 ≤ (11564531322999181/10000000000000000 : ℝ)^69 := by
      have hnat : (93585736581113747241 : ℕ)^16*10000000000000000^69 ≤ 11564531322999181^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93585736581113747241 50000000000000000000 11564531322999181 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11564531322999181/10000000000000000 : ℝ)) (X := (93585736581113747241/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(875058601835743/8248400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(344736360581719/4124200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (20621/25000 : ℝ)) (alpha := (875058601835743/8248400000000000 : ℝ)) (beta := (344736360581719/4124200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (20621/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(875058601835743/8248400000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(344736360581719/4124200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3080773509/10000000000 : ℝ)*X 0 0+(153988923/500000000 : ℝ)*X 0 1+(3220547123/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309059_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((385037139/1250000000 : ℝ)*X 1 0+(-3078810773/10000000000 : ℝ)*X 1 1+(805281839/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309059_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-932478877/5000000000 : ℝ)*X 0 0+(1193268887/10000000000 : ℝ)*X 0 1+(2151285541/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309059_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((875509063/5000000000 : ℝ)*X 1 0+(-658737997/5000000000 : ℝ)*X 1 1+(4303346659/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309059_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4110394143/10000000000 : ℝ)*X 2 0+(1865358753/2500000000 : ℝ)*X 2 1+(-1157347/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309059_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1960560639/10000000000 : ℝ)*X 0 0+(4109026903/5000000000 : ℝ)*X 0 1+(1739978747/10000000000 : ℝ)*X 0 2+(1960560639/10000000000 : ℝ)*X 1 0+(4109026903/5000000000 : ℝ)*X 1 1+(1739978747/10000000000 : ℝ)*X 1 2+(1960560639/10000000000 : ℝ)*X 2 0+(4109026903/5000000000 : ℝ)*X 2 1+(1739978747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309059_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-155415963/1000000000 : ℝ)*X 0 0+(489456449/2500000000 : ℝ)*X 0 1+(8334997619/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309059_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((733698059/5000000000 : ℝ)*X 1 0+(-1017706469/5000000000 : ℝ)*X 1 1+(4168250221/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309059_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((849734547/1000000000 : ℝ)*X 2 0+(1390236513/5000000000 : ℝ)*X 2 1+(2919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309059_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((6669306943/10000000000 : ℝ)*X 0 0+(3793665809/10000000000 : ℝ)*X 0 1+(1996107953/10000000000 : ℝ)*X 0 2+(6669306943/10000000000 : ℝ)*X 1 0+(3793665809/10000000000 : ℝ)*X 1 1+(1996107953/10000000000 : ℝ)*X 1 2+(6669306943/10000000000 : ℝ)*X 2 0+(3793665809/10000000000 : ℝ)*X 2 1+(1996107953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309059_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-2890527397/5000000000 : ℝ)*X 0 0+(1225556627/5000000000 : ℝ)*X 0 1+(4419152687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309059_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((452098543/2500000000 : ℝ)*X 1 0+(-476638051/2000000000 : ℝ)*X 1 1+(7887805209/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309059_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4167386313/5000000000 : ℝ)*X 2 0+(600354679/2000000000 : ℝ)*X 2 1+(12046831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309059_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((485165723/2500000000 : ℝ)*X 0 0+(7702163591/10000000000 : ℝ)*X 0 1+(2522550613/10000000000 : ℝ)*X 0 2+(485165723/2500000000 : ℝ)*X 1 0+(7702163591/10000000000 : ℝ)*X 1 1+(2522550613/10000000000 : ℝ)*X 1 2+(485165723/2500000000 : ℝ)*X 2 0+(7702163591/10000000000 : ℝ)*X 2 1+(2522550613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309059_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((16149/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16149/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5522116327630159415321446715439/380209350500600000000000000000000000 : ℝ) := by norm_num
    linear_combination (225582479873/250000000000 : ℝ)*(base7) + (94507/200000000000 : ℝ)*(base29) + (597011/1000000000000 : ℝ)*(base39) + (1933027/1000000000000 : ℝ)*(base50) + (7254107/1000000000000 : ℝ)*(base53) + (839107/1000000000000 : ℝ)*(base60) + (418510130233/250000000000 : ℝ)*(major_s1_0) + (418510130233/250000000000 : ℝ)*(major_s1_1) + (66961330673/40000000000 : ℝ)*(major_s1_2) + (1747394699053/1000000000000 : ℝ)*(sp_s1_7) + (436872450683/250000000000 : ℝ)*(sp_s1_8) + (1747497056839/1000000000000 : ℝ)*(sp_s1_9) + (1953552089099/1000000000000 : ℝ)*(sp_s1_13) + (95103679/1000000000000 : ℝ)*(sp_s1_14) + (525611321071/500000000000 : ℝ)*(f.failure) + (1747497056839/1000000000000 : ℝ)*(f.sum) + (67884277960564578087/151026554320000000000000000000000 : ℝ)*base62 + (11299687444559/824840000000000000000000000 : ℝ)*base65 + (431847830926007/1144362500000000000000000000 : ℝ)*base67 + (717270125346419/1649680000000000000000000000 : ℝ)*base68 + (1428444970045012931/5814297160000000000000000000000 : ℝ)*base71 + (38382780458769/352450000000000000000000000 : ℝ)*base73 + (41035890755999/91549000000000000000000000 : ℝ)*base74 + (513660162343/1409800000000000000000000 : ℝ)*base77 + (8979275783741937493/32266445050000000000000000000000 : ℝ)*base79 + (6463/50000000000000000 : ℝ)*base86 + (6463/50000000000000000 : ℝ)*base88 + (6463/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80323/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(80323/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17633756754052916861847519384273/1383962035822184000000000000000000000 : ℝ) := by norm_num
    linear_combination (11105767929/62500000000 : ℝ)*(base5) + (904309913427/1000000000000 : ℝ)*(base7) + (882597/250000000000 : ℝ)*(base33) + (108802752969/1000000000000 : ℝ)*(base60) + (1872408502871/1000000000000 : ℝ)*(major_s1_0) + (1872412033259/1000000000000 : ℝ)*(major_s1_1) + (1872412033259/1000000000000 : ℝ)*(major_s1_2) + (6922979/1000000000000 : ℝ)*(sp_s1_0) + (9717099/200000000000 : ℝ)*(sp_s1_8) + (2018459847283/1000000000000 : ℝ)*(sp_s1_14) + (2018411266851/1000000000000 : ℝ)*(sp_s1_15) + (1098077763369/500000000000 : ℝ)*(sp_s1_16) + (475602178539/250000000000 : ℝ)*(sp_s1_20) + (423441/125000000000 : ℝ)*(sp_s1_22) + (1175791087593/1000000000000 : ℝ)*(f.failure) + (1009233385131/500000000000 : ℝ)*(f.sum) + (76281453768578326727/755132771600000000000000000000000 : ℝ)*base63 + (2010670341387181/4124200000000000000000000000 : ℝ)*base65 + (2745185414567667/9154900000000000000000000000 : ℝ)*base67 + (3430689457817483/8248400000000000000000000000 : ℝ)*base69 + (98836633349399144877/377929315400000000000000000000000 : ℝ)*base71 + (2895767051094557/9163700000000000000000000000 : ℝ)*base73 + (40068599430479/114436250000000000000000000 : ℝ)*base75 + (148758559454203/916370000000000000000000000 : ℝ)*base77 + (4371882304771048199/419463785650000000000000000000000 : ℝ)*base78 + (22471/100000000000000000 : ℝ)*base87 + (22471/100000000000000000 : ℝ)*base89 + (22471/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(15581/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(15581/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2844722763207732109691712361623/308920097281737500000000000000000000 : ℝ) := by norm_num
    linear_combination (11193/2000000000 : ℝ)*(base5) + (92784154637/200000000000 : ℝ)*(base7) + (48217304509/500000000000 : ℝ)*(base33) + (655892975151/1000000000000 : ℝ)*(base44) + (43798867497/1000000000000 : ℝ)*(base50) + (1568050818383/1000000000000 : ℝ)*(major_s1_0) + (1008592452251/1000000000000 : ℝ)*(major_s1_1) + (832242713701/500000000000 : ℝ)*(major_s1_2) + (147425871/1000000000000 : ℝ)*(sp_s1_1) + (39350227/250000000000 : ℝ)*(sp_s1_16) + (2001301069757/1000000000000 : ℝ)*(sp_s1_21) + (1248826059717/1000000000000 : ℝ)*(sp_s1_22) + (1904714656331/1000000000000 : ℝ)*(sp_s1_23) + (853244671911/1000000000000 : ℝ)*(sp_s1_27) + (1045222470377/1000000000000 : ℝ)*(f.failure) + (2001301069757/1000000000000 : ℝ)*(f.sum) + (82653338853213869193/377566385800000000000000000000000 : ℝ)*base63 + (100253143294571/2062100000000000000000000000 : ℝ)*base64 + (233937424140827/9154900000000000000000000000 : ℝ)*base66 + (2378087862475803/4124200000000000000000000000 : ℝ)*base68 + (2169888706871023071/26994951100000000000000000000000 : ℝ)*base70 + (167197644106603/1309100000000000000000000000 : ℝ)*base73 + (104212070792313/457745000000000000000000000 : ℝ)*base74 + (14474480577641/130910000000000000000000000 : ℝ)*base76 + (141811651410408623/479387183600000000000000000000 : ℝ)*base78 + (26119/100000000000000000 : ℝ)*base87 + (73881/100000000000000000 : ℝ)*base88 + (73881/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((91637/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(91637/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91549/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(91549/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(20621/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(20621/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16149/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16149/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80323/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(80323/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(15581/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(15581/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309059_s1 p hpa hpb X hX hprev0

#print axioms solution

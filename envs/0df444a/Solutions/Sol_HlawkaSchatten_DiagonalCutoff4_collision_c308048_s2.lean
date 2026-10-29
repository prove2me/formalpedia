-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308048_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:34:56.921951+00:00
-- url     : https://prove2.me/submissions/ff51abc9-0b36-4d9a-a0be-27a82dbc1be9

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
theorem collision_support_c308048_s2_s2_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-627794287/2000000000 : ℝ)*x 0 + (1569388857/5000000000 : ℝ)*x 1 + (-1586608951/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (627794287/2000000000 : ℝ)^35 ≤ (22268313313577/100000000000000 : ℝ)^27 := by
    have hnat : (627794287 : ℕ)^35*100000000000000^27 ≤ 22268313313577^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627794287 2000000000 22268313313577 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1569388857/5000000000 : ℝ)^35 ≤ (11133265924951/50000000000000 : ℝ)^27 := by
    have hnat : (1569388857 : ℕ)^35*50000000000000^27 ≤ 11133265924951^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1569388857 5000000000 11133265924951 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1586608951/2500000000 : ℝ)^35 ≤ (11093030964389/20000000000000 : ℝ)^27 := by
    have hnat : (1586608951 : ℕ)^35*20000000000000^27 ≤ 11093030964389^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586608951 2500000000 11093030964389 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-627794287/2000000000 : ℝ), (1569388857/5000000000 : ℝ), (-1586608951/2500000000 : ℝ)] ![(22268313313577/100000000000000 : ℝ), (11133265924951/50000000000000 : ℝ), (11093030964389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-627794287/2000000000 : ℝ)|^35 ≤ (22268313313577/100000000000000 : ℝ)^27
        have hw : |(-627794287/2000000000 : ℝ)|=(627794287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1569388857/5000000000 : ℝ)|^35 ≤ (11133265924951/50000000000000 : ℝ)^27
        have hw : |(1569388857/5000000000 : ℝ)|=(1569388857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1586608951/2500000000 : ℝ)|^35 ≤ (11093030964389/20000000000000 : ℝ)^27
        have hw : |(-1586608951/2500000000 : ℝ)|=(1586608951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s2_s2_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4993752661/10000000000 : ℝ)*x 0 + (4994034661/10000000000 : ℝ)*x 1 + (-1371373773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4993752661/10000000000 : ℝ)^35 ≤ (5081384826923/12500000000000 : ℝ)^27 := by
    have hnat : (4993752661 : ℕ)^35*12500000000000^27 ≤ 5081384826923^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4993752661 10000000000 5081384826923 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4994034661/10000000000 : ℝ)^35 ≤ (1626162176157/4000000000000 : ℝ)^27 := by
    have hnat : (4994034661 : ℕ)^35*4000000000000^27 ≤ 1626162176157^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4994034661 10000000000 1626162176157 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1371373773/5000000000 : ℝ)^35 ≤ (4673716740163/25000000000000 : ℝ)^27 := by
    have hnat : (1371373773 : ℕ)^35*25000000000000^27 ≤ 4673716740163^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371373773 5000000000 4673716740163 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4993752661/10000000000 : ℝ), (4994034661/10000000000 : ℝ), (-1371373773/5000000000 : ℝ)] ![(5081384826923/12500000000000 : ℝ), (1626162176157/4000000000000 : ℝ), (4673716740163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4993752661/10000000000 : ℝ)|^35 ≤ (5081384826923/12500000000000 : ℝ)^27
        have hw : |(4993752661/10000000000 : ℝ)|=(4993752661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4994034661/10000000000 : ℝ)|^35 ≤ (1626162176157/4000000000000 : ℝ)^27
        have hw : |(4994034661/10000000000 : ℝ)|=(4994034661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1371373773/5000000000 : ℝ)|^35 ≤ (4673716740163/25000000000000 : ℝ)^27
        have hw : |(-1371373773/5000000000 : ℝ)|=(1371373773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s2_s2_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-758858573/2500000000 : ℝ)*x 0 + (1376286721/5000000000 : ℝ)*x 1 + (-336710129/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (758858573/2500000000 : ℝ)^35 ≤ (21320863394709/100000000000000 : ℝ)^27 := by
    have hnat : (758858573 : ℕ)^35*100000000000000^27 ≤ 21320863394709^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758858573 2500000000 21320863394709 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376286721/5000000000 : ℝ)^35 ≤ (18781731641927/100000000000000 : ℝ)^27 := by
    have hnat : (1376286721 : ℕ)^35*100000000000000^27 ≤ 18781731641927^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376286721 5000000000 18781731641927 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336710129/500000000 : ℝ)^35 ≤ (29948702471241/50000000000000 : ℝ)^27 := by
    have hnat : (336710129 : ℕ)^35*50000000000000^27 ≤ 29948702471241^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336710129 500000000 29948702471241 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-758858573/2500000000 : ℝ), (1376286721/5000000000 : ℝ), (-336710129/500000000 : ℝ)] ![(21320863394709/100000000000000 : ℝ), (18781731641927/100000000000000 : ℝ), (29948702471241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-758858573/2500000000 : ℝ)|^35 ≤ (21320863394709/100000000000000 : ℝ)^27
        have hw : |(-758858573/2500000000 : ℝ)|=(758858573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1376286721/5000000000 : ℝ)|^35 ≤ (18781731641927/100000000000000 : ℝ)^27
        have hw : |(1376286721/5000000000 : ℝ)|=(1376286721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-336710129/500000000 : ℝ)|^35 ≤ (29948702471241/50000000000000 : ℝ)^27
        have hw : |(-336710129/500000000 : ℝ)|=(336710129/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s2_s2_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (744474397/2000000000 : ℝ)*x 0 + (-3375497961/10000000000 : ℝ)*x 1 + (-5654632107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (744474397/2000000000 : ℝ)^35 ≤ (6943769043607/25000000000000 : ℝ)^27 := by
    have hnat : (744474397 : ℕ)^35*25000000000000^27 ≤ 6943769043607^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744474397 2000000000 6943769043607 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3375497961/10000000000 : ℝ)^35 ≤ (12233651544417/50000000000000 : ℝ)^27 := by
    have hnat : (3375497961 : ℕ)^35*50000000000000^27 ≤ 12233651544417^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3375497961 10000000000 12233651544417 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5654632107/10000000000 : ℝ)^35 ≤ (47757620716659/100000000000000 : ℝ)^27 := by
    have hnat : (5654632107 : ℕ)^35*100000000000000^27 ≤ 47757620716659^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5654632107 10000000000 47757620716659 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(744474397/2000000000 : ℝ), (-3375497961/10000000000 : ℝ), (-5654632107/10000000000 : ℝ)] ![(6943769043607/25000000000000 : ℝ), (12233651544417/50000000000000 : ℝ), (47757620716659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(744474397/2000000000 : ℝ)|^35 ≤ (6943769043607/25000000000000 : ℝ)^27
        have hw : |(744474397/2000000000 : ℝ)|=(744474397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3375497961/10000000000 : ℝ)|^35 ≤ (12233651544417/50000000000000 : ℝ)^27
        have hw : |(-3375497961/10000000000 : ℝ)|=(3375497961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5654632107/10000000000 : ℝ)|^35 ≤ (47757620716659/100000000000000 : ℝ)^27
        have hw : |(-5654632107/10000000000 : ℝ)|=(5654632107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s2_s2_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2555448601/5000000000 : ℝ)*x 0 + (5895050317/10000000000 : ℝ)*x 1 + (691954959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2555448601/5000000000 : ℝ)^35 ≤ (41891501783887/100000000000000 : ℝ)^27 := by
    have hnat : (2555448601 : ℕ)^35*100000000000000^27 ≤ 41891501783887^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2555448601 5000000000 41891501783887 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5895050317/10000000000 : ℝ)^35 ≤ (50406183660381/100000000000000 : ℝ)^27 := by
    have hnat : (5895050317 : ℕ)^35*100000000000000^27 ≤ 50406183660381^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5895050317 10000000000 50406183660381 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (691954959/5000000000 : ℝ)^35 ≤ (60174332411/781250000000 : ℝ)^27 := by
    have hnat : (691954959 : ℕ)^35*781250000000^27 ≤ 60174332411^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691954959 5000000000 60174332411 781250000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2555448601/5000000000 : ℝ), (5895050317/10000000000 : ℝ), (691954959/5000000000 : ℝ)] ![(41891501783887/100000000000000 : ℝ), (50406183660381/100000000000000 : ℝ), (60174332411/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2555448601/5000000000 : ℝ)|^35 ≤ (41891501783887/100000000000000 : ℝ)^27
        have hw : |(2555448601/5000000000 : ℝ)|=(2555448601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5895050317/10000000000 : ℝ)|^35 ≤ (50406183660381/100000000000000 : ℝ)^27
        have hw : |(5895050317/10000000000 : ℝ)|=(5895050317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(691954959/5000000000 : ℝ)|^35 ≤ (60174332411/781250000000 : ℝ)^27
        have hw : |(691954959/5000000000 : ℝ)|=(691954959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s2_s2_12 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (153949103/312500000 : ℝ)*x 0 + (5682213029/10000000000 : ℝ)*x 1 + (-1948132869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (153949103/312500000 : ℝ)^35 ≤ (39941472507493/100000000000000 : ℝ)^27 := by
    have hnat : (153949103 : ℕ)^35*100000000000000^27 ≤ 39941472507493^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153949103 312500000 39941472507493 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5682213029/10000000000 : ℝ)^35 ≤ (48059800036521/100000000000000 : ℝ)^27 := by
    have hnat : (5682213029 : ℕ)^35*100000000000000^27 ≤ 48059800036521^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5682213029 10000000000 48059800036521 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1948132869/10000000000 : ℝ)^35 ≤ (11998727445527/100000000000000 : ℝ)^27 := by
    have hnat : (1948132869 : ℕ)^35*100000000000000^27 ≤ 11998727445527^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948132869 10000000000 11998727445527 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(153949103/312500000 : ℝ), (5682213029/10000000000 : ℝ), (-1948132869/10000000000 : ℝ)] ![(39941472507493/100000000000000 : ℝ), (48059800036521/100000000000000 : ℝ), (11998727445527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(153949103/312500000 : ℝ)|^35 ≤ (39941472507493/100000000000000 : ℝ)^27
        have hw : |(153949103/312500000 : ℝ)|=(153949103/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5682213029/10000000000 : ℝ)|^35 ≤ (48059800036521/100000000000000 : ℝ)^27
        have hw : |(5682213029/10000000000 : ℝ)|=(5682213029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1948132869/10000000000 : ℝ)|^35 ≤ (11998727445527/100000000000000 : ℝ)^27
        have hw : |(-1948132869/10000000000 : ℝ)|=(1948132869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s2_s2_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1376383163/5000000000 : ℝ)*x 0 + (379405849/1250000000 : ℝ)*x 1 + (-6734202677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1376383163/5000000000 : ℝ)^35 ≤ (9391718865513/50000000000000 : ℝ)^27 := by
    have hnat : (1376383163 : ℕ)^35*50000000000000^27 ≤ 9391718865513^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376383163 5000000000 9391718865513 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (379405849/1250000000 : ℝ)^35 ≤ (10659578095139/50000000000000 : ℝ)^27 := by
    have hnat : (379405849 : ℕ)^35*50000000000000^27 ≤ 10659578095139^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379405849 1250000000 10659578095139 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6734202677/10000000000 : ℝ)^35 ≤ (14974351515221/25000000000000 : ℝ)^27 := by
    have hnat : (6734202677 : ℕ)^35*25000000000000^27 ≤ 14974351515221^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6734202677 10000000000 14974351515221 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1376383163/5000000000 : ℝ), (379405849/1250000000 : ℝ), (-6734202677/10000000000 : ℝ)] ![(9391718865513/50000000000000 : ℝ), (10659578095139/50000000000000 : ℝ), (14974351515221/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1376383163/5000000000 : ℝ)|^35 ≤ (9391718865513/50000000000000 : ℝ)^27
        have hw : |(-1376383163/5000000000 : ℝ)|=(1376383163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(379405849/1250000000 : ℝ)|^35 ≤ (10659578095139/50000000000000 : ℝ)^27
        have hw : |(379405849/1250000000 : ℝ)|=(379405849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6734202677/10000000000 : ℝ)|^35 ≤ (14974351515221/25000000000000 : ℝ)^27
        have hw : |(-6734202677/10000000000 : ℝ)|=(6734202677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s2_s2_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1687867231/5000000000 : ℝ)*x 0 + (-1861071007/5000000000 : ℝ)*x 1 + (-5654632303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1687867231/5000000000 : ℝ)^35 ≤ (6117381331007/25000000000000 : ℝ)^27 := by
    have hnat : (1687867231 : ℕ)^35*25000000000000^27 ≤ 6117381331007^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687867231 5000000000 6117381331007 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1861071007/5000000000 : ℝ)^35 ≤ (27772851795017/100000000000000 : ℝ)^27 := by
    have hnat : (1861071007 : ℕ)^35*100000000000000^27 ≤ 27772851795017^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861071007 5000000000 27772851795017 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5654632303/10000000000 : ℝ)^35 ≤ (23878811431253/50000000000000 : ℝ)^27 := by
    have hnat : (5654632303 : ℕ)^35*50000000000000^27 ≤ 23878811431253^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5654632303 10000000000 23878811431253 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1687867231/5000000000 : ℝ), (-1861071007/5000000000 : ℝ), (-5654632303/10000000000 : ℝ)] ![(6117381331007/25000000000000 : ℝ), (27772851795017/100000000000000 : ℝ), (23878811431253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1687867231/5000000000 : ℝ)|^35 ≤ (6117381331007/25000000000000 : ℝ)^27
        have hw : |(1687867231/5000000000 : ℝ)|=(1687867231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1861071007/5000000000 : ℝ)|^35 ≤ (27772851795017/100000000000000 : ℝ)^27
        have hw : |(-1861071007/5000000000 : ℝ)|=(1861071007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5654632303/10000000000 : ℝ)|^35 ≤ (23878811431253/50000000000000 : ℝ)^27
        have hw : |(-5654632303/10000000000 : ℝ)|=(5654632303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s2_s2_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2947377187/5000000000 : ℝ)*x 0 + (319450381/625000000 : ℝ)*x 1 + (43247177/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2947377187/5000000000 : ℝ)^35 ≤ (12600725855467/25000000000000 : ℝ)^27 := by
    have hnat : (2947377187 : ℕ)^35*25000000000000^27 ≤ 12600725855467^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2947377187 5000000000 12600725855467 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (319450381/625000000 : ℝ)^35 ≤ (13092119951/31250000000 : ℝ)^27 := by
    have hnat : (319450381 : ℕ)^35*31250000000^27 ≤ 13092119951^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319450381 625000000 13092119951 31250000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43247177/312500000 : ℝ)^35 ≤ (1925578179019/25000000000000 : ℝ)^27 := by
    have hnat : (43247177 : ℕ)^35*25000000000000^27 ≤ 1925578179019^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43247177 312500000 1925578179019 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2947377187/5000000000 : ℝ), (319450381/625000000 : ℝ), (43247177/312500000 : ℝ)] ![(12600725855467/25000000000000 : ℝ), (13092119951/31250000000 : ℝ), (1925578179019/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2947377187/5000000000 : ℝ)|^35 ≤ (12600725855467/25000000000000 : ℝ)^27
        have hw : |(2947377187/5000000000 : ℝ)|=(2947377187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(319450381/625000000 : ℝ)|^35 ≤ (13092119951/31250000000 : ℝ)^27
        have hw : |(319450381/625000000 : ℝ)|=(319450381/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43247177/312500000 : ℝ)|^35 ≤ (1925578179019/25000000000000 : ℝ)^27
        have hw : |(43247177/312500000 : ℝ)|=(43247177/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s2_s2_18 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (35512049/62500000 : ℝ)*x 0 + (2463334549/5000000000 : ℝ)*x 1 + (-487033119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35512049/62500000 : ℝ)^35 ≤ (24028336624863/50000000000000 : ℝ)^27 := by
    have hnat : (35512049 : ℕ)^35*50000000000000^27 ≤ 24028336624863^27*62500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35512049 62500000 24028336624863 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2463334549/5000000000 : ℝ)^35 ≤ (2496537651481/6250000000000 : ℝ)^27 := by
    have hnat : (2463334549 : ℕ)^35*6250000000000^27 ≤ 2496537651481^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2463334549 5000000000 2496537651481 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (487033119/2500000000 : ℝ)^35 ≤ (2999681076953/25000000000000 : ℝ)^27 := by
    have hnat : (487033119 : ℕ)^35*25000000000000^27 ≤ 2999681076953^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487033119 2500000000 2999681076953 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(35512049/62500000 : ℝ), (2463334549/5000000000 : ℝ), (-487033119/2500000000 : ℝ)] ![(24028336624863/50000000000000 : ℝ), (2496537651481/6250000000000 : ℝ), (2999681076953/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(35512049/62500000 : ℝ)|^35 ≤ (24028336624863/50000000000000 : ℝ)^27
        have hw : |(35512049/62500000 : ℝ)|=(35512049/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2463334549/5000000000 : ℝ)|^35 ≤ (2496537651481/6250000000000 : ℝ)^27
        have hw : |(2463334549/5000000000 : ℝ)|=(2463334549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-487033119/2500000000 : ℝ)|^35 ≤ (2999681076953/25000000000000 : ℝ)^27
        have hw : |(-487033119/2500000000 : ℝ)|=(487033119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s2_s2_19 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3427350991/10000000000 : ℝ)*x 0 + (1479957323/5000000000 : ℝ)*x 1 + (-3126484351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3427350991/10000000000 : ℝ)^35 ≤ (24955629688943/100000000000000 : ℝ)^27 := by
    have hnat : (3427350991 : ℕ)^35*100000000000000^27 ≤ 24955629688943^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3427350991 10000000000 24955629688943 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1479957323/5000000000 : ℝ)^35 ≤ (515894832607/2500000000000 : ℝ)^27 := by
    have hnat : (1479957323 : ℕ)^35*2500000000000^27 ≤ 515894832607^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479957323 5000000000 515894832607 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3126484351/5000000000 : ℝ)^35 ≤ (13602144248281/25000000000000 : ℝ)^27 := by
    have hnat : (3126484351 : ℕ)^35*25000000000000^27 ≤ 13602144248281^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3126484351 5000000000 13602144248281 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3427350991/10000000000 : ℝ), (1479957323/5000000000 : ℝ), (-3126484351/5000000000 : ℝ)] ![(24955629688943/100000000000000 : ℝ), (515894832607/2500000000000 : ℝ), (13602144248281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3427350991/10000000000 : ℝ)|^35 ≤ (24955629688943/100000000000000 : ℝ)^27
        have hw : |(-3427350991/10000000000 : ℝ)|=(3427350991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1479957323/5000000000 : ℝ)|^35 ≤ (515894832607/2500000000000 : ℝ)^27
        have hw : |(1479957323/5000000000 : ℝ)|=(1479957323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3126484351/5000000000 : ℝ)|^35 ≤ (13602144248281/25000000000000 : ℝ)^27
        have hw : |(-3126484351/5000000000 : ℝ)|=(3126484351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s2_s2_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3584741229/10000000000 : ℝ)*x 0 + (-4051744481/10000000000 : ℝ)*x 1 + (-5172475099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3584741229/10000000000 : ℝ)^35 ≤ (5290239159967/20000000000000 : ℝ)^27 := by
    have hnat : (3584741229 : ℕ)^35*20000000000000^27 ≤ 5290239159967^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3584741229 10000000000 5290239159967 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4051744481/10000000000 : ℝ)^35 ≤ (31001866486687/100000000000000 : ℝ)^27 := by
    have hnat : (4051744481 : ℕ)^35*100000000000000^27 ≤ 31001866486687^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051744481 10000000000 31001866486687 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172475099/10000000000 : ℝ)^35 ≤ (5318367213353/12500000000000 : ℝ)^27 := by
    have hnat : (5172475099 : ℕ)^35*12500000000000^27 ≤ 5318367213353^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172475099 10000000000 5318367213353 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3584741229/10000000000 : ℝ), (-4051744481/10000000000 : ℝ), (-5172475099/10000000000 : ℝ)] ![(5290239159967/20000000000000 : ℝ), (31001866486687/100000000000000 : ℝ), (5318367213353/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3584741229/10000000000 : ℝ)|^35 ≤ (5290239159967/20000000000000 : ℝ)^27
        have hw : |(3584741229/10000000000 : ℝ)|=(3584741229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4051744481/10000000000 : ℝ)|^35 ≤ (31001866486687/100000000000000 : ℝ)^27
        have hw : |(-4051744481/10000000000 : ℝ)|=(4051744481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5172475099/10000000000 : ℝ)|^35 ≤ (5318367213353/12500000000000 : ℝ)^27
        have hw : |(-5172475099/10000000000 : ℝ)|=(5172475099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s2_s2_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2756114943/5000000000 : ℝ)*x 0 + (1306367843/2500000000 : ℝ)*x 1 + (890566751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2756114943/5000000000 : ℝ)^35 ≤ (46204424450519/100000000000000 : ℝ)^27 := by
    have hnat : (2756114943 : ℕ)^35*100000000000000^27 ≤ 46204424450519^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756114943 5000000000 46204424450519 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306367843/2500000000 : ℝ)^35 ≤ (43112885861697/100000000000000 : ℝ)^27 := by
    have hnat : (1306367843 : ℕ)^35*100000000000000^27 ≤ 43112885861697^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306367843 2500000000 43112885861697 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (890566751/5000000000 : ℝ)^35 ≤ (10682689673137/100000000000000 : ℝ)^27 := by
    have hnat : (890566751 : ℕ)^35*100000000000000^27 ≤ 10682689673137^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890566751 5000000000 10682689673137 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2756114943/5000000000 : ℝ), (1306367843/2500000000 : ℝ), (890566751/5000000000 : ℝ)] ![(46204424450519/100000000000000 : ℝ), (43112885861697/100000000000000 : ℝ), (10682689673137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2756114943/5000000000 : ℝ)|^35 ≤ (46204424450519/100000000000000 : ℝ)^27
        have hw : |(2756114943/5000000000 : ℝ)|=(2756114943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1306367843/2500000000 : ℝ)|^35 ≤ (43112885861697/100000000000000 : ℝ)^27
        have hw : |(1306367843/2500000000 : ℝ)|=(1306367843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(890566751/5000000000 : ℝ)|^35 ≤ (10682689673137/100000000000000 : ℝ)^27
        have hw : |(890566751/5000000000 : ℝ)|=(890566751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s2_s2_25 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4582349549/10000000000 : ℝ)*x 0 + (1306367843/2500000000 : ℝ)*x 1 + (-147372749/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4582349549/10000000000 : ℝ)^35 ≤ (7272770844521/20000000000000 : ℝ)^27 := by
    have hnat : (4582349549 : ℕ)^35*20000000000000^27 ≤ 7272770844521^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582349549 10000000000 7272770844521 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306367843/2500000000 : ℝ)^35 ≤ (43112885861697/100000000000000 : ℝ)^27 := by
    have hnat : (1306367843 : ℕ)^35*100000000000000^27 ≤ 43112885861697^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306367843 2500000000 43112885861697 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147372749/500000000 : ℝ)^35 ≤ (2565407486987/12500000000000 : ℝ)^27 := by
    have hnat : (147372749 : ℕ)^35*12500000000000^27 ≤ 2565407486987^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147372749 500000000 2565407486987 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4582349549/10000000000 : ℝ), (1306367843/2500000000 : ℝ), (-147372749/500000000 : ℝ)] ![(7272770844521/20000000000000 : ℝ), (43112885861697/100000000000000 : ℝ), (2565407486987/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4582349549/10000000000 : ℝ)|^35 ≤ (7272770844521/20000000000000 : ℝ)^27
        have hw : |(4582349549/10000000000 : ℝ)|=(4582349549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1306367843/2500000000 : ℝ)|^35 ≤ (43112885861697/100000000000000 : ℝ)^27
        have hw : |(1306367843/2500000000 : ℝ)|=(1306367843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147372749/500000000 : ℝ)|^35 ≤ (2565407486987/12500000000000 : ℝ)^27
        have hw : |(-147372749/500000000 : ℝ)|=(147372749/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308048_s2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((60981/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60981/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12191/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12191/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-6177/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-6177/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1439/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1439/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14389/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14389/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1723/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1723/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (60981/100000 : ℝ) ^ (17/4 : ℝ) ≤ (2444031498074706189/20000000000000000000 : ℝ) := by
    have hpowers : (60981/100000 : ℝ)^17 ≤ (2444031498074706189/20000000000000000000 : ℝ)^4 := by
      have hnat : (60981 : ℕ)^17*20000000000000000000^4 ≤ 2444031498074706189^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60981 100000 2444031498074706189 20000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (60981/100000 : ℝ)) (X := (2444031498074706189/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0a : (22444031498074706189/20000000000000000000 : ℝ) ≤ (5137494694888517/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (22444031498074706189/20000000000000000000 : ℝ)^4 ≤ (5137494694888517/5000000000000000 : ℝ)^17 := by
      have hnat : (22444031498074706189 : ℕ)^4*5000000000000000^17 ≤ 5137494694888517^17*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22444031498074706189 20000000000000000000 5137494694888517 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5137494694888517/5000000000000000 : ℝ)) (X := (22444031498074706189/20000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0b : (12444031498074706189/10000000000000000000 : ℝ) ≤ (10527949392572937/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (12444031498074706189/10000000000000000000 : ℝ)^4 ≤ (10527949392572937/10000000000000000 : ℝ)^17 := by
      have hnat : (12444031498074706189 : ℕ)^4*10000000000000000^17 ≤ 10527949392572937^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12444031498074706189 10000000000000000000 10527949392572937 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10527949392572937/10000000000000000 : ℝ)) (X := (12444031498074706189/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(45831564962839/1016350000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(252960002795903/6098100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (60981/100000 : ℝ)) (alpha := (45831564962839/1016350000000000 : ℝ)) (beta := (252960002795903/6098100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (60981/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(45831564962839/1016350000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(252960002795903/6098100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (12191/20000 : ℝ) ^ (17/4 : ℝ) ≤ (12198029415355773039/100000000000000000000 : ℝ) := by
    have hpowers : (12191/20000 : ℝ)^17 ≤ (12198029415355773039/100000000000000000000 : ℝ)^4 := by
      have hnat : (12191 : ℕ)^17*100000000000000000000^4 ≤ 12198029415355773039^4*20000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12191 20000 12198029415355773039 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12191/20000 : ℝ)) (X := (12198029415355773039/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1a : (112198029415355773039/100000000000000000000 : ℝ) ≤ (10274512631810161/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (112198029415355773039/100000000000000000000 : ℝ)^4 ≤ (10274512631810161/10000000000000000 : ℝ)^17 := by
      have hnat : (112198029415355773039 : ℕ)^4*10000000000000000^17 ≤ 10274512631810161^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112198029415355773039 100000000000000000000 10274512631810161 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10274512631810161/10000000000000000 : ℝ)) (X := (112198029415355773039/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1b : (62198029415355773039/50000000000000000000 : ℝ) ≤ (10527068290036197/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (62198029415355773039/50000000000000000000 : ℝ)^4 ≤ (10527068290036197/10000000000000000 : ℝ)^17 := by
      have hnat : (62198029415355773039 : ℕ)^4*10000000000000000^17 ≤ 10527068290036197^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62198029415355773039 50000000000000000000 10527068290036197 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10527068290036197/10000000000000000 : ℝ)) (X := (62198029415355773039/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(274512631810161/6095500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(63138914556509/1523875000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (12191/20000 : ℝ)) (alpha := (274512631810161/6095500000000000 : ℝ)) (beta := (63138914556509/1523875000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (12191/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(274512631810161/6095500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(63138914556509/1523875000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (6177/50000 : ℝ) ^ (17/4 : ℝ) ≤ (13809637775533593/100000000000000000000 : ℝ) := by
    have hpowers : (6177/50000 : ℝ)^17 ≤ (13809637775533593/100000000000000000000 : ℝ)^4 := by
      have hnat : (6177 : ℕ)^17*100000000000000000000^4 ≤ 13809637775533593^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6177 50000 13809637775533593 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6177/50000 : ℝ)) (X := (13809637775533593/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2a : (100013809637775533593/100000000000000000000 : ℝ) ≤ (5000162457748993/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100013809637775533593/100000000000000000000 : ℝ)^4 ≤ (5000162457748993/5000000000000000 : ℝ)^17 := by
      have hnat : (100013809637775533593 : ℕ)^4*5000000000000000^17 ≤ 5000162457748993^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100013809637775533593 100000000000000000000 5000162457748993 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000162457748993/5000000000000000 : ℝ)) (X := (100013809637775533593/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2b : (50013809637775533593/50000000000000000000 : ℝ) ≤ (10000649796690433/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50013809637775533593/50000000000000000000 : ℝ)^4 ≤ (10000649796690433/10000000000000000 : ℝ)^17 := by
      have hnat : (50013809637775533593 : ℕ)^4*10000000000000000^17 ≤ 10000649796690433^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013809637775533593 50000000000000000000 10000649796690433 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000649796690433/10000000000000000 : ℝ)) (X := (50013809637775533593/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(162457748993/617700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(324881192447/1235400000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (6177/50000 : ℝ)) (alpha := (162457748993/617700000000000 : ℝ)) (beta := (324881192447/1235400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (6177/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(162457748993/617700000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(324881192447/1235400000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-627794287/2000000000 : ℝ)*X 0 0+(1569388857/5000000000 : ℝ)*X 0 1+(-1586608951/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((4993752661/10000000000 : ℝ)*X 0 0+(4994034661/10000000000 : ℝ)*X 0 1+(-1371373773/5000000000 : ℝ)*X 0 2+(4993752661/10000000000 : ℝ)*X 1 0+(4994034661/10000000000 : ℝ)*X 1 1+(-1371373773/5000000000 : ℝ)*X 1 2+(4993752661/10000000000 : ℝ)*X 2 0+(4994034661/10000000000 : ℝ)*X 2 1+(-1371373773/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-758858573/2500000000 : ℝ)*X 0 0+(1376286721/5000000000 : ℝ)*X 0 1+(-336710129/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((744474397/2000000000 : ℝ)*X 1 0+(-3375497961/10000000000 : ℝ)*X 1 1+(-5654632107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2555448601/5000000000 : ℝ)*X 2 0+(5895050317/10000000000 : ℝ)*X 2 1+(691954959/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((153949103/312500000 : ℝ)*X 0 0+(5682213029/10000000000 : ℝ)*X 0 1+(-1948132869/10000000000 : ℝ)*X 0 2+(153949103/312500000 : ℝ)*X 1 0+(5682213029/10000000000 : ℝ)*X 1 1+(-1948132869/10000000000 : ℝ)*X 1 2+(153949103/312500000 : ℝ)*X 2 0+(5682213029/10000000000 : ℝ)*X 2 1+(-1948132869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-1376383163/5000000000 : ℝ)*X 0 0+(379405849/1250000000 : ℝ)*X 0 1+(-6734202677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((1687867231/5000000000 : ℝ)*X 1 0+(-1861071007/5000000000 : ℝ)*X 1 1+(-5654632303/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2947377187/5000000000 : ℝ)*X 2 0+(319450381/625000000 : ℝ)*X 2 1+(43247177/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_18 : ((35512049/62500000 : ℝ)*X 0 0+(2463334549/5000000000 : ℝ)*X 0 1+(-487033119/2500000000 : ℝ)*X 0 2+(35512049/62500000 : ℝ)*X 1 0+(2463334549/5000000000 : ℝ)*X 1 1+(-487033119/2500000000 : ℝ)*X 1 2+(35512049/62500000 : ℝ)*X 2 0+(2463334549/5000000000 : ℝ)*X 2 1+(-487033119/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s2_s2_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((-3427350991/10000000000 : ℝ)*X 0 0+(1479957323/5000000000 : ℝ)*X 0 1+(-3126484351/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s2_s2_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3584741229/10000000000 : ℝ)*X 1 0+(-4051744481/10000000000 : ℝ)*X 1 1+(-5172475099/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s2_s2_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((2756114943/5000000000 : ℝ)*X 2 0+(1306367843/2500000000 : ℝ)*X 2 1+(890566751/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s2_s2_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((4582349549/10000000000 : ℝ)*X 0 0+(1306367843/2500000000 : ℝ)*X 0 1+(-147372749/500000000 : ℝ)*X 0 2+(4582349549/10000000000 : ℝ)*X 1 0+(1306367843/2500000000 : ℝ)*X 1 1+(-147372749/500000000 : ℝ)*X 1 2+(4582349549/10000000000 : ℝ)*X 2 0+(1306367843/2500000000 : ℝ)*X 2 1+(-147372749/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((1439/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1439/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18975238403480791962819707/1046332325000000000000000000000 : ℝ) := by norm_num
    linear_combination (266379139219/500000000000 : ℝ)*(base39) + (4296733/1000000000000 : ℝ)*(base49) + (1687313206061/500000000000 : ℝ)*(base59) + (597519032741/500000000000 : ℝ)*(base60) + (2077569050449/250000000000 : ℝ)*(major_s2_0) + (2077569050449/250000000000 : ℝ)*(major_s2_1) + (2077569050449/250000000000 : ℝ)*(major_s2_2) + (206120491/1000000000000 : ℝ)*(sp_s2_0) + (11317166174823/1000000000000 : ℝ)*(sp_s2_7) + (1414701919633/125000000000 : ℝ)*(sp_s2_8) + (1414701919633/125000000000 : ℝ)*(sp_s2_9) + (2651383482157/500000000000 : ℝ)*(sp_s2_12) + (972247/4000000000 : ℝ)*(sp_s2_13) + (164037209/1000000000000 : ℝ)*(sp_s2_25) + (5302931001523/1000000000000 : ℝ)*(f.failure) + (1414701919633/125000000000 : ℝ)*(f.sum) + (962925098502442717/2353243968750000000000000000000 : ℝ)*base63 + (245922092720393/308850000000000000000000000 : ℝ)*base64 + (91344796780793/761937500000000000000000000 : ℝ)*base67 + (4343643922339/308850000000000000000000000 : ℝ)*base68 + (2393384825823959743/6277993950000000000000000000000 : ℝ)*base70 + (474908596486291/762262500000000000000000000 : ℝ)*base73 + (1702100619552497/3047750000000000000000000000 : ℝ)*base74 + (317359812334163/508175000000000000000000000 : ℝ)*base76 + (10527334800208731287/46463710687500000000000000000000 : ℝ)*base78 + (70853/100000000000000000 : ℝ)*base87 + (70853/100000000000000000 : ℝ)*base89 + (70853/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14389/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14389/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34777235831856369/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (532774066847/1000000000000 : ℝ)*(base39) + (3388461/500000000000 : ℝ)*(base40) + (689400014137/200000000000 : ℝ)*(base59) + (737229128007/500000000000 : ℝ)*(base60) + (10387780561/1250000000 : ℝ)*(major_s2_0) + (10387780561/1250000000 : ℝ)*(major_s2_1) + (10387780561/1250000000 : ℝ)*(major_s2_2) + (20472973/500000000000 : ℝ)*(sp_s2_6) + (343863357/1000000000000 : ℝ)*(sp_s2_8) + (1131754628359/100000000000 : ℝ)*(sp_s2_13) + (11317202420233/1000000000000 : ℝ)*(sp_s2_14) + (5658730705659/500000000000 : ℝ)*(sp_s2_15) + (1060571406219/200000000000 : ℝ)*(sp_s2_18) + (84872271/1000000000000 : ℝ)*(sp_s2_21) + (5302897977041/1000000000000 : ℝ)*(f.failure) + (1131754628359/100000000000 : ℝ)*(f.sum) + (6552296895238147/75303807000000000000000000000 : ℝ)*base63 + (1830956020517/3860625000000000000000000 : ℝ)*base64 + (7772916990457/12191000000000000000000000 : ℝ)*base67 + (29895827448109/61770000000000000000000000 : ℝ)*base68 + (148981133208822437/1255598790000000000000000000000 : ℝ)*base71 + (46143027194747/304905000000000000000000000 : ℝ)*base73 + (1997464622921/15238750000000000000000000 : ℝ)*base74 + (6681528453993/50817500000000000000000000 : ℝ)*base76 + (1061248118625603047/3717096855000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (72151/100000000000000000 : ℝ)*base87 + (72151/100000000000000000 : ℝ)*base89 + (72151/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1723/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1723/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (122696862085043267955214439/12390322850000000000000000000000 : ℝ) := by norm_num
    linear_combination (45333379953/500000000000 : ℝ)*(base5) + (70241870303/250000000000 : ℝ)*(base39) + (1506863/250000000000 : ℝ)*(base50) + (1198522417723/1000000000000 : ℝ)*(base59) + (874780928759/200000000000 : ℝ)*(major_s2_0) + (874780928759/200000000000 : ℝ)*(major_s2_1) + (874780928759/200000000000 : ℝ)*(major_s2_2) + (129198007/1000000000000 : ℝ)*(sp_s2_0) + (51098889/1000000000000 : ℝ)*(sp_s2_9) + (1487897/10000000000 : ℝ)*(sp_s2_15) + (1489153143133/250000000000 : ℝ)*(sp_s2_19) + (5956741770539/1000000000000 : ℝ)*(sp_s2_20) + (94487635029/15625000000 : ℝ)*(sp_s2_21) + (2700397456259/1000000000000 : ℝ)*(sp_s2_25) + (1395532108083/500000000000 : ℝ)*(f.failure) + (5956741770539/1000000000000 : ℝ)*(f.sum) + (2506645870631625379/3765190350000000000000000000000 : ℝ)*base63 + (21866675324017/247080000000000000000000000 : ℝ)*base64 + (284932307315649/304775000000000000000000000 : ℝ)*base67 + (387010357919/988320000000000000000000 : ℝ)*base68 + (3110197608821319913/5022395160000000000000000000000 : ℝ)*base71 + (992257799085499/1219620000000000000000000000 : ℝ)*base73 + (7953616071151/1219100000000000000000000000 : ℝ)*base74 + (5627277407651/20327000000000000000000000 : ℝ)*base76 + (37334286506580987451/74341937100000000000000000000000 : ℝ)*base79 + (45013/50000000000000000 : ℝ)*base87 + (45013/50000000000000000 : ℝ)*base89 + (45013/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((60981/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60981/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12191/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12191/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-6177/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-6177/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1439/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1439/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14389/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14389/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1723/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1723/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308048_s2 p hpa hpb X hX hprev1

#print axioms solution

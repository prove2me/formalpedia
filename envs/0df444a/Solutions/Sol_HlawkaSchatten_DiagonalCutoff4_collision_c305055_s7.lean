-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305055_s7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:29:34.642854+00:00
-- url     : https://prove2.me/submissions/575c06ef-5e5d-468c-80ae-ed30b13c9f9e

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
theorem collision_support_c305055_s7_s7_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2629158279/10000000000 : ℝ)*x 0 + (5468547283/10000000000 : ℝ)*x 1 + (2367856393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629158279/10000000000 : ℝ)^67 ≤ (270158401461/1562500000000 : ℝ)^51 := by
    have hnat : (2629158279 : ℕ)^67*1562500000000^51 ≤ 270158401461^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629158279 10000000000 270158401461 1562500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468547283/10000000000 : ℝ)^67 ≤ (45251786277911/100000000000000 : ℝ)^51 := by
    have hnat : (5468547283 : ℕ)^67*100000000000000^51 ≤ 45251786277911^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468547283 10000000000 45251786277911 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2367856393/5000000000 : ℝ)^67 ≤ (37458076013413/100000000000000 : ℝ)^51 := by
    have hnat : (2367856393 : ℕ)^67*100000000000000^51 ≤ 37458076013413^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2367856393 5000000000 37458076013413 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2629158279/10000000000 : ℝ), (5468547283/10000000000 : ℝ), (2367856393/5000000000 : ℝ)] ![(270158401461/1562500000000 : ℝ), (45251786277911/100000000000000 : ℝ), (37458076013413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2629158279/10000000000 : ℝ)|^67 ≤ (270158401461/1562500000000 : ℝ)^51
        have hw : |(-2629158279/10000000000 : ℝ)|=(2629158279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468547283/10000000000 : ℝ)|^67 ≤ (45251786277911/100000000000000 : ℝ)^51
        have hw : |(5468547283/10000000000 : ℝ)|=(5468547283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2367856393/5000000000 : ℝ)|^67 ≤ (37458076013413/100000000000000 : ℝ)^51
        have hw : |(2367856393/5000000000 : ℝ)|=(2367856393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s7_s7_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (236689281/500000000 : ℝ)*x 0 + (-379917777/2000000000 : ℝ)*x 1 + (6014766073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (236689281/500000000 : ℝ)^67 ≤ (18719025884519/50000000000000 : ℝ)^51 := by
    have hnat : (236689281 : ℕ)^67*50000000000000^51 ≤ 18719025884519^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236689281 500000000 18719025884519 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (379917777/2000000000 : ℝ)^67 ≤ (90249902697/800000000000 : ℝ)^51 := by
    have hnat : (379917777 : ℕ)^67*800000000000^51 ≤ 90249902697^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379917777 2000000000 90249902697 800000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6014766073/10000000000 : ℝ)^67 ≤ (12820177596393/25000000000000 : ℝ)^51 := by
    have hnat : (6014766073 : ℕ)^67*25000000000000^51 ≤ 12820177596393^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6014766073 10000000000 12820177596393 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(236689281/500000000 : ℝ), (-379917777/2000000000 : ℝ), (6014766073/10000000000 : ℝ)] ![(18719025884519/50000000000000 : ℝ), (90249902697/800000000000 : ℝ), (12820177596393/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(236689281/500000000 : ℝ)|^67 ≤ (18719025884519/50000000000000 : ℝ)^51
        have hw : |(236689281/500000000 : ℝ)|=(236689281/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-379917777/2000000000 : ℝ)|^67 ≤ (90249902697/800000000000 : ℝ)^51
        have hw : |(-379917777/2000000000 : ℝ)|=(379917777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6014766073/10000000000 : ℝ)|^67 ≤ (12820177596393/25000000000000 : ℝ)^51
        have hw : |(6014766073/10000000000 : ℝ)|=(6014766073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s7_s7_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4735548771/10000000000 : ℝ)*x 0 + (1093140191/2000000000 : ℝ)*x 1 + (-2632935921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4735548771/10000000000 : ℝ)^67 ≤ (18728185856897/50000000000000 : ℝ)^51 := by
    have hnat : (4735548771 : ℕ)^67*50000000000000^51 ≤ 18728185856897^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4735548771 10000000000 18728185856897 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093140191/2000000000 : ℝ)^67 ≤ (9044169290431/20000000000000 : ℝ)^51 := by
    have hnat : (1093140191 : ℕ)^67*20000000000000^51 ≤ 9044169290431^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093140191 2000000000 9044169290431 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632935921/10000000000 : ℝ)^67 ≤ (17322781814939/100000000000000 : ℝ)^51 := by
    have hnat : (2632935921 : ℕ)^67*100000000000000^51 ≤ 17322781814939^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632935921 10000000000 17322781814939 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4735548771/10000000000 : ℝ), (1093140191/2000000000 : ℝ), (-2632935921/10000000000 : ℝ)] ![(18728185856897/50000000000000 : ℝ), (9044169290431/20000000000000 : ℝ), (17322781814939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4735548771/10000000000 : ℝ)|^67 ≤ (18728185856897/50000000000000 : ℝ)^51
        have hw : |(4735548771/10000000000 : ℝ)|=(4735548771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093140191/2000000000 : ℝ)|^67 ≤ (9044169290431/20000000000000 : ℝ)^51
        have hw : |(1093140191/2000000000 : ℝ)|=(1093140191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2632935921/10000000000 : ℝ)|^67 ≤ (17322781814939/100000000000000 : ℝ)^51
        have hw : |(-2632935921/10000000000 : ℝ)|=(2632935921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s7_s7_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5676919097/10000000000 : ℝ)*x 0 + (2081486723/5000000000 : ℝ)*x 1 + (60629783/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5676919097/10000000000 : ℝ)^67 ≤ (47530413539677/100000000000000 : ℝ)^51 := by
    have hnat : (5676919097 : ℕ)^67*100000000000000^51 ≤ 47530413539677^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5676919097 10000000000 47530413539677 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2081486723/5000000000 : ℝ)^67 ≤ (3952854914663/12500000000000 : ℝ)^51 := by
    have hnat : (2081486723 : ℕ)^67*12500000000000^51 ≤ 3952854914663^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081486723 5000000000 3952854914663 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60629783/200000000 : ℝ)^67 ≤ (10423373563723/50000000000000 : ℝ)^51 := by
    have hnat : (60629783 : ℕ)^67*50000000000000^51 ≤ 10423373563723^51*200000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60629783 200000000 10423373563723 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5676919097/10000000000 : ℝ), (2081486723/5000000000 : ℝ), (60629783/200000000 : ℝ)] ![(47530413539677/100000000000000 : ℝ), (3952854914663/12500000000000 : ℝ), (10423373563723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5676919097/10000000000 : ℝ)|^67 ≤ (47530413539677/100000000000000 : ℝ)^51
        have hw : |(5676919097/10000000000 : ℝ)|=(5676919097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2081486723/5000000000 : ℝ)|^67 ≤ (3952854914663/12500000000000 : ℝ)^51
        have hw : |(2081486723/5000000000 : ℝ)|=(2081486723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(60629783/200000000 : ℝ)|^67 ≤ (10423373563723/50000000000000 : ℝ)^51
        have hw : |(60629783/200000000 : ℝ)|=(60629783/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s7_s7_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-130180611/500000000 : ℝ)*x 0 + (1341822903/2500000000 : ℝ)*x 1 + (4862016679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130180611/500000000 : ℝ)^67 ≤ (3413954160563/20000000000000 : ℝ)^51 := by
    have hnat : (130180611 : ℕ)^67*20000000000000^51 ≤ 3413954160563^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130180611 500000000 3413954160563 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1341822903/2500000000 : ℝ)^67 ≤ (22077124719773/50000000000000 : ℝ)^51 := by
    have hnat : (1341822903 : ℕ)^67*50000000000000^51 ≤ 22077124719773^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341822903 2500000000 22077124719773 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4862016679/10000000000 : ℝ)^67 ≤ (7755195948417/20000000000000 : ℝ)^51 := by
    have hnat : (4862016679 : ℕ)^67*20000000000000^51 ≤ 7755195948417^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4862016679 10000000000 7755195948417 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130180611/500000000 : ℝ), (1341822903/2500000000 : ℝ), (4862016679/10000000000 : ℝ)] ![(3413954160563/20000000000000 : ℝ), (22077124719773/50000000000000 : ℝ), (7755195948417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130180611/500000000 : ℝ)|^67 ≤ (3413954160563/20000000000000 : ℝ)^51
        have hw : |(-130180611/500000000 : ℝ)|=(130180611/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1341822903/2500000000 : ℝ)|^67 ≤ (22077124719773/50000000000000 : ℝ)^51
        have hw : |(1341822903/2500000000 : ℝ)|=(1341822903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4862016679/10000000000 : ℝ)|^67 ≤ (7755195948417/20000000000000 : ℝ)^51
        have hw : |(4862016679/10000000000 : ℝ)|=(4862016679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s7_s7_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (236174759/500000000 : ℝ)*x 0 + (-1792108891/10000000000 : ℝ)*x 1 + (6098320473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (236174759/500000000 : ℝ)^67 ≤ (37331172115933/100000000000000 : ℝ)^51 := by
    have hnat : (236174759 : ℕ)^67*100000000000000^51 ≤ 37331172115933^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236174759 500000000 37331172115933 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1792108891/10000000000 : ℝ)^67 ≤ (5225114087243/50000000000000 : ℝ)^51 := by
    have hnat : (1792108891 : ℕ)^67*50000000000000^51 ≤ 5225114087243^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792108891 10000000000 5225114087243 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6098320473/10000000000 : ℝ)^67 ≤ (52218599696657/100000000000000 : ℝ)^51 := by
    have hnat : (6098320473 : ℕ)^67*100000000000000^51 ≤ 52218599696657^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6098320473 10000000000 52218599696657 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(236174759/500000000 : ℝ), (-1792108891/10000000000 : ℝ), (6098320473/10000000000 : ℝ)] ![(37331172115933/100000000000000 : ℝ), (5225114087243/50000000000000 : ℝ), (52218599696657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(236174759/500000000 : ℝ)|^67 ≤ (37331172115933/100000000000000 : ℝ)^51
        have hw : |(236174759/500000000 : ℝ)|=(236174759/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1792108891/10000000000 : ℝ)|^67 ≤ (5225114087243/50000000000000 : ℝ)^51
        have hw : |(-1792108891/10000000000 : ℝ)|=(1792108891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6098320473/10000000000 : ℝ)|^67 ≤ (52218599696657/100000000000000 : ℝ)^51
        have hw : |(6098320473/10000000000 : ℝ)|=(6098320473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s7_s7_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2362629553/5000000000 : ℝ)*x 0 + (278706487/500000000 : ℝ)*x 1 + (-313447681/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2362629553/5000000000 : ℝ)^67 ≤ (37349487607331/100000000000000 : ℝ)^51 := by
    have hnat : (2362629553 : ℕ)^67*100000000000000^51 ≤ 37349487607331^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2362629553 5000000000 37349487607331 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278706487/500000000 : ℝ)^67 ≤ (5800378894499/12500000000000 : ℝ)^51 := by
    have hnat : (278706487 : ℕ)^67*12500000000000^51 ≤ 5800378894499^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278706487 500000000 5800378894499 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313447681/1250000000 : ℝ)^67 ≤ (16247481217941/100000000000000 : ℝ)^51 := by
    have hnat : (313447681 : ℕ)^67*100000000000000^51 ≤ 16247481217941^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313447681 1250000000 16247481217941 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2362629553/5000000000 : ℝ), (278706487/500000000 : ℝ), (-313447681/1250000000 : ℝ)] ![(37349487607331/100000000000000 : ℝ), (5800378894499/12500000000000 : ℝ), (16247481217941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2362629553/5000000000 : ℝ)|^67 ≤ (37349487607331/100000000000000 : ℝ)^51
        have hw : |(2362629553/5000000000 : ℝ)|=(2362629553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(278706487/500000000 : ℝ)|^67 ≤ (5800378894499/12500000000000 : ℝ)^51
        have hw : |(278706487/500000000 : ℝ)|=(278706487/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-313447681/1250000000 : ℝ)|^67 ≤ (16247481217941/100000000000000 : ℝ)^51
        have hw : |(-313447681/1250000000 : ℝ)|=(313447681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s7_s7_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5623634303/10000000000 : ℝ)*x 0 + (874572891/2000000000 : ℝ)*x 1 + (286108259/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5623634303/10000000000 : ℝ)^67 ≤ (11736296241803/25000000000000 : ℝ)^51 := by
    have hnat : (5623634303 : ℕ)^67*25000000000000^51 ≤ 11736296241803^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5623634303 10000000000 11736296241803 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (874572891/2000000000 : ℝ)^67 ≤ (33733791629447/100000000000000 : ℝ)^51 := by
    have hnat : (874572891 : ℕ)^67*100000000000000^51 ≤ 33733791629447^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874572891 2000000000 33733791629447 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (286108259/1000000000 : ℝ)^67 ≤ (19321023390783/100000000000000 : ℝ)^51 := by
    have hnat : (286108259 : ℕ)^67*100000000000000^51 ≤ 19321023390783^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286108259 1000000000 19321023390783 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5623634303/10000000000 : ℝ), (874572891/2000000000 : ℝ), (286108259/1000000000 : ℝ)] ![(11736296241803/25000000000000 : ℝ), (33733791629447/100000000000000 : ℝ), (19321023390783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5623634303/10000000000 : ℝ)|^67 ≤ (11736296241803/25000000000000 : ℝ)^51
        have hw : |(5623634303/10000000000 : ℝ)|=(5623634303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(874572891/2000000000 : ℝ)|^67 ≤ (33733791629447/100000000000000 : ℝ)^51
        have hw : |(874572891/2000000000 : ℝ)|=(874572891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(286108259/1000000000 : ℝ)|^67 ≤ (19321023390783/100000000000000 : ℝ)^51
        have hw : |(286108259/1000000000 : ℝ)|=(286108259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s7_s7_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-498552751/2000000000 : ℝ)*x 0 + (340261583/625000000 : ℝ)*x 1 + (4873028727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (498552751/2000000000 : ℝ)^67 ≤ (3224293784493/20000000000000 : ℝ)^51 := by
    have hnat : (498552751 : ℕ)^67*20000000000000^51 ≤ 3224293784493^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498552751 2000000000 3224293784493 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340261583/625000000 : ℝ)^67 ≤ (22493566702459/50000000000000 : ℝ)^51 := by
    have hnat : (340261583 : ℕ)^67*50000000000000^51 ≤ 22493566702459^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340261583 625000000 22493566702459 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4873028727/10000000000 : ℝ)^67 ≤ (19445698831517/50000000000000 : ℝ)^51 := by
    have hnat : (4873028727 : ℕ)^67*50000000000000^51 ≤ 19445698831517^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4873028727 10000000000 19445698831517 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-498552751/2000000000 : ℝ), (340261583/625000000 : ℝ), (4873028727/10000000000 : ℝ)] ![(3224293784493/20000000000000 : ℝ), (22493566702459/50000000000000 : ℝ), (19445698831517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-498552751/2000000000 : ℝ)|^67 ≤ (3224293784493/20000000000000 : ℝ)^51
        have hw : |(-498552751/2000000000 : ℝ)|=(498552751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340261583/625000000 : ℝ)|^67 ≤ (22493566702459/50000000000000 : ℝ)^51
        have hw : |(340261583/625000000 : ℝ)|=(340261583/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4873028727/10000000000 : ℝ)|^67 ≤ (19445698831517/50000000000000 : ℝ)^51
        have hw : |(4873028727/10000000000 : ℝ)|=(4873028727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s7_s7_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (930963327/2000000000 : ℝ)*x 0 + (-1885318791/10000000000 : ℝ)*x 1 + (95274637/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (930963327/2000000000 : ℝ)^67 ≤ (18309865556483/50000000000000 : ℝ)^51 := by
    have hnat : (930963327 : ℕ)^67*50000000000000^51 ≤ 18309865556483^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930963327 2000000000 18309865556483 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1885318791/10000000000 : ℝ)^67 ≤ (11170035056947/100000000000000 : ℝ)^51 := by
    have hnat : (1885318791 : ℕ)^67*100000000000000^51 ≤ 11170035056947^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885318791 10000000000 11170035056947 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95274637/156250000 : ℝ)^67 ≤ (10442046761917/20000000000000 : ℝ)^51 := by
    have hnat : (95274637 : ℕ)^67*20000000000000^51 ≤ 10442046761917^51*156250000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95274637 156250000 10442046761917 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(930963327/2000000000 : ℝ), (-1885318791/10000000000 : ℝ), (95274637/156250000 : ℝ)] ![(18309865556483/50000000000000 : ℝ), (11170035056947/100000000000000 : ℝ), (10442046761917/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(930963327/2000000000 : ℝ)|^67 ≤ (18309865556483/50000000000000 : ℝ)^51
        have hw : |(930963327/2000000000 : ℝ)|=(930963327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1885318791/10000000000 : ℝ)|^67 ≤ (11170035056947/100000000000000 : ℝ)^51
        have hw : |(-1885318791/10000000000 : ℝ)|=(1885318791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95274637/156250000 : ℝ)|^67 ≤ (10442046761917/20000000000000 : ℝ)^51
        have hw : |(95274637/156250000 : ℝ)|=(95274637/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s7_s7_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2436446013/5000000000 : ℝ)*x 0 + (2720669283/5000000000 : ℝ)*x 1 + (-2496568573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2436446013/5000000000 : ℝ)^67 ≤ (19444982194907/50000000000000 : ℝ)^51 := by
    have hnat : (2436446013 : ℕ)^67*50000000000000^51 ≤ 19444982194907^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2436446013 5000000000 19444982194907 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720669283/5000000000 : ℝ)^67 ≤ (44956232188303/100000000000000 : ℝ)^51 := by
    have hnat : (2720669283 : ℕ)^67*100000000000000^51 ≤ 44956232188303^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720669283 5000000000 44956232188303 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2496568573/10000000000 : ℝ)^67 ≤ (16153803406567/100000000000000 : ℝ)^51 := by
    have hnat : (2496568573 : ℕ)^67*100000000000000^51 ≤ 16153803406567^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2496568573 10000000000 16153803406567 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2436446013/5000000000 : ℝ), (2720669283/5000000000 : ℝ), (-2496568573/10000000000 : ℝ)] ![(19444982194907/50000000000000 : ℝ), (44956232188303/100000000000000 : ℝ), (16153803406567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2436446013/5000000000 : ℝ)|^67 ≤ (19444982194907/50000000000000 : ℝ)^51
        have hw : |(2436446013/5000000000 : ℝ)|=(2436446013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720669283/5000000000 : ℝ)|^67 ≤ (44956232188303/100000000000000 : ℝ)^51
        have hw : |(2720669283/5000000000 : ℝ)|=(2720669283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2496568573/10000000000 : ℝ)|^67 ≤ (16153803406567/100000000000000 : ℝ)^51
        have hw : |(-2496568573/10000000000 : ℝ)|=(2496568573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s7_s7_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1460184181/2500000000 : ℝ)*x 0 + (4133094489/10000000000 : ℝ)*x 1 + (715653403/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1460184181/2500000000 : ℝ)^67 ≤ (4934038948339/10000000000000 : ℝ)^51 := by
    have hnat : (1460184181 : ℕ)^67*10000000000000^51 ≤ 4934038948339^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460184181 2500000000 4934038948339 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4133094489/10000000000 : ℝ)^67 ≤ (1957812704903/6250000000000 : ℝ)^51 := by
    have hnat : (4133094489 : ℕ)^67*6250000000000^51 ≤ 1957812704903^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133094489 10000000000 1957812704903 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (715653403/2500000000 : ℝ)^67 ≤ (19334607220803/100000000000000 : ℝ)^51 := by
    have hnat : (715653403 : ℕ)^67*100000000000000^51 ≤ 19334607220803^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715653403 2500000000 19334607220803 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1460184181/2500000000 : ℝ), (4133094489/10000000000 : ℝ), (715653403/2500000000 : ℝ)] ![(4934038948339/10000000000000 : ℝ), (1957812704903/6250000000000 : ℝ), (19334607220803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1460184181/2500000000 : ℝ)|^67 ≤ (4934038948339/10000000000000 : ℝ)^51
        have hw : |(1460184181/2500000000 : ℝ)|=(1460184181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4133094489/10000000000 : ℝ)|^67 ≤ (1957812704903/6250000000000 : ℝ)^51
        have hw : |(4133094489/10000000000 : ℝ)|=(4133094489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(715653403/2500000000 : ℝ)|^67 ≤ (19334607220803/100000000000000 : ℝ)^51
        have hw : |(715653403/2500000000 : ℝ)|=(715653403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s7_s7_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-625478529/2500000000 : ℝ)*x 0 + (1115187461/2000000000 : ℝ)*x 1 + (2363999541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (625478529/2500000000 : ℝ)^67 ≤ (1012453597133/6250000000000 : ℝ)^51 := by
    have hnat : (625478529 : ℕ)^67*6250000000000^51 ≤ 1012453597133^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625478529 2500000000 1012453597133 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115187461/2000000000 : ℝ)^67 ≤ (46422800393403/100000000000000 : ℝ)^51 := by
    have hnat : (1115187461 : ℕ)^67*100000000000000^51 ≤ 46422800393403^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115187461 2000000000 46422800393403 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2363999541/5000000000 : ℝ)^67 ≤ (1868897101903/5000000000000 : ℝ)^51 := by
    have hnat : (2363999541 : ℕ)^67*5000000000000^51 ≤ 1868897101903^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2363999541 5000000000 1868897101903 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-625478529/2500000000 : ℝ), (1115187461/2000000000 : ℝ), (2363999541/5000000000 : ℝ)] ![(1012453597133/6250000000000 : ℝ), (46422800393403/100000000000000 : ℝ), (1868897101903/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-625478529/2500000000 : ℝ)|^67 ≤ (1012453597133/6250000000000 : ℝ)^51
        have hw : |(-625478529/2500000000 : ℝ)|=(625478529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1115187461/2000000000 : ℝ)|^67 ≤ (46422800393403/100000000000000 : ℝ)^51
        have hw : |(1115187461/2000000000 : ℝ)|=(1115187461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2363999541/5000000000 : ℝ)|^67 ≤ (1868897101903/5000000000000 : ℝ)^51
        have hw : |(2363999541/5000000000 : ℝ)|=(2363999541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s7_s7_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2430989373/5000000000 : ℝ)*x 0 + (-448286639/2500000000 : ℝ)*x 1 + (1492194561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2430989373/5000000000 : ℝ)^67 ≤ (19387791152851/50000000000000 : ℝ)^51 := by
    have hnat : (2430989373 : ℕ)^67*50000000000000^51 ≤ 19387791152851^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2430989373 5000000000 19387791152851 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448286639/2500000000 : ℝ)^67 ≤ (326818065369/3125000000000 : ℝ)^51 := by
    have hnat : (448286639 : ℕ)^67*3125000000000^51 ≤ 326818065369^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448286639 2500000000 326818065369 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1492194561/2500000000 : ℝ)^67 ≤ (50766239586711/100000000000000 : ℝ)^51 := by
    have hnat : (1492194561 : ℕ)^67*100000000000000^51 ≤ 50766239586711^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1492194561 2500000000 50766239586711 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2430989373/5000000000 : ℝ), (-448286639/2500000000 : ℝ), (1492194561/2500000000 : ℝ)] ![(19387791152851/50000000000000 : ℝ), (326818065369/3125000000000 : ℝ), (50766239586711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2430989373/5000000000 : ℝ)|^67 ≤ (19387791152851/50000000000000 : ℝ)^51
        have hw : |(2430989373/5000000000 : ℝ)|=(2430989373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-448286639/2500000000 : ℝ)|^67 ≤ (326818065369/3125000000000 : ℝ)^51
        have hw : |(-448286639/2500000000 : ℝ)|=(448286639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1492194561/2500000000 : ℝ)|^67 ≤ (50766239586711/100000000000000 : ℝ)^51
        have hw : |(1492194561/2500000000 : ℝ)|=(1492194561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s7_s7_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2323700747/5000000000 : ℝ)*x 0 + (5573090933/10000000000 : ℝ)*x 1 + (-2603083341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2323700747/5000000000 : ℝ)^67 ≤ (4567889200283/12500000000000 : ℝ)^51 := by
    have hnat : (2323700747 : ℕ)^67*12500000000000^51 ≤ 4567889200283^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2323700747 5000000000 4567889200283 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5573090933/10000000000 : ℝ)^67 ≤ (927833413837/2000000000000 : ℝ)^51 := by
    have hnat : (5573090933 : ℕ)^67*2000000000000^51 ≤ 927833413837^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5573090933 10000000000 927833413837 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2603083341/10000000000 : ℝ)^67 ≤ (17065215696697/100000000000000 : ℝ)^51 := by
    have hnat : (2603083341 : ℕ)^67*100000000000000^51 ≤ 17065215696697^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603083341 10000000000 17065215696697 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2323700747/5000000000 : ℝ), (5573090933/10000000000 : ℝ), (-2603083341/10000000000 : ℝ)] ![(4567889200283/12500000000000 : ℝ), (927833413837/2000000000000 : ℝ), (17065215696697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2323700747/5000000000 : ℝ)|^67 ≤ (4567889200283/12500000000000 : ℝ)^51
        have hw : |(2323700747/5000000000 : ℝ)|=(2323700747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5573090933/10000000000 : ℝ)|^67 ≤ (927833413837/2000000000000 : ℝ)^51
        have hw : |(5573090933/10000000000 : ℝ)|=(5573090933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2603083341/10000000000 : ℝ)|^67 ≤ (17065215696697/100000000000000 : ℝ)^51
        have hw : |(-2603083341/10000000000 : ℝ)|=(2603083341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s7_s7_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (366227083/625000000 : ℝ)*x 0 + (3943352379/10000000000 : ℝ)*x 1 + (3048467367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (366227083/625000000 : ℝ)^67 ≤ (6193775982179/12500000000000 : ℝ)^51 := by
    have hnat : (366227083 : ℕ)^67*12500000000000^51 ≤ 6193775982179^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366227083 625000000 6193775982179 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3943352379/10000000000 : ℝ)^67 ≤ (29449526795923/100000000000000 : ℝ)^51 := by
    have hnat : (3943352379 : ℕ)^67*100000000000000^51 ≤ 29449526795923^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3943352379 10000000000 29449526795923 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3048467367/10000000000 : ℝ)^67 ≤ (21000265328347/100000000000000 : ℝ)^51 := by
    have hnat : (3048467367 : ℕ)^67*100000000000000^51 ≤ 21000265328347^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3048467367 10000000000 21000265328347 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(366227083/625000000 : ℝ), (3943352379/10000000000 : ℝ), (3048467367/10000000000 : ℝ)] ![(6193775982179/12500000000000 : ℝ), (29449526795923/100000000000000 : ℝ), (21000265328347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(366227083/625000000 : ℝ)|^67 ≤ (6193775982179/12500000000000 : ℝ)^51
        have hw : |(366227083/625000000 : ℝ)|=(366227083/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3943352379/10000000000 : ℝ)|^67 ≤ (29449526795923/100000000000000 : ℝ)^51
        have hw : |(3943352379/10000000000 : ℝ)|=(3943352379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3048467367/10000000000 : ℝ)|^67 ≤ (21000265328347/100000000000000 : ℝ)^51
        have hw : |(3048467367/10000000000 : ℝ)|=(3048467367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305055_s7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev6 : (0 : ℝ) ≤ ((34127/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34127/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7009/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7009/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34739/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(34739/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((17543/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17543/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18299/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18299/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4451/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4451/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev6 with ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩
  have s7_pow0 : (34127/100000 : ℝ) ^ (133/32 : ℝ) ≤ (286667882564268709/25000000000000000000 : ℝ) := by
    have hpowers : (34127/100000 : ℝ)^133 ≤ (286667882564268709/25000000000000000000 : ℝ)^32 := by
      have hnat : (34127 : ℕ)^133*25000000000000000000^32 ≤ 286667882564268709^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34127 100000 286667882564268709 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34127/100000 : ℝ)) (X := (286667882564268709/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s7_corner0a : (25286667882564268709/25000000000000000000 : ℝ) ≤ (80219758165437/80000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (25286667882564268709/25000000000000000000 : ℝ)^32 ≤ (80219758165437/80000000000000 : ℝ)^133 := by
      have hnat : (25286667882564268709 : ℕ)^32*80000000000000^133 ≤ 80219758165437^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25286667882564268709 25000000000000000000 80219758165437 80000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80219758165437/80000000000000 : ℝ)) (X := (25286667882564268709/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s7_corner0b : (12786667882564268709/12500000000000000000 : ℝ) ≤ (10054704059811021/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (12786667882564268709/12500000000000000000 : ℝ)^32 ≤ (10054704059811021/10000000000000000 : ℝ)^133 := by
      have hnat : (12786667882564268709 : ℕ)^32*10000000000000000^133 ≤ 10054704059811021^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12786667882564268709 12500000000000000000 10054704059811021 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10054704059811021/10000000000000000 : ℝ)) (X := (12786667882564268709/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s7_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(219758165437/27301600000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(6808572282849/853175000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (34127/100000 : ℝ)) (alpha := (219758165437/27301600000000 : ℝ)) (beta := (6808572282849/853175000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow0,s7_corner0a]) (by linarith only [s7_pow0,s7_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (34127/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(219758165437/27301600000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(6808572282849/853175000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow1 : (7009/20000 : ℝ) ^ (133/32 : ℝ) ≤ (320104727784101891/25000000000000000000 : ℝ) := by
    have hpowers : (7009/20000 : ℝ)^133 ≤ (320104727784101891/25000000000000000000 : ℝ)^32 := by
      have hnat : (7009 : ℕ)^133*25000000000000000000^32 ≤ 320104727784101891^32*20000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7009 20000 320104727784101891 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7009/20000 : ℝ)) (X := (320104727784101891/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s7_corner1a : (25320104727784101891/25000000000000000000 : ℝ) ≤ (5015329205202857/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (25320104727784101891/25000000000000000000 : ℝ)^32 ≤ (5015329205202857/5000000000000000 : ℝ)^133 := by
      have hnat : (25320104727784101891 : ℕ)^32*5000000000000000^133 ≤ 5015329205202857^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25320104727784101891 25000000000000000000 5015329205202857 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015329205202857/5000000000000000 : ℝ)) (X := (25320104727784101891/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s7_corner1b : (12820104727784101891/12500000000000000000 : ℝ) ≤ (10061023880744109/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (12820104727784101891/12500000000000000000 : ℝ)^32 ≤ (10061023880744109/10000000000000000 : ℝ)^133 := by
      have hnat : (12820104727784101891 : ℕ)^32*10000000000000000^133 ≤ 10061023880744109^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12820104727784101891 12500000000000000000 10061023880744109 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10061023880744109/10000000000000000 : ℝ)) (X := (12820104727784101891/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s7_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(15329205202857/1752250000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(6073094067679/700900000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (7009/20000 : ℝ)) (alpha := (15329205202857/1752250000000000 : ℝ)) (beta := (6073094067679/700900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow1,s7_corner1a]) (by linarith only [s7_pow1,s7_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (7009/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(15329205202857/1752250000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(6073094067679/700900000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow2 : (34739/100000 : ℝ) ^ (133/32 : ℝ) ≤ (123458772802510867/10000000000000000000 : ℝ) := by
    have hpowers : (34739/100000 : ℝ)^133 ≤ (123458772802510867/10000000000000000000 : ℝ)^32 := by
      have hnat : (34739 : ℕ)^133*10000000000000000000^32 ≤ 123458772802510867^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34739 100000 123458772802510867 10000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34739/100000 : ℝ)) (X := (123458772802510867/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s7_corner2a : (10123458772802510867/10000000000000000000 : ℝ) ≤ (10029566120319423/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (10123458772802510867/10000000000000000000 : ℝ)^32 ≤ (10029566120319423/10000000000000000 : ℝ)^133 := by
      have hnat : (10123458772802510867 : ℕ)^32*10000000000000000^133 ≤ 10029566120319423^133*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10123458772802510867 10000000000000000000 10029566120319423 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10029566120319423/10000000000000000 : ℝ)) (X := (10123458772802510867/10000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s7_corner2b : (5123458772802510867/5000000000000000000 : ℝ) ≤ (5029429840224357/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (5123458772802510867/5000000000000000000 : ℝ)^32 ≤ (5029429840224357/5000000000000000 : ℝ)^133 := by
      have hnat : (5123458772802510867 : ℕ)^32*5000000000000000^133 ≤ 5029429840224357^133*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5123458772802510867 5000000000000000000 5029429840224357 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029429840224357/5000000000000000 : ℝ)) (X := (5123458772802510867/5000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s7_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(29566120319423/3473900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(29293560129291/3473900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (34739/100000 : ℝ)) (alpha := (29566120319423/3473900000000000 : ℝ)) (beta := (29293560129291/3473900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow2,s7_corner2a]) (by linarith only [s7_pow2,s7_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (34739/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(29566120319423/3473900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(29293560129291/3473900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s7_0 : ((-2629158279/10000000000 : ℝ)*X 0 0+(5468547283/10000000000 : ℝ)*X 0 1+(2367856393/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_1 : ((236689281/500000000 : ℝ)*X 1 0+(-379917777/2000000000 : ℝ)*X 1 1+(6014766073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_2 : ((4735548771/10000000000 : ℝ)*X 2 0+(1093140191/2000000000 : ℝ)*X 2 1+(-2632935921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_6 : ((5676919097/10000000000 : ℝ)*X 0 0+(2081486723/5000000000 : ℝ)*X 0 1+(60629783/200000000 : ℝ)*X 0 2+(5676919097/10000000000 : ℝ)*X 1 0+(2081486723/5000000000 : ℝ)*X 1 1+(60629783/200000000 : ℝ)*X 1 2+(5676919097/10000000000 : ℝ)*X 2 0+(2081486723/5000000000 : ℝ)*X 2 1+(60629783/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_7 : ((-130180611/500000000 : ℝ)*X 0 0+(1341822903/2500000000 : ℝ)*X 0 1+(4862016679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_8 : ((236174759/500000000 : ℝ)*X 1 0+(-1792108891/10000000000 : ℝ)*X 1 1+(6098320473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_9 : ((2362629553/5000000000 : ℝ)*X 2 0+(278706487/500000000 : ℝ)*X 2 1+(-313447681/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_13 : ((5623634303/10000000000 : ℝ)*X 0 0+(874572891/2000000000 : ℝ)*X 0 1+(286108259/1000000000 : ℝ)*X 0 2+(5623634303/10000000000 : ℝ)*X 1 0+(874572891/2000000000 : ℝ)*X 1 1+(286108259/1000000000 : ℝ)*X 1 2+(5623634303/10000000000 : ℝ)*X 2 0+(874572891/2000000000 : ℝ)*X 2 1+(286108259/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_14 : ((-498552751/2000000000 : ℝ)*X 0 0+(340261583/625000000 : ℝ)*X 0 1+(4873028727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_15 : ((930963327/2000000000 : ℝ)*X 1 0+(-1885318791/10000000000 : ℝ)*X 1 1+(95274637/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_16 : ((2436446013/5000000000 : ℝ)*X 2 0+(2720669283/5000000000 : ℝ)*X 2 1+(-2496568573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_20 : ((1460184181/2500000000 : ℝ)*X 0 0+(4133094489/10000000000 : ℝ)*X 0 1+(715653403/2500000000 : ℝ)*X 0 2+(1460184181/2500000000 : ℝ)*X 1 0+(4133094489/10000000000 : ℝ)*X 1 1+(715653403/2500000000 : ℝ)*X 1 2+(1460184181/2500000000 : ℝ)*X 2 0+(4133094489/10000000000 : ℝ)*X 2 1+(715653403/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_21 : ((-625478529/2500000000 : ℝ)*X 0 0+(1115187461/2000000000 : ℝ)*X 0 1+(2363999541/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_22 : ((2430989373/5000000000 : ℝ)*X 1 0+(-448286639/2500000000 : ℝ)*X 1 1+(1492194561/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_23 : ((2323700747/5000000000 : ℝ)*X 2 0+(5573090933/10000000000 : ℝ)*X 2 1+(-2603083341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_27 : ((366227083/625000000 : ℝ)*X 0 0+(3943352379/10000000000 : ℝ)*X 0 1+(3048467367/10000000000 : ℝ)*X 0 2+(366227083/625000000 : ℝ)*X 1 0+(3943352379/10000000000 : ℝ)*X 1 1+(3048467367/10000000000 : ℝ)*X 1 2+(366227083/625000000 : ℝ)*X 2 0+(3943352379/10000000000 : ℝ)*X 2 1+(3048467367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s7_s7_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s7_0 : (0 : ℝ) ≤ ((17543/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17543/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (85156512900370261484224857/12174282550000000000000000000000 : ℝ) := by norm_num
    linear_combination (5306326053971/1000000000000 : ℝ)*(base49) + (360897/200000000000 : ℝ)*(base60) + (3542898510777/100000000000 : ℝ)*(major_s7_0) + (3542898510777/100000000000 : ℝ)*(major_s7_1) + (3542898510777/100000000000 : ℝ)*(major_s7_2) + (159742749/500000000000 : ℝ)*(sp_s7_0) + (269961571/1000000000000 : ℝ)*(sp_s7_1) + (201132941/1000000000000 : ℝ)*(sp_s7_6) + (11922636704037/250000000000 : ℝ)*(sp_s7_7) + (2384527092951/50000000000 : ℝ)*(sp_s7_8) + (47690431384153/1000000000000 : ℝ)*(sp_s7_9) + (23166900449353/1000000000000 : ℝ)*(sp_s7_13) + (10896211/200000000000 : ℝ)*(sp_s7_22) + (217458747/500000000000 : ℝ)*(sp_s7_23) + (11583550791147/500000000000 : ℝ)*(f.failure) + (23845433150823/500000000000 : ℝ)*(f.sum) + (8503436971021836033/12174282550000000000000000000000 : ℝ)*base62 + (82446339609889/173695000000000000000000000 : ℝ)*base65 + (6573368964357/70090000000000000000000000 : ℝ)*base67 + (110364015698083/347390000000000000000000000 : ℝ)*base68 + (565992672800326833/5927689265000000000000000000000 : ℝ)*base71 + (69158205021851/341270000000000000000000000 : ℝ)*base73 + (18950474984659/43806250000000000000000000 : ℝ)*base74 + (18261126283137/42658750000000000000000000 : ℝ)*base76 + (78807449810483159/2391961430000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (111/195312500000000 : ℝ)*base87 + (111/195312500000000 : ℝ)*base89 + (111/195312500000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s7_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18299/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18299/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (859797495262442493400535457/60871412750000000000000000000000 : ℝ) := by norm_num
    linear_combination (9940265381/1953125000 : ℝ)*(base49) + (416929/100000000000 : ℝ)*(base60) + (34343627727859/1000000000000 : ℝ)*(major_s7_0) + (34343627727859/1000000000000 : ℝ)*(major_s7_1) + (34343627727859/1000000000000 : ℝ)*(major_s7_2) + (576446521/1000000000000 : ℝ)*(sp_s7_1) + (456438729/1000000000000 : ℝ)*(sp_s7_2) + (54744091/125000000000 : ℝ)*(sp_s7_7) + (132317017/1000000000000 : ℝ)*(sp_s7_8) + (46229429105749/1000000000000 : ℝ)*(sp_s7_14) + (2311457914747/50000000000 : ℝ)*(sp_s7_15) + (46229410619749/1000000000000 : ℝ)*(sp_s7_16) + (2245703008201/100000000000 : ℝ)*(sp_s7_20) + (176803477/500000000000 : ℝ)*(sp_s7_27) + (5614345922241/250000000000 : ℝ)*(f.failure) + (23114933529239/500000000000 : ℝ)*(f.sum) + (15800825492583512371/121742825500000000000000000000000 : ℝ)*base62 + (1127742502891009/3473900000000000000000000000 : ℝ)*base65 + (179640145834169/700900000000000000000000000 : ℝ)*base67 + (1138783456040123/3473900000000000000000000000 : ℝ)*base68 + (3427281181645623521/14819223162500000000000000000000 : ℝ)*base71 + (292631859865869/853175000000000000000000000 : ℝ)*base72 + (207075780355481/876125000000000000000000000 : ℝ)*base74 + (41756687828403/136508000000000000000000000 : ℝ)*base76 + (5418572792790065969/23919614300000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (419/3125000000000000 : ℝ)*base86 + (419/3125000000000000 : ℝ)*base88 + (419/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s7_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4451/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4451/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28499989645934068138983526792299/2077358702919250000000000000000000000 : ℝ) := by norm_num
    linear_combination (45523/8000000000 : ℝ)*(base39) + (504121/50000000000 : ℝ)*(base40) + (1290947817009/250000000000 : ℝ)*(base49) + (17169578145863/500000000000 : ℝ)*(major_s7_0) + (17169578145863/500000000000 : ℝ)*(major_s7_1) + (17169578145863/500000000000 : ℝ)*(major_s7_2) + (799885561/1000000000000 : ℝ)*(sp_s7_0) + (752309397/1000000000000 : ℝ)*(sp_s7_1) + (71864661/1000000000000 : ℝ)*(sp_s7_6) + (153117743/200000000000 : ℝ)*(sp_s7_20) + (46223048319029/1000000000000 : ℝ)*(sp_s7_21) + (23111547947597/500000000000 : ℝ)*(sp_s7_22) + (46223848204591/1000000000000 : ℝ)*(sp_s7_23) + (11226811176183/500000000000 : ℝ)*(sp_s7_27) + (22454459805743/1000000000000 : ℝ)*(f.failure) + (46223848204591/1000000000000 : ℝ)*(f.sum) + (8020339136973777653/60871412750000000000000000000000 : ℝ)*base63 + (9138768398741/13569921875000000000000000 : ℝ)*base65 + (146211569266103/350450000000000000000000000 : ℝ)*base67 + (195878172640597/868475000000000000000000000 : ℝ)*base69 + (8008329850715143163/29638446325000000000000000000000 : ℝ)*base71 + (86899482689567/1706350000000000000000000000 : ℝ)*base72 + (417702388735907/1752250000000000000000000000 : ℝ)*base75 + (37465743840409/341270000000000000000000000 : ℝ)*base77 + (41306387896128569/5979903575000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (2047/3125000000000000 : ℝ)*base87 + (2047/3125000000000000 : ℝ)*base89 + (2047/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s7_0,ratio_s7_1,ratio_s7_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev6 : (0 : ℝ) ≤ ((34127/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34127/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7009/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7009/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34739/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(34739/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((17543/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17543/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18299/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18299/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4451/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4451/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305055_s7 p hpa hpb X hX hprev6

#print axioms solution

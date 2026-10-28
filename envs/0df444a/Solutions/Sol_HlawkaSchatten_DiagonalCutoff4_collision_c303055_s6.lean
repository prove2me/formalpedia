-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c303055_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:56:23.42286+00:00
-- url     : https://prove2.me/submissions/fe8437d4-685e-4c62-80b0-e71cc43401c5

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
theorem collision_support_c303055_s6_s6_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-634039607/2500000000 : ℝ)*x 0 + (5554736919/10000000000 : ℝ)*x 1 + (4769008711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (634039607/2500000000 : ℝ)^33 ≤ (16349814168913/100000000000000 : ℝ)^25 := by
    have hnat : (634039607 : ℕ)^33*100000000000000^25 ≤ 16349814168913^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634039607 2500000000 16349814168913 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5554736919/10000000000 : ℝ)^33 ≤ (23010487387617/50000000000000 : ℝ)^25 := by
    have hnat : (5554736919 : ℕ)^33*50000000000000^25 ≤ 23010487387617^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5554736919 10000000000 23010487387617 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4769008711/10000000000 : ℝ)^33 ≤ (37629211043479/100000000000000 : ℝ)^25 := by
    have hnat : (4769008711 : ℕ)^33*100000000000000^25 ≤ 37629211043479^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4769008711 10000000000 37629211043479 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-634039607/2500000000 : ℝ), (5554736919/10000000000 : ℝ), (4769008711/10000000000 : ℝ)] ![(16349814168913/100000000000000 : ℝ), (23010487387617/50000000000000 : ℝ), (37629211043479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-634039607/2500000000 : ℝ)|^33 ≤ (16349814168913/100000000000000 : ℝ)^25
        have hw : |(-634039607/2500000000 : ℝ)|=(634039607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5554736919/10000000000 : ℝ)|^33 ≤ (23010487387617/50000000000000 : ℝ)^25
        have hw : |(5554736919/10000000000 : ℝ)|=(5554736919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4769008711/10000000000 : ℝ)|^33 ≤ (37629211043479/100000000000000 : ℝ)^25
        have hw : |(4769008711/10000000000 : ℝ)|=(4769008711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s6_s6_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (953426287/2000000000 : ℝ)*x 0 + (-1759040653/10000000000 : ℝ)*x 1 + (1530045731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (953426287/2000000000 : ℝ)^33 ≤ (940241498021/2500000000000 : ℝ)^25 := by
    have hnat : (953426287 : ℕ)^33*2500000000000^25 ≤ 940241498021^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953426287 2000000000 940241498021 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1759040653/10000000000 : ℝ)^33 ≤ (10087049614963/100000000000000 : ℝ)^25 := by
    have hnat : (1759040653 : ℕ)^33*100000000000000^25 ≤ 10087049614963^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759040653 10000000000 10087049614963 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1530045731/2500000000 : ℝ)^33 ≤ (13075822615751/25000000000000 : ℝ)^25 := by
    have hnat : (1530045731 : ℕ)^33*25000000000000^25 ≤ 13075822615751^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1530045731 2500000000 13075822615751 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(953426287/2000000000 : ℝ), (-1759040653/10000000000 : ℝ), (1530045731/2500000000 : ℝ)] ![(940241498021/2500000000000 : ℝ), (10087049614963/100000000000000 : ℝ), (13075822615751/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(953426287/2000000000 : ℝ)|^33 ≤ (940241498021/2500000000000 : ℝ)^25
        have hw : |(953426287/2000000000 : ℝ)|=(953426287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1759040653/10000000000 : ℝ)|^33 ≤ (10087049614963/100000000000000 : ℝ)^25
        have hw : |(-1759040653/10000000000 : ℝ)|=(1759040653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1530045731/2500000000 : ℝ)|^33 ≤ (13075822615751/25000000000000 : ℝ)^25
        have hw : |(1530045731/2500000000 : ℝ)|=(1530045731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s6_s6_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4766018989/10000000000 : ℝ)*x 0 + (346738191/625000000 : ℝ)*x 1 + (-2548706421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4766018989/10000000000 : ℝ)^33 ≤ (4699759422137/12500000000000 : ℝ)^25 := by
    have hnat : (4766018989 : ℕ)^33*12500000000000^25 ≤ 4699759422137^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4766018989 10000000000 4699759422137 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346738191/625000000 : ℝ)^33 ≤ (45945247300679/100000000000000 : ℝ)^25 := by
    have hnat : (346738191 : ℕ)^33*100000000000000^25 ≤ 45945247300679^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346738191 625000000 45945247300679 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2548706421/10000000000 : ℝ)^33 ≤ (16456677305449/100000000000000 : ℝ)^25 := by
    have hnat : (2548706421 : ℕ)^33*100000000000000^25 ≤ 16456677305449^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548706421 10000000000 16456677305449 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4766018989/10000000000 : ℝ), (346738191/625000000 : ℝ), (-2548706421/10000000000 : ℝ)] ![(4699759422137/12500000000000 : ℝ), (45945247300679/100000000000000 : ℝ), (16456677305449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4766018989/10000000000 : ℝ)|^33 ≤ (4699759422137/12500000000000 : ℝ)^25
        have hw : |(4766018989/10000000000 : ℝ)|=(4766018989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(346738191/625000000 : ℝ)|^33 ≤ (45945247300679/100000000000000 : ℝ)^25
        have hw : |(346738191/625000000 : ℝ)|=(346738191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2548706421/10000000000 : ℝ)|^33 ≤ (16456677305449/100000000000000 : ℝ)^25
        have hw : |(-2548706421/10000000000 : ℝ)|=(2548706421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s6_s6_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (719386489/1250000000 : ℝ)*x 0 + (831608207/2000000000 : ℝ)*x 1 + (2996338031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (719386489/1250000000 : ℝ)^33 ≤ (9644927869287/20000000000000 : ℝ)^25 := by
    have hnat : (719386489 : ℕ)^33*20000000000000^25 ≤ 9644927869287^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719386489 1250000000 9644927869287 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (831608207/2000000000 : ℝ)^33 ≤ (31400255198159/100000000000000 : ℝ)^25 := by
    have hnat : (831608207 : ℕ)^33*100000000000000^25 ≤ 31400255198159^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831608207 2000000000 31400255198159 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2996338031/10000000000 : ℝ)^33 ≤ (10187552716259/50000000000000 : ℝ)^25 := by
    have hnat : (2996338031 : ℕ)^33*50000000000000^25 ≤ 10187552716259^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2996338031 10000000000 10187552716259 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(719386489/1250000000 : ℝ), (831608207/2000000000 : ℝ), (2996338031/10000000000 : ℝ)] ![(9644927869287/20000000000000 : ℝ), (31400255198159/100000000000000 : ℝ), (10187552716259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(719386489/1250000000 : ℝ)|^33 ≤ (9644927869287/20000000000000 : ℝ)^25
        have hw : |(719386489/1250000000 : ℝ)|=(719386489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(831608207/2000000000 : ℝ)|^33 ≤ (31400255198159/100000000000000 : ℝ)^25
        have hw : |(831608207/2000000000 : ℝ)|=(831608207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2996338031/10000000000 : ℝ)|^33 ≤ (10187552716259/50000000000000 : ℝ)^25
        have hw : |(2996338031/10000000000 : ℝ)|=(2996338031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s6_s6_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-9459847/40000000 : ℝ)*x 0 + (504546209/1000000000 : ℝ)*x 1 + (2710133341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9459847/40000000 : ℝ)^33 ≤ (7454488413821/50000000000000 : ℝ)^25 := by
    have hnat : (9459847 : ℕ)^33*50000000000000^25 ≤ 7454488413821^25*40000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9459847 40000000 7454488413821 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504546209/1000000000 : ℝ)^33 ≤ (2533432093423/6250000000000 : ℝ)^25 := by
    have hnat : (504546209 : ℕ)^33*6250000000000^25 ≤ 2533432093423^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504546209 1000000000 2533432093423 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710133341/5000000000 : ℝ)^33 ≤ (8911221934367/20000000000000 : ℝ)^25 := by
    have hnat : (2710133341 : ℕ)^33*20000000000000^25 ≤ 8911221934367^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710133341 5000000000 8911221934367 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9459847/40000000 : ℝ), (504546209/1000000000 : ℝ), (2710133341/5000000000 : ℝ)] ![(7454488413821/50000000000000 : ℝ), (2533432093423/6250000000000 : ℝ), (8911221934367/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9459847/40000000 : ℝ)|^33 ≤ (7454488413821/50000000000000 : ℝ)^25
        have hw : |(-9459847/40000000 : ℝ)|=(9459847/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(504546209/1000000000 : ℝ)|^33 ≤ (2533432093423/6250000000000 : ℝ)^25
        have hw : |(504546209/1000000000 : ℝ)|=(504546209/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710133341/5000000000 : ℝ)|^33 ≤ (8911221934367/20000000000000 : ℝ)^25
        have hw : |(2710133341/5000000000 : ℝ)|=(2710133341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s6_s6_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4659862109/10000000000 : ℝ)*x 0 + (-61314697/500000000 : ℝ)*x 1 + (163820381/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4659862109/10000000000 : ℝ)^33 ≤ (2281037703883/6250000000000 : ℝ)^25 := by
    have hnat : (4659862109 : ℕ)^33*6250000000000^25 ≤ 2281037703883^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4659862109 10000000000 2281037703883 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (61314697/500000000 : ℝ)^33 ≤ (6265342952181/100000000000000 : ℝ)^25 := by
    have hnat : (61314697 : ℕ)^33*100000000000000^25 ≤ 6265342952181^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61314697 500000000 6265342952181 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163820381/250000000 : ℝ)^33 ≤ (5723805377397/10000000000000 : ℝ)^25 := by
    have hnat : (163820381 : ℕ)^33*10000000000000^25 ≤ 5723805377397^25*250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163820381 250000000 5723805377397 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4659862109/10000000000 : ℝ), (-61314697/500000000 : ℝ), (163820381/250000000 : ℝ)] ![(2281037703883/6250000000000 : ℝ), (6265342952181/100000000000000 : ℝ), (5723805377397/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4659862109/10000000000 : ℝ)|^33 ≤ (2281037703883/6250000000000 : ℝ)^25
        have hw : |(4659862109/10000000000 : ℝ)|=(4659862109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-61314697/500000000 : ℝ)|^33 ≤ (6265342952181/100000000000000 : ℝ)^25
        have hw : |(-61314697/500000000 : ℝ)|=(61314697/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163820381/250000000 : ℝ)|^33 ≤ (5723805377397/10000000000000 : ℝ)^25
        have hw : |(163820381/250000000 : ℝ)|=(163820381/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s6_s6_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4658747123/10000000000 : ℝ)*x 0 + (6107355621/10000000000 : ℝ)*x 1 + (-1924287447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4658747123/10000000000 : ℝ)^33 ≤ (36485076532703/100000000000000 : ℝ)^25 := by
    have hnat : (4658747123 : ℕ)^33*100000000000000^25 ≤ 36485076532703^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4658747123 10000000000 36485076532703 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6107355621/10000000000 : ℝ)^33 ≤ (52158637224277/100000000000000 : ℝ)^25 := by
    have hnat : (6107355621 : ℕ)^33*100000000000000^25 ≤ 52158637224277^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6107355621 10000000000 52158637224277 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1924287447/10000000000 : ℝ)^33 ≤ (5678143109077/50000000000000 : ℝ)^25 := by
    have hnat : (1924287447 : ℕ)^33*50000000000000^25 ≤ 5678143109077^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924287447 10000000000 5678143109077 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4658747123/10000000000 : ℝ), (6107355621/10000000000 : ℝ), (-1924287447/10000000000 : ℝ)] ![(36485076532703/100000000000000 : ℝ), (52158637224277/100000000000000 : ℝ), (5678143109077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4658747123/10000000000 : ℝ)|^33 ≤ (36485076532703/100000000000000 : ℝ)^25
        have hw : |(4658747123/10000000000 : ℝ)|=(4658747123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6107355621/10000000000 : ℝ)|^33 ≤ (52158637224277/100000000000000 : ℝ)^25
        have hw : |(6107355621/10000000000 : ℝ)|=(6107355621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1924287447/10000000000 : ℝ)|^33 ≤ (5678143109077/50000000000000 : ℝ)^25
        have hw : |(-1924287447/10000000000 : ℝ)|=(1924287447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s6_s6_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1348144427/2500000000 : ℝ)*x 0 + (2610895629/5000000000 : ℝ)*x 1 + (271565519/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348144427/2500000000 : ℝ)^33 ≤ (22127954424679/50000000000000 : ℝ)^25 := by
    have hnat : (1348144427 : ℕ)^33*50000000000000^25 ≤ 22127954424679^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348144427 2500000000 22127954424679 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610895629/5000000000 : ℝ)^33 ≤ (10603805612259/25000000000000 : ℝ)^25 := by
    have hnat : (2610895629 : ℕ)^33*25000000000000^25 ≤ 10603805612259^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610895629 5000000000 10603805612259 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271565519/1250000000 : ℝ)^33 ≤ (666443434389/5000000000000 : ℝ)^25 := by
    have hnat : (271565519 : ℕ)^33*5000000000000^25 ≤ 666443434389^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271565519 1250000000 666443434389 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348144427/2500000000 : ℝ), (2610895629/5000000000 : ℝ), (271565519/1250000000 : ℝ)] ![(22127954424679/50000000000000 : ℝ), (10603805612259/25000000000000 : ℝ), (666443434389/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348144427/2500000000 : ℝ)|^33 ≤ (22127954424679/50000000000000 : ℝ)^25
        have hw : |(1348144427/2500000000 : ℝ)|=(1348144427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610895629/5000000000 : ℝ)|^33 ≤ (10603805612259/25000000000000 : ℝ)^25
        have hw : |(2610895629/5000000000 : ℝ)|=(2610895629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271565519/1250000000 : ℝ)|^33 ≤ (666443434389/5000000000000 : ℝ)^25
        have hw : |(271565519/1250000000 : ℝ)|=(271565519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s6_s6_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-926902201/5000000000 : ℝ)*x 0 + (5369913329/10000000000 : ℝ)*x 1 + (1369393429/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (926902201/5000000000 : ℝ)^33 ≤ (10810464625471/100000000000000 : ℝ)^25 := by
    have hnat : (926902201 : ℕ)^33*100000000000000^25 ≤ 10810464625471^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926902201 5000000000 10810464625471 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5369913329/10000000000 : ℝ)^33 ≤ (44010550871561/100000000000000 : ℝ)^25 := by
    have hnat : (5369913329 : ℕ)^33*100000000000000^25 ≤ 44010550871561^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369913329 10000000000 44010550871561 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369393429/2500000000 : ℝ)^33 ≤ (22589492242891/50000000000000 : ℝ)^25 := by
    have hnat : (1369393429 : ℕ)^33*50000000000000^25 ≤ 22589492242891^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369393429 2500000000 22589492242891 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-926902201/5000000000 : ℝ), (5369913329/10000000000 : ℝ), (1369393429/2500000000 : ℝ)] ![(10810464625471/100000000000000 : ℝ), (44010550871561/100000000000000 : ℝ), (22589492242891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-926902201/5000000000 : ℝ)|^33 ≤ (10810464625471/100000000000000 : ℝ)^25
        have hw : |(-926902201/5000000000 : ℝ)|=(926902201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5369913329/10000000000 : ℝ)|^33 ≤ (44010550871561/100000000000000 : ℝ)^25
        have hw : |(5369913329/10000000000 : ℝ)|=(5369913329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369393429/2500000000 : ℝ)|^33 ≤ (22589492242891/50000000000000 : ℝ)^25
        have hw : |(1369393429/2500000000 : ℝ)|=(1369393429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s6_s6_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4376116961/10000000000 : ℝ)*x 0 + (-1647367253/10000000000 : ℝ)*x 1 + (102278451/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376116961/10000000000 : ℝ)^33 ≤ (8398029276159/25000000000000 : ℝ)^25 := by
    have hnat : (4376116961 : ℕ)^33*25000000000000^25 ≤ 8398029276159^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376116961 10000000000 8398029276159 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1647367253/10000000000 : ℝ)^33 ≤ (1156307596603/12500000000000 : ℝ)^25 := by
    have hnat : (1647367253 : ℕ)^33*12500000000000^25 ≤ 1156307596603^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1647367253 10000000000 1156307596603 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102278451/156250000 : ℝ)^33 ≤ (57157422105237/100000000000000 : ℝ)^25 := by
    have hnat : (102278451 : ℕ)^33*100000000000000^25 ≤ 57157422105237^25*156250000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102278451 156250000 57157422105237 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376116961/10000000000 : ℝ), (-1647367253/10000000000 : ℝ), (102278451/156250000 : ℝ)] ![(8398029276159/25000000000000 : ℝ), (1156307596603/12500000000000 : ℝ), (57157422105237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376116961/10000000000 : ℝ)|^33 ≤ (8398029276159/25000000000000 : ℝ)^25
        have hw : |(4376116961/10000000000 : ℝ)|=(4376116961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1647367253/10000000000 : ℝ)|^33 ≤ (1156307596603/12500000000000 : ℝ)^25
        have hw : |(-1647367253/10000000000 : ℝ)|=(1647367253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(102278451/156250000 : ℝ)|^33 ≤ (57157422105237/100000000000000 : ℝ)^25
        have hw : |(102278451/156250000 : ℝ)|=(102278451/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s6_s6_16 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5475156719/10000000000 : ℝ)*x 0 + (5362958727/10000000000 : ℝ)*x 1 + (-933489973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5475156719/10000000000 : ℝ)^33 ≤ (45152671652691/100000000000000 : ℝ)^25 := by
    have hnat : (5475156719 : ℕ)^33*100000000000000^25 ≤ 45152671652691^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475156719 10000000000 45152671652691 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5362958727/10000000000 : ℝ)^33 ≤ (10983832181709/25000000000000 : ℝ)^25 := by
    have hnat : (5362958727 : ℕ)^33*25000000000000^25 ≤ 10983832181709^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362958727 10000000000 10983832181709 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (933489973/5000000000 : ℝ)^33 ≤ (10911999615531/100000000000000 : ℝ)^25 := by
    have hnat : (933489973 : ℕ)^33*100000000000000^25 ≤ 10911999615531^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933489973 5000000000 10911999615531 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5475156719/10000000000 : ℝ), (5362958727/10000000000 : ℝ), (-933489973/5000000000 : ℝ)] ![(45152671652691/100000000000000 : ℝ), (10983832181709/25000000000000 : ℝ), (10911999615531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5475156719/10000000000 : ℝ)|^33 ≤ (45152671652691/100000000000000 : ℝ)^25
        have hw : |(5475156719/10000000000 : ℝ)|=(5475156719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5362958727/10000000000 : ℝ)|^33 ≤ (10983832181709/25000000000000 : ℝ)^25
        have hw : |(5362958727/10000000000 : ℝ)|=(5362958727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-933489973/5000000000 : ℝ)|^33 ≤ (10911999615531/100000000000000 : ℝ)^25
        have hw : |(-933489973/5000000000 : ℝ)|=(933489973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s6_s6_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1643879909/2500000000 : ℝ)*x 0 + (1960399437/5000000000 : ℝ)*x 1 + (1093287357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1643879909/2500000000 : ℝ)^33 ≤ (28749990705563/50000000000000 : ℝ)^25 := by
    have hnat : (1643879909 : ℕ)^33*50000000000000^25 ≤ 28749990705563^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1643879909 2500000000 28749990705563 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1960399437/5000000000 : ℝ)^33 ≤ (14528622175221/50000000000000 : ℝ)^25 := by
    have hnat : (1960399437 : ℕ)^33*50000000000000^25 ≤ 14528622175221^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960399437 5000000000 14528622175221 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093287357/5000000000 : ℝ)^33 ≤ (3360693554811/25000000000000 : ℝ)^25 := by
    have hnat : (1093287357 : ℕ)^33*25000000000000^25 ≤ 3360693554811^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093287357 5000000000 3360693554811 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1643879909/2500000000 : ℝ), (1960399437/5000000000 : ℝ), (1093287357/5000000000 : ℝ)] ![(28749990705563/50000000000000 : ℝ), (14528622175221/50000000000000 : ℝ), (3360693554811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1643879909/2500000000 : ℝ)|^33 ≤ (28749990705563/50000000000000 : ℝ)^25
        have hw : |(1643879909/2500000000 : ℝ)|=(1643879909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1960399437/5000000000 : ℝ)|^33 ≤ (14528622175221/50000000000000 : ℝ)^25
        have hw : |(1960399437/5000000000 : ℝ)|=(1960399437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093287357/5000000000 : ℝ)|^33 ≤ (3360693554811/25000000000000 : ℝ)^25
        have hw : |(1093287357/5000000000 : ℝ)|=(1093287357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s6_s6_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1834749929/10000000000 : ℝ)*x 0 + (6015497793/10000000000 : ℝ)*x 1 + (1206175669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1834749929/10000000000 : ℝ)^33 ≤ (10664033016903/100000000000000 : ℝ)^25 := by
    have hnat : (1834749929 : ℕ)^33*100000000000000^25 ≤ 10664033016903^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834749929 10000000000 10664033016903 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6015497793/10000000000 : ℝ)^33 ≤ (12781401675389/25000000000000 : ℝ)^25 := by
    have hnat : (6015497793 : ℕ)^33*25000000000000^25 ≤ 12781401675389^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6015497793 10000000000 12781401675389 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1206175669/2500000000 : ℝ)^33 ≤ (38210360273973/100000000000000 : ℝ)^25 := by
    have hnat : (1206175669 : ℕ)^33*100000000000000^25 ≤ 38210360273973^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206175669 2500000000 38210360273973 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1834749929/10000000000 : ℝ), (6015497793/10000000000 : ℝ), (1206175669/2500000000 : ℝ)] ![(10664033016903/100000000000000 : ℝ), (12781401675389/25000000000000 : ℝ), (38210360273973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1834749929/10000000000 : ℝ)|^33 ≤ (10664033016903/100000000000000 : ℝ)^25
        have hw : |(-1834749929/10000000000 : ℝ)|=(1834749929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6015497793/10000000000 : ℝ)|^33 ≤ (12781401675389/25000000000000 : ℝ)^25
        have hw : |(6015497793/10000000000 : ℝ)|=(6015497793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1206175669/2500000000 : ℝ)|^33 ≤ (38210360273973/100000000000000 : ℝ)^25
        have hw : |(1206175669/2500000000 : ℝ)|=(1206175669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s6_s6_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2747662463/5000000000 : ℝ)*x 0 + (-18847307/156250000 : ℝ)*x 1 + (361232769/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2747662463/5000000000 : ℝ)^33 ≤ (5671543531189/12500000000000 : ℝ)^25 := by
    have hnat : (2747662463 : ℕ)^33*12500000000000^25 ≤ 5671543531189^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747662463 5000000000 5671543531189 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18847307/156250000 : ℝ)^33 ≤ (6130369444789/100000000000000 : ℝ)^25 := by
    have hnat : (18847307 : ℕ)^33*100000000000000^25 ≤ 6130369444789^25*156250000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18847307 156250000 6130369444789 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (361232769/625000000 : ℝ)^33 ≤ (24248641146107/50000000000000 : ℝ)^25 := by
    have hnat : (361232769 : ℕ)^33*50000000000000^25 ≤ 24248641146107^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361232769 625000000 24248641146107 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2747662463/5000000000 : ℝ), (-18847307/156250000 : ℝ), (361232769/625000000 : ℝ)] ![(5671543531189/12500000000000 : ℝ), (6130369444789/100000000000000 : ℝ), (24248641146107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2747662463/5000000000 : ℝ)|^33 ≤ (5671543531189/12500000000000 : ℝ)^25
        have hw : |(2747662463/5000000000 : ℝ)|=(2747662463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18847307/156250000 : ℝ)|^33 ≤ (6130369444789/100000000000000 : ℝ)^25
        have hw : |(-18847307/156250000 : ℝ)|=(18847307/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(361232769/625000000 : ℝ)|^33 ≤ (24248641146107/50000000000000 : ℝ)^25
        have hw : |(361232769/625000000 : ℝ)|=(361232769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s6_s6_23 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4338569001/10000000000 : ℝ)*x 0 + (6127418947/10000000000 : ℝ)*x 1 + (-575972513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338569001/10000000000 : ℝ)^33 ≤ (33212180668997/100000000000000 : ℝ)^25 := by
    have hnat : (4338569001 : ℕ)^33*100000000000000^25 ≤ 33212180668997^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338569001 10000000000 33212180668997 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6127418947/10000000000 : ℝ)^33 ≤ (26192466886633/50000000000000 : ℝ)^25 := by
    have hnat : (6127418947 : ℕ)^33*50000000000000^25 ≤ 26192466886633^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6127418947 10000000000 26192466886633 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (575972513/2500000000 : ℝ)^33 ≤ (14402885540027/100000000000000 : ℝ)^25 := by
    have hnat : (575972513 : ℕ)^33*100000000000000^25 ≤ 14402885540027^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575972513 2500000000 14402885540027 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338569001/10000000000 : ℝ), (6127418947/10000000000 : ℝ), (-575972513/2500000000 : ℝ)] ![(33212180668997/100000000000000 : ℝ), (26192466886633/50000000000000 : ℝ), (14402885540027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338569001/10000000000 : ℝ)|^33 ≤ (33212180668997/100000000000000 : ℝ)^25
        have hw : |(4338569001/10000000000 : ℝ)|=(4338569001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6127418947/10000000000 : ℝ)|^33 ≤ (26192466886633/50000000000000 : ℝ)^25
        have hw : |(6127418947/10000000000 : ℝ)|=(6127418947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-575972513/2500000000 : ℝ)|^33 ≤ (14402885540027/100000000000000 : ℝ)^25
        have hw : |(-575972513/2500000000 : ℝ)|=(575972513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s6_s6_27 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1329740431/2000000000 : ℝ)*x 0 + (51149489/156250000 : ℝ)*x 1 + (2813951871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1329740431/2000000000 : ℝ)^33 ≤ (29173106900611/50000000000000 : ℝ)^25 := by
    have hnat : (1329740431 : ℕ)^33*50000000000000^25 ≤ 29173106900611^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1329740431 2000000000 29173106900611 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51149489/156250000 : ℝ)^33 ≤ (1431225607781/6250000000000 : ℝ)^25 := by
    have hnat : (51149489 : ℕ)^33*6250000000000^25 ≤ 1431225607781^25*156250000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51149489 156250000 1431225607781 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2813951871/10000000000 : ℝ)^33 ≤ (4688544114379/25000000000000 : ℝ)^25 := by
    have hnat : (2813951871 : ℕ)^33*25000000000000^25 ≤ 4688544114379^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2813951871 10000000000 4688544114379 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1329740431/2000000000 : ℝ), (51149489/156250000 : ℝ), (2813951871/10000000000 : ℝ)] ![(29173106900611/50000000000000 : ℝ), (1431225607781/6250000000000 : ℝ), (4688544114379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1329740431/2000000000 : ℝ)|^33 ≤ (29173106900611/50000000000000 : ℝ)^25
        have hw : |(1329740431/2000000000 : ℝ)|=(1329740431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51149489/156250000 : ℝ)|^33 ≤ (1431225607781/6250000000000 : ℝ)^25
        have hw : |(51149489/156250000 : ℝ)|=(51149489/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2813951871/10000000000 : ℝ)|^33 ≤ (4688544114379/25000000000000 : ℝ)^25
        have hw : |(2813951871/10000000000 : ℝ)|=(2813951871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303055_s6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((893/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(893/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22833/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22833/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45771/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(45771/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((357/1250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(357/1250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2939/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2939/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1159/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1159/4000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (893/2000 : ℝ) ^ (131/32 : ℝ) ≤ (3685162261711810133/100000000000000000000 : ℝ) := by
    have hpowers : (893/2000 : ℝ)^131 ≤ (3685162261711810133/100000000000000000000 : ℝ)^32 := by
      have hnat : (893 : ℕ)^131*100000000000000000000^32 ≤ 3685162261711810133^32*2000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        893 2000 3685162261711810133 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (893/2000 : ℝ)) (X := (3685162261711810133/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s6_corner0a : (103685162261711810133/100000000000000000000 : ℝ) ≤ (630549505819953/625000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (103685162261711810133/100000000000000000000 : ℝ)^32 ≤ (630549505819953/625000000000000 : ℝ)^131 := by
      have hnat : (103685162261711810133 : ℕ)^32*625000000000000^131 ≤ 630549505819953^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103685162261711810133 100000000000000000000 630549505819953 625000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (630549505819953/625000000000000 : ℝ)) (X := (103685162261711810133/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s6_corner0b : (53685162261711810133/50000000000000000000 : ℝ) ≤ (2543807578257317/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (53685162261711810133/50000000000000000000 : ℝ)^32 ≤ (2543807578257317/2500000000000000 : ℝ)^131 := by
      have hnat : (53685162261711810133 : ℕ)^32*2500000000000000^131 ≤ 2543807578257317^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53685162261711810133 50000000000000000000 2543807578257317 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2543807578257317/2500000000000000 : ℝ)) (X := (53685162261711810133/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(5549505819953/279062500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(4321910995501/223250000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (893/2000 : ℝ)) (alpha := (5549505819953/279062500000000 : ℝ)) (beta := (4321910995501/223250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (893/2000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(5549505819953/279062500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(4321910995501/223250000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (22833/50000 : ℝ) ^ (131/32 : ℝ) ≤ (2020359875439297691/50000000000000000000 : ℝ) := by
    have hpowers : (22833/50000 : ℝ)^131 ≤ (2020359875439297691/50000000000000000000 : ℝ)^32 := by
      have hnat : (22833 : ℕ)^131*50000000000000000000^32 ≤ 2020359875439297691^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22833 50000 2020359875439297691 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22833/50000 : ℝ)) (X := (2020359875439297691/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s6_corner1a : (52020359875439297691/50000000000000000000 : ℝ) ≤ (10097232222276033/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (52020359875439297691/50000000000000000000 : ℝ)^32 ≤ (10097232222276033/10000000000000000 : ℝ)^131 := by
      have hnat : (52020359875439297691 : ℕ)^32*10000000000000000^131 ≤ 10097232222276033^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52020359875439297691 50000000000000000000 10097232222276033 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10097232222276033/10000000000000000 : ℝ)) (X := (52020359875439297691/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s6_corner1b : (27020359875439297691/25000000000000000000 : ℝ) ≤ (5095825559563297/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (27020359875439297691/25000000000000000000 : ℝ)^32 ≤ (5095825559563297/5000000000000000 : ℝ)^131 := by
      have hnat : (27020359875439297691 : ℕ)^32*5000000000000000^131 ≤ 5095825559563297^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27020359875439297691 25000000000000000000 5095825559563297 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5095825559563297/5000000000000000 : ℝ)) (X := (27020359875439297691/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(97232222276033/4566600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(94418896850561/4566600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (22833/50000 : ℝ)) (alpha := (97232222276033/4566600000000000 : ℝ)) (beta := (94418896850561/4566600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (22833/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(97232222276033/4566600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(94418896850561/4566600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (45771/100000 : ℝ) ^ (131/32 : ℝ) ≤ (4078889629251914551/100000000000000000000 : ℝ) := by
    have hpowers : (45771/100000 : ℝ)^131 ≤ (4078889629251914551/100000000000000000000 : ℝ)^32 := by
      have hnat : (45771 : ℕ)^131*100000000000000000000^32 ≤ 4078889629251914551^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45771 100000 4078889629251914551 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45771/100000 : ℝ)) (X := (4078889629251914551/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s6_corner2a : (104078889629251914551/100000000000000000000 : ℝ) ≤ (10098136992414899/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (104078889629251914551/100000000000000000000 : ℝ)^32 ≤ (10098136992414899/10000000000000000 : ℝ)^131 := by
      have hnat : (104078889629251914551 : ℕ)^32*10000000000000000^131 ≤ 10098136992414899^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104078889629251914551 100000000000000000000 10098136992414899 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10098136992414899/10000000000000000 : ℝ)) (X := (104078889629251914551/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s6_corner2b : (54078889629251914551/50000000000000000000 : ℝ) ≤ (1019340907109883/1000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (54078889629251914551/50000000000000000000 : ℝ)^32 ≤ (1019340907109883/1000000000000000 : ℝ)^131 := by
      have hnat : (54078889629251914551 : ℕ)^32*1000000000000000^131 ≤ 1019340907109883^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54078889629251914551 50000000000000000000 1019340907109883 1000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1019340907109883/1000000000000000 : ℝ)) (X := (54078889629251914551/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(98136992414899/4577100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(95272078683931/4577100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (45771/100000 : ℝ)) (alpha := (98136992414899/4577100000000000 : ℝ)) (beta := (95272078683931/4577100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (45771/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(98136992414899/4577100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(95272078683931/4577100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-634039607/2500000000 : ℝ)*X 0 0+(5554736919/10000000000 : ℝ)*X 0 1+(4769008711/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_1 : ((953426287/2000000000 : ℝ)*X 1 0+(-1759040653/10000000000 : ℝ)*X 1 1+(1530045731/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((4766018989/10000000000 : ℝ)*X 2 0+(346738191/625000000 : ℝ)*X 2 1+(-2548706421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((719386489/1250000000 : ℝ)*X 0 0+(831608207/2000000000 : ℝ)*X 0 1+(2996338031/10000000000 : ℝ)*X 0 2+(719386489/1250000000 : ℝ)*X 1 0+(831608207/2000000000 : ℝ)*X 1 1+(2996338031/10000000000 : ℝ)*X 1 2+(719386489/1250000000 : ℝ)*X 2 0+(831608207/2000000000 : ℝ)*X 2 1+(2996338031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-9459847/40000000 : ℝ)*X 0 0+(504546209/1000000000 : ℝ)*X 0 1+(2710133341/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((4659862109/10000000000 : ℝ)*X 1 0+(-61314697/500000000 : ℝ)*X 1 1+(163820381/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((4658747123/10000000000 : ℝ)*X 2 0+(6107355621/10000000000 : ℝ)*X 2 1+(-1924287447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((1348144427/2500000000 : ℝ)*X 0 0+(2610895629/5000000000 : ℝ)*X 0 1+(271565519/1250000000 : ℝ)*X 0 2+(1348144427/2500000000 : ℝ)*X 1 0+(2610895629/5000000000 : ℝ)*X 1 1+(271565519/1250000000 : ℝ)*X 1 2+(1348144427/2500000000 : ℝ)*X 2 0+(2610895629/5000000000 : ℝ)*X 2 1+(271565519/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-926902201/5000000000 : ℝ)*X 0 0+(5369913329/10000000000 : ℝ)*X 0 1+(1369393429/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((4376116961/10000000000 : ℝ)*X 1 0+(-1647367253/10000000000 : ℝ)*X 1 1+(102278451/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((5475156719/10000000000 : ℝ)*X 2 0+(5362958727/10000000000 : ℝ)*X 2 1+(-933489973/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((1643879909/2500000000 : ℝ)*X 0 0+(1960399437/5000000000 : ℝ)*X 0 1+(1093287357/5000000000 : ℝ)*X 0 2+(1643879909/2500000000 : ℝ)*X 1 0+(1960399437/5000000000 : ℝ)*X 1 1+(1093287357/5000000000 : ℝ)*X 1 2+(1643879909/2500000000 : ℝ)*X 2 0+(1960399437/5000000000 : ℝ)*X 2 1+(1093287357/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-1834749929/10000000000 : ℝ)*X 0 0+(6015497793/10000000000 : ℝ)*X 0 1+(1206175669/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((2747662463/5000000000 : ℝ)*X 1 0+(-18847307/156250000 : ℝ)*X 1 1+(361232769/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((4338569001/10000000000 : ℝ)*X 2 0+(6127418947/10000000000 : ℝ)*X 2 1+(-575972513/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((1329740431/2000000000 : ℝ)*X 0 0+(51149489/156250000 : ℝ)*X 0 1+(2813951871/10000000000 : ℝ)*X 0 2+(1329740431/2000000000 : ℝ)*X 1 0+(51149489/156250000 : ℝ)*X 1 1+(2813951871/10000000000 : ℝ)*X 1 2+(1329740431/2000000000 : ℝ)*X 2 0+(51149489/156250000 : ℝ)*X 2 1+(2813951871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((357/1250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(357/1250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (42146016995930386492684475651/2728844134500000000000000000000000 : ℝ) := by norm_num
    linear_combination (779077220591/1000000000000 : ℝ)*(base49) + (599841/200000000000 : ℝ)*(base60) + (1401433627637/200000000000 : ℝ)*(major_s6_0) + (1401433627637/200000000000 : ℝ)*(major_s6_1) + (1401433627637/200000000000 : ℝ)*(major_s6_2) + (81372157/1000000000000 : ℝ)*(sp_s6_0) + (46498827/1000000000000 : ℝ)*(sp_s6_6) + (4677910122939/500000000000 : ℝ)*(sp_s6_7) + (9355780410491/1000000000000 : ℝ)*(sp_s6_8) + (9355713211347/1000000000000 : ℝ)*(sp_s6_9) + (4658355401309/1000000000000 : ℝ)*(sp_s6_13) + (27609981/1000000000000 : ℝ)*(sp_s6_14) + (5952701/40000000000 : ℝ)*(sp_s6_15) + (216016669/1000000000000 : ℝ)*(sp_s6_23) + (582300237517/125000000000 : ℝ)*(f.failure) + (584745576751/62500000000 : ℝ)*(f.sum) + (793189191702450671/13934523240000000000000000000000 : ℝ)*base63 + (362939396086349/915420000000000000000000000 : ℝ)*base65 + (63474489607/7306560000000000000000000 : ℝ)*base67 + (346613234673983/915420000000000000000000000 : ℝ)*base69 + (52285968018829117/1075618500000000000000000000000 : ℝ)*base71 + (3902652643803/11162500000000000000000000 : ℝ)*base73 + (333784914575149/913320000000000000000000000 : ℝ)*base75 + (90087835978719/223250000000000000000000000 : ℝ)*base77 + (1241003512650664561/4077973800000000000000000000000 : ℝ)*base78 + (67/156250000000000 : ℝ)*base86 + (67/156250000000000 : ℝ)*base88 + (67/156250000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2939/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2939/10000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7019787131729164510799438099/454807355750000000000000000000000 : ℝ) := by norm_num
    linear_combination (349225083181/500000000000 : ℝ)*(base49) + (1096969/250000000000 : ℝ)*(base60) + (3403882111793/500000000000 : ℝ)*(major_s6_0) + (3403882111793/500000000000 : ℝ)*(major_s6_1) + (3403882111793/500000000000 : ℝ)*(major_s6_2) + (25655331/250000000000 : ℝ)*(sp_s6_1) + (57804247/1000000000000 : ℝ)*(sp_s6_2) + (38322069/500000000000 : ℝ)*(sp_s6_7) + (74533143/1000000000000 : ℝ)*(sp_s6_8) + (71012574373/7812500000 : ℝ)*(sp_s6_14) + (4544754504707/500000000000 : ℝ)*(sp_s6_15) + (4544814179817/500000000000 : ℝ)*(sp_s6_16) + (4525731254941/1000000000000 : ℝ)*(sp_s6_20) + (52941731/500000000000 : ℝ)*(sp_s6_27) + (4525837138403/1000000000000 : ℝ)*(f.failure) + (4544843081941/500000000000 : ℝ)*(f.sum) + (20771913571514586407/34836308100000000000000000000000 : ℝ)*base63 + (1151087564029327/2288550000000000000000000000 : ℝ)*base64 + (504261319574447/2283300000000000000000000000 : ℝ)*base67 + (1036537351911811/1144275000000000000000000000 : ℝ)*base69 + (1439132514600623687/2689046250000000000000000000000 : ℝ)*base70 + (64508916099243/111625000000000000000000000 : ℝ)*base73 + (1122731193496219/2283300000000000000000000000 : ℝ)*base75 + (67051821148729/139531250000000000000000000 : ℝ)*base77 + (1482427528950302081/10194934500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (1037/5000000000000000 : ℝ)*base86 + (1037/5000000000000000 : ℝ)*base88 + (1037/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1159/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1159/4000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16866487135799801181505597/1935350450000000000000000000000 : ℝ) := by norm_num
    linear_combination (102872658517/1000000000000 : ℝ)*(base40) + (334905776329/500000000000 : ℝ)*(base49) + (95097/125000000000 : ℝ)*(base50) + (4627573/1000000000000 : ℝ)*(base59) + (6480852626343/1000000000000 : ℝ)*(major_s6_0) + (6480852626343/1000000000000 : ℝ)*(major_s6_1) + (6480852626343/1000000000000 : ℝ)*(major_s6_2) + (7367547/200000000000 : ℝ)*(sp_s6_0) + (10233643/1000000000000 : ℝ)*(sp_s6_6) + (36536671/250000000000 : ℝ)*(sp_s6_20) + (8653160905293/1000000000000 : ℝ)*(sp_s6_21) + (8653197743029/1000000000000 : ℝ)*(sp_s6_22) + (8653197743029/1000000000000 : ℝ)*(sp_s6_23) + (2154174112171/500000000000 : ℝ)*(sp_s6_27) + (4308504604669/1000000000000 : ℝ)*(f.failure) + (8653197743029/1000000000000 : ℝ)*(f.sum) + (1925325701065197341/23224205400000000000000000000000 : ℝ)*base62 + (118123315304921/1525700000000000000000000000 : ℝ)*base65 + (653257603310179/1522200000000000000000000000 : ℝ)*base67 + (565160927953161/1525700000000000000000000000 : ℝ)*base68 + (27475840093001371/1792697500000000000000000000000 : ℝ)*base71 + (13114012502929/27906250000000000000000000 : ℝ)*base72 + (552151100727607/1522200000000000000000000000 : ℝ)*base74 + (131495506124621/279062500000000000000000000 : ℝ)*base76 + (3145676220023951827/6796623000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (549/5000000000000000 : ℝ)*base87 + (549/5000000000000000 : ℝ)*base89 + (549/5000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((893/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(893/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22833/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22833/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45771/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(45771/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((357/1250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(357/1250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2939/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2939/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1159/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1159/4000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c303055_s6 p hpa hpb X hX hprev5

#print axioms solution

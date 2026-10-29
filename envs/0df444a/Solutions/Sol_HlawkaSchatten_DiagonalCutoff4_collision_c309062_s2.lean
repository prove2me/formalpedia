-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309062_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:05:18.816869+00:00
-- url     : https://prove2.me/submissions/9d229525-ba3f-4d9a-b214-a80800ae1216

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
theorem collision_support_c309062_s2_s2_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-760630037/5000000000 : ℝ)*x 0 + (993347689/2000000000 : ℝ)*x 1 + (-5941915977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (760630037/5000000000 : ℝ)^35 ≤ (8707498000771/100000000000000 : ℝ)^27 := by
    have hnat : (760630037 : ℕ)^35*100000000000000^27 ≤ 8707498000771^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760630037 5000000000 8707498000771 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993347689/2000000000 : ℝ)^35 ≤ (40366243809453/100000000000000 : ℝ)^27 := by
    have hnat : (993347689 : ℕ)^35*100000000000000^27 ≤ 40366243809453^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993347689 2000000000 40366243809453 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5941915977/10000000000 : ℝ)^35 ≤ (12731564543269/25000000000000 : ℝ)^27 := by
    have hnat : (5941915977 : ℕ)^35*25000000000000^27 ≤ 12731564543269^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5941915977 10000000000 12731564543269 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-760630037/5000000000 : ℝ), (993347689/2000000000 : ℝ), (-5941915977/10000000000 : ℝ)] ![(8707498000771/100000000000000 : ℝ), (40366243809453/100000000000000 : ℝ), (12731564543269/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-760630037/5000000000 : ℝ)|^35 ≤ (8707498000771/100000000000000 : ℝ)^27
        have hw : |(-760630037/5000000000 : ℝ)|=(760630037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(993347689/2000000000 : ℝ)|^35 ≤ (40366243809453/100000000000000 : ℝ)^27
        have hw : |(993347689/2000000000 : ℝ)|=(993347689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5941915977/10000000000 : ℝ)|^35 ≤ (12731564543269/25000000000000 : ℝ)^27
        have hw : |(-5941915977/10000000000 : ℝ)|=(5941915977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s2_s2_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2491606679/5000000000 : ℝ)*x 0 + (-1532864029/10000000000 : ℝ)*x 1 + (-2959256807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2491606679/5000000000 : ℝ)^35 ≤ (5067487369531/12500000000000 : ℝ)^27 := by
    have hnat : (2491606679 : ℕ)^35*12500000000000^27 ≤ 5067487369531^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491606679 5000000000 5067487369531 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1532864029/10000000000 : ℝ)^35 ≤ (8793694545433/100000000000000 : ℝ)^27 := by
    have hnat : (1532864029 : ℕ)^35*100000000000000^27 ≤ 8793694545433^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1532864029 10000000000 8793694545433 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2959256807/5000000000 : ℝ)^35 ≤ (50666406486443/100000000000000 : ℝ)^27 := by
    have hnat : (2959256807 : ℕ)^35*100000000000000^27 ≤ 50666406486443^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2959256807 5000000000 50666406486443 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2491606679/5000000000 : ℝ), (-1532864029/10000000000 : ℝ), (-2959256807/5000000000 : ℝ)] ![(5067487369531/12500000000000 : ℝ), (8793694545433/100000000000000 : ℝ), (50666406486443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2491606679/5000000000 : ℝ)|^35 ≤ (5067487369531/12500000000000 : ℝ)^27
        have hw : |(2491606679/5000000000 : ℝ)|=(2491606679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1532864029/10000000000 : ℝ)|^35 ≤ (8793694545433/100000000000000 : ℝ)^27
        have hw : |(-1532864029/10000000000 : ℝ)|=(1532864029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2959256807/5000000000 : ℝ)|^35 ≤ (50666406486443/100000000000000 : ℝ)^27
        have hw : |(-2959256807/5000000000 : ℝ)|=(2959256807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s2_s2_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1322768403/2500000000 : ℝ)*x 0 + (5310862111/10000000000 : ℝ)*x 1 + (245972681/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322768403/2500000000 : ℝ)^35 ≤ (43815811206413/100000000000000 : ℝ)^27 := by
    have hnat : (1322768403 : ℕ)^35*100000000000000^27 ≤ 43815811206413^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322768403 2500000000 43815811206413 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5310862111/10000000000 : ℝ)^35 ≤ (44028353096841/100000000000000 : ℝ)^27 := by
    have hnat : (5310862111 : ℕ)^35*100000000000000^27 ≤ 44028353096841^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310862111 10000000000 44028353096841 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245972681/1250000000 : ℝ)^35 ≤ (12155835682171/100000000000000 : ℝ)^27 := by
    have hnat : (245972681 : ℕ)^35*100000000000000^27 ≤ 12155835682171^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245972681 1250000000 12155835682171 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322768403/2500000000 : ℝ), (5310862111/10000000000 : ℝ), (245972681/1250000000 : ℝ)] ![(43815811206413/100000000000000 : ℝ), (44028353096841/100000000000000 : ℝ), (12155835682171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322768403/2500000000 : ℝ)|^35 ≤ (43815811206413/100000000000000 : ℝ)^27
        have hw : |(1322768403/2500000000 : ℝ)|=(1322768403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5310862111/10000000000 : ℝ)|^35 ≤ (44028353096841/100000000000000 : ℝ)^27
        have hw : |(5310862111/10000000000 : ℝ)|=(5310862111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(245972681/1250000000 : ℝ)|^35 ≤ (12155835682171/100000000000000 : ℝ)^27
        have hw : |(245972681/1250000000 : ℝ)|=(245972681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s2_s2_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1220017971/10000000000 : ℝ)*x 0 + (129476163/312500000 : ℝ)*x 1 + (-6876776153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1220017971/10000000000 : ℝ)^35 ≤ (3270618804671/50000000000000 : ℝ)^27 := by
    have hnat : (1220017971 : ℕ)^35*50000000000000^27 ≤ 3270618804671^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220017971 10000000000 3270618804671 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129476163/312500000 : ℝ)^35 ≤ (3989045699527/12500000000000 : ℝ)^27 := by
    have hnat : (129476163 : ℕ)^35*12500000000000^27 ≤ 3989045699527^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129476163 312500000 3989045699527 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6876776153/10000000000 : ℝ)^35 ≤ (30773198388303/50000000000000 : ℝ)^27 := by
    have hnat : (6876776153 : ℕ)^35*50000000000000^27 ≤ 30773198388303^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6876776153 10000000000 30773198388303 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1220017971/10000000000 : ℝ), (129476163/312500000 : ℝ), (-6876776153/10000000000 : ℝ)] ![(3270618804671/50000000000000 : ℝ), (3989045699527/12500000000000 : ℝ), (30773198388303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1220017971/10000000000 : ℝ)|^35 ≤ (3270618804671/50000000000000 : ℝ)^27
        have hw : |(-1220017971/10000000000 : ℝ)|=(1220017971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129476163/312500000 : ℝ)|^35 ≤ (3989045699527/12500000000000 : ℝ)^27
        have hw : |(129476163/312500000 : ℝ)|=(129476163/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6876776153/10000000000 : ℝ)|^35 ≤ (30773198388303/50000000000000 : ℝ)^27
        have hw : |(-6876776153/10000000000 : ℝ)|=(6876776153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s2_s2_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1109175601/2500000000 : ℝ)*x 0 + (-38628481/500000000 : ℝ)*x 1 + (-6873600601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1109175601/2500000000 : ℝ)^35 ≤ (2179543745281/6250000000000 : ℝ)^27 := by
    have hnat : (1109175601 : ℕ)^35*6250000000000^27 ≤ 2179543745281^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109175601 2500000000 2179543745281 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38628481/500000000 : ℝ)^35 ≤ (904435649571/25000000000000 : ℝ)^27 := by
    have hnat : (38628481 : ℕ)^35*25000000000000^27 ≤ 904435649571^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38628481 500000000 904435649571 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6873600601/10000000000 : ℝ)^35 ≤ (61509557462269/100000000000000 : ℝ)^27 := by
    have hnat : (6873600601 : ℕ)^35*100000000000000^27 ≤ 61509557462269^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6873600601 10000000000 61509557462269 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1109175601/2500000000 : ℝ), (-38628481/500000000 : ℝ), (-6873600601/10000000000 : ℝ)] ![(2179543745281/6250000000000 : ℝ), (904435649571/25000000000000 : ℝ), (61509557462269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1109175601/2500000000 : ℝ)|^35 ≤ (2179543745281/6250000000000 : ℝ)^27
        have hw : |(1109175601/2500000000 : ℝ)|=(1109175601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-38628481/500000000 : ℝ)|^35 ≤ (904435649571/25000000000000 : ℝ)^27
        have hw : |(-38628481/500000000 : ℝ)|=(38628481/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6873600601/10000000000 : ℝ)|^35 ≤ (61509557462269/100000000000000 : ℝ)^27
        have hw : |(-6873600601/10000000000 : ℝ)|=(6873600601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s2_s2_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (567788363/1250000000 : ℝ)*x 0 + (3285823131/5000000000 : ℝ)*x 1 + (35749061/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (567788363/1250000000 : ℝ)^35 ≤ (3595247251507/10000000000000 : ℝ)^27 := by
    have hnat : (567788363 : ℕ)^35*10000000000000^27 ≤ 3595247251507^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567788363 1250000000 3595247251507 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3285823131/5000000000 : ℝ)^35 ≤ (29014942674273/50000000000000 : ℝ)^27 := by
    have hnat : (3285823131 : ℕ)^35*50000000000000^27 ≤ 29014942674273^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3285823131 5000000000 29014942674273 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35749061/312500000 : ℝ)^35 ≤ (3008821058533/50000000000000 : ℝ)^27 := by
    have hnat : (35749061 : ℕ)^35*50000000000000^27 ≤ 3008821058533^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35749061 312500000 3008821058533 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(567788363/1250000000 : ℝ), (3285823131/5000000000 : ℝ), (35749061/312500000 : ℝ)] ![(3595247251507/10000000000000 : ℝ), (29014942674273/50000000000000 : ℝ), (3008821058533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(567788363/1250000000 : ℝ)|^35 ≤ (3595247251507/10000000000000 : ℝ)^27
        have hw : |(567788363/1250000000 : ℝ)|=(567788363/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3285823131/5000000000 : ℝ)|^35 ≤ (29014942674273/50000000000000 : ℝ)^27
        have hw : |(3285823131/5000000000 : ℝ)|=(3285823131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35749061/312500000 : ℝ)|^35 ≤ (3008821058533/50000000000000 : ℝ)^27
        have hw : |(35749061/312500000 : ℝ)|=(35749061/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s2_s2_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (122374233/250000000 : ℝ)*x 0 + (1692125427/2500000000 : ℝ)*x 1 + (-23322843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (122374233/250000000 : ℝ)^35 ≤ (1237867219159/3125000000000 : ℝ)^27 := by
    have hnat : (122374233 : ℕ)^35*3125000000000^27 ≤ 1237867219159^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122374233 250000000 1237867219159 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1692125427/2500000000 : ℝ)^35 ≤ (60293169023867/100000000000000 : ℝ)^27 := by
    have hnat : (1692125427 : ℕ)^35*100000000000000^27 ≤ 60293169023867^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692125427 2500000000 60293169023867 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23322843/5000000000 : ℝ)^35 ≤ (95079953649/100000000000000 : ℝ)^27 := by
    have hnat : (23322843 : ℕ)^35*100000000000000^27 ≤ 95079953649^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23322843 5000000000 95079953649 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(122374233/250000000 : ℝ), (1692125427/2500000000 : ℝ), (-23322843/5000000000 : ℝ)] ![(1237867219159/3125000000000 : ℝ), (60293169023867/100000000000000 : ℝ), (95079953649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(122374233/250000000 : ℝ)|^35 ≤ (1237867219159/3125000000000 : ℝ)^27
        have hw : |(122374233/250000000 : ℝ)|=(122374233/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1692125427/2500000000 : ℝ)|^35 ≤ (60293169023867/100000000000000 : ℝ)^27
        have hw : |(1692125427/2500000000 : ℝ)|=(1692125427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23322843/5000000000 : ℝ)|^35 ≤ (95079953649/100000000000000 : ℝ)^27
        have hw : |(-23322843/5000000000 : ℝ)|=(23322843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s2_s2_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-38260927/500000000 : ℝ)*x 0 + (4416130297/10000000000 : ℝ)*x 1 + (-3447744323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38260927/500000000 : ℝ)^35 ≤ (3573182980203/100000000000000 : ℝ)^27 := by
    have hnat : (38260927 : ℕ)^35*100000000000000^27 ≤ 3573182980203^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38260927 500000000 3573182980203 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4416130297/10000000000 : ℝ)^35 ≤ (6932647167877/20000000000000 : ℝ)^27 := by
    have hnat : (4416130297 : ℕ)^35*20000000000000^27 ≤ 6932647167877^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416130297 10000000000 6932647167877 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3447744323/5000000000 : ℝ)^35 ≤ (61763581165433/100000000000000 : ℝ)^27 := by
    have hnat : (3447744323 : ℕ)^35*100000000000000^27 ≤ 61763581165433^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3447744323 5000000000 61763581165433 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38260927/500000000 : ℝ), (4416130297/10000000000 : ℝ), (-3447744323/5000000000 : ℝ)] ![(3573182980203/100000000000000 : ℝ), (6932647167877/20000000000000 : ℝ), (61763581165433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38260927/500000000 : ℝ)|^35 ≤ (3573182980203/100000000000000 : ℝ)^27
        have hw : |(-38260927/500000000 : ℝ)|=(38260927/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4416130297/10000000000 : ℝ)|^35 ≤ (6932647167877/20000000000000 : ℝ)^27
        have hw : |(4416130297/10000000000 : ℝ)|=(4416130297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3447744323/5000000000 : ℝ)|^35 ≤ (61763581165433/100000000000000 : ℝ)^27
        have hw : |(-3447744323/5000000000 : ℝ)|=(3447744323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s2_s2_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2062945819/5000000000 : ℝ)*x 0 + (-609498247/5000000000 : ℝ)*x 1 + (-3446150581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2062945819/5000000000 : ℝ)^35 ≤ (31739287324587/100000000000000 : ℝ)^27 := by
    have hnat : (2062945819 : ℕ)^35*100000000000000^27 ≤ 31739287324587^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062945819 5000000000 31739287324587 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (609498247/5000000000 : ℝ)^35 ≤ (1633534752411/25000000000000 : ℝ)^27 := by
    have hnat : (609498247 : ℕ)^35*25000000000000^27 ≤ 1633534752411^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609498247 5000000000 1633534752411 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3446150581/5000000000 : ℝ)^35 ≤ (61726573646551/100000000000000 : ℝ)^27 := by
    have hnat : (3446150581 : ℕ)^35*100000000000000^27 ≤ 61726573646551^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3446150581 5000000000 61726573646551 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2062945819/5000000000 : ℝ), (-609498247/5000000000 : ℝ), (-3446150581/5000000000 : ℝ)] ![(31739287324587/100000000000000 : ℝ), (1633534752411/25000000000000 : ℝ), (61726573646551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2062945819/5000000000 : ℝ)|^35 ≤ (31739287324587/100000000000000 : ℝ)^27
        have hw : |(2062945819/5000000000 : ℝ)|=(2062945819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-609498247/5000000000 : ℝ)|^35 ≤ (1633534752411/25000000000000 : ℝ)^27
        have hw : |(-609498247/5000000000 : ℝ)|=(609498247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3446150581/5000000000 : ℝ)|^35 ≤ (61726573646551/100000000000000 : ℝ)^27
        have hw : |(-3446150581/5000000000 : ℝ)|=(3446150581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s2_s2_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6354898829/10000000000 : ℝ)*x 0 + (2387901161/5000000000 : ℝ)*x 1 + (1152040557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6354898829/10000000000 : ℝ)^35 ≤ (1736282876223/3125000000000 : ℝ)^27 := by
    have hnat : (6354898829 : ℕ)^35*3125000000000^27 ≤ 1736282876223^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6354898829 10000000000 1736282876223 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2387901161/5000000000 : ℝ)^35 ≤ (2397888471253/6250000000000 : ℝ)^27 := by
    have hnat : (2387901161 : ℕ)^35*6250000000000^27 ≤ 2397888471253^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2387901161 5000000000 2397888471253 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1152040557/10000000000 : ℝ)^35 ≤ (1214546480891/20000000000000 : ℝ)^27 := by
    have hnat : (1152040557 : ℕ)^35*20000000000000^27 ≤ 1214546480891^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152040557 10000000000 1214546480891 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6354898829/10000000000 : ℝ), (2387901161/5000000000 : ℝ), (1152040557/10000000000 : ℝ)] ![(1736282876223/3125000000000 : ℝ), (2397888471253/6250000000000 : ℝ), (1214546480891/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6354898829/10000000000 : ℝ)|^35 ≤ (1736282876223/3125000000000 : ℝ)^27
        have hw : |(6354898829/10000000000 : ℝ)|=(6354898829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2387901161/5000000000 : ℝ)|^35 ≤ (2397888471253/6250000000000 : ℝ)^27
        have hw : |(2387901161/5000000000 : ℝ)|=(2387901161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1152040557/10000000000 : ℝ)|^35 ≤ (1214546480891/20000000000000 : ℝ)^27
        have hw : |(1152040557/10000000000 : ℝ)|=(1152040557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s2_s2_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3620313029/5000000000 : ℝ)*x 0 + (34055051/78125000 : ℝ)*x 1 + (-27209333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3620313029/5000000000 : ℝ)^35 ≤ (13160072988727/20000000000000 : ℝ)^27 := by
    have hnat : (3620313029 : ℕ)^35*20000000000000^27 ≤ 13160072988727^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3620313029 5000000000 13160072988727 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34055051/78125000 : ℝ)^35 ≤ (34083528051033/100000000000000 : ℝ)^27 := by
    have hnat : (34055051 : ℕ)^35*100000000000000^27 ≤ 34083528051033^27*78125000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34055051 78125000 34083528051033 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27209333/5000000000 : ℝ)^35 ≤ (29026748261/25000000000000 : ℝ)^27 := by
    have hnat : (27209333 : ℕ)^35*25000000000000^27 ≤ 29026748261^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27209333 5000000000 29026748261 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3620313029/5000000000 : ℝ), (34055051/78125000 : ℝ), (-27209333/5000000000 : ℝ)] ![(13160072988727/20000000000000 : ℝ), (34083528051033/100000000000000 : ℝ), (29026748261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3620313029/5000000000 : ℝ)|^35 ≤ (13160072988727/20000000000000 : ℝ)^27
        have hw : |(3620313029/5000000000 : ℝ)|=(3620313029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34055051/78125000 : ℝ)|^35 ≤ (34083528051033/100000000000000 : ℝ)^27
        have hw : |(34055051/78125000 : ℝ)|=(34055051/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27209333/5000000000 : ℝ)|^35 ≤ (29026748261/25000000000000 : ℝ)^27
        have hw : |(-27209333/5000000000 : ℝ)|=(27209333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s2_s2_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-324853309/10000000000 : ℝ)*x 0 + (5916063367/10000000000 : ℝ)*x 1 + (-227741413/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324853309/10000000000 : ℝ)^35 ≤ (1176808380907/100000000000000 : ℝ)^27 := by
    have hnat : (324853309 : ℕ)^35*100000000000000^27 ≤ 1176808380907^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324853309 10000000000 1176808380907 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5916063367/10000000000 : ℝ)^35 ≤ (2025568695141/4000000000000 : ℝ)^27 := by
    have hnat : (5916063367 : ℕ)^35*4000000000000^27 ≤ 2025568695141^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5916063367 10000000000 2025568695141 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227741413/400000000 : ℝ)^35 ≤ (12045993558123/25000000000000 : ℝ)^27 := by
    have hnat : (227741413 : ℕ)^35*25000000000000^27 ≤ 12045993558123^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227741413 400000000 12045993558123 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-324853309/10000000000 : ℝ), (5916063367/10000000000 : ℝ), (-227741413/400000000 : ℝ)] ![(1176808380907/100000000000000 : ℝ), (2025568695141/4000000000000 : ℝ), (12045993558123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-324853309/10000000000 : ℝ)|^35 ≤ (1176808380907/100000000000000 : ℝ)^27
        have hw : |(-324853309/10000000000 : ℝ)|=(324853309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5916063367/10000000000 : ℝ)|^35 ≤ (2025568695141/4000000000000 : ℝ)^27
        have hw : |(5916063367/10000000000 : ℝ)|=(5916063367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-227741413/400000000 : ℝ)|^35 ≤ (12045993558123/25000000000000 : ℝ)^27
        have hw : |(-227741413/400000000 : ℝ)|=(227741413/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s2_s2_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6295892093/10000000000 : ℝ)*x 0 + (-87465639/1250000000 : ℝ)*x 1 + (-639255059/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6295892093/10000000000 : ℝ)^35 ≤ (54893217984809/100000000000000 : ℝ)^27 := by
    have hnat : (6295892093 : ℕ)^35*100000000000000^27 ≤ 54893217984809^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6295892093 10000000000 54893217984809 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87465639/1250000000 : ℝ)^35 ≤ (3181879619193/100000000000000 : ℝ)^27 := by
    have hnat : (87465639 : ℕ)^35*100000000000000^27 ≤ 3181879619193^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87465639 1250000000 3181879619193 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (639255059/1250000000 : ℝ)^35 ≤ (209624511937/500000000000 : ℝ)^27 := by
    have hnat : (639255059 : ℕ)^35*500000000000^27 ≤ 209624511937^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639255059 1250000000 209624511937 500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6295892093/10000000000 : ℝ), (-87465639/1250000000 : ℝ), (-639255059/1250000000 : ℝ)] ![(54893217984809/100000000000000 : ℝ), (3181879619193/100000000000000 : ℝ), (209624511937/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6295892093/10000000000 : ℝ)|^35 ≤ (54893217984809/100000000000000 : ℝ)^27
        have hw : |(6295892093/10000000000 : ℝ)|=(6295892093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-87465639/1250000000 : ℝ)|^35 ≤ (3181879619193/100000000000000 : ℝ)^27
        have hw : |(-87465639/1250000000 : ℝ)|=(87465639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-639255059/1250000000 : ℝ)|^35 ≤ (209624511937/500000000000 : ℝ)^27
        have hw : |(-639255059/1250000000 : ℝ)|=(639255059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s2_s2_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (442061191/1000000000 : ℝ)*x 0 + (39164613/62500000 : ℝ)*x 1 + (893719169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442061191/1000000000 : ℝ)^35 ≤ (6941768559953/20000000000000 : ℝ)^27 := by
    have hnat : (442061191 : ℕ)^35*20000000000000^27 ≤ 6941768559953^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442061191 1000000000 6941768559953 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39164613/62500000 : ℝ)^35 ≤ (10911884617407/20000000000000 : ℝ)^27 := by
    have hnat : (39164613 : ℕ)^35*20000000000000^27 ≤ 10911884617407^27*62500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39164613 62500000 10911884617407 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (893719169/5000000000 : ℝ)^35 ≤ (10731734105883/100000000000000 : ℝ)^27 := by
    have hnat : (893719169 : ℕ)^35*100000000000000^27 ≤ 10731734105883^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893719169 5000000000 10731734105883 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(442061191/1000000000 : ℝ), (39164613/62500000 : ℝ), (893719169/5000000000 : ℝ)] ![(6941768559953/20000000000000 : ℝ), (10911884617407/20000000000000 : ℝ), (10731734105883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(442061191/1000000000 : ℝ)|^35 ≤ (6941768559953/20000000000000 : ℝ)^27
        have hw : |(442061191/1000000000 : ℝ)|=(442061191/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(39164613/62500000 : ℝ)|^35 ≤ (10911884617407/20000000000000 : ℝ)^27
        have hw : |(39164613/62500000 : ℝ)|=(39164613/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(893719169/5000000000 : ℝ)|^35 ≤ (10731734105883/100000000000000 : ℝ)^27
        have hw : |(893719169/5000000000 : ℝ)|=(893719169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s2_s2_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7724697209/10000000000 : ℝ)*x 0 + (925681321/2500000000 : ℝ)*x 1 + (-63550111/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7724697209/10000000000 : ℝ)^35 ≤ (35779244235697/50000000000000 : ℝ)^27 := by
    have hnat : (7724697209 : ℕ)^35*50000000000000^27 ≤ 35779244235697^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7724697209 10000000000 35779244235697 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (925681321/2500000000 : ℝ)^35 ≤ (27585191784933/100000000000000 : ℝ)^27 := by
    have hnat : (925681321 : ℕ)^35*100000000000000^27 ≤ 27585191784933^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925681321 2500000000 27585191784933 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63550111/2500000000 : ℝ)^35 ≤ (214079932579/25000000000000 : ℝ)^27 := by
    have hnat : (63550111 : ℕ)^35*25000000000000^27 ≤ 214079932579^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63550111 2500000000 214079932579 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7724697209/10000000000 : ℝ), (925681321/2500000000 : ℝ), (-63550111/2500000000 : ℝ)] ![(35779244235697/50000000000000 : ℝ), (27585191784933/100000000000000 : ℝ), (214079932579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7724697209/10000000000 : ℝ)|^35 ≤ (35779244235697/50000000000000 : ℝ)^27
        have hw : |(7724697209/10000000000 : ℝ)|=(7724697209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(925681321/2500000000 : ℝ)|^35 ≤ (27585191784933/100000000000000 : ℝ)^27
        have hw : |(925681321/2500000000 : ℝ)|=(925681321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-63550111/2500000000 : ℝ)|^35 ≤ (214079932579/25000000000000 : ℝ)^27
        have hw : |(-63550111/2500000000 : ℝ)|=(63550111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309062_s2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((39249/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39249/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15659/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15659/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31681/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31681/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((60329/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60329/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60723/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(60723/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42617/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42617/100000 : ℝ)*X 1 2) := by
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
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91323/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (39249/50000 : ℝ) ^ (69/16 : ℝ) ≤ (35202837998207861141/100000000000000000000 : ℝ) := by
    have hpowers : (39249/50000 : ℝ)^69 ≤ (35202837998207861141/100000000000000000000 : ℝ)^16 := by
      have hnat : (39249 : ℕ)^69*100000000000000000000^16 ≤ 35202837998207861141^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39249 50000 35202837998207861141 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39249/50000 : ℝ)) (X := (35202837998207861141/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (135202837998207861141/100000000000000000000 : ℝ) ≤ (670275797418299/625000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (135202837998207861141/100000000000000000000 : ℝ)^16 ≤ (670275797418299/625000000000000 : ℝ)^69 := by
      have hnat : (135202837998207861141 : ℕ)^16*625000000000000^69 ≤ 670275797418299^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        135202837998207861141 100000000000000000000 670275797418299 625000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (670275797418299/625000000000000 : ℝ)) (X := (135202837998207861141/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (85202837998207861141/50000000000000000000 : ℝ) ≤ (226311935057723/200000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (85202837998207861141/50000000000000000000 : ℝ)^16 ≤ (226311935057723/200000000000000 : ℝ)^69 := by
      have hnat : (85202837998207861141 : ℕ)^16*200000000000000^69 ≤ 226311935057723^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85202837998207861141 50000000000000000000 226311935057723 200000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (226311935057723/200000000000000 : ℝ)) (X := (85202837998207861141/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(6467971059757/70087500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(6032489736667/80100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (39249/50000 : ℝ)) (alpha := (6467971059757/70087500000000 : ℝ)) (beta := (6032489736667/80100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (39249/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(6467971059757/70087500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(6032489736667/80100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (15659/20000 : ℝ) ^ (69/16 : ℝ) ≤ (8702980418063109699/25000000000000000000 : ℝ) := by
    have hpowers : (15659/20000 : ℝ)^69 ≤ (8702980418063109699/25000000000000000000 : ℝ)^16 := by
      have hnat : (15659 : ℕ)^69*25000000000000000000^16 ≤ 8702980418063109699^16*20000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15659 20000 8702980418063109699 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15659/20000 : ℝ)) (X := (8702980418063109699/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (33702980418063109699/25000000000000000000 : ℝ) ≤ (10717214536872853/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (33702980418063109699/25000000000000000000 : ℝ)^16 ≤ (10717214536872853/10000000000000000 : ℝ)^69 := by
      have hnat : (33702980418063109699 : ℕ)^16*10000000000000000^69 ≤ 10717214536872853^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33702980418063109699 25000000000000000000 10717214536872853 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10717214536872853/10000000000000000 : ℝ)) (X := (33702980418063109699/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (21202980418063109699/12500000000000000000 : ℝ) ≤ (2260707364705517/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (21202980418063109699/12500000000000000000 : ℝ)^16 ≤ (2260707364705517/2000000000000000 : ℝ)^69 := by
      have hnat : (21202980418063109699 : ℕ)^16*2000000000000000^69 ≤ 2260707364705517^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21202980418063109699 12500000000000000000 2260707364705517 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2260707364705517/2000000000000000 : ℝ)) (X := (21202980418063109699/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(717214536872853/7829500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(146580571663683/1957375000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (15659/20000 : ℝ)) (alpha := (717214536872853/7829500000000000 : ℝ)) (beta := (146580571663683/1957375000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (15659/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(717214536872853/7829500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(146580571663683/1957375000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (31681/50000 : ℝ) ^ (69/16 : ℝ) ≤ (13976133254088451901/100000000000000000000 : ℝ) := by
    have hpowers : (31681/50000 : ℝ)^69 ≤ (13976133254088451901/100000000000000000000 : ℝ)^16 := by
      have hnat : (31681 : ℕ)^69*100000000000000000000^16 ≤ 13976133254088451901^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31681 50000 13976133254088451901 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31681/50000 : ℝ)) (X := (13976133254088451901/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (113976133254088451901/100000000000000000000 : ℝ) ≤ (644249751106253/625000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (113976133254088451901/100000000000000000000 : ℝ)^16 ≤ (644249751106253/625000000000000 : ℝ)^69 := by
      have hnat : (113976133254088451901 : ℕ)^16*625000000000000^69 ≤ 644249751106253^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113976133254088451901 100000000000000000000 644249751106253 625000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (644249751106253/625000000000000 : ℝ)) (X := (113976133254088451901/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (63976133254088451901/50000000000000000000 : ℝ) ≤ (10588214254647701/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (63976133254088451901/50000000000000000000 : ℝ)^16 ≤ (10588214254647701/10000000000000000 : ℝ)^69 := by
      have hnat : (63976133254088451901 : ℕ)^16*10000000000000000^69 ≤ 10588214254647701^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63976133254088451901 50000000000000000000 10588214254647701 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10588214254647701/10000000000000000 : ℝ)) (X := (63976133254088451901/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(19249751106253/396012500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(280218236947653/6336200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (31681/50000 : ℝ)) (alpha := (19249751106253/396012500000000 : ℝ)) (beta := (280218236947653/6336200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (31681/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(19249751106253/396012500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(280218236947653/6336200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-760630037/5000000000 : ℝ)*X 0 0+(993347689/2000000000 : ℝ)*X 0 1+(-5941915977/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((2491606679/5000000000 : ℝ)*X 1 0+(-1532864029/10000000000 : ℝ)*X 1 1+(-2959256807/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((1322768403/2500000000 : ℝ)*X 2 0+(5310862111/10000000000 : ℝ)*X 2 1+(245972681/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1220017971/10000000000 : ℝ)*X 0 0+(129476163/312500000 : ℝ)*X 0 1+(-6876776153/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1109175601/2500000000 : ℝ)*X 1 0+(-38628481/500000000 : ℝ)*X 1 1+(-6873600601/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((567788363/1250000000 : ℝ)*X 2 0+(3285823131/5000000000 : ℝ)*X 2 1+(35749061/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((122374233/250000000 : ℝ)*X 0 0+(1692125427/2500000000 : ℝ)*X 0 1+(-23322843/5000000000 : ℝ)*X 0 2+(122374233/250000000 : ℝ)*X 1 0+(1692125427/2500000000 : ℝ)*X 1 1+(-23322843/5000000000 : ℝ)*X 1 2+(122374233/250000000 : ℝ)*X 2 0+(1692125427/2500000000 : ℝ)*X 2 1+(-23322843/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-38260927/500000000 : ℝ)*X 0 0+(4416130297/10000000000 : ℝ)*X 0 1+(-3447744323/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2062945819/5000000000 : ℝ)*X 1 0+(-609498247/5000000000 : ℝ)*X 1 1+(-3446150581/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6354898829/10000000000 : ℝ)*X 2 0+(2387901161/5000000000 : ℝ)*X 2 1+(1152040557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3620313029/5000000000 : ℝ)*X 0 0+(34055051/78125000 : ℝ)*X 0 1+(-27209333/5000000000 : ℝ)*X 0 2+(3620313029/5000000000 : ℝ)*X 1 0+(34055051/78125000 : ℝ)*X 1 1+(-27209333/5000000000 : ℝ)*X 1 2+(3620313029/5000000000 : ℝ)*X 2 0+(34055051/78125000 : ℝ)*X 2 1+(-27209333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-324853309/10000000000 : ℝ)*X 0 0+(5916063367/10000000000 : ℝ)*X 0 1+(-227741413/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((6295892093/10000000000 : ℝ)*X 1 0+(-87465639/1250000000 : ℝ)*X 1 1+(-639255059/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((442061191/1000000000 : ℝ)*X 2 0+(39164613/62500000 : ℝ)*X 2 1+(893719169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((7724697209/10000000000 : ℝ)*X 0 0+(925681321/2500000000 : ℝ)*X 0 1+(-63550111/2500000000 : ℝ)*X 0 2+(7724697209/10000000000 : ℝ)*X 1 0+(925681321/2500000000 : ℝ)*X 1 1+(-63550111/2500000000 : ℝ)*X 1 2+(7724697209/10000000000 : ℝ)*X 2 0+(925681321/2500000000 : ℝ)*X 2 1+(-63550111/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((60329/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60329/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (100912817624746744654187/16266975000000000000000000000 : ℝ) := by norm_num
    linear_combination (207277058209/1000000000000 : ℝ)*(base7) + (954113/1000000000000 : ℝ)*(base18) + (28991007027/250000000000 : ℝ)*(base60) + (1005343457209/250000000000 : ℝ)*(major_s2_0) + (1005343457209/250000000000 : ℝ)*(major_s2_1) + (1005343457209/250000000000 : ℝ)*(major_s2_2) + (110007/500000000000 : ℝ)*(sp_s2_2) + (5391257737397/1000000000000 : ℝ)*(sp_s2_7) + (5391302381247/1000000000000 : ℝ)*(sp_s2_8) + (1347826358947/250000000000 : ℝ)*(sp_s2_9) + (2732520126421/1000000000000 : ℝ)*(sp_s2_13) + (50365629/1000000000000 : ℝ)*(sp_s2_14) + (4767667/1000000000000 : ℝ)*(sp_s2_15) + (305903/125000000000 : ℝ)*(sp_s2_16) + (631310767053/250000000000 : ℝ)*(f.failure) + (5391308103027/1000000000000 : ℝ)*(f.sum) + (155997488781132071/1362892250000000000000000000000 : ℝ)*base62 + (12053836109953/15231250000000000000000000 : ℝ)*base65 + (339916136808507/559250000000000000000000000 : ℝ)*base66 + (10841083413763/60925000000000000000000000 : ℝ)*base68 + (41241462117893707/97601850000000000000000000000 : ℝ)*base71 + (838357565659/40050000000000000000000000 : ℝ)*base72 + (179797297916711/279625000000000000000000000 : ℝ)*base75 + (14058741743657/20025000000000000000000000 : ℝ)*base77 + (13828775098431707/111989812500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (10909/25000000000000000 : ℝ)*base86 + (10909/25000000000000000 : ℝ)*base88 + (10909/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60723/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(60723/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (62734723815899511223889/14931975000000000000000000000 : ℝ) := by norm_num
    linear_combination (231013242731/1000000000000 : ℝ)*(base7) + (579/10000000000 : ℝ)*(base39) + (196197907507/50000000000 : ℝ)*(major_s2_0) + (196197907507/50000000000 : ℝ)*(major_s2_1) + (196197907507/50000000000 : ℝ)*(major_s2_2) + (2854119/1000000000000 : ℝ)*(sp_s2_0) + (535189/100000000000 : ℝ)*(sp_s2_2) + (31307973/1000000000000 : ℝ)*(sp_s2_8) + (5243190922653/1000000000000 : ℝ)*(sp_s2_14) + (524316773437/100000000000 : ℝ)*(sp_s2_15) + (5243193690453/1000000000000 : ℝ)*(sp_s2_16) + (168442364677/62500000000 : ℝ)*(sp_s2_20) + (5265571/1000000000000 : ℝ)*(sp_s2_21) + (5782939/1000000000000 : ℝ)*(sp_s2_27) + (3850109961/1562500000 : ℝ)*(f.failure) + (5243199042343/1000000000000 : ℝ)*(f.sum) + (13727615026378053/442939981250000000000000000000 : ℝ)*base62 + (25610045886823/158405000000000000000000000 : ℝ)*base65 + (972258590081/6990625000000000000000000 : ℝ)*base66 + (47228541428557/316810000000000000000000000 : ℝ)*base69 + (6296447034141149/253764810000000000000000000000 : ℝ)*base70 + (2398077660121/8010000000000000000000000 : ℝ)*base72 + (10334548328883/55925000000000000000000000 : ℝ)*base75 + (234278427271/2002500000000000000000000 : ℝ)*base77 + (9670353825438211/89591850000000000000000000000 : ℝ)*base78 + (1/19531250000000 : ℝ)*base86 + (1/19531250000000 : ℝ)*base88 + (1/19531250000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42617/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42617/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3966117840915499860434617/348412750000000000000000000000 : ℝ) := by norm_num
    linear_combination (24931/1000000000000 : ℝ)*(base7) + (12319511/1000000000000 : ℝ)*(base11) + (131674792727/500000000000 : ℝ)*(base39) + (3330100744917/1000000000000 : ℝ)*(major_s2_0) + (3330100744917/1000000000000 : ℝ)*(major_s2_1) + (3330100744917/1000000000000 : ℝ)*(major_s2_2) + (14062863/500000000000 : ℝ)*(sp_s2_0) + (297239/100000000000 : ℝ)*(sp_s2_1) + (4093173/1000000000000 : ℝ)*(sp_s2_2) + (95420489/1000000000000 : ℝ)*(sp_s2_9) + (2284501386847/500000000000 : ℝ)*(sp_s2_21) + (228452012327/50000000000 : ℝ)*(sp_s2_22) + (1142235926317/250000000000 : ℝ)*(sp_s2_23) + (2091154486187/1000000000000 : ℝ)*(sp_s2_27) + (2091154461257/1000000000000 : ℝ)*(f.failure) + (456904321893/100000000000 : ℝ)*(f.sum) + (28939588664671970891/248046389500000000000000000000000 : ℝ)*base63 + (4863459689321319/6336200000000000000000000000 : ℝ)*base64 + (1038594597110811/1957375000000000000000000000 : ℝ)*base67 + (6856776268811/1584050000000000000000000000 : ℝ)*base68 + (27647426518901837/11842357800000000000000000000000 : ℝ)*base71 + (15996314409773/26700000000000000000000000 : ℝ)*base73 + (317740590702049/7829500000000000000000000000 : ℝ)*base74 + (8007212628913/93450000000000000000000000 : ℝ)*base76 + (942220720069037783/2090476500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (93479/100000000000000000 : ℝ)*base87 + (93479/100000000000000000 : ℝ)*base89 + (93479/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((39249/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39249/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15659/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15659/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31681/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31681/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((60329/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60329/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60723/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(60723/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42617/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42617/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309062_s2 p hpa hpb X hX hprev1

#print axioms solution

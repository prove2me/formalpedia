-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310057_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:27:14.113719+00:00
-- url     : https://prove2.me/submissions/19db2d4f-3b62-4507-99b9-1f4c0b1ed2d6

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
theorem collision_support_c310057_s1_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3096373339/10000000000 : ℝ)*x 0 + (1542043641/5000000000 : ℝ)*x 1 + (319439917/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3096373339/10000000000 : ℝ)^71 ≤ (343999607751/1562500000000 : ℝ)^55 := by
    have hnat : (3096373339 : ℕ)^71*1562500000000^55 ≤ 343999607751^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3096373339 10000000000 343999607751 1562500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1542043641/5000000000 : ℝ)^71 ≤ (5475817561993/25000000000000 : ℝ)^55 := by
    have hnat : (1542043641 : ℕ)^71*25000000000000^55 ≤ 5475817561993^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542043641 5000000000 5475817561993 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319439917/500000000 : ℝ)^71 ≤ (2243230193639/4000000000000 : ℝ)^55 := by
    have hnat : (319439917 : ℕ)^71*4000000000000^55 ≤ 2243230193639^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319439917 500000000 2243230193639 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3096373339/10000000000 : ℝ), (1542043641/5000000000 : ℝ), (319439917/500000000 : ℝ)] ![(343999607751/1562500000000 : ℝ), (5475817561993/25000000000000 : ℝ), (2243230193639/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3096373339/10000000000 : ℝ)|^71 ≤ (343999607751/1562500000000 : ℝ)^55
        have hw : |(-3096373339/10000000000 : ℝ)|=(3096373339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1542043641/5000000000 : ℝ)|^71 ≤ (5475817561993/25000000000000 : ℝ)^55
        have hw : |(1542043641/5000000000 : ℝ)|=(1542043641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(319439917/500000000 : ℝ)|^71 ≤ (2243230193639/4000000000000 : ℝ)^55
        have hw : |(319439917/500000000 : ℝ)|=(319439917/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310057_s1_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1544373009/5000000000 : ℝ)*x 0 + (-123059609/400000000 : ℝ)*x 1 + (6401115241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1544373009/5000000000 : ℝ)^71 ≤ (21945991250883/100000000000000 : ℝ)^55 := by
    have hnat : (1544373009 : ℕ)^71*100000000000000^55 ≤ 21945991250883^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1544373009 5000000000 21945991250883 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123059609/400000000 : ℝ)^71 ≤ (21833644861429/100000000000000 : ℝ)^55 := by
    have hnat : (123059609 : ℕ)^71*100000000000000^55 ≤ 21833644861429^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123059609 400000000 21833644861429 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6401115241/10000000000 : ℝ)^71 ≤ (28110181932811/50000000000000 : ℝ)^55 := by
    have hnat : (6401115241 : ℕ)^71*50000000000000^55 ≤ 28110181932811^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6401115241 10000000000 28110181932811 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1544373009/5000000000 : ℝ), (-123059609/400000000 : ℝ), (6401115241/10000000000 : ℝ)] ![(21945991250883/100000000000000 : ℝ), (21833644861429/100000000000000 : ℝ), (28110181932811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1544373009/5000000000 : ℝ)|^71 ≤ (21945991250883/100000000000000 : ℝ)^55
        have hw : |(1544373009/5000000000 : ℝ)|=(1544373009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123059609/400000000 : ℝ)|^71 ≤ (21833644861429/100000000000000 : ℝ)^55
        have hw : |(-123059609/400000000 : ℝ)|=(123059609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6401115241/10000000000 : ℝ)|^71 ≤ (28110181932811/50000000000000 : ℝ)^55
        have hw : |(6401115241/10000000000 : ℝ)|=(6401115241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310057_s1_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5835914639/10000000000 : ℝ)*x 0 + (731742411/1250000000 : ℝ)*x 1 + (-3504969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5835914639/10000000000 : ℝ)^71 ≤ (12474062086243/25000000000000 : ℝ)^55 := by
    have hnat : (5835914639 : ℕ)^71*25000000000000^55 ≤ 12474062086243^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5835914639 10000000000 12474062086243 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (731742411/1250000000 : ℝ)^71 ≤ (50095277343053/100000000000000 : ℝ)^55 := by
    have hnat : (731742411 : ℕ)^71*100000000000000^55 ≤ 50095277343053^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731742411 1250000000 50095277343053 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3504969/5000000000 : ℝ)^71 ≤ (8474298461/100000000000000 : ℝ)^55 := by
    have hnat : (3504969 : ℕ)^71*100000000000000^55 ≤ 8474298461^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3504969 5000000000 8474298461 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5835914639/10000000000 : ℝ), (731742411/1250000000 : ℝ), (-3504969/5000000000 : ℝ)] ![(12474062086243/25000000000000 : ℝ), (50095277343053/100000000000000 : ℝ), (8474298461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5835914639/10000000000 : ℝ)|^71 ≤ (12474062086243/25000000000000 : ℝ)^55
        have hw : |(5835914639/10000000000 : ℝ)|=(5835914639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(731742411/1250000000 : ℝ)|^71 ≤ (50095277343053/100000000000000 : ℝ)^55
        have hw : |(731742411/1250000000 : ℝ)|=(731742411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3504969/5000000000 : ℝ)|^71 ≤ (8474298461/100000000000000 : ℝ)^55
        have hw : |(-3504969/5000000000 : ℝ)|=(3504969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310057_s1_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (483178511/1000000000 : ℝ)*x 0 + (4846708431/10000000000 : ℝ)*x 1 + (3055085159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (483178511/1000000000 : ℝ)^71 ≤ (7820628191029/20000000000000 : ℝ)^55 := by
    have hnat : (483178511 : ℕ)^71*20000000000000^55 ≤ 7820628191029^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483178511 1000000000 7820628191029 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4846708431/10000000000 : ℝ)^71 ≤ (7851823557179/20000000000000 : ℝ)^55 := by
    have hnat : (4846708431 : ℕ)^71*20000000000000^55 ≤ 7851823557179^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4846708431 10000000000 7851823557179 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3055085159/10000000000 : ℝ)^71 ≤ (2163774123711/10000000000000 : ℝ)^55 := by
    have hnat : (3055085159 : ℕ)^71*10000000000000^55 ≤ 2163774123711^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3055085159 10000000000 2163774123711 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(483178511/1000000000 : ℝ), (4846708431/10000000000 : ℝ), (3055085159/10000000000 : ℝ)] ![(7820628191029/20000000000000 : ℝ), (7851823557179/20000000000000 : ℝ), (2163774123711/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(483178511/1000000000 : ℝ)|^71 ≤ (7820628191029/20000000000000 : ℝ)^55
        have hw : |(483178511/1000000000 : ℝ)|=(483178511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4846708431/10000000000 : ℝ)|^71 ≤ (7851823557179/20000000000000 : ℝ)^55
        have hw : |(4846708431/10000000000 : ℝ)|=(4846708431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3055085159/10000000000 : ℝ)|^71 ≤ (2163774123711/10000000000000 : ℝ)^55
        have hw : |(3055085159/10000000000 : ℝ)|=(3055085159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310057_s1_s1_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2286674613/10000000000 : ℝ)*x 0 + (341289413/2000000000 : ℝ)*x 1 + (7994987059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2286674613/10000000000 : ℝ)^71 ≤ (14886448388741/100000000000000 : ℝ)^55 := by
    have hnat : (2286674613 : ℕ)^71*100000000000000^55 ≤ 14886448388741^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286674613 10000000000 14886448388741 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341289413/2000000000 : ℝ)^71 ≤ (2550595857529/25000000000000 : ℝ)^55 := by
    have hnat : (341289413 : ℕ)^71*25000000000000^55 ≤ 2550595857529^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341289413 2000000000 2550595857529 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7994987059/10000000000 : ℝ)^71 ≤ (74911168165161/100000000000000 : ℝ)^55 := by
    have hnat : (7994987059 : ℕ)^71*100000000000000^55 ≤ 74911168165161^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7994987059 10000000000 74911168165161 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2286674613/10000000000 : ℝ), (341289413/2000000000 : ℝ), (7994987059/10000000000 : ℝ)] ![(14886448388741/100000000000000 : ℝ), (2550595857529/25000000000000 : ℝ), (74911168165161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2286674613/10000000000 : ℝ)|^71 ≤ (14886448388741/100000000000000 : ℝ)^55
        have hw : |(-2286674613/10000000000 : ℝ)|=(2286674613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341289413/2000000000 : ℝ)|^71 ≤ (2550595857529/25000000000000 : ℝ)^55
        have hw : |(341289413/2000000000 : ℝ)|=(341289413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7994987059/10000000000 : ℝ)|^71 ≤ (74911168165161/100000000000000 : ℝ)^55
        have hw : |(7994987059/10000000000 : ℝ)|=(7994987059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310057_s1_s1_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2273513497/10000000000 : ℝ)*x 0 + (-106039093/625000000 : ℝ)*x 1 + (2002595289/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2273513497/10000000000 : ℝ)^71 ≤ (230874000369/1562500000000 : ℝ)^55 := by
    have hnat : (2273513497 : ℕ)^71*1562500000000^55 ≤ 230874000369^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273513497 10000000000 230874000369 1562500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106039093/625000000 : ℝ)^71 ≤ (10126644096961/100000000000000 : ℝ)^55 := by
    have hnat : (106039093 : ℕ)^71*100000000000000^55 ≤ 10126644096961^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106039093 625000000 10126644096961 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2002595289/2500000000 : ℝ)^71 ≤ (15019483972749/20000000000000 : ℝ)^55 := by
    have hnat : (2002595289 : ℕ)^71*20000000000000^55 ≤ 15019483972749^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002595289 2500000000 15019483972749 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2273513497/10000000000 : ℝ), (-106039093/625000000 : ℝ), (2002595289/2500000000 : ℝ)] ![(230874000369/1562500000000 : ℝ), (10126644096961/100000000000000 : ℝ), (15019483972749/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2273513497/10000000000 : ℝ)|^71 ≤ (230874000369/1562500000000 : ℝ)^55
        have hw : |(2273513497/10000000000 : ℝ)|=(2273513497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106039093/625000000 : ℝ)|^71 ≤ (10126644096961/100000000000000 : ℝ)^55
        have hw : |(-106039093/625000000 : ℝ)|=(106039093/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2002595289/2500000000 : ℝ)|^71 ≤ (15019483972749/20000000000000 : ℝ)^55
        have hw : |(2002595289/2500000000 : ℝ)|=(2002595289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310057_s1_s1_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1845435299/5000000000 : ℝ)*x 0 + (1557004753/2000000000 : ℝ)*x 1 + (-6757/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1845435299/5000000000 : ℝ)^71 ≤ (5523732682769/20000000000000 : ℝ)^55 := by
    have hnat : (1845435299 : ℕ)^71*20000000000000^55 ≤ 5523732682769^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845435299 5000000000 5523732682769 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1557004753/2000000000 : ℝ)^71 ≤ (2261916106601/3125000000000 : ℝ)^55 := by
    have hnat : (1557004753 : ℕ)^71*3125000000000^55 ≤ 2261916106601^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557004753 2000000000 2261916106601 3125000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6757/1000000000 : ℝ)^71 ≤ (21168123/100000000000000 : ℝ)^55 := by
    have hnat : (6757 : ℕ)^71*100000000000000^55 ≤ 21168123^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6757 1000000000 21168123 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1845435299/5000000000 : ℝ), (1557004753/2000000000 : ℝ), (-6757/1000000000 : ℝ)] ![(5523732682769/20000000000000 : ℝ), (2261916106601/3125000000000 : ℝ), (21168123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1845435299/5000000000 : ℝ)|^71 ≤ (5523732682769/20000000000000 : ℝ)^55
        have hw : |(1845435299/5000000000 : ℝ)|=(1845435299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1557004753/2000000000 : ℝ)|^71 ≤ (2261916106601/3125000000000 : ℝ)^55
        have hw : |(1557004753/2000000000 : ℝ)|=(1557004753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6757/1000000000 : ℝ)|^71 ≤ (21168123/100000000000000 : ℝ)^55
        have hw : |(-6757/1000000000 : ℝ)|=(6757/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310057_s1_s1_12 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (842391427/2500000000 : ℝ)*x 0 + (7107306643/10000000000 : ℝ)*x 1 + (910344281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842391427/2500000000 : ℝ)^71 ≤ (24555053861627/100000000000000 : ℝ)^55 := by
    have hnat : (842391427 : ℕ)^71*100000000000000^55 ≤ 24555053861627^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842391427 2500000000 24555053861627 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7107306643/10000000000 : ℝ)^71 ≤ (64352393608379/100000000000000 : ℝ)^55 := by
    have hnat : (7107306643 : ℕ)^71*100000000000000^55 ≤ 64352393608379^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7107306643 10000000000 64352393608379 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (910344281/5000000000 : ℝ)^71 ≤ (5546276256393/50000000000000 : ℝ)^55 := by
    have hnat : (910344281 : ℕ)^71*50000000000000^55 ≤ 5546276256393^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910344281 5000000000 5546276256393 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(842391427/2500000000 : ℝ), (7107306643/10000000000 : ℝ), (910344281/5000000000 : ℝ)] ![(24555053861627/100000000000000 : ℝ), (64352393608379/100000000000000 : ℝ), (5546276256393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(842391427/2500000000 : ℝ)|^71 ≤ (24555053861627/100000000000000 : ℝ)^55
        have hw : |(842391427/2500000000 : ℝ)|=(842391427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7107306643/10000000000 : ℝ)|^71 ≤ (64352393608379/100000000000000 : ℝ)^55
        have hw : |(7107306643/10000000000 : ℝ)|=(7107306643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(910344281/5000000000 : ℝ)|^71 ≤ (5546276256393/50000000000000 : ℝ)^55
        have hw : |(910344281/5000000000 : ℝ)|=(910344281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310057_s1_s1_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1719396061/10000000000 : ℝ)*x 0 + (142050039/625000000 : ℝ)*x 1 + (399817321/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1719396061/10000000000 : ℝ)^71 ≤ (1030243382533/10000000000000 : ℝ)^55 := by
    have hnat : (1719396061 : ℕ)^71*10000000000000^55 ≤ 1030243382533^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1719396061 10000000000 1030243382533 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142050039/625000000 : ℝ)^71 ≤ (7384977706817/50000000000000 : ℝ)^55 := by
    have hnat : (142050039 : ℕ)^71*50000000000000^55 ≤ 7384977706817^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142050039 625000000 7384977706817 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (399817321/500000000 : ℝ)^71 ≤ (37463805373451/50000000000000 : ℝ)^55 := by
    have hnat : (399817321 : ℕ)^71*50000000000000^55 ≤ 37463805373451^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399817321 500000000 37463805373451 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1719396061/10000000000 : ℝ), (142050039/625000000 : ℝ), (399817321/500000000 : ℝ)] ![(1030243382533/10000000000000 : ℝ), (7384977706817/50000000000000 : ℝ), (37463805373451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1719396061/10000000000 : ℝ)|^71 ≤ (1030243382533/10000000000000 : ℝ)^55
        have hw : |(-1719396061/10000000000 : ℝ)|=(1719396061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142050039/625000000 : ℝ)|^71 ≤ (7384977706817/50000000000000 : ℝ)^55
        have hw : |(142050039/625000000 : ℝ)|=(142050039/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(399817321/500000000 : ℝ)|^71 ≤ (37463805373451/50000000000000 : ℝ)^55
        have hw : |(399817321/500000000 : ℝ)|=(399817321/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310057_s1_s1_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (854745081/5000000000 : ℝ)*x 0 + (-2259706413/10000000000 : ℝ)*x 1 + (8011744879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854745081/5000000000 : ℝ)^71 ≤ (10225876126423/100000000000000 : ℝ)^55 := by
    have hnat : (854745081 : ℕ)^71*100000000000000^55 ≤ 10225876126423^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854745081 5000000000 10225876126423 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259706413/10000000000 : ℝ)^71 ≤ (2932039883851/20000000000000 : ℝ)^55 := by
    have hnat : (2259706413 : ℕ)^71*20000000000000^55 ≤ 2932039883851^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259706413 10000000000 2932039883851 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8011744879/10000000000 : ℝ)^71 ≤ (75113924441303/100000000000000 : ℝ)^55 := by
    have hnat : (8011744879 : ℕ)^71*100000000000000^55 ≤ 75113924441303^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8011744879 10000000000 75113924441303 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854745081/5000000000 : ℝ), (-2259706413/10000000000 : ℝ), (8011744879/10000000000 : ℝ)] ![(10225876126423/100000000000000 : ℝ), (2932039883851/20000000000000 : ℝ), (75113924441303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854745081/5000000000 : ℝ)|^71 ≤ (10225876126423/100000000000000 : ℝ)^55
        have hw : |(854745081/5000000000 : ℝ)|=(854745081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2259706413/10000000000 : ℝ)|^71 ≤ (2932039883851/20000000000000 : ℝ)^55
        have hw : |(-2259706413/10000000000 : ℝ)|=(2259706413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8011744879/10000000000 : ℝ)|^71 ≤ (75113924441303/100000000000000 : ℝ)^55
        have hw : |(8011744879/10000000000 : ℝ)|=(8011744879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310057_s1_s1_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7770747601/10000000000 : ℝ)*x 0 + (3708591461/10000000000 : ℝ)*x 1 + (-68149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7770747601/10000000000 : ℝ)^71 ≤ (36105007617573/50000000000000 : ℝ)^55 := by
    have hnat : (7770747601 : ℕ)^71*50000000000000^55 ≤ 36105007617573^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7770747601 10000000000 36105007617573 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3708591461/10000000000 : ℝ)^71 ≤ (6947490838687/25000000000000 : ℝ)^55 := by
    have hnat : (3708591461 : ℕ)^71*25000000000000^55 ≤ 6947490838687^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3708591461 10000000000 6947490838687 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68149/10000000000 : ℝ)^71 ≤ (2675321/12500000000000 : ℝ)^55 := by
    have hnat : (68149 : ℕ)^71*12500000000000^55 ≤ 2675321^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68149 10000000000 2675321 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7770747601/10000000000 : ℝ), (3708591461/10000000000 : ℝ), (-68149/10000000000 : ℝ)] ![(36105007617573/50000000000000 : ℝ), (6947490838687/25000000000000 : ℝ), (2675321/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7770747601/10000000000 : ℝ)|^71 ≤ (36105007617573/50000000000000 : ℝ)^55
        have hw : |(7770747601/10000000000 : ℝ)|=(7770747601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3708591461/10000000000 : ℝ)|^71 ≤ (6947490838687/25000000000000 : ℝ)^55
        have hw : |(3708591461/10000000000 : ℝ)|=(3708591461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68149/10000000000 : ℝ)|^71 ≤ (2675321/12500000000000 : ℝ)^55
        have hw : |(-68149/10000000000 : ℝ)|=(68149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310057_s1_s1_18 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7094546519/10000000000 : ℝ)*x 0 + (1692937153/5000000000 : ℝ)*x 1 + (1820126497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7094546519/10000000000 : ℝ)^71 ≤ (16050821763859/25000000000000 : ℝ)^55 := by
    have hnat : (7094546519 : ℕ)^71*25000000000000^55 ≤ 16050821763859^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7094546519 10000000000 16050821763859 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1692937153/5000000000 : ℝ)^71 ≤ (24708580780213/100000000000000 : ℝ)^55 := by
    have hnat : (1692937153 : ℕ)^71*100000000000000^55 ≤ 24708580780213^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692937153 5000000000 24708580780213 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1820126497/10000000000 : ℝ)^71 ≤ (1774101143/16000000000 : ℝ)^55 := by
    have hnat : (1820126497 : ℕ)^71*16000000000^55 ≤ 1774101143^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820126497 10000000000 1774101143 16000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7094546519/10000000000 : ℝ), (1692937153/5000000000 : ℝ), (1820126497/10000000000 : ℝ)] ![(16050821763859/25000000000000 : ℝ), (24708580780213/100000000000000 : ℝ), (1774101143/16000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7094546519/10000000000 : ℝ)|^71 ≤ (16050821763859/25000000000000 : ℝ)^55
        have hw : |(7094546519/10000000000 : ℝ)|=(7094546519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1692937153/5000000000 : ℝ)|^71 ≤ (24708580780213/100000000000000 : ℝ)^55
        have hw : |(1692937153/5000000000 : ℝ)|=(1692937153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1820126497/10000000000 : ℝ)|^71 ≤ (1774101143/16000000000 : ℝ)^55
        have hw : |(1820126497/10000000000 : ℝ)|=(1820126497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310057_s1_s1_19 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-305031183/625000000 : ℝ)*x 0 + (109563697/625000000 : ℝ)*x 1 + (1457340711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (305031183/625000000 : ℝ)^71 ≤ (3961280824669/10000000000000 : ℝ)^55 := by
    have hnat : (305031183 : ℕ)^71*10000000000000^55 ≤ 3961280824669^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305031183 625000000 3961280824669 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109563697/625000000 : ℝ)^71 ≤ (5281622172321/50000000000000 : ℝ)^55 := by
    have hnat : (109563697 : ℕ)^71*50000000000000^55 ≤ 5281622172321^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109563697 625000000 5281622172321 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1457340711/2500000000 : ℝ)^71 ≤ (24911973699669/50000000000000 : ℝ)^55 := by
    have hnat : (1457340711 : ℕ)^71*50000000000000^55 ≤ 24911973699669^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1457340711 2500000000 24911973699669 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-305031183/625000000 : ℝ), (109563697/625000000 : ℝ), (1457340711/2500000000 : ℝ)] ![(3961280824669/10000000000000 : ℝ), (5281622172321/50000000000000 : ℝ), (24911973699669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-305031183/625000000 : ℝ)|^71 ≤ (3961280824669/10000000000000 : ℝ)^55
        have hw : |(-305031183/625000000 : ℝ)|=(305031183/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109563697/625000000 : ℝ)|^71 ≤ (5281622172321/50000000000000 : ℝ)^55
        have hw : |(109563697/625000000 : ℝ)|=(109563697/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1457340711/2500000000 : ℝ)|^71 ≤ (24911973699669/50000000000000 : ℝ)^55
        have hw : |(1457340711/2500000000 : ℝ)|=(1457340711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310057_s1_s1_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (880069817/5000000000 : ℝ)*x 0 + (-1215317523/2500000000 : ℝ)*x 1 + (5842585331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (880069817/5000000000 : ℝ)^71 ≤ (5309332520757/50000000000000 : ℝ)^55 := by
    have hnat : (880069817 : ℕ)^71*50000000000000^55 ≤ 5309332520757^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880069817 5000000000 5309332520757 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1215317523/2500000000 : ℝ)^71 ≤ (4926431165731/12500000000000 : ℝ)^55 := by
    have hnat : (1215317523 : ℕ)^71*12500000000000^55 ≤ 4926431165731^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215317523 2500000000 4926431165731 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5842585331/10000000000 : ℝ)^71 ≤ (24984942808423/50000000000000 : ℝ)^55 := by
    have hnat : (5842585331 : ℕ)^71*50000000000000^55 ≤ 24984942808423^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5842585331 10000000000 24984942808423 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(880069817/5000000000 : ℝ), (-1215317523/2500000000 : ℝ), (5842585331/10000000000 : ℝ)] ![(5309332520757/50000000000000 : ℝ), (4926431165731/12500000000000 : ℝ), (24984942808423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(880069817/5000000000 : ℝ)|^71 ≤ (5309332520757/50000000000000 : ℝ)^55
        have hw : |(880069817/5000000000 : ℝ)|=(880069817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1215317523/2500000000 : ℝ)|^71 ≤ (4926431165731/12500000000000 : ℝ)^55
        have hw : |(-1215317523/2500000000 : ℝ)|=(1215317523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5842585331/10000000000 : ℝ)|^71 ≤ (24984942808423/50000000000000 : ℝ)^55
        have hw : |(5842585331/10000000000 : ℝ)|=(5842585331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310057_s1_s1_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6154716861/10000000000 : ℝ)*x 0 + (1381226973/2500000000 : ℝ)*x 1 + (34742313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6154716861/10000000000 : ℝ)^71 ≤ (10688500652113/20000000000000 : ℝ)^55 := by
    have hnat : (6154716861 : ℕ)^71*20000000000000^55 ≤ 10688500652113^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6154716861 10000000000 10688500652113 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1381226973/2500000000 : ℝ)^71 ≤ (11622647409867/25000000000000 : ℝ)^55 := by
    have hnat : (1381226973 : ℕ)^71*25000000000000^55 ≤ 11622647409867^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381226973 2500000000 11622647409867 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34742313/10000000000 : ℝ)^71 ≤ (33453547733/50000000000000 : ℝ)^55 := by
    have hnat : (34742313 : ℕ)^71*50000000000000^55 ≤ 33453547733^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34742313 10000000000 33453547733 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6154716861/10000000000 : ℝ), (1381226973/2500000000 : ℝ), (34742313/10000000000 : ℝ)] ![(10688500652113/20000000000000 : ℝ), (11622647409867/25000000000000 : ℝ), (33453547733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6154716861/10000000000 : ℝ)|^71 ≤ (10688500652113/20000000000000 : ℝ)^55
        have hw : |(6154716861/10000000000 : ℝ)|=(6154716861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1381226973/2500000000 : ℝ)|^71 ≤ (11622647409867/25000000000000 : ℝ)^55
        have hw : |(1381226973/2500000000 : ℝ)|=(1381226973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34742313/10000000000 : ℝ)|^71 ≤ (33453547733/50000000000000 : ℝ)^55
        have hw : |(34742313/10000000000 : ℝ)|=(34742313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310057_s1_s1_25 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (341421101/1000000000 : ℝ)*x 0 + (1381226973/2500000000 : ℝ)*x 1 + (3785233253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341421101/1000000000 : ℝ)^71 ≤ (12487925101703/50000000000000 : ℝ)^55 := by
    have hnat : (341421101 : ℕ)^71*50000000000000^55 ≤ 12487925101703^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341421101 1000000000 12487925101703 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1381226973/2500000000 : ℝ)^71 ≤ (11622647409867/25000000000000 : ℝ)^55 := by
    have hnat : (1381226973 : ℕ)^71*25000000000000^55 ≤ 11622647409867^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381226973 2500000000 11622647409867 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3785233253/10000000000 : ℝ)^71 ≤ (28533560140139/100000000000000 : ℝ)^55 := by
    have hnat : (3785233253 : ℕ)^71*100000000000000^55 ≤ 28533560140139^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3785233253 10000000000 28533560140139 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(341421101/1000000000 : ℝ), (1381226973/2500000000 : ℝ), (3785233253/10000000000 : ℝ)] ![(12487925101703/50000000000000 : ℝ), (11622647409867/25000000000000 : ℝ), (28533560140139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(341421101/1000000000 : ℝ)|^71 ≤ (12487925101703/50000000000000 : ℝ)^55
        have hw : |(341421101/1000000000 : ℝ)|=(341421101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1381226973/2500000000 : ℝ)|^71 ≤ (11622647409867/25000000000000 : ℝ)^55
        have hw : |(1381226973/2500000000 : ℝ)|=(1381226973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3785233253/10000000000 : ℝ)|^71 ≤ (28533560140139/100000000000000 : ℝ)^55
        have hw : |(3785233253/10000000000 : ℝ)|=(3785233253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310057_s1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((44571/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44571/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17647/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17647/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(9777/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(9777/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2306/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2306/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(73647/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(73647/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(12187/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(12187/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (18111/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (44571/50000 : ℝ) ^ (35/8 : ℝ) ≤ (2419192216014498651/4000000000000000000 : ℝ) := by
    have hpowers : (44571/50000 : ℝ)^35 ≤ (2419192216014498651/4000000000000000000 : ℝ)^8 := by
      have hnat : (44571 : ℕ)^35*4000000000000000000^8 ≤ 2419192216014498651^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44571 50000 2419192216014498651 4000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44571/50000 : ℝ)) (X := (2419192216014498651/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (6419192216014498651/4000000000000000000 : ℝ) ≤ (11141745441238879/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (6419192216014498651/4000000000000000000 : ℝ)^8 ≤ (11141745441238879/10000000000000000 : ℝ)^35 := by
      have hnat : (6419192216014498651 : ℕ)^8*10000000000000000^35 ≤ 11141745441238879^35*4000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6419192216014498651 4000000000000000000 11141745441238879 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11141745441238879/10000000000000000 : ℝ)) (X := (6419192216014498651/4000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (4419192216014498651/2000000000000000000 : ℝ) ≤ (11986712544938397/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (4419192216014498651/2000000000000000000 : ℝ)^8 ≤ (11986712544938397/10000000000000000 : ℝ)^35 := by
      have hnat : (4419192216014498651 : ℕ)^8*10000000000000000^35 ≤ 11986712544938397^35*2000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4419192216014498651 2000000000000000000 11986712544938397 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11986712544938397/10000000000000000 : ℝ)) (X := (4419192216014498651/2000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(380581813746293/2971400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(422483551849759/4457100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (44571/50000 : ℝ)) (alpha := (380581813746293/2971400000000000 : ℝ)) (beta := (422483551849759/4457100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (44571/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(380581813746293/2971400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(422483551849759/4457100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (17647/20000 : ℝ) ^ (35/8 : ℝ) ≤ (28916711241391985413/50000000000000000000 : ℝ) := by
    have hpowers : (17647/20000 : ℝ)^35 ≤ (28916711241391985413/50000000000000000000 : ℝ)^8 := by
      have hnat : (17647 : ℕ)^35*50000000000000000000^8 ≤ 28916711241391985413^8*20000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17647 20000 28916711241391985413 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17647/20000 : ℝ)) (X := (28916711241391985413/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (78916711241391985413/50000000000000000000 : ℝ) ≤ (5549739867459407/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (78916711241391985413/50000000000000000000 : ℝ)^8 ≤ (5549739867459407/5000000000000000 : ℝ)^35 := by
      have hnat : (78916711241391985413 : ℕ)^8*5000000000000000^35 ≤ 5549739867459407^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78916711241391985413 50000000000000000000 5549739867459407 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5549739867459407/5000000000000000 : ℝ)) (X := (78916711241391985413/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (53916711241391985413/25000000000000000000 : ℝ) ≤ (11920469068079219/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (53916711241391985413/25000000000000000000 : ℝ)^8 ≤ (11920469068079219/10000000000000000 : ℝ)^35 := by
      have hnat : (53916711241391985413 : ℕ)^8*10000000000000000^35 ≤ 11920469068079219^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53916711241391985413 25000000000000000000 11920469068079219 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11920469068079219/10000000000000000 : ℝ)) (X := (53916711241391985413/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(549739867459407/4411750000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(164197866632081/1764700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (17647/20000 : ℝ)) (alpha := (549739867459407/4411750000000000 : ℝ)) (beta := (164197866632081/1764700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (17647/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(549739867459407/4411750000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(164197866632081/1764700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (9777/20000 : ℝ) ^ (35/8 : ℝ) ≤ (2183299622797762181/50000000000000000000 : ℝ) := by
    have hpowers : (9777/20000 : ℝ)^35 ≤ (2183299622797762181/50000000000000000000 : ℝ)^8 := by
      have hnat : (9777 : ℕ)^35*50000000000000000000^8 ≤ 2183299622797762181^8*20000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9777 20000 2183299622797762181 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9777/20000 : ℝ)) (X := (2183299622797762181/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (52183299622797762181/50000000000000000000 : ℝ) ≤ (5049084515326629/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (52183299622797762181/50000000000000000000 : ℝ)^8 ≤ (5049084515326629/5000000000000000 : ℝ)^35 := by
      have hnat : (52183299622797762181 : ℕ)^8*5000000000000000^35 ≤ 5049084515326629^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52183299622797762181 50000000000000000000 5049084515326629 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5049084515326629/5000000000000000 : ℝ)) (X := (52183299622797762181/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (27183299622797762181/25000000000000000000 : ℝ) ≤ (10193218919324983/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (27183299622797762181/25000000000000000000 : ℝ)^8 ≤ (10193218919324983/10000000000000000 : ℝ)^35 := by
      have hnat : (27183299622797762181 : ℕ)^8*10000000000000000^35 ≤ 10193218919324983^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27183299622797762181 25000000000000000000 10193218919324983 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10193218919324983/10000000000000000 : ℝ)) (X := (27183299622797762181/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(49084515326629/2444250000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(3801995546869/195540000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (9777/20000 : ℝ)) (alpha := (49084515326629/2444250000000000 : ℝ)) (beta := (3801995546869/195540000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (9777/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(49084515326629/2444250000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(3801995546869/195540000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3096373339/10000000000 : ℝ)*X 0 0+(1542043641/5000000000 : ℝ)*X 0 1+(319439917/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1544373009/5000000000 : ℝ)*X 1 0+(-123059609/400000000 : ℝ)*X 1 1+(6401115241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5835914639/10000000000 : ℝ)*X 2 0+(731742411/1250000000 : ℝ)*X 2 1+(-3504969/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((483178511/1000000000 : ℝ)*X 0 0+(4846708431/10000000000 : ℝ)*X 0 1+(3055085159/10000000000 : ℝ)*X 0 2+(483178511/1000000000 : ℝ)*X 1 0+(4846708431/10000000000 : ℝ)*X 1 1+(3055085159/10000000000 : ℝ)*X 1 2+(483178511/1000000000 : ℝ)*X 2 0+(4846708431/10000000000 : ℝ)*X 2 1+(3055085159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2286674613/10000000000 : ℝ)*X 0 0+(341289413/2000000000 : ℝ)*X 0 1+(7994987059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2273513497/10000000000 : ℝ)*X 1 0+(-106039093/625000000 : ℝ)*X 1 1+(2002595289/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1845435299/5000000000 : ℝ)*X 2 0+(1557004753/2000000000 : ℝ)*X 2 1+(-6757/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((842391427/2500000000 : ℝ)*X 0 0+(7107306643/10000000000 : ℝ)*X 0 1+(910344281/5000000000 : ℝ)*X 0 2+(842391427/2500000000 : ℝ)*X 1 0+(7107306643/10000000000 : ℝ)*X 1 1+(910344281/5000000000 : ℝ)*X 1 2+(842391427/2500000000 : ℝ)*X 2 0+(7107306643/10000000000 : ℝ)*X 2 1+(910344281/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-1719396061/10000000000 : ℝ)*X 0 0+(142050039/625000000 : ℝ)*X 0 1+(399817321/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((854745081/5000000000 : ℝ)*X 1 0+(-2259706413/10000000000 : ℝ)*X 1 1+(8011744879/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((7770747601/10000000000 : ℝ)*X 2 0+(3708591461/10000000000 : ℝ)*X 2 1+(-68149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((7094546519/10000000000 : ℝ)*X 0 0+(1692937153/5000000000 : ℝ)*X 0 1+(1820126497/10000000000 : ℝ)*X 0 2+(7094546519/10000000000 : ℝ)*X 1 0+(1692937153/5000000000 : ℝ)*X 1 1+(1820126497/10000000000 : ℝ)*X 1 2+(7094546519/10000000000 : ℝ)*X 2 0+(1692937153/5000000000 : ℝ)*X 2 1+(1820126497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-305031183/625000000 : ℝ)*X 0 0+(109563697/625000000 : ℝ)*X 0 1+(1457340711/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((880069817/5000000000 : ℝ)*X 1 0+(-1215317523/2500000000 : ℝ)*X 1 1+(5842585331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((6154716861/10000000000 : ℝ)*X 2 0+(1381226973/2500000000 : ℝ)*X 2 1+(34742313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((341421101/1000000000 : ℝ)*X 0 0+(1381226973/2500000000 : ℝ)*X 0 1+(3785233253/10000000000 : ℝ)*X 0 2+(341421101/1000000000 : ℝ)*X 1 0+(1381226973/2500000000 : ℝ)*X 1 1+(3785233253/10000000000 : ℝ)*X 1 2+(341421101/1000000000 : ℝ)*X 2 0+(1381226973/2500000000 : ℝ)*X 2 1+(3785233253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310057_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((2306/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2306/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (965045256723279658427/74285000000000000000000000 : ℝ) := by norm_num
    linear_combination (85002003157/100000000000 : ℝ)*(base7) + (17947565031/125000000000 : ℝ)*(base59) + (32438934131/1000000000000 : ℝ)*(base60) + (411003199279/200000000000 : ℝ)*(major_s1_0) + (411003199279/200000000000 : ℝ)*(major_s1_1) + (411003199279/200000000000 : ℝ)*(major_s1_2) + (2195797/250000000000 : ℝ)*(sp_s1_0) + (6428177/1000000000000 : ℝ)*(sp_s1_1) + (2326628602067/1000000000000 : ℝ)*(sp_s1_7) + (2326712777149/1000000000000 : ℝ)*(sp_s1_8) + (93068768213/40000000000 : ℝ)*(sp_s1_9) + (2120162422127/1000000000000 : ℝ)*(sp_s1_12) + (8182007/100000000000 : ℝ)*(sp_s1_13) + (8973467/1000000000000 : ℝ)*(sp_s1_25) + (1270151364023/1000000000000 : ℝ)*(f.failure) + (93068768213/40000000000 : ℝ)*(f.sum) + (1590317564148463231/8626735950000000000000000000000 : ℝ)*base62 + (42413274063841/195540000000000000000000000 : ℝ)*base65 + (143102977106987/352940000000000000000000000 : ℝ)*base67 + (1560615008887/15276562500000000000000000 : ℝ)*base69 + (552792195316388179/5810275560000000000000000000000 : ℝ)*base70 + (216754862628731/891420000000000000000000000 : ℝ)*base72 + (330925333469593/882350000000000000000000000 : ℝ)*base75 + (130168534716947/594280000000000000000000000 : ℝ)*base77 + (734076022481329477/7865444370000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (126761/100000000000000000 : ℝ)*base86 + (126761/100000000000000000 : ℝ)*base88 + (126761/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(73647/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(73647/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6997776630359289412112249/410796950000000000000000000000 : ℝ) := by norm_num
    linear_combination (849597178767/1000000000000 : ℝ)*(base7) + (30747/25000000000 : ℝ)*(base40) + (142093586931/1000000000000 : ℝ)*(base59) + (1391114561/12500000000 : ℝ)*(base60) + (6413798867/3125000000 : ℝ)*(major_s1_0) + (6413798867/3125000000 : ℝ)*(major_s1_1) + (6413798867/3125000000 : ℝ)*(major_s1_2) + (973449/125000000000 : ℝ)*(sp_s1_1) + (3532869/500000000000 : ℝ)*(sp_s1_6) + (114744903/1000000000000 : ℝ)*(sp_s1_8) + (2323379629327/1000000000000 : ℝ)*(sp_s1_13) + (2323257096831/1000000000000 : ℝ)*(sp_s1_14) + (2323379629327/1000000000000 : ℝ)*(sp_s1_15) + (1059067131771/500000000000 : ℝ)*(sp_s1_18) + (1268544150513/1000000000000 : ℝ)*(f.failure) + (2323379629327/1000000000000 : ℝ)*(f.sum) + (309996075554608249/1232390850000000000000000000000 : ℝ)*base63 + (20576718162793/48885000000000000000000000 : ℝ)*base64 + (448868687053/3151250000000000000000000 : ℝ)*base66 + (214596094361953/488850000000000000000000000 : ℝ)*base69 + (14722690984064903/58102755600000000000000000000 : ℝ)*base70 + (167019827245141/445710000000000000000000000 : ℝ)*base73 + (29435181795937/126050000000000000000000000 : ℝ)*base74 + (50700766337307/148570000000000000000000000 : ℝ)*base77 + (67568733627273511/224726982000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (50191/100000000000000000 : ℝ)*base86 + (50191/100000000000000000 : ℝ)*base88 + (50191/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(12187/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(12187/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11986971166048599412464030129/3051605143075000000000000000000000 : ℝ) := by norm_num
    linear_combination (20713357169/50000000000 : ℝ)*(base5) + (45214410553/250000000000 : ℝ)*(base7) + (6767273/1000000000000 : ℝ)*(base8) + (19009/1000000000000 : ℝ)*(base11) + (6510577/1000000000000 : ℝ)*(base16) + (828337472321/1000000000000 : ℝ)*(base59) + (214277190253/125000000000 : ℝ)*(major_s1_0) + (214277190253/125000000000 : ℝ)*(major_s1_1) + (214277190253/125000000000 : ℝ)*(major_s1_2) + (333641/100000000000 : ℝ)*(sp_s1_2) + (1129865201843/500000000000 : ℝ)*(sp_s1_19) + (2259730679391/1000000000000 : ℝ)*(sp_s1_20) + (1337000498469/500000000000 : ℝ)*(sp_s1_21) + (826103284937/1000000000000 : ℝ)*(sp_s1_25) + (211902557221/200000000000 : ℝ)*(f.failure) + (141233574373/62500000000 : ℝ)*(f.sum) + (767483321543588809/3080977125000000000000000000000 : ℝ)*base62 + (643638215587/2444250000000000000000000 : ℝ)*base64 + (92214251685771/126050000000000000000000000 : ℝ)*base67 + (119212279589963/305531250000000000000000000 : ℝ)*base69 + (1891337883843998377/3631422225000000000000000000000 : ℝ)*base70 + (289448071357499/1114275000000000000000000000 : ℝ)*base73 + (160070664159687/315125000000000000000000000 : ℝ)*base75 + (189672501486979/371425000000000000000000000 : ℝ)*base77 + (496981292947803859/5618174550000000000000000000000 : ℝ)*base79 + (22747/20000000000000000 : ℝ)*base86 + (22747/20000000000000000 : ℝ)*base88 + (22747/20000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((44571/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44571/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17647/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17647/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(9777/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(9777/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2306/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2306/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(73647/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(73647/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(12187/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(12187/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310057_s1 p hpa hpb X hX hprev0

#print axioms solution

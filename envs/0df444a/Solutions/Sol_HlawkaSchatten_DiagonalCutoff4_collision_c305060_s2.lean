-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305060_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:31:30.108987+00:00
-- url     : https://prove2.me/submissions/5fd04381-e08b-477a-861f-f5c4d04c19d4

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
theorem collision_support_c305060_s2_s2_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-319550373/2000000000 : ℝ)*x 0 + (226004171/500000000 : ℝ)*x 1 + (-6412324619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (319550373/2000000000 : ℝ)^67 ≤ (8987313852463/100000000000000 : ℝ)^51 := by
    have hnat : (319550373 : ℕ)^67*100000000000000^51 ≤ 8987313852463^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319550373 2000000000 8987313852463 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226004171/500000000 : ℝ)^67 ≤ (35233606601173/100000000000000 : ℝ)^51 := by
    have hnat : (226004171 : ℕ)^67*100000000000000^51 ≤ 35233606601173^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226004171 500000000 35233606601173 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6412324619/10000000000 : ℝ)^67 ≤ (55779079528223/100000000000000 : ℝ)^51 := by
    have hnat : (6412324619 : ℕ)^67*100000000000000^51 ≤ 55779079528223^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6412324619 10000000000 55779079528223 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-319550373/2000000000 : ℝ), (226004171/500000000 : ℝ), (-6412324619/10000000000 : ℝ)] ![(8987313852463/100000000000000 : ℝ), (35233606601173/100000000000000 : ℝ), (55779079528223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-319550373/2000000000 : ℝ)|^67 ≤ (8987313852463/100000000000000 : ℝ)^51
        have hw : |(-319550373/2000000000 : ℝ)|=(319550373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226004171/500000000 : ℝ)|^67 ≤ (35233606601173/100000000000000 : ℝ)^51
        have hw : |(226004171/500000000 : ℝ)|=(226004171/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6412324619/10000000000 : ℝ)|^67 ≤ (55779079528223/100000000000000 : ℝ)^51
        have hw : |(-6412324619/10000000000 : ℝ)|=(6412324619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s2_s2_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2256476109/5000000000 : ℝ)*x 0 + (-1600544641/10000000000 : ℝ)*x 1 + (-1283381269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2256476109/5000000000 : ℝ)^67 ≤ (17580299297699/50000000000000 : ℝ)^51 := by
    have hnat : (2256476109 : ℕ)^67*50000000000000^51 ≤ 17580299297699^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256476109 5000000000 17580299297699 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1600544641/10000000000 : ℝ)^67 ≤ (9007957209279/100000000000000 : ℝ)^51 := by
    have hnat : (1600544641 : ℕ)^67*100000000000000^51 ≤ 9007957209279^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1600544641 10000000000 9007957209279 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1283381269/2000000000 : ℝ)^67 ≤ (55831444183517/100000000000000 : ℝ)^51 := by
    have hnat : (1283381269 : ℕ)^67*100000000000000^51 ≤ 55831444183517^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283381269 2000000000 55831444183517 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2256476109/5000000000 : ℝ), (-1600544641/10000000000 : ℝ), (-1283381269/2000000000 : ℝ)] ![(17580299297699/50000000000000 : ℝ), (9007957209279/100000000000000 : ℝ), (55831444183517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2256476109/5000000000 : ℝ)|^67 ≤ (17580299297699/50000000000000 : ℝ)^51
        have hw : |(2256476109/5000000000 : ℝ)|=(2256476109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1600544641/10000000000 : ℝ)|^67 ≤ (9007957209279/100000000000000 : ℝ)^51
        have hw : |(-1600544641/10000000000 : ℝ)|=(1600544641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1283381269/2000000000 : ℝ)|^67 ≤ (55831444183517/100000000000000 : ℝ)^51
        have hw : |(-1283381269/2000000000 : ℝ)|=(1283381269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s2_s2_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-622194097/5000000000 : ℝ)*x 0 + (2351157717/10000000000 : ℝ)*x 1 + (-2081288653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (622194097/5000000000 : ℝ)^67 ≤ (6471731227187/100000000000000 : ℝ)^51 := by
    have hnat : (622194097 : ℕ)^67*100000000000000^51 ≤ 6471731227187^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622194097 5000000000 6471731227187 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2351157717/10000000000 : ℝ)^67 ≤ (14929209953119/100000000000000 : ℝ)^51 := by
    have hnat : (2351157717 : ℕ)^67*100000000000000^51 ≤ 14929209953119^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351157717 10000000000 14929209953119 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081288653/2500000000 : ℝ)^67 ≤ (39299529404509/50000000000000 : ℝ)^51 := by
    have hnat : (2081288653 : ℕ)^67*50000000000000^51 ≤ 39299529404509^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081288653 2500000000 39299529404509 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-622194097/5000000000 : ℝ), (2351157717/10000000000 : ℝ), (-2081288653/2500000000 : ℝ)] ![(6471731227187/100000000000000 : ℝ), (14929209953119/100000000000000 : ℝ), (39299529404509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-622194097/5000000000 : ℝ)|^67 ≤ (6471731227187/100000000000000 : ℝ)^51
        have hw : |(-622194097/5000000000 : ℝ)|=(622194097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2351157717/10000000000 : ℝ)|^67 ≤ (14929209953119/100000000000000 : ℝ)^51
        have hw : |(2351157717/10000000000 : ℝ)|=(2351157717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2081288653/2500000000 : ℝ)|^67 ≤ (39299529404509/50000000000000 : ℝ)^51
        have hw : |(-2081288653/2500000000 : ℝ)|=(2081288653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s2_s2_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2654241547/10000000000 : ℝ)*x 0 + (-416528781/5000000000 : ℝ)*x 1 + (-1041387759/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654241547/10000000000 : ℝ)^67 ≤ (4376791765369/25000000000000 : ℝ)^51 := by
    have hnat : (2654241547 : ℕ)^67*25000000000000^51 ≤ 4376791765369^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654241547 10000000000 4376791765369 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416528781/5000000000 : ℝ)^67 ≤ (1909999502329/50000000000000 : ℝ)^51 := by
    have hnat : (416528781 : ℕ)^67*50000000000000^51 ≤ 1909999502329^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416528781 5000000000 1909999502329 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041387759/1250000000 : ℝ)^67 ≤ (19668208479151/25000000000000 : ℝ)^51 := by
    have hnat : (1041387759 : ℕ)^67*25000000000000^51 ≤ 19668208479151^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041387759 1250000000 19668208479151 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654241547/10000000000 : ℝ), (-416528781/5000000000 : ℝ), (-1041387759/1250000000 : ℝ)] ![(4376791765369/25000000000000 : ℝ), (1909999502329/50000000000000 : ℝ), (19668208479151/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654241547/10000000000 : ℝ)|^67 ≤ (4376791765369/25000000000000 : ℝ)^51
        have hw : |(2654241547/10000000000 : ℝ)|=(2654241547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-416528781/5000000000 : ℝ)|^67 ≤ (1909999502329/50000000000000 : ℝ)^51
        have hw : |(-416528781/5000000000 : ℝ)|=(416528781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1041387759/1250000000 : ℝ)|^67 ≤ (19668208479151/25000000000000 : ℝ)^51
        have hw : |(-1041387759/1250000000 : ℝ)|=(1041387759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s2_s2_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2494143997/10000000000 : ℝ)*x 0 + (994727269/1250000000 : ℝ)*x 1 + (1705520759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2494143997/10000000000 : ℝ)^67 ≤ (4033299211113/25000000000000 : ℝ)^51 := by
    have hnat : (2494143997 : ℕ)^67*25000000000000^51 ≤ 4033299211113^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2494143997 10000000000 4033299211113 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994727269/1250000000 : ℝ)^67 ≤ (74074812866957/100000000000000 : ℝ)^51 := by
    have hnat : (994727269 : ℕ)^67*100000000000000^51 ≤ 74074812866957^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994727269 1250000000 74074812866957 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1705520759/10000000000 : ℝ)^67 ≤ (1958398056143/20000000000000 : ℝ)^51 := by
    have hnat : (1705520759 : ℕ)^67*20000000000000^51 ≤ 1958398056143^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705520759 10000000000 1958398056143 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2494143997/10000000000 : ℝ), (994727269/1250000000 : ℝ), (1705520759/10000000000 : ℝ)] ![(4033299211113/25000000000000 : ℝ), (74074812866957/100000000000000 : ℝ), (1958398056143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2494143997/10000000000 : ℝ)|^67 ≤ (4033299211113/25000000000000 : ℝ)^51
        have hw : |(2494143997/10000000000 : ℝ)|=(2494143997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(994727269/1250000000 : ℝ)|^67 ≤ (74074812866957/100000000000000 : ℝ)^51
        have hw : |(994727269/1250000000 : ℝ)|=(994727269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1705520759/10000000000 : ℝ)|^67 ≤ (1958398056143/20000000000000 : ℝ)^51
        have hw : |(1705520759/10000000000 : ℝ)|=(1705520759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s2_s2_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1113953489/2500000000 : ℝ)*x 0 + (1447989583/2000000000 : ℝ)*x 1 + (1/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1113953489/2500000000 : ℝ)^67 ≤ (17288468390489/50000000000000 : ℝ)^51 := by
    have hnat : (1113953489 : ℕ)^67*50000000000000^51 ≤ 17288468390489^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113953489 2500000000 17288468390489 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1447989583/2000000000 : ℝ)^67 ≤ (32711531602721/50000000000000 : ℝ)^51 := by
    have hnat : (1447989583 : ℕ)^67*50000000000000^51 ≤ 32711531602721^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1447989583 2000000000 32711531602721 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1/156250000 : ℝ)^67 ≤ (1721/100000000000000 : ℝ)^51 := by
    have hnat : (1 : ℕ)^67*100000000000000^51 ≤ 1721^51*156250000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 156250000 1721 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1113953489/2500000000 : ℝ), (1447989583/2000000000 : ℝ), (1/156250000 : ℝ)] ![(17288468390489/50000000000000 : ℝ), (32711531602721/50000000000000 : ℝ), (1721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1113953489/2500000000 : ℝ)|^67 ≤ (17288468390489/50000000000000 : ℝ)^51
        have hw : |(1113953489/2500000000 : ℝ)|=(1113953489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1447989583/2000000000 : ℝ)|^67 ≤ (32711531602721/50000000000000 : ℝ)^51
        have hw : |(1447989583/2000000000 : ℝ)|=(1447989583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1/156250000 : ℝ)|^67 ≤ (1721/100000000000000 : ℝ)^51
        have hw : |(1/156250000 : ℝ)|=(1/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s2_s2_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-284940833/2000000000 : ℝ)*x 0 + (951065053/5000000000 : ℝ)*x 1 + (-8515479339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (284940833/2000000000 : ℝ)^67 ≤ (1932709437601/25000000000000 : ℝ)^51 := by
    have hnat : (284940833 : ℕ)^67*25000000000000^51 ≤ 1932709437601^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284940833 2000000000 1932709437601 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (951065053/5000000000 : ℝ)^67 ≤ (11301068411609/100000000000000 : ℝ)^51 := by
    have hnat : (951065053 : ℕ)^67*100000000000000^51 ≤ 11301068411609^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951065053 5000000000 11301068411609 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8515479339/10000000000 : ℝ)^67 ≤ (80968093825139/100000000000000 : ℝ)^51 := by
    have hnat : (8515479339 : ℕ)^67*100000000000000^51 ≤ 80968093825139^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8515479339 10000000000 80968093825139 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-284940833/2000000000 : ℝ), (951065053/5000000000 : ℝ), (-8515479339/10000000000 : ℝ)] ![(1932709437601/25000000000000 : ℝ), (11301068411609/100000000000000 : ℝ), (80968093825139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-284940833/2000000000 : ℝ)|^67 ≤ (1932709437601/25000000000000 : ℝ)^51
        have hw : |(-284940833/2000000000 : ℝ)|=(284940833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(951065053/5000000000 : ℝ)|^67 ≤ (11301068411609/100000000000000 : ℝ)^51
        have hw : |(951065053/5000000000 : ℝ)|=(951065053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8515479339/10000000000 : ℝ)|^67 ≤ (80968093825139/100000000000000 : ℝ)^51
        have hw : |(-8515479339/10000000000 : ℝ)|=(8515479339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s2_s2_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1520565967/10000000000 : ℝ)*x 0 + (-450778041/2500000000 : ℝ)*x 1 + (-8521562727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1520565967/10000000000 : ℝ)^67 ≤ (842130636289/10000000000000 : ℝ)^51 := by
    have hnat : (1520565967 : ℕ)^67*10000000000000^51 ≤ 842130636289^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1520565967 10000000000 842130636289 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450778041/2500000000 : ℝ)^67 ≤ (5267300770857/50000000000000 : ℝ)^51 := by
    have hnat : (450778041 : ℕ)^67*50000000000000^51 ≤ 5267300770857^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450778041 2500000000 5267300770857 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8521562727/10000000000 : ℝ)^67 ≤ (2532627877479/3125000000000 : ℝ)^51 := by
    have hnat : (8521562727 : ℕ)^67*3125000000000^51 ≤ 2532627877479^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8521562727 10000000000 2532627877479 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1520565967/10000000000 : ℝ), (-450778041/2500000000 : ℝ), (-8521562727/10000000000 : ℝ)] ![(842130636289/10000000000000 : ℝ), (5267300770857/50000000000000 : ℝ), (2532627877479/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1520565967/10000000000 : ℝ)|^67 ≤ (842130636289/10000000000000 : ℝ)^51
        have hw : |(1520565967/10000000000 : ℝ)|=(1520565967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-450778041/2500000000 : ℝ)|^67 ≤ (5267300770857/50000000000000 : ℝ)^51
        have hw : |(-450778041/2500000000 : ℝ)|=(450778041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8521562727/10000000000 : ℝ)|^67 ≤ (2532627877479/3125000000000 : ℝ)^51
        have hw : |(-8521562727/10000000000 : ℝ)|=(8521562727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s2_s2_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1331525641/2000000000 : ℝ)*x 0 + (1944123419/5000000000 : ℝ)*x 1 + (1026367121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1331525641/2000000000 : ℝ)^67 ≤ (2343960912713/4000000000000 : ℝ)^51 := by
    have hnat : (1331525641 : ℕ)^67*4000000000000^51 ≤ 2343960912713^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331525641 2000000000 2343960912713 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1944123419/5000000000 : ℝ)^67 ≤ (3613758772409/12500000000000 : ℝ)^51 := by
    have hnat : (1944123419 : ℕ)^67*12500000000000^51 ≤ 3613758772409^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944123419 5000000000 3613758772409 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026367121/5000000000 : ℝ)^67 ≤ (249818139831/2000000000000 : ℝ)^51 := by
    have hnat : (1026367121 : ℕ)^67*2000000000000^51 ≤ 249818139831^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026367121 5000000000 249818139831 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1331525641/2000000000 : ℝ), (1944123419/5000000000 : ℝ), (1026367121/5000000000 : ℝ)] ![(2343960912713/4000000000000 : ℝ), (3613758772409/12500000000000 : ℝ), (249818139831/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1331525641/2000000000 : ℝ)|^67 ≤ (2343960912713/4000000000000 : ℝ)^51
        have hw : |(1331525641/2000000000 : ℝ)|=(1331525641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1944123419/5000000000 : ℝ)|^67 ≤ (3613758772409/12500000000000 : ℝ)^51
        have hw : |(1944123419/5000000000 : ℝ)|=(1944123419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1026367121/5000000000 : ℝ)|^67 ≤ (249818139831/2000000000000 : ℝ)^51
        have hw : |(1026367121/5000000000 : ℝ)|=(1026367121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s2_s2_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4386565391/5000000000 : ℝ)*x 0 + (2454637631/10000000000 : ℝ)*x 1 + (1361/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4386565391/5000000000 : ℝ)^67 ≤ (84201679403161/100000000000000 : ℝ)^51 := by
    have hnat : (4386565391 : ℕ)^67*100000000000000^51 ≤ 84201679403161^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386565391 5000000000 84201679403161 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2454637631/10000000000 : ℝ)^67 ≤ (3949579780033/25000000000000 : ℝ)^51 := by
    have hnat : (2454637631 : ℕ)^67*25000000000000^51 ≤ 3949579780033^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2454637631 10000000000 3949579780033 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361/1250000000 : ℝ)^67 ≤ (1466179/100000000000000 : ℝ)^51 := by
    have hnat : (1361 : ℕ)^67*100000000000000^51 ≤ 1466179^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361 1250000000 1466179 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4386565391/5000000000 : ℝ), (2454637631/10000000000 : ℝ), (1361/1250000000 : ℝ)] ![(84201679403161/100000000000000 : ℝ), (3949579780033/25000000000000 : ℝ), (1466179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4386565391/5000000000 : ℝ)|^67 ≤ (84201679403161/100000000000000 : ℝ)^51
        have hw : |(4386565391/5000000000 : ℝ)|=(4386565391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2454637631/10000000000 : ℝ)|^67 ≤ (3949579780033/25000000000000 : ℝ)^51
        have hw : |(2454637631/10000000000 : ℝ)|=(2454637631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1361/1250000000 : ℝ)|^67 ≤ (1466179/100000000000000 : ℝ)^51
        have hw : |(1361/1250000000 : ℝ)|=(1361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s2_s2_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-751379481/5000000000 : ℝ)*x 0 + (2117503203/5000000000 : ℝ)*x 1 + (-6723715871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (751379481/5000000000 : ℝ)^67 ≤ (4145992684939/50000000000000 : ℝ)^51 := by
    have hnat : (751379481 : ℕ)^67*50000000000000^51 ≤ 4145992684939^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751379481 5000000000 4145992684939 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117503203/5000000000 : ℝ)^67 ≤ (32343624199671/100000000000000 : ℝ)^51 := by
    have hnat : (2117503203 : ℕ)^67*100000000000000^51 ≤ 32343624199671^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117503203 5000000000 32343624199671 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6723715871/10000000000 : ℝ)^67 ≤ (11872878082377/20000000000000 : ℝ)^51 := by
    have hnat : (6723715871 : ℕ)^67*20000000000000^51 ≤ 11872878082377^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6723715871 10000000000 11872878082377 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-751379481/5000000000 : ℝ), (2117503203/5000000000 : ℝ), (-6723715871/10000000000 : ℝ)] ![(4145992684939/50000000000000 : ℝ), (32343624199671/100000000000000 : ℝ), (11872878082377/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-751379481/5000000000 : ℝ)|^67 ≤ (4145992684939/50000000000000 : ℝ)^51
        have hw : |(-751379481/5000000000 : ℝ)|=(751379481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117503203/5000000000 : ℝ)|^67 ≤ (32343624199671/100000000000000 : ℝ)^51
        have hw : |(2117503203/5000000000 : ℝ)|=(2117503203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6723715871/10000000000 : ℝ)|^67 ≤ (11872878082377/20000000000000 : ℝ)^51
        have hw : |(-6723715871/10000000000 : ℝ)|=(6723715871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s2_s2_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (449987049/625000000 : ℝ)*x 0 + (-249417913/2000000000 : ℝ)*x 1 + (-385266619/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449987049/625000000 : ℝ)^67 ≤ (32473391452207/50000000000000 : ℝ)^51 := by
    have hnat : (449987049 : ℕ)^67*50000000000000^51 ≤ 32473391452207^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449987049 625000000 32473391452207 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249417913/2000000000 : ℝ)^67 ≤ (3245097091699/50000000000000 : ℝ)^51 := by
    have hnat : (249417913 : ℕ)^67*50000000000000^51 ≤ 3245097091699^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249417913 2000000000 3245097091699 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385266619/1000000000 : ℝ)^67 ≤ (7140755725341/25000000000000 : ℝ)^51 := by
    have hnat : (385266619 : ℕ)^67*25000000000000^51 ≤ 7140755725341^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385266619 1000000000 7140755725341 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(449987049/625000000 : ℝ), (-249417913/2000000000 : ℝ), (-385266619/1000000000 : ℝ)] ![(32473391452207/50000000000000 : ℝ), (3245097091699/50000000000000 : ℝ), (7140755725341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(449987049/625000000 : ℝ)|^67 ≤ (32473391452207/50000000000000 : ℝ)^51
        have hw : |(449987049/625000000 : ℝ)|=(449987049/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-249417913/2000000000 : ℝ)|^67 ≤ (3245097091699/50000000000000 : ℝ)^51
        have hw : |(-249417913/2000000000 : ℝ)|=(249417913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-385266619/1000000000 : ℝ)|^67 ≤ (7140755725341/25000000000000 : ℝ)^51
        have hw : |(-385266619/1000000000 : ℝ)|=(385266619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s2_s2_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (90442981/400000000 : ℝ)*x 0 + (47822119/62500000 : ℝ)*x 1 + (2415171307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90442981/400000000 : ℝ)^67 ≤ (14182310690021/100000000000000 : ℝ)^51 := by
    have hnat : (90442981 : ℕ)^67*100000000000000^51 ≤ 14182310690021^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90442981 400000000 14182310690021 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47822119/62500000 : ℝ)^67 ≤ (2198507011233/3125000000000 : ℝ)^51 := by
    have hnat : (47822119 : ℕ)^67*3125000000000^51 ≤ 2198507011233^51*62500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47822119 62500000 2198507011233 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2415171307/10000000000 : ℝ)^67 ≤ (1546546493517/10000000000000 : ℝ)^51 := by
    have hnat : (2415171307 : ℕ)^67*10000000000000^51 ≤ 1546546493517^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2415171307 10000000000 1546546493517 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(90442981/400000000 : ℝ), (47822119/62500000 : ℝ), (2415171307/10000000000 : ℝ)] ![(14182310690021/100000000000000 : ℝ), (2198507011233/3125000000000 : ℝ), (1546546493517/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(90442981/400000000 : ℝ)|^67 ≤ (14182310690021/100000000000000 : ℝ)^51
        have hw : |(90442981/400000000 : ℝ)|=(90442981/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(47822119/62500000 : ℝ)|^67 ≤ (2198507011233/3125000000000 : ℝ)^51
        have hw : |(47822119/62500000 : ℝ)|=(47822119/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2415171307/10000000000 : ℝ)|^67 ≤ (1546546493517/10000000000000 : ℝ)^51
        have hw : |(2415171307/10000000000 : ℝ)|=(2415171307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s2_s2_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9116962573/10000000000 : ℝ)*x 0 + (191943529/1000000000 : ℝ)*x 1 + (-309471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9116962573/10000000000 : ℝ)^67 ≤ (1771267455269/2000000000000 : ℝ)^51 := by
    have hnat : (9116962573 : ℕ)^67*2000000000000^51 ≤ 1771267455269^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9116962573 10000000000 1771267455269 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191943529/1000000000 : ℝ)^67 ≤ (11436331154897/100000000000000 : ℝ)^51 := by
    have hnat : (191943529 : ℕ)^67*100000000000000^51 ≤ 11436331154897^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191943529 1000000000 11436331154897 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (309471/5000000000 : ℝ)^67 ≤ (74015603/25000000000000 : ℝ)^51 := by
    have hnat : (309471 : ℕ)^67*25000000000000^51 ≤ 74015603^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309471 5000000000 74015603 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9116962573/10000000000 : ℝ), (191943529/1000000000 : ℝ), (-309471/5000000000 : ℝ)] ![(1771267455269/2000000000000 : ℝ), (11436331154897/100000000000000 : ℝ), (74015603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9116962573/10000000000 : ℝ)|^67 ≤ (1771267455269/2000000000000 : ℝ)^51
        have hw : |(9116962573/10000000000 : ℝ)|=(9116962573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(191943529/1000000000 : ℝ)|^67 ≤ (11436331154897/100000000000000 : ℝ)^51
        have hw : |(191943529/1000000000 : ℝ)|=(191943529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-309471/5000000000 : ℝ)|^67 ≤ (74015603/25000000000000 : ℝ)^51
        have hw : |(-309471/5000000000 : ℝ)|=(309471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305060_s2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((574/625 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(574/625 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9219/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9219/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42167/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42167/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((84723/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84723/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1711/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1711/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-75157/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-75157/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (93447/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (574/625 : ℝ) ^ (133/32 : ℝ) ≤ (70202282182416633081/100000000000000000000 : ℝ) := by
    have hpowers : (574/625 : ℝ)^133 ≤ (70202282182416633081/100000000000000000000 : ℝ)^32 := by
      have hnat : (574 : ℕ)^133*100000000000000000000^32 ≤ 70202282182416633081^32*625^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        574 625 70202282182416633081 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (574/625 : ℝ)) (X := (70202282182416633081/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (170202282182416633081/100000000000000000000 : ℝ) ≤ (11365030812961821/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (170202282182416633081/100000000000000000000 : ℝ)^32 ≤ (11365030812961821/10000000000000000 : ℝ)^133 := by
      have hnat : (170202282182416633081 : ℕ)^32*10000000000000000^133 ≤ 11365030812961821^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        170202282182416633081 100000000000000000000 11365030812961821 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11365030812961821/10000000000000000 : ℝ)) (X := (170202282182416633081/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (120202282182416633081/50000000000000000000 : ℝ) ≤ (12349671018627967/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (120202282182416633081/50000000000000000000 : ℝ)^32 ≤ (12349671018627967/10000000000000000 : ℝ)^133 := by
      have hnat : (120202282182416633081 : ℕ)^32*10000000000000000^133 ≤ 12349671018627967^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        120202282182416633081 50000000000000000000 12349671018627967 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12349671018627967/10000000000000000 : ℝ)) (X := (120202282182416633081/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1365030812961821/9184000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(492320102833073/4592000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (574/625 : ℝ)) (alpha := (1365030812961821/9184000000000000 : ℝ)) (beta := (492320102833073/4592000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (574/625 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1365030812961821/9184000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(492320102833073/4592000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (9219/10000 : ℝ) ^ (133/32 : ℝ) ≤ (2852837912106169583/4000000000000000000 : ℝ) := by
    have hpowers : (9219/10000 : ℝ)^133 ≤ (2852837912106169583/4000000000000000000 : ℝ)^32 := by
      have hnat : (9219 : ℕ)^133*4000000000000000000^32 ≤ 2852837912106169583^32*10000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9219 10000 2852837912106169583 4000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9219/10000 : ℝ)) (X := (2852837912106169583/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (6852837912106169583/4000000000000000000 : ℝ) ≤ (11382958441997883/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (6852837912106169583/4000000000000000000 : ℝ)^32 ≤ (11382958441997883/10000000000000000 : ℝ)^133 := by
      have hnat : (6852837912106169583 : ℕ)^32*10000000000000000^133 ≤ 11382958441997883^133*4000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6852837912106169583 4000000000000000000 11382958441997883 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11382958441997883/10000000000000000 : ℝ)) (X := (6852837912106169583/4000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (4852837912106169583/2000000000000000000 : ℝ) ≤ (6188613385711463/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (4852837912106169583/2000000000000000000 : ℝ)^32 ≤ (6188613385711463/5000000000000000 : ℝ)^133 := by
      have hnat : (4852837912106169583 : ℕ)^32*5000000000000000^133 ≤ 6188613385711463^133*2000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4852837912106169583 2000000000000000000 6188613385711463 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6188613385711463/5000000000000000 : ℝ)) (X := (4852837912106169583/2000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1382958441997883/9219000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(994268329425043/9219000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (9219/10000 : ℝ)) (alpha := (1382958441997883/9219000000000000 : ℝ)) (beta := (994268329425043/9219000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (9219/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1382958441997883/9219000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(994268329425043/9219000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (42167/50000 : ℝ) ^ (133/32 : ℝ) ≤ (24627409088138956789/50000000000000000000 : ℝ) := by
    have hpowers : (42167/50000 : ℝ)^133 ≤ (24627409088138956789/50000000000000000000 : ℝ)^32 := by
      have hnat : (42167 : ℕ)^133*50000000000000000000^32 ≤ 24627409088138956789^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42167 50000 24627409088138956789 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42167/50000 : ℝ)) (X := (24627409088138956789/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (74627409088138956789/50000000000000000000 : ℝ) ≤ (11011523878502233/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (74627409088138956789/50000000000000000000 : ℝ)^32 ≤ (11011523878502233/10000000000000000 : ℝ)^133 := by
      have hnat : (74627409088138956789 : ℕ)^32*10000000000000000^133 ≤ 11011523878502233^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74627409088138956789 50000000000000000000 11011523878502233 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11011523878502233/10000000000000000 : ℝ)) (X := (74627409088138956789/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (49627409088138956789/25000000000000000000 : ℝ) ≤ (11793608293398599/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (49627409088138956789/25000000000000000000 : ℝ)^32 ≤ (11793608293398599/10000000000000000 : ℝ)^133 := by
      have hnat : (49627409088138956789 : ℕ)^32*10000000000000000^133 ≤ 11793608293398599^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        49627409088138956789 25000000000000000000 11793608293398599 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11793608293398599/10000000000000000 : ℝ)) (X := (49627409088138956789/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1011523878502233/8433400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(391042207448183/4216700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (42167/50000 : ℝ)) (alpha := (1011523878502233/8433400000000000 : ℝ)) (beta := (391042207448183/4216700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (42167/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1011523878502233/8433400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(391042207448183/4216700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-319550373/2000000000 : ℝ)*X 0 0+(226004171/500000000 : ℝ)*X 0 1+(-6412324619/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((2256476109/5000000000 : ℝ)*X 1 0+(-1600544641/10000000000 : ℝ)*X 1 1+(-1283381269/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-622194097/5000000000 : ℝ)*X 0 0+(2351157717/10000000000 : ℝ)*X 0 1+(-2081288653/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2654241547/10000000000 : ℝ)*X 1 0+(-416528781/5000000000 : ℝ)*X 1 1+(-1041387759/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2494143997/10000000000 : ℝ)*X 2 0+(994727269/1250000000 : ℝ)*X 2 1+(1705520759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1113953489/2500000000 : ℝ)*X 0 0+(1447989583/2000000000 : ℝ)*X 0 1+(1/156250000 : ℝ)*X 0 2+(1113953489/2500000000 : ℝ)*X 1 0+(1447989583/2000000000 : ℝ)*X 1 1+(1/156250000 : ℝ)*X 1 2+(1113953489/2500000000 : ℝ)*X 2 0+(1447989583/2000000000 : ℝ)*X 2 1+(1/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-284940833/2000000000 : ℝ)*X 0 0+(951065053/5000000000 : ℝ)*X 0 1+(-8515479339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1520565967/10000000000 : ℝ)*X 1 0+(-450778041/2500000000 : ℝ)*X 1 1+(-8521562727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1331525641/2000000000 : ℝ)*X 2 0+(1944123419/5000000000 : ℝ)*X 2 1+(1026367121/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((4386565391/5000000000 : ℝ)*X 0 0+(2454637631/10000000000 : ℝ)*X 0 1+(1361/1250000000 : ℝ)*X 0 2+(4386565391/5000000000 : ℝ)*X 1 0+(2454637631/10000000000 : ℝ)*X 1 1+(1361/1250000000 : ℝ)*X 1 2+(4386565391/5000000000 : ℝ)*X 2 0+(2454637631/10000000000 : ℝ)*X 2 1+(1361/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-751379481/5000000000 : ℝ)*X 0 0+(2117503203/5000000000 : ℝ)*X 0 1+(-6723715871/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((449987049/625000000 : ℝ)*X 1 0+(-249417913/2000000000 : ℝ)*X 1 1+(-385266619/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((90442981/400000000 : ℝ)*X 2 0+(47822119/62500000 : ℝ)*X 2 1+(2415171307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((9116962573/10000000000 : ℝ)*X 0 0+(191943529/1000000000 : ℝ)*X 0 1+(-309471/5000000000 : ℝ)*X 0 2+(9116962573/10000000000 : ℝ)*X 1 0+(191943529/1000000000 : ℝ)*X 1 1+(-309471/5000000000 : ℝ)*X 1 2+(9116962573/10000000000 : ℝ)*X 2 0+(191943529/1000000000 : ℝ)*X 2 1+(-309471/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((84723/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84723/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (35596970259406796900139/2108350000000000000000000000 : ℝ) := by norm_num
    linear_combination (371159506211/1000000000000 : ℝ)*(base5) + (863621828649/1000000000000 : ℝ)*(base7) + (283189/125000000000 : ℝ)*(base43) + (597277/250000000000 : ℝ)*(base53) + (980135108791/500000000000 : ℝ)*(major_s2_0) + (196026795207/100000000000 : ℝ)*(major_s2_1) + (980133914237/500000000000 : ℝ)*(major_s2_2) + (8303503/500000000000 : ℝ)*(sp_s2_1) + (525171362331/250000000000 : ℝ)*(sp_s2_7) + (525154107631/250000000000 : ℝ)*(sp_s2_8) + (154489035069/62500000000 : ℝ)*(sp_s2_9) + (1774287898907/1000000000000 : ℝ)*(sp_s2_13) + (10935461/200000000000 : ℝ)*(sp_s2_15) + (22783539/1000000000000 : ℝ)*(sp_s2_23) + (1281825576469/1000000000000 : ℝ)*(f.failure) + (262586262993/125000000000 : ℝ)*(f.sum) + (1382117962435156909/6478959550000000000000000000000 : ℝ)*base62 + (334469297079613/1054175000000000000000000000 : ℝ)*base64 + (90274652941833/307300000000000000000000000 : ℝ)*base66 + (1278669009443011/4216700000000000000000000000 : ℝ)*base69 + (94827064604373432403/193630864000000000000000000000000 : ℝ)*base70 + (2001429982399257/2296000000000000000000000000 : ℝ)*base72 + (32577003787777/307300000000000000000000000 : ℝ)*base75 + (202229299906811/4592000000000000000000000000 : ℝ)*base77 + (97283078488933137/1007944000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1601/3125000000000000 : ℝ)*base87 + (1601/3125000000000000 : ℝ)*base89 + (1601/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1711/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1711/2000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (138764459740579839053780494317/8500394929600000000000000000000000 : ℝ) := by norm_num
    linear_combination (55295899879/62500000000 : ℝ)*(base7) + (233431/250000000000 : ℝ)*(base34) + (114001/500000000000 : ℝ)*(base39) + (404033/250000000000 : ℝ)*(base53) + (12295801229/200000000000 : ℝ)*(base60) + (1847013198869/1000000000000 : ℝ)*(major_s2_0) + (1847014132593/1000000000000 : ℝ)*(major_s2_1) + (1847012516461/1000000000000 : ℝ)*(major_s2_2) + (48477551/1000000000000 : ℝ)*(sp_s2_8) + (1935081298047/1000000000000 : ℝ)*(sp_s2_14) + (96751687711/50000000000 : ℝ)*(sp_s2_15) + (967541923951/500000000000 : ℝ)*(sp_s2_16) + (2092441921139/1000000000000 : ℝ)*(sp_s2_20) + (29341841/500000000000 : ℝ)*(sp_s2_27) + (1887136157/1562500000 : ℝ)*(f.failure) + (967541923951/500000000000 : ℝ)*(f.sum) + (4306307647891694263/4627828250000000000000000000000 : ℝ)*base62 + (1194378765386933/4216700000000000000000000000 : ℝ)*base64 + (23992375970381/439000000000000000000000000 : ℝ)*base66 + (11350582031796727/8433400000000000000000000000 : ℝ)*base68 + (166197418171025426537/387261728000000000000000000000000 : ℝ)*base70 + (1325490557135237/4592000000000000000000000000 : ℝ)*base73 + (292004435472761/439000000000000000000000000 : ℝ)*base74 + (864134326964449/9184000000000000000000000000 : ℝ)*base77 + (97669780956598691/2015888000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (159/625000000000000 : ℝ)*base87 + (159/625000000000000 : ℝ)*base89 + (159/625000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-75157/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-75157/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4193999186142570850497/1536500000000000000000000000 : ℝ) := by norm_num
    linear_combination (296663936523/500000000000 : ℝ)*(base7) + (586921/250000000000 : ℝ)*(base16) + (924469/500000000000 : ℝ)*(base34) + (134369234413/200000000000 : ℝ)*(base43) + (814129848249/500000000000 : ℝ)*(major_s2_0) + (956415373371/1000000000000 : ℝ)*(major_s2_1) + (407065386359/250000000000 : ℝ)*(major_s2_2) + (7438419/125000000000 : ℝ)*(sp_s2_0) + (3257439/1000000000000 : ℝ)*(sp_s2_9) + (31373847/1000000000000 : ℝ)*(sp_s2_20) + (575129487637/500000000000 : ℝ)*(sp_s2_21) + (227770519493/125000000000 : ℝ)*(sp_s2_22) + (287579268531/250000000000 : ℝ)*(sp_s2_23) + (414504732323/250000000000 : ℝ)*(sp_s2_27) + (1064724279031/1000000000000 : ℝ)*(f.failure) + (455541625907/250000000000 : ℝ)*(f.sum) + (19396440861810405097/129579191000000000000000000000000 : ℝ)*base63 + (60428595234071/2108350000000000000000000000 : ℝ)*base65 + (801369699507651/3073000000000000000000000000 : ℝ)*base67 + (157389781849963/2108350000000000000000000000 : ℝ)*base68 + (11568811987144201117/193630864000000000000000000000000 : ℝ)*base70 + (462052879936023/2296000000000000000000000000 : ℝ)*base72 + (983673574982369/3073000000000000000000000000 : ℝ)*base74 + (1227854329061429/4592000000000000000000000000 : ℝ)*base77 + (18093189899949831/1007944000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1649/3125000000000000 : ℝ)*base87 + (1649/3125000000000000 : ℝ)*base89 + (1649/3125000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((574/625 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(574/625 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9219/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9219/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42167/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42167/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((84723/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84723/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1711/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1711/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-75157/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-75157/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305060_s2 p hpa hpb X hX hprev1

#print axioms solution

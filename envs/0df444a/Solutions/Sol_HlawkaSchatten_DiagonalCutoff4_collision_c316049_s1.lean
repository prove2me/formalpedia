-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c316049_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:05:57.667604+00:00
-- url     : https://prove2.me/submissions/da339ec8-2aee-41b8-86b5-ded2ca2f01da

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
theorem collision_support_c316049_s1_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (725066389/2500000000 : ℝ)*x 0 + (-90634873/312500000 : ℝ)*x 1 + (6472783363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (725066389/2500000000 : ℝ)^39 ≤ (21072304182213/100000000000000 : ℝ)^31 := by
    have hnat : (725066389 : ℕ)^39*100000000000000^31 ≤ 21072304182213^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      725066389 2500000000 21072304182213 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90634873/312500000 : ℝ)^39 ≤ (21072764689293/100000000000000 : ℝ)^31 := by
    have hnat : (90634873 : ℕ)^39*100000000000000^31 ≤ 21072764689293^31*312500000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90634873 312500000 21072764689293 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6472783363/10000000000 : ℝ)^39 ≤ (28927465553931/50000000000000 : ℝ)^31 := by
    have hnat : (6472783363 : ℕ)^39*50000000000000^31 ≤ 28927465553931^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6472783363 10000000000 28927465553931 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(725066389/2500000000 : ℝ), (-90634873/312500000 : ℝ), (6472783363/10000000000 : ℝ)] ![(21072304182213/100000000000000 : ℝ), (21072764689293/100000000000000 : ℝ), (28927465553931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(725066389/2500000000 : ℝ)|^39 ≤ (21072304182213/100000000000000 : ℝ)^31
        have hw : |(725066389/2500000000 : ℝ)|=(725066389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90634873/312500000 : ℝ)|^39 ≤ (21072764689293/100000000000000 : ℝ)^31
        have hw : |(-90634873/312500000 : ℝ)|=(90634873/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6472783363/10000000000 : ℝ)|^39 ≤ (28927465553931/50000000000000 : ℝ)^31
        have hw : |(6472783363/10000000000 : ℝ)|=(6472783363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316049_s1_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1341098651/2500000000 : ℝ)*x 0 + (1341077787/2500000000 : ℝ)*x 1 + (-1428088009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341098651/2500000000 : ℝ)^39 ≤ (45679318052287/100000000000000 : ℝ)^31 := by
    have hnat : (1341098651 : ℕ)^39*100000000000000^31 ≤ 45679318052287^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341098651 2500000000 45679318052287 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1341077787/2500000000 : ℝ)^39 ≤ (45678424009093/100000000000000 : ℝ)^31 := by
    have hnat : (1341077787 : ℕ)^39*100000000000000^31 ≤ 45678424009093^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341077787 2500000000 45678424009093 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1428088009/10000000000 : ℝ)^39 ≤ (2160564481567/25000000000000 : ℝ)^31 := by
    have hnat : (1428088009 : ℕ)^39*25000000000000^31 ≤ 2160564481567^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428088009 10000000000 2160564481567 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341098651/2500000000 : ℝ), (1341077787/2500000000 : ℝ), (-1428088009/10000000000 : ℝ)] ![(45679318052287/100000000000000 : ℝ), (45678424009093/100000000000000 : ℝ), (2160564481567/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341098651/2500000000 : ℝ)|^39 ≤ (45679318052287/100000000000000 : ℝ)^31
        have hw : |(1341098651/2500000000 : ℝ)|=(1341098651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1341077787/2500000000 : ℝ)|^39 ≤ (45678424009093/100000000000000 : ℝ)^31
        have hw : |(1341077787/2500000000 : ℝ)|=(1341077787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1428088009/10000000000 : ℝ)|^39 ≤ (2160564481567/25000000000000 : ℝ)^31
        have hw : |(-1428088009/10000000000 : ℝ)|=(1428088009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316049_s1_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2548406419/5000000000 : ℝ)*x 0 + (1019346709/2000000000 : ℝ)*x 1 + (427114841/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2548406419/5000000000 : ℝ)^39 ≤ (42831458474559/100000000000000 : ℝ)^31 := by
    have hnat : (2548406419 : ℕ)^39*100000000000000^31 ≤ 42831458474559^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548406419 5000000000 42831458474559 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1019346709/2000000000 : ℝ)^39 ≤ (42830620171467/100000000000000 : ℝ)^31 := by
    have hnat : (1019346709 : ℕ)^39*100000000000000^31 ≤ 42830620171467^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019346709 2000000000 42830620171467 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427114841/2000000000 : ℝ)^39 ≤ (716896066807/5000000000000 : ℝ)^31 := by
    have hnat : (427114841 : ℕ)^39*5000000000000^31 ≤ 716896066807^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427114841 2000000000 716896066807 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2548406419/5000000000 : ℝ), (1019346709/2000000000 : ℝ), (427114841/2000000000 : ℝ)] ![(42831458474559/100000000000000 : ℝ), (42830620171467/100000000000000 : ℝ), (716896066807/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2548406419/5000000000 : ℝ)|^39 ≤ (42831458474559/100000000000000 : ℝ)^31
        have hw : |(2548406419/5000000000 : ℝ)|=(2548406419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1019346709/2000000000 : ℝ)|^39 ≤ (42830620171467/100000000000000 : ℝ)^31
        have hw : |(1019346709/2000000000 : ℝ)|=(1019346709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(427114841/2000000000 : ℝ)|^39 ≤ (716896066807/5000000000000 : ℝ)^31
        have hw : |(427114841/2000000000 : ℝ)|=(427114841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316049_s1_s1_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-446106317/1250000000 : ℝ)*x 0 + (1682182713/5000000000 : ℝ)*x 1 + (5510059407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (446106317/1250000000 : ℝ)^39 ≤ (1367797520431/5000000000000 : ℝ)^31 := by
    have hnat : (446106317 : ℕ)^39*5000000000000^31 ≤ 1367797520431^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446106317 1250000000 1367797520431 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1682182713/5000000000 : ℝ)^39 ≤ (5079765336403/20000000000000 : ℝ)^31 := by
    have hnat : (1682182713 : ℕ)^39*20000000000000^31 ≤ 5079765336403^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1682182713 5000000000 5079765336403 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5510059407/10000000000 : ℝ)^39 ≤ (23622611445023/50000000000000 : ℝ)^31 := by
    have hnat : (5510059407 : ℕ)^39*50000000000000^31 ≤ 23622611445023^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510059407 10000000000 23622611445023 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-446106317/1250000000 : ℝ), (1682182713/5000000000 : ℝ), (5510059407/10000000000 : ℝ)] ![(1367797520431/5000000000000 : ℝ), (5079765336403/20000000000000 : ℝ), (23622611445023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-446106317/1250000000 : ℝ)|^39 ≤ (1367797520431/5000000000000 : ℝ)^31
        have hw : |(-446106317/1250000000 : ℝ)|=(446106317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1682182713/5000000000 : ℝ)|^39 ≤ (5079765336403/20000000000000 : ℝ)^31
        have hw : |(1682182713/5000000000 : ℝ)|=(1682182713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5510059407/10000000000 : ℝ)|^39 ≤ (23622611445023/50000000000000 : ℝ)^31
        have hw : |(5510059407/10000000000 : ℝ)|=(5510059407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316049_s1_s1_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (570309561/2000000000 : ℝ)*x 0 + (-2688162127/10000000000 : ℝ)*x 1 + (1670557191/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (570309561/2000000000 : ℝ)^39 ≤ (20627961401761/100000000000000 : ℝ)^31 := by
    have hnat : (570309561 : ℕ)^39*100000000000000^31 ≤ 20627961401761^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570309561 2000000000 20627961401761 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688162127/10000000000 : ℝ)^39 ≤ (19152177451813/100000000000000 : ℝ)^31 := by
    have hnat : (2688162127 : ℕ)^39*100000000000000^31 ≤ 19152177451813^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688162127 10000000000 19152177451813 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1670557191/2500000000 : ℝ)^39 ≤ (60219861131361/100000000000000 : ℝ)^31 := by
    have hnat : (1670557191 : ℕ)^39*100000000000000^31 ≤ 60219861131361^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1670557191 2500000000 60219861131361 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(570309561/2000000000 : ℝ), (-2688162127/10000000000 : ℝ), (1670557191/2500000000 : ℝ)] ![(20627961401761/100000000000000 : ℝ), (19152177451813/100000000000000 : ℝ), (60219861131361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(570309561/2000000000 : ℝ)|^39 ≤ (20627961401761/100000000000000 : ℝ)^31
        have hw : |(570309561/2000000000 : ℝ)|=(570309561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2688162127/10000000000 : ℝ)|^39 ≤ (19152177451813/100000000000000 : ℝ)^31
        have hw : |(-2688162127/10000000000 : ℝ)|=(2688162127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1670557191/2500000000 : ℝ)|^39 ≤ (60219861131361/100000000000000 : ℝ)^31
        have hw : |(1670557191/2500000000 : ℝ)|=(1670557191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316049_s1_s1_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2621291653/5000000000 : ℝ)*x 0 + (713472287/1250000000 : ℝ)*x 1 + (-220303447/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621291653/5000000000 : ℝ)^39 ≤ (8875645336203/20000000000000 : ℝ)^31 := by
    have hnat : (2621291653 : ℕ)^39*20000000000000^31 ≤ 8875645336203^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621291653 5000000000 8875645336203 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (713472287/1250000000 : ℝ)^39 ≤ (24693912159191/50000000000000 : ℝ)^31 := by
    have hnat : (713472287 : ℕ)^39*50000000000000^31 ≤ 24693912159191^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713472287 1250000000 24693912159191 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220303447/2000000000 : ℝ)^39 ≤ (1246789798101/20000000000000 : ℝ)^31 := by
    have hnat : (220303447 : ℕ)^39*20000000000000^31 ≤ 1246789798101^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220303447 2000000000 1246789798101 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621291653/5000000000 : ℝ), (713472287/1250000000 : ℝ), (-220303447/2000000000 : ℝ)] ![(8875645336203/20000000000000 : ℝ), (24693912159191/50000000000000 : ℝ), (1246789798101/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621291653/5000000000 : ℝ)|^39 ≤ (8875645336203/20000000000000 : ℝ)^31
        have hw : |(2621291653/5000000000 : ℝ)|=(2621291653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(713472287/1250000000 : ℝ)|^39 ≤ (24693912159191/50000000000000 : ℝ)^31
        have hw : |(713472287/1250000000 : ℝ)|=(713472287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220303447/2000000000 : ℝ)|^39 ≤ (1246789798101/20000000000000 : ℝ)^31
        have hw : |(-220303447/2000000000 : ℝ)|=(220303447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316049_s1_s1_12 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (633737897/1250000000 : ℝ)*x 0 + (275988779/500000000 : ℝ)*x 1 + (1616807753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (633737897/1250000000 : ℝ)^39 ≤ (42547157086079/100000000000000 : ℝ)^31 := by
    have hnat : (633737897 : ℕ)^39*100000000000000^31 ≤ 42547157086079^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633737897 1250000000 42547157086079 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275988779/500000000 : ℝ)^39 ≤ (2367502800771/5000000000000 : ℝ)^31 := by
    have hnat : (275988779 : ℕ)^39*5000000000000^31 ≤ 2367502800771^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275988779 500000000 2367502800771 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1616807753/10000000000 : ℝ)^39 ≤ (5051393440301/50000000000000 : ℝ)^31 := by
    have hnat : (1616807753 : ℕ)^39*50000000000000^31 ≤ 5051393440301^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616807753 10000000000 5051393440301 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(633737897/1250000000 : ℝ), (275988779/500000000 : ℝ), (1616807753/10000000000 : ℝ)] ![(42547157086079/100000000000000 : ℝ), (2367502800771/5000000000000 : ℝ), (5051393440301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(633737897/1250000000 : ℝ)|^39 ≤ (42547157086079/100000000000000 : ℝ)^31
        have hw : |(633737897/1250000000 : ℝ)|=(633737897/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(275988779/500000000 : ℝ)|^39 ≤ (2367502800771/5000000000000 : ℝ)^31
        have hw : |(275988779/500000000 : ℝ)|=(275988779/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1616807753/10000000000 : ℝ)|^39 ≤ (5051393440301/50000000000000 : ℝ)^31
        have hw : |(1616807753/10000000000 : ℝ)|=(1616807753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316049_s1_s1_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3364301769/10000000000 : ℝ)*x 0 + (446114207/1250000000 : ℝ)*x 1 + (5510059027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3364301769/10000000000 : ℝ)^39 ≤ (1269911104771/5000000000000 : ℝ)^31 := by
    have hnat : (3364301769 : ℕ)^39*5000000000000^31 ≤ 1269911104771^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3364301769 10000000000 1269911104771 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (446114207/1250000000 : ℝ)^39 ≤ (27356559096063/100000000000000 : ℝ)^31 := by
    have hnat : (446114207 : ℕ)^39*100000000000000^31 ≤ 27356559096063^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446114207 1250000000 27356559096063 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5510059027/10000000000 : ℝ)^39 ≤ (944904375819/2000000000000 : ℝ)^31 := by
    have hnat : (5510059027 : ℕ)^39*2000000000000^31 ≤ 944904375819^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510059027 10000000000 944904375819 2000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3364301769/10000000000 : ℝ), (446114207/1250000000 : ℝ), (5510059027/10000000000 : ℝ)] ![(1269911104771/5000000000000 : ℝ), (27356559096063/100000000000000 : ℝ), (944904375819/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3364301769/10000000000 : ℝ)|^39 ≤ (1269911104771/5000000000000 : ℝ)^31
        have hw : |(-3364301769/10000000000 : ℝ)|=(3364301769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(446114207/1250000000 : ℝ)|^39 ≤ (27356559096063/100000000000000 : ℝ)^31
        have hw : |(446114207/1250000000 : ℝ)|=(446114207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5510059027/10000000000 : ℝ)|^39 ≤ (944904375819/2000000000000 : ℝ)^31
        have hw : |(5510059027/10000000000 : ℝ)|=(5510059027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316049_s1_s1_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2688111631/10000000000 : ℝ)*x 0 + (-712899657/2500000000 : ℝ)*x 1 + (6682227889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688111631/10000000000 : ℝ)^39 ≤ (19151724844531/100000000000000 : ℝ)^31 := by
    have hnat : (2688111631 : ℕ)^39*100000000000000^31 ≤ 19151724844531^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688111631 10000000000 19151724844531 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (712899657/2500000000 : ℝ)^39 ≤ (10314211965857/50000000000000 : ℝ)^31 := by
    have hnat : (712899657 : ℕ)^39*50000000000000^31 ≤ 10314211965857^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712899657 2500000000 10314211965857 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6682227889/10000000000 : ℝ)^39 ≤ (15054962802739/25000000000000 : ℝ)^31 := by
    have hnat : (6682227889 : ℕ)^39*25000000000000^31 ≤ 15054962802739^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6682227889 10000000000 15054962802739 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688111631/10000000000 : ℝ), (-712899657/2500000000 : ℝ), (6682227889/10000000000 : ℝ)] ![(19151724844531/100000000000000 : ℝ), (10314211965857/50000000000000 : ℝ), (15054962802739/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688111631/10000000000 : ℝ)|^39 ≤ (19151724844531/100000000000000 : ℝ)^31
        have hw : |(2688111631/10000000000 : ℝ)|=(2688111631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-712899657/2500000000 : ℝ)|^39 ≤ (10314211965857/50000000000000 : ℝ)^31
        have hw : |(-712899657/2500000000 : ℝ)|=(712899657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6682227889/10000000000 : ℝ)|^39 ≤ (15054962802739/25000000000000 : ℝ)^31
        have hw : |(6682227889/10000000000 : ℝ)|=(6682227889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316049_s1_s1_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (228314431/400000000 : ℝ)*x 0 + (5242499061/10000000000 : ℝ)*x 1 + (-550758569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228314431/400000000 : ℝ)^39 ≤ (12347180540091/25000000000000 : ℝ)^31 := by
    have hnat : (228314431 : ℕ)^39*25000000000000^31 ≤ 12347180540091^31*400000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228314431 400000000 12347180540091 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242499061/10000000000 : ℝ)^39 ≤ (44377329519261/100000000000000 : ℝ)^31 := by
    have hnat : (5242499061 : ℕ)^39*100000000000000^31 ≤ 44377329519261^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242499061 10000000000 44377329519261 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550758569/5000000000 : ℝ)^39 ≤ (6233948299873/100000000000000 : ℝ)^31 := by
    have hnat : (550758569 : ℕ)^39*100000000000000^31 ≤ 6233948299873^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550758569 5000000000 6233948299873 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(228314431/400000000 : ℝ), (5242499061/10000000000 : ℝ), (-550758569/5000000000 : ℝ)] ![(12347180540091/25000000000000 : ℝ), (44377329519261/100000000000000 : ℝ), (6233948299873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(228314431/400000000 : ℝ)|^39 ≤ (12347180540091/25000000000000 : ℝ)^31
        have hw : |(228314431/400000000 : ℝ)|=(228314431/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242499061/10000000000 : ℝ)|^39 ≤ (44377329519261/100000000000000 : ℝ)^31
        have hw : |(5242499061/10000000000 : ℝ)|=(5242499061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-550758569/5000000000 : ℝ)|^39 ≤ (6233948299873/100000000000000 : ℝ)^31
        have hw : |(-550758569/5000000000 : ℝ)|=(550758569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316049_s1_s1_18 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2759927737/5000000000 : ℝ)*x 0 + (2534910913/5000000000 : ℝ)*x 1 + (1616807329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2759927737/5000000000 : ℝ)^39 ≤ (47350918233183/100000000000000 : ℝ)^31 := by
    have hnat : (2759927737 : ℕ)^39*100000000000000^31 ≤ 47350918233183^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759927737 5000000000 47350918233183 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2534910913/5000000000 : ℝ)^39 ≤ (42546298210107/100000000000000 : ℝ)^31 := by
    have hnat : (2534910913 : ℕ)^39*100000000000000^31 ≤ 42546298210107^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2534910913 5000000000 42546298210107 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1616807329/10000000000 : ℝ)^39 ≤ (5051391773739/50000000000000 : ℝ)^31 := by
    have hnat : (1616807329 : ℕ)^39*50000000000000^31 ≤ 5051391773739^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616807329 10000000000 5051391773739 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2759927737/5000000000 : ℝ), (2534910913/5000000000 : ℝ), (1616807329/10000000000 : ℝ)] ![(47350918233183/100000000000000 : ℝ), (42546298210107/100000000000000 : ℝ), (5051391773739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2759927737/5000000000 : ℝ)|^39 ≤ (47350918233183/100000000000000 : ℝ)^31
        have hw : |(2759927737/5000000000 : ℝ)|=(2759927737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2534910913/5000000000 : ℝ)|^39 ≤ (42546298210107/100000000000000 : ℝ)^31
        have hw : |(2534910913/5000000000 : ℝ)|=(2534910913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1616807329/10000000000 : ℝ)|^39 ≤ (5051391773739/50000000000000 : ℝ)^31
        have hw : |(1616807329/10000000000 : ℝ)|=(1616807329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316049_s1_s1_19 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3713979631/10000000000 : ℝ)*x 0 + (3597971713/10000000000 : ℝ)*x 1 + (5169391523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3713979631/10000000000 : ℝ)^39 ≤ (7190686743473/25000000000000 : ℝ)^31 := by
    have hnat : (3713979631 : ℕ)^39*25000000000000^31 ≤ 7190686743473^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3713979631 10000000000 7190686743473 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3597971713/10000000000 : ℝ)^39 ≤ (690926754417/2500000000000 : ℝ)^31 := by
    have hnat : (3597971713 : ℕ)^39*2500000000000^31 ≤ 690926754417^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3597971713 10000000000 690926754417 2500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5169391523/10000000000 : ℝ)^39 ≤ (1090004571027/2500000000000 : ℝ)^31 := by
    have hnat : (5169391523 : ℕ)^39*2500000000000^31 ≤ 1090004571027^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169391523 10000000000 1090004571027 2500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3713979631/10000000000 : ℝ), (3597971713/10000000000 : ℝ), (5169391523/10000000000 : ℝ)] ![(7190686743473/25000000000000 : ℝ), (690926754417/2500000000000 : ℝ), (1090004571027/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3713979631/10000000000 : ℝ)|^39 ≤ (7190686743473/25000000000000 : ℝ)^31
        have hw : |(-3713979631/10000000000 : ℝ)|=(3713979631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3597971713/10000000000 : ℝ)|^39 ≤ (690926754417/2500000000000 : ℝ)^31
        have hw : |(3597971713/10000000000 : ℝ)|=(3597971713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5169391523/10000000000 : ℝ)|^39 ≤ (1090004571027/2500000000000 : ℝ)^31
        have hw : |(5169391523/10000000000 : ℝ)|=(5169391523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316049_s1_s1_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (56869197/200000000 : ℝ)*x 0 + (-739895513/2500000000 : ℝ)*x 1 + (6470539377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56869197/200000000 : ℝ)^39 ≤ (5138595417117/25000000000000 : ℝ)^31 := by
    have hnat : (56869197 : ℕ)^39*25000000000000^31 ≤ 5138595417117^31*200000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56869197 200000000 5138595417117 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (739895513/2500000000 : ℝ)^39 ≤ (2161591928887/10000000000000 : ℝ)^31 := by
    have hnat : (739895513 : ℕ)^39*10000000000000^31 ≤ 2161591928887^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739895513 2500000000 2161591928887 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6470539377/10000000000 : ℝ)^39 ≤ (5782969903467/10000000000000 : ℝ)^31 := by
    have hnat : (6470539377 : ℕ)^39*10000000000000^31 ≤ 5782969903467^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6470539377 10000000000 5782969903467 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(56869197/200000000 : ℝ), (-739895513/2500000000 : ℝ), (6470539377/10000000000 : ℝ)] ![(5138595417117/25000000000000 : ℝ), (2161591928887/10000000000000 : ℝ), (5782969903467/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(56869197/200000000 : ℝ)|^39 ≤ (5138595417117/25000000000000 : ℝ)^31
        have hw : |(56869197/200000000 : ℝ)|=(56869197/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-739895513/2500000000 : ℝ)|^39 ≤ (2161591928887/10000000000000 : ℝ)^31
        have hw : |(-739895513/2500000000 : ℝ)|=(739895513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6470539377/10000000000 : ℝ)|^39 ≤ (5782969903467/10000000000000 : ℝ)^31
        have hw : |(6470539377/10000000000 : ℝ)|=(6470539377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316049_s1_s1_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (168732383/312500000 : ℝ)*x 0 + (5331354321/10000000000 : ℝ)*x 1 + (-1425075121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168732383/312500000 : ℝ)^39 ≤ (23027513566523/50000000000000 : ℝ)^31 := by
    have hnat : (168732383 : ℕ)^39*50000000000000^31 ≤ 23027513566523^31*312500000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168732383 312500000 23027513566523 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5331354321/10000000000 : ℝ)^39 ≤ (1813025872221/4000000000000 : ℝ)^31 := by
    have hnat : (5331354321 : ℕ)^39*4000000000000^31 ≤ 1813025872221^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5331354321 10000000000 1813025872221 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1425075121/10000000000 : ℝ)^39 ≤ (8619326036333/100000000000000 : ℝ)^31 := by
    have hnat : (1425075121 : ℕ)^39*100000000000000^31 ≤ 8619326036333^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1425075121 10000000000 8619326036333 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168732383/312500000 : ℝ), (5331354321/10000000000 : ℝ), (-1425075121/10000000000 : ℝ)] ![(23027513566523/50000000000000 : ℝ), (1813025872221/4000000000000 : ℝ), (8619326036333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168732383/312500000 : ℝ)|^39 ≤ (23027513566523/50000000000000 : ℝ)^31
        have hw : |(168732383/312500000 : ℝ)|=(168732383/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5331354321/10000000000 : ℝ)|^39 ≤ (1813025872221/4000000000000 : ℝ)^31
        have hw : |(5331354321/10000000000 : ℝ)|=(5331354321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1425075121/10000000000 : ℝ)|^39 ≤ (8619326036333/100000000000000 : ℝ)^31
        have hw : |(-1425075121/10000000000 : ℝ)|=(1425075121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316049_s1_s1_25 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (50194759/100000000 : ℝ)*x 0 + (2596231741/5000000000 : ℝ)*x 1 + (422407943/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50194759/100000000 : ℝ)^39 ≤ (42015440521087/100000000000000 : ℝ)^31 := by
    have hnat : (50194759 : ℕ)^39*100000000000000^31 ≤ 42015440521087^31*100000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50194759 100000000 42015440521087 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596231741/5000000000 : ℝ)^39 ≤ (43845137683541/100000000000000 : ℝ)^31 := by
    have hnat : (2596231741 : ℕ)^39*100000000000000^31 ≤ 43845137683541^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596231741 5000000000 43845137683541 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422407943/2000000000 : ℝ)^39 ≤ (14139421776567/100000000000000 : ℝ)^31 := by
    have hnat : (422407943 : ℕ)^39*100000000000000^31 ≤ 14139421776567^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422407943 2000000000 14139421776567 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(50194759/100000000 : ℝ), (2596231741/5000000000 : ℝ), (422407943/2000000000 : ℝ)] ![(42015440521087/100000000000000 : ℝ), (43845137683541/100000000000000 : ℝ), (14139421776567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(50194759/100000000 : ℝ)|^39 ≤ (42015440521087/100000000000000 : ℝ)^31
        have hw : |(50194759/100000000 : ℝ)|=(50194759/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596231741/5000000000 : ℝ)|^39 ≤ (43845137683541/100000000000000 : ℝ)^31
        have hw : |(2596231741/5000000000 : ℝ)|=(2596231741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(422407943/2000000000 : ℝ)|^39 ≤ (14139421776567/100000000000000 : ℝ)^31
        have hw : |(422407943/2000000000 : ℝ)|=(422407943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316049_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((72571/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72571/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72577/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(72577/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16149/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16149/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((848/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(848/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(848/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(848/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(797/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(797/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s1_pow0 : (72571/100000 : ℝ) ^ (19/4 : ℝ) ≤ (21808448034949650103/100000000000000000000 : ℝ) := by
    have hpowers : (72571/100000 : ℝ)^19 ≤ (21808448034949650103/100000000000000000000 : ℝ)^4 := by
      have hnat : (72571 : ℕ)^19*100000000000000000000^4 ≤ 21808448034949650103^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72571 100000 21808448034949650103 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72571/100000 : ℝ)) (X := (21808448034949650103/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (121808448034949650103/100000000000000000000 : ℝ) ≤ (2606017682093629/2500000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (121808448034949650103/100000000000000000000 : ℝ)^4 ≤ (2606017682093629/2500000000000000 : ℝ)^19 := by
      have hnat : (121808448034949650103 : ℕ)^4*2500000000000000^19 ≤ 2606017682093629^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        121808448034949650103 100000000000000000000 2606017682093629 2500000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2606017682093629/2500000000000000 : ℝ)) (X := (121808448034949650103/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (71808448034949650103/50000000000000000000 : ℝ) ≤ (10791850051948211/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (71808448034949650103/50000000000000000000 : ℝ)^4 ≤ (10791850051948211/10000000000000000 : ℝ)^19 := by
      have hnat : (71808448034949650103 : ℕ)^4*10000000000000000^19 ≤ 10791850051948211^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71808448034949650103 50000000000000000000 10791850051948211 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10791850051948211/10000000000000000 : ℝ)) (X := (71808448034949650103/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(106017682093629/1814275000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(73555864714739/1451420000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (72571/100000 : ℝ)) (alpha := (106017682093629/1814275000000000 : ℝ)) (beta := (73555864714739/1451420000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (72571/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(106017682093629/1814275000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(73555864714739/1451420000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (72577/100000 : ℝ) ^ (19/4 : ℝ) ≤ (545425348786792563/2500000000000000000 : ℝ) := by
    have hpowers : (72577/100000 : ℝ)^19 ≤ (545425348786792563/2500000000000000000 : ℝ)^4 := by
      have hnat : (72577 : ℕ)^19*2500000000000000000^4 ≤ 545425348786792563^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72577 100000 545425348786792563 2500000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72577/100000 : ℝ)) (X := (545425348786792563/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (3045425348786792563/2500000000000000000 : ℝ) ≤ (10424225050470221/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3045425348786792563/2500000000000000000 : ℝ)^4 ≤ (10424225050470221/10000000000000000 : ℝ)^19 := by
      have hnat : (3045425348786792563 : ℕ)^4*10000000000000000^19 ≤ 10424225050470221^19*2500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3045425348786792563 2500000000000000000 10424225050470221 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10424225050470221/10000000000000000 : ℝ)) (X := (3045425348786792563/2500000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (1795425348786792563/1250000000000000000 : ℝ) ≤ (674507566169923/625000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (1795425348786792563/1250000000000000000 : ℝ)^4 ≤ (674507566169923/625000000000000 : ℝ)^19 := by
      have hnat : (1795425348786792563 : ℕ)^4*625000000000000^19 ≤ 674507566169923^19*1250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1795425348786792563 1250000000000000000 674507566169923 625000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (674507566169923/625000000000000 : ℝ)) (X := (1795425348786792563/1250000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(424225050470221/7257700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(367896008248547/7257700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (72577/100000 : ℝ)) (alpha := (424225050470221/7257700000000000 : ℝ)) (beta := (367896008248547/7257700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (72577/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(424225050470221/7257700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(367896008248547/7257700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (16149/100000 : ℝ) ^ (19/4 : ℝ) ≤ (17325738851185649/100000000000000000000 : ℝ) := by
    have hpowers : (16149/100000 : ℝ)^19 ≤ (17325738851185649/100000000000000000000 : ℝ)^4 := by
      have hnat : (16149 : ℕ)^19*100000000000000000000^4 ≤ 17325738851185649^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16149 100000 17325738851185649 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16149/100000 : ℝ)) (X := (17325738851185649/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100017325738851185649/100000000000000000000 : ℝ) ≤ (10000364727453637/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (100017325738851185649/100000000000000000000 : ℝ)^4 ≤ (10000364727453637/10000000000000000 : ℝ)^19 := by
      have hnat : (100017325738851185649 : ℕ)^4*10000000000000000^19 ≤ 10000364727453637^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100017325738851185649 100000000000000000000 10000364727453637 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000364727453637/10000000000000000 : ℝ)) (X := (100017325738851185649/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50017325738851185649/50000000000000000000 : ℝ) ≤ (10000729405031121/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (50017325738851185649/50000000000000000000 : ℝ)^4 ≤ (10000729405031121/10000000000000000 : ℝ)^19 := by
      have hnat : (50017325738851185649 : ℕ)^4*10000000000000000^19 ≤ 10000729405031121^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017325738851185649 50000000000000000000 10000729405031121 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000729405031121/10000000000000000 : ℝ)) (X := (50017325738851185649/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(121575817879/538300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(91169394371/403725000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (16149/100000 : ℝ)) (alpha := (121575817879/538300000000000 : ℝ)) (beta := (91169394371/403725000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (16149/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(121575817879/538300000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(91169394371/403725000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((725066389/2500000000 : ℝ)*X 1 0+(-90634873/312500000 : ℝ)*X 1 1+(6472783363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316049_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1341098651/2500000000 : ℝ)*X 2 0+(1341077787/2500000000 : ℝ)*X 2 1+(-1428088009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316049_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2548406419/5000000000 : ℝ)*X 0 0+(1019346709/2000000000 : ℝ)*X 0 1+(427114841/2000000000 : ℝ)*X 0 2+(2548406419/5000000000 : ℝ)*X 1 0+(1019346709/2000000000 : ℝ)*X 1 1+(427114841/2000000000 : ℝ)*X 1 2+(2548406419/5000000000 : ℝ)*X 2 0+(1019346709/2000000000 : ℝ)*X 2 1+(427114841/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316049_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-446106317/1250000000 : ℝ)*X 0 0+(1682182713/5000000000 : ℝ)*X 0 1+(5510059407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316049_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((570309561/2000000000 : ℝ)*X 1 0+(-2688162127/10000000000 : ℝ)*X 1 1+(1670557191/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316049_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2621291653/5000000000 : ℝ)*X 2 0+(713472287/1250000000 : ℝ)*X 2 1+(-220303447/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316049_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((633737897/1250000000 : ℝ)*X 0 0+(275988779/500000000 : ℝ)*X 0 1+(1616807753/10000000000 : ℝ)*X 0 2+(633737897/1250000000 : ℝ)*X 1 0+(275988779/500000000 : ℝ)*X 1 1+(1616807753/10000000000 : ℝ)*X 1 2+(633737897/1250000000 : ℝ)*X 2 0+(275988779/500000000 : ℝ)*X 2 1+(1616807753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316049_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-3364301769/10000000000 : ℝ)*X 0 0+(446114207/1250000000 : ℝ)*X 0 1+(5510059027/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316049_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((2688111631/10000000000 : ℝ)*X 1 0+(-712899657/2500000000 : ℝ)*X 1 1+(6682227889/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316049_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((228314431/400000000 : ℝ)*X 2 0+(5242499061/10000000000 : ℝ)*X 2 1+(-550758569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316049_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((2759927737/5000000000 : ℝ)*X 0 0+(2534910913/5000000000 : ℝ)*X 0 1+(1616807329/10000000000 : ℝ)*X 0 2+(2759927737/5000000000 : ℝ)*X 1 0+(2534910913/5000000000 : ℝ)*X 1 1+(1616807329/10000000000 : ℝ)*X 1 2+(2759927737/5000000000 : ℝ)*X 2 0+(2534910913/5000000000 : ℝ)*X 2 1+(1616807329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316049_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-3713979631/10000000000 : ℝ)*X 0 0+(3597971713/10000000000 : ℝ)*X 0 1+(5169391523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316049_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((56869197/200000000 : ℝ)*X 1 0+(-739895513/2500000000 : ℝ)*X 1 1+(6470539377/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316049_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((168732383/312500000 : ℝ)*X 2 0+(5331354321/10000000000 : ℝ)*X 2 1+(-1425075121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316049_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((50194759/100000000 : ℝ)*X 0 0+(2596231741/5000000000 : ℝ)*X 0 1+(422407943/2000000000 : ℝ)*X 0 2+(50194759/100000000 : ℝ)*X 1 0+(2596231741/5000000000 : ℝ)*X 1 1+(422407943/2000000000 : ℝ)*X 1 2+(50194759/100000000 : ℝ)*X 2 0+(2596231741/5000000000 : ℝ)*X 2 1+(422407943/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316049_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((848/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(848/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (958229948952799891970758566241/70880456922152500000000000000000000 : ℝ) := by norm_num
    linear_combination (230770384579/250000000000 : ℝ)*(base49) + (6756621477323/1000000000000 : ℝ)*(base59) + (3925347028091/1000000000000 : ℝ)*(base60) + (551625939853/40000000000 : ℝ)*(major_s1_0) + (551625939853/40000000000 : ℝ)*(major_s1_1) + (551625939853/40000000000 : ℝ)*(major_s1_2) + (83925477/100000000000 : ℝ)*(sp_s1_1) + (3378543/50000000000 : ℝ)*(sp_s1_2) + (247514711303/12500000000 : ℝ)*(sp_s1_7) + (19800422825801/1000000000000 : ℝ)*(sp_s1_8) + (19801194509711/1000000000000 : ℝ)*(sp_s1_9) + (311186252171/40000000000 : ℝ)*(sp_s1_12) + (8517633/100000000000 : ℝ)*(sp_s1_13) + (374101477/1000000000000 : ℝ)*(sp_s1_25) + (7780030405753/1000000000000 : ℝ)*(f.failure) + (19801262080571/1000000000000 : ℝ)*(f.sum) + (50402827283101003/195340995500000000000000000000 : ℝ)*base63 + (35092544224351/40372500000000000000000000 : ℝ)*base65 + (223684781189033/290308000000000000000000000 : ℝ)*base67 + (6112098542463/21532000000000000000000000 : ℝ)*base69 + (9854097678719100007/11719490790000000000000000000000 : ℝ)*base71 + (295567959859593/1451420000000000000000000000 : ℝ)*base72 + (102552991238841/1451540000000000000000000000 : ℝ)*base75 + (185132962321/2267843750000000000000000 : ℝ)*base77 + (293709102147248139/526698546700000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (59521/100000000000000000 : ℝ)*base87 + (59521/100000000000000000 : ℝ)*base89 + (59521/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(848/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(848/3125 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4184101499415406222059900321423/708804569221525000000000000000000000 : ℝ) := by norm_num
    linear_combination (461541493969/500000000000 : ℝ)*(base49) + (3337603107859/500000000000 : ℝ)*(base59) + (834053567469/200000000000 : ℝ)*(base60) + (13790659259651/1000000000000 : ℝ)*(major_s1_0) + (13790659259651/1000000000000 : ℝ)*(major_s1_1) + (13790659259651/1000000000000 : ℝ)*(major_s1_2) + (385927007/500000000000 : ℝ)*(sp_s1_1) + (168486577/500000000000 : ℝ)*(sp_s1_6) + (112646391/1000000000000 : ℝ)*(sp_s1_8) + (9900640036853/500000000000 : ℝ)*(sp_s1_13) + (9900197786651/500000000000 : ℝ)*(sp_s1_14) + (1237577159789/62500000000 : ℝ)*(sp_s1_15) + (7779699504757/1000000000000 : ℝ)*(sp_s1_18) + (22758541/500000000000 : ℝ)*(sp_s1_21) + (7780036477911/1000000000000 : ℝ)*(f.failure) + (9900640036853/500000000000 : ℝ)*(f.sum) + (43658620880530421/78136398200000000000000000000 : ℝ)*base63 + (127994474109151/403725000000000000000000000 : ℝ)*base64 + (2964351458629547/7257700000000000000000000000 : ℝ)*base66 + (71519796060841/538300000000000000000000000 : ℝ)*base69 + (1218898635660251747/11719490790000000000000000000000 : ℝ)*base71 + (221408301183541/290284000000000000000000000 : ℝ)*base72 + (157165183482869/7257700000000000000000000000 : ℝ)*base74 + (21079968912583/907137500000000000000000000 : ℝ)*base76 + (37315317476144235063/131674636675000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (29873/100000000000000000 : ℝ)*base86 + (29873/100000000000000000 : ℝ)*base88 + (29873/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(797/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(797/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (699290438944151303564143407/263349273350000000000000000000000 : ℝ) := by norm_num
    linear_combination (227811/500000000000 : ℝ)*(base5) + (313413/200000000000 : ℝ)*(base40) + (138583365531/500000000000 : ℝ)*(base49) + (616972147913/1000000000000 : ℝ)*(base59) + (3243368632603/1000000000000 : ℝ)*(major_s1_0) + (3243368632603/1000000000000 : ℝ)*(major_s1_1) + (3243368632603/1000000000000 : ℝ)*(major_s1_2) + (128610707/1000000000000 : ℝ)*(sp_s1_1) + (31324469/500000000000 : ℝ)*(sp_s1_12) + (4961389/1000000000000 : ℝ)*(sp_s1_18) + (1164245371499/250000000000 : ℝ)*(sp_s1_19) + (4656852875289/1000000000000 : ℝ)*(sp_s1_20) + (4656981941619/1000000000000 : ℝ)*(sp_s1_21) + (1829686828133/1000000000000 : ℝ)*(sp_s1_25) + (914877447041/500000000000 : ℝ)*(f.failure) + (1164245371499/250000000000 : ℝ)*(f.sum) + (9525332547635803/24417624437500000000000000000 : ℝ)*base62 + (12498795625807/403725000000000000000000000 : ℝ)*base65 + (2400479094642699/7257700000000000000000000000 : ℝ)*base67 + (121269991712683/538300000000000000000000000 : ℝ)*base69 + (455597544709745579/732468174375000000000000000000 : ℝ)*base70 + (911294952495889/1451420000000000000000000000 : ℝ)*base73 + (211994340635997/7257700000000000000000000000 : ℝ)*base74 + (209448941146371/3628550000000000000000000000 : ℝ)*base76 + (4841443694992366071/32918659168750000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (3463/50000000000000000 : ℝ)*base86 + (3463/50000000000000000 : ℝ)*base88 + (3463/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((72571/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72571/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72577/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(72577/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16149/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16149/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((848/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(848/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(848/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(848/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(797/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(797/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c316049_s1 p hpa hpb X hX hprev0

#print axioms solution

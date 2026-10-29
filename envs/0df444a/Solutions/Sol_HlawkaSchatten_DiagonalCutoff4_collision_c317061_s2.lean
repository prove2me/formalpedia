-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c317061_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:15:39.400272+00:00
-- url     : https://prove2.me/submissions/dd848fd8-10ba-4543-b58e-058d81738574

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
theorem collision_support_c317061_s2_s2_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050781293/5000000000 : ℝ)*x 0 + (4451698813/10000000000 : ℝ)*x 1 + (14369189/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050781293/5000000000 : ℝ)^39 ≤ (14051236444093/100000000000000 : ℝ)^31 := by
    have hnat : (1050781293 : ℕ)^39*100000000000000^31 ≤ 14051236444093^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050781293 5000000000 14051236444093 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4451698813/10000000000 : ℝ)^39 ≤ (9031559684753/25000000000000 : ℝ)^31 := by
    have hnat : (4451698813 : ℕ)^39*25000000000000^31 ≤ 9031559684753^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4451698813 10000000000 9031559684753 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14369189/25000000 : ℝ)^39 ≤ (49822524794539/100000000000000 : ℝ)^31 := by
    have hnat : (14369189 : ℕ)^39*100000000000000^31 ≤ 49822524794539^31*25000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14369189 25000000 49822524794539 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050781293/5000000000 : ℝ), (4451698813/10000000000 : ℝ), (14369189/25000000 : ℝ)] ![(14051236444093/100000000000000 : ℝ), (9031559684753/25000000000000 : ℝ), (49822524794539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050781293/5000000000 : ℝ)|^39 ≤ (14051236444093/100000000000000 : ℝ)^31
        have hw : |(-1050781293/5000000000 : ℝ)|=(1050781293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4451698813/10000000000 : ℝ)|^39 ≤ (9031559684753/25000000000000 : ℝ)^31
        have hw : |(4451698813/10000000000 : ℝ)|=(4451698813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(14369189/25000000 : ℝ)|^39 ≤ (49822524794539/100000000000000 : ℝ)^31
        have hw : |(14369189/25000000 : ℝ)|=(14369189/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s2_s2_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (930788431/2000000000 : ℝ)*x 0 + (-536264933/2500000000 : ℝ)*x 1 + (276122513/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (930788431/2000000000 : ℝ)^39 ≤ (38202990742759/100000000000000 : ℝ)^31 := by
    have hnat : (930788431 : ℕ)^39*100000000000000^31 ≤ 38202990742759^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930788431 2000000000 38202990742759 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (536264933/2500000000 : ℝ)^39 ≤ (7209043137267/50000000000000 : ℝ)^31 := by
    have hnat : (536264933 : ℕ)^39*50000000000000^31 ≤ 7209043137267^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536264933 2500000000 7209043137267 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276122513/500000000 : ℝ)^39 ≤ (947578459401/2000000000000 : ℝ)^31 := by
    have hnat : (276122513 : ℕ)^39*2000000000000^31 ≤ 947578459401^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276122513 500000000 947578459401 2000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(930788431/2000000000 : ℝ), (-536264933/2500000000 : ℝ), (276122513/500000000 : ℝ)] ![(38202990742759/100000000000000 : ℝ), (7209043137267/50000000000000 : ℝ), (947578459401/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(930788431/2000000000 : ℝ)|^39 ≤ (38202990742759/100000000000000 : ℝ)^31
        have hw : |(930788431/2000000000 : ℝ)|=(930788431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-536264933/2500000000 : ℝ)|^39 ≤ (7209043137267/50000000000000 : ℝ)^31
        have hw : |(-536264933/2500000000 : ℝ)|=(536264933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276122513/500000000 : ℝ)|^39 ≤ (947578459401/2000000000000 : ℝ)^31
        have hw : |(276122513/500000000 : ℝ)|=(276122513/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s2_s2_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4699214021/10000000000 : ℝ)*x 0 + (6136243831/10000000000 : ℝ)*x 1 + (-247921231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4699214021/10000000000 : ℝ)^39 ≤ (2416944014913/6250000000000 : ℝ)^31 := by
    have hnat : (4699214021 : ℕ)^39*6250000000000^31 ≤ 2416944014913^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4699214021 10000000000 2416944014913 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6136243831/10000000000 : ℝ)^39 ≤ (5409632938453/10000000000000 : ℝ)^31 := by
    have hnat : (6136243831 : ℕ)^39*10000000000000^31 ≤ 5409632938453^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6136243831 10000000000 5409632938453 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (247921231/2000000000 : ℝ)^39 ≤ (7232566357779/100000000000000 : ℝ)^31 := by
    have hnat : (247921231 : ℕ)^39*100000000000000^31 ≤ 7232566357779^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247921231 2000000000 7232566357779 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4699214021/10000000000 : ℝ), (6136243831/10000000000 : ℝ), (-247921231/2000000000 : ℝ)] ![(2416944014913/6250000000000 : ℝ), (5409632938453/10000000000000 : ℝ), (7232566357779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4699214021/10000000000 : ℝ)|^39 ≤ (2416944014913/6250000000000 : ℝ)^31
        have hw : |(4699214021/10000000000 : ℝ)|=(4699214021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6136243831/10000000000 : ℝ)|^39 ≤ (5409632938453/10000000000000 : ℝ)^31
        have hw : |(6136243831/10000000000 : ℝ)|=(6136243831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-247921231/2000000000 : ℝ)|^39 ≤ (7232566357779/100000000000000 : ℝ)^31
        have hw : |(-247921231/2000000000 : ℝ)|=(247921231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s2_s2_6 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3069028937/5000000000 : ℝ)*x 0 + (2808709293/10000000000 : ℝ)*x 1 + (339022719/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3069028937/5000000000 : ℝ)^39 ≤ (845569524723/1562500000000 : ℝ)^31 := by
    have hnat : (3069028937 : ℕ)^39*1562500000000^31 ≤ 845569524723^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3069028937 5000000000 845569524723 1562500000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2808709293/10000000000 : ℝ)^39 ≤ (2529857015779/12500000000000 : ℝ)^31 := by
    have hnat : (2808709293 : ℕ)^39*12500000000000^31 ≤ 2529857015779^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2808709293 10000000000 2529857015779 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339022719/1000000000 : ℝ)^39 ≤ (25644694271873/100000000000000 : ℝ)^31 := by
    have hnat : (339022719 : ℕ)^39*100000000000000^31 ≤ 25644694271873^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339022719 1000000000 25644694271873 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3069028937/5000000000 : ℝ), (2808709293/10000000000 : ℝ), (339022719/1000000000 : ℝ)] ![(845569524723/1562500000000 : ℝ), (2529857015779/12500000000000 : ℝ), (25644694271873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3069028937/5000000000 : ℝ)|^39 ≤ (845569524723/1562500000000 : ℝ)^31
        have hw : |(3069028937/5000000000 : ℝ)|=(3069028937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2808709293/10000000000 : ℝ)|^39 ≤ (2529857015779/12500000000000 : ℝ)^31
        have hw : |(2808709293/10000000000 : ℝ)|=(2808709293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339022719/1000000000 : ℝ)|^39 ≤ (25644694271873/100000000000000 : ℝ)^31
        have hw : |(339022719/1000000000 : ℝ)|=(339022719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s2_s2_7 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2126817937/10000000000 : ℝ)*x 0 + (205526081/500000000 : ℝ)*x 1 + (1510606233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126817937/10000000000 : ℝ)^39 ≤ (570560043463/4000000000000 : ℝ)^31 := by
    have hnat : (2126817937 : ℕ)^39*4000000000000^31 ≤ 570560043463^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126817937 10000000000 570560043463 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205526081/500000000 : ℝ)^39 ≤ (1307125923737/4000000000000 : ℝ)^31 := by
    have hnat : (205526081 : ℕ)^39*4000000000000^31 ≤ 1307125923737^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205526081 500000000 1307125923737 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1510606233/2500000000 : ℝ)^39 ≤ (53057850815753/100000000000000 : ℝ)^31 := by
    have hnat : (1510606233 : ℕ)^39*100000000000000^31 ≤ 53057850815753^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510606233 2500000000 53057850815753 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2126817937/10000000000 : ℝ), (205526081/500000000 : ℝ), (1510606233/2500000000 : ℝ)] ![(570560043463/4000000000000 : ℝ), (1307125923737/4000000000000 : ℝ), (53057850815753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2126817937/10000000000 : ℝ)|^39 ≤ (570560043463/4000000000000 : ℝ)^31
        have hw : |(-2126817937/10000000000 : ℝ)|=(2126817937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205526081/500000000 : ℝ)|^39 ≤ (1307125923737/4000000000000 : ℝ)^31
        have hw : |(205526081/500000000 : ℝ)|=(205526081/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1510606233/2500000000 : ℝ)|^39 ≤ (53057850815753/100000000000000 : ℝ)^31
        have hw : |(1510606233/2500000000 : ℝ)|=(1510606233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s2_s2_8 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4432525111/10000000000 : ℝ)*x 0 + (-1775232643/10000000000 : ℝ)*x 1 + (3005268911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4432525111/10000000000 : ℝ)^39 ≤ (8982648950163/25000000000000 : ℝ)^31 := by
    have hnat : (4432525111 : ℕ)^39*25000000000000^31 ≤ 8982648950163^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4432525111 10000000000 8982648950163 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1775232643/10000000000 : ℝ)^39 ≤ (2840891907231/25000000000000 : ℝ)^31 := by
    have hnat : (1775232643 : ℕ)^39*25000000000000^31 ≤ 2840891907231^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775232643 10000000000 2840891907231 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3005268911/5000000000 : ℝ)^39 ≤ (6588229569977/12500000000000 : ℝ)^31 := by
    have hnat : (3005268911 : ℕ)^39*12500000000000^31 ≤ 6588229569977^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3005268911 5000000000 6588229569977 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4432525111/10000000000 : ℝ), (-1775232643/10000000000 : ℝ), (3005268911/5000000000 : ℝ)] ![(8982648950163/25000000000000 : ℝ), (2840891907231/25000000000000 : ℝ), (6588229569977/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4432525111/10000000000 : ℝ)|^39 ≤ (8982648950163/25000000000000 : ℝ)^31
        have hw : |(4432525111/10000000000 : ℝ)|=(4432525111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1775232643/10000000000 : ℝ)|^39 ≤ (2840891907231/25000000000000 : ℝ)^31
        have hw : |(-1775232643/10000000000 : ℝ)|=(1775232643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3005268911/5000000000 : ℝ)|^39 ≤ (6588229569977/12500000000000 : ℝ)^31
        have hw : |(3005268911/5000000000 : ℝ)|=(3005268911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s2_s2_9 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (895585057/2000000000 : ℝ)*x 0 + (828759309/1250000000 : ℝ)*x 1 + (-385270489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (895585057/2000000000 : ℝ)^39 ≤ (36394198322533/100000000000000 : ℝ)^31 := by
    have hnat : (895585057 : ℕ)^39*100000000000000^31 ≤ 36394198322533^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895585057 2000000000 36394198322533 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (828759309/1250000000 : ℝ)^39 ≤ (59629153016723/100000000000000 : ℝ)^31 := by
    have hnat : (828759309 : ℕ)^39*100000000000000^31 ≤ 59629153016723^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828759309 1250000000 59629153016723 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385270489/5000000000 : ℝ)^39 ≤ (3976648647353/100000000000000 : ℝ)^31 := by
    have hnat : (385270489 : ℕ)^39*100000000000000^31 ≤ 3976648647353^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385270489 5000000000 3976648647353 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(895585057/2000000000 : ℝ), (828759309/1250000000 : ℝ), (-385270489/5000000000 : ℝ)] ![(36394198322533/100000000000000 : ℝ), (59629153016723/100000000000000 : ℝ), (3976648647353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(895585057/2000000000 : ℝ)|^39 ≤ (36394198322533/100000000000000 : ℝ)^31
        have hw : |(895585057/2000000000 : ℝ)|=(895585057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(828759309/1250000000 : ℝ)|^39 ≤ (59629153016723/100000000000000 : ℝ)^31
        have hw : |(828759309/1250000000 : ℝ)|=(828759309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-385270489/5000000000 : ℝ)|^39 ≤ (3976648647353/100000000000000 : ℝ)^31
        have hw : |(-385270489/5000000000 : ℝ)|=(385270489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s2_s2_13 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (773537281/1250000000 : ℝ)*x 0 + (1732893403/5000000000 : ℝ)*x 1 + (2666688563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (773537281/1250000000 : ℝ)^39 ≤ (27337146043507/50000000000000 : ℝ)^31 := by
    have hnat : (773537281 : ℕ)^39*50000000000000^31 ≤ 27337146043507^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773537281 1250000000 27337146043507 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1732893403/5000000000 : ℝ)^39 ≤ (26365804628911/100000000000000 : ℝ)^31 := by
    have hnat : (1732893403 : ℕ)^39*100000000000000^31 ≤ 26365804628911^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732893403 5000000000 26365804628911 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2666688563/10000000000 : ℝ)^39 ≤ (18959903265867/100000000000000 : ℝ)^31 := by
    have hnat : (2666688563 : ℕ)^39*100000000000000^31 ≤ 18959903265867^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2666688563 10000000000 18959903265867 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(773537281/1250000000 : ℝ), (1732893403/5000000000 : ℝ), (2666688563/10000000000 : ℝ)] ![(27337146043507/50000000000000 : ℝ), (26365804628911/100000000000000 : ℝ), (18959903265867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(773537281/1250000000 : ℝ)|^39 ≤ (27337146043507/50000000000000 : ℝ)^31
        have hw : |(773537281/1250000000 : ℝ)|=(773537281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1732893403/5000000000 : ℝ)|^39 ≤ (26365804628911/100000000000000 : ℝ)^31
        have hw : |(1732893403/5000000000 : ℝ)|=(1732893403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2666688563/10000000000 : ℝ)|^39 ≤ (18959903265867/100000000000000 : ℝ)^31
        have hw : |(2666688563/10000000000 : ℝ)|=(2666688563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s2_s2_14 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-734612703/5000000000 : ℝ)*x 0 + (4631681781/10000000000 : ℝ)*x 1 + (3021768951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (734612703/5000000000 : ℝ)^39 ≤ (895660678653/10000000000000 : ℝ)^31 := by
    have hnat : (734612703 : ℕ)^39*10000000000000^31 ≤ 895660678653^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734612703 5000000000 895660678653 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4631681781/10000000000 : ℝ)^39 ≤ (1898662359973/5000000000000 : ℝ)^31 := by
    have hnat : (4631681781 : ℕ)^39*5000000000000^31 ≤ 1898662359973^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4631681781 10000000000 1898662359973 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3021768951/5000000000 : ℝ)^39 ≤ (13267536500297/25000000000000 : ℝ)^31 := by
    have hnat : (3021768951 : ℕ)^39*25000000000000^31 ≤ 13267536500297^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021768951 5000000000 13267536500297 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-734612703/5000000000 : ℝ), (4631681781/10000000000 : ℝ), (3021768951/5000000000 : ℝ)] ![(895660678653/10000000000000 : ℝ), (1898662359973/5000000000000 : ℝ), (13267536500297/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-734612703/5000000000 : ℝ)|^39 ≤ (895660678653/10000000000000 : ℝ)^31
        have hw : |(-734612703/5000000000 : ℝ)|=(734612703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4631681781/10000000000 : ℝ)|^39 ≤ (1898662359973/5000000000000 : ℝ)^31
        have hw : |(4631681781/10000000000 : ℝ)|=(4631681781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3021768951/5000000000 : ℝ)|^39 ≤ (13267536500297/25000000000000 : ℝ)^31
        have hw : |(3021768951/5000000000 : ℝ)|=(3021768951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s2_s2_15 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4334474497/10000000000 : ℝ)*x 0 + (-474116809/2500000000 : ℝ)*x 1 + (6011650779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334474497/10000000000 : ℝ)^39 ≤ (34933542892177/100000000000000 : ℝ)^31 := by
    have hnat : (4334474497 : ℕ)^39*100000000000000^31 ≤ 34933542892177^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334474497 10000000000 34933542892177 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474116809/2500000000 : ℝ)^39 ≤ (98786738157/800000000000 : ℝ)^31 := by
    have hnat : (474116809 : ℕ)^39*800000000000^31 ≤ 98786738157^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474116809 2500000000 98786738157 800000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6011650779/10000000000 : ℝ)^39 ≤ (52718114826187/100000000000000 : ℝ)^31 := by
    have hnat : (6011650779 : ℕ)^39*100000000000000^31 ≤ 52718114826187^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6011650779 10000000000 52718114826187 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334474497/10000000000 : ℝ), (-474116809/2500000000 : ℝ), (6011650779/10000000000 : ℝ)] ![(34933542892177/100000000000000 : ℝ), (98786738157/800000000000 : ℝ), (52718114826187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334474497/10000000000 : ℝ)|^39 ≤ (34933542892177/100000000000000 : ℝ)^31
        have hw : |(4334474497/10000000000 : ℝ)|=(4334474497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-474116809/2500000000 : ℝ)|^39 ≤ (98786738157/800000000000 : ℝ)^31
        have hw : |(-474116809/2500000000 : ℝ)|=(474116809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6011650779/10000000000 : ℝ)|^39 ≤ (52718114826187/100000000000000 : ℝ)^31
        have hw : |(6011650779/10000000000 : ℝ)|=(6011650779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s2_s2_16 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1337670419/2500000000 : ℝ)*x 0 + (5809540849/10000000000 : ℝ)*x 1 + (-769427477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337670419/2500000000 : ℝ)^39 ≤ (22766231542621/50000000000000 : ℝ)^31 := by
    have hnat : (1337670419 : ℕ)^39*50000000000000^31 ≤ 22766231542621^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337670419 2500000000 22766231542621 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5809540849/10000000000 : ℝ)^39 ≤ (2524905825391/5000000000000 : ℝ)^31 := by
    have hnat : (5809540849 : ℕ)^39*5000000000000^31 ≤ 2524905825391^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5809540849 10000000000 2524905825391 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (769427477/10000000000 : ℝ)^39 ≤ (396942038363/10000000000000 : ℝ)^31 := by
    have hnat : (769427477 : ℕ)^39*10000000000000^31 ≤ 396942038363^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769427477 10000000000 396942038363 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337670419/2500000000 : ℝ), (5809540849/10000000000 : ℝ), (-769427477/10000000000 : ℝ)] ![(22766231542621/50000000000000 : ℝ), (2524905825391/5000000000000 : ℝ), (396942038363/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337670419/2500000000 : ℝ)|^39 ≤ (22766231542621/50000000000000 : ℝ)^31
        have hw : |(1337670419/2500000000 : ℝ)|=(1337670419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5809540849/10000000000 : ℝ)|^39 ≤ (2524905825391/5000000000000 : ℝ)^31
        have hw : |(5809540849/10000000000 : ℝ)|=(5809540849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-769427477/10000000000 : ℝ)|^39 ≤ (396942038363/10000000000000 : ℝ)^31
        have hw : |(-769427477/10000000000 : ℝ)|=(769427477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s2_s2_20 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (875224223/1250000000 : ℝ)*x 0 + (1234046561/5000000000 : ℝ)*x 1 + (2663794589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875224223/1250000000 : ℝ)^39 ≤ (31932530609719/50000000000000 : ℝ)^31 := by
    have hnat : (875224223 : ℕ)^39*50000000000000^31 ≤ 31932530609719^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875224223 1250000000 31932530609719 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1234046561/5000000000 : ℝ)^39 ≤ (4300229416291/25000000000000 : ℝ)^31 := by
    have hnat : (1234046561 : ℕ)^39*25000000000000^31 ≤ 4300229416291^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1234046561 5000000000 4300229416291 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2663794589/10000000000 : ℝ)^39 ≤ (9467010552793/50000000000000 : ℝ)^31 := by
    have hnat : (2663794589 : ℕ)^39*50000000000000^31 ≤ 9467010552793^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663794589 10000000000 9467010552793 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875224223/1250000000 : ℝ), (1234046561/5000000000 : ℝ), (2663794589/10000000000 : ℝ)] ![(31932530609719/50000000000000 : ℝ), (4300229416291/25000000000000 : ℝ), (9467010552793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875224223/1250000000 : ℝ)|^39 ≤ (31932530609719/50000000000000 : ℝ)^31
        have hw : |(875224223/1250000000 : ℝ)|=(875224223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1234046561/5000000000 : ℝ)|^39 ≤ (4300229416291/25000000000000 : ℝ)^31
        have hw : |(1234046561/5000000000 : ℝ)|=(1234046561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2663794589/10000000000 : ℝ)|^39 ≤ (9467010552793/50000000000000 : ℝ)^31
        have hw : |(2663794589/10000000000 : ℝ)|=(2663794589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s2_s2_21 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1476820721/10000000000 : ℝ)*x 0 + (977468089/2000000000 : ℝ)*x 1 + (231863007/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1476820721/10000000000 : ℝ)^39 ≤ (9014896646267/100000000000000 : ℝ)^31 := by
    have hnat : (1476820721 : ℕ)^39*100000000000000^31 ≤ 9014896646267^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1476820721 10000000000 9014896646267 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977468089/2000000000 : ℝ)^39 ≤ (2539295708827/6250000000000 : ℝ)^31 := by
    have hnat : (977468089 : ℕ)^39*6250000000000^31 ≤ 2539295708827^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977468089 2000000000 2539295708827 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (231863007/400000000 : ℝ)^39 ≤ (50356372003647/100000000000000 : ℝ)^31 := by
    have hnat : (231863007 : ℕ)^39*100000000000000^31 ≤ 50356372003647^31*400000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231863007 400000000 50356372003647 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1476820721/10000000000 : ℝ), (977468089/2000000000 : ℝ), (231863007/400000000 : ℝ)] ![(9014896646267/100000000000000 : ℝ), (2539295708827/6250000000000 : ℝ), (50356372003647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1476820721/10000000000 : ℝ)|^39 ≤ (9014896646267/100000000000000 : ℝ)^31
        have hw : |(-1476820721/10000000000 : ℝ)|=(1476820721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(977468089/2000000000 : ℝ)|^39 ≤ (2539295708827/6250000000000 : ℝ)^31
        have hw : |(977468089/2000000000 : ℝ)|=(977468089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(231863007/400000000 : ℝ)|^39 ≤ (50356372003647/100000000000000 : ℝ)^31
        have hw : |(231863007/400000000 : ℝ)|=(231863007/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s2_s2_22 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5297687189/10000000000 : ℝ)*x 0 + (-1521344619/10000000000 : ℝ)*x 1 + (335255377/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5297687189/10000000000 : ℝ)^39 ≤ (8993169400107/20000000000000 : ℝ)^31 := by
    have hnat : (5297687189 : ℕ)^39*20000000000000^31 ≤ 8993169400107^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5297687189 10000000000 8993169400107 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1521344619/10000000000 : ℝ)^39 ≤ (9358140574707/100000000000000 : ℝ)^31 := by
    have hnat : (1521344619 : ℕ)^39*100000000000000^31 ≤ 9358140574707^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521344619 10000000000 9358140574707 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (335255377/625000000 : ℝ)^39 ≤ (5709501551969/12500000000000 : ℝ)^31 := by
    have hnat : (335255377 : ℕ)^39*12500000000000^31 ≤ 5709501551969^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335255377 625000000 5709501551969 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5297687189/10000000000 : ℝ), (-1521344619/10000000000 : ℝ), (335255377/625000000 : ℝ)] ![(8993169400107/20000000000000 : ℝ), (9358140574707/100000000000000 : ℝ), (5709501551969/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5297687189/10000000000 : ℝ)|^39 ≤ (8993169400107/20000000000000 : ℝ)^31
        have hw : |(5297687189/10000000000 : ℝ)|=(5297687189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1521344619/10000000000 : ℝ)|^39 ≤ (9358140574707/100000000000000 : ℝ)^31
        have hw : |(-1521344619/10000000000 : ℝ)|=(1521344619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(335255377/625000000 : ℝ)|^39 ≤ (5709501551969/12500000000000 : ℝ)^31
        have hw : |(335255377/625000000 : ℝ)|=(335255377/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s2_s2_23 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (431125077/1000000000 : ℝ)*x 0 + (6554252539/10000000000 : ℝ)*x 1 + (-228558883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431125077/1000000000 : ℝ)^39 ≤ (6939646591583/20000000000000 : ℝ)^31 := by
    have hnat : (431125077 : ℕ)^39*20000000000000^31 ≤ 6939646591583^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431125077 1000000000 6939646591583 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6554252539/10000000000 : ℝ)^39 ≤ (58772519923857/100000000000000 : ℝ)^31 := by
    have hnat : (6554252539 : ℕ)^39*100000000000000^31 ≤ 58772519923857^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6554252539 10000000000 58772519923857 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228558883/2000000000 : ℝ)^39 ≤ (408077944089/6250000000000 : ℝ)^31 := by
    have hnat : (228558883 : ℕ)^39*6250000000000^31 ≤ 408077944089^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228558883 2000000000 408077944089 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431125077/1000000000 : ℝ), (6554252539/10000000000 : ℝ), (-228558883/2000000000 : ℝ)] ![(6939646591583/20000000000000 : ℝ), (58772519923857/100000000000000 : ℝ), (408077944089/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431125077/1000000000 : ℝ)|^39 ≤ (6939646591583/20000000000000 : ℝ)^31
        have hw : |(431125077/1000000000 : ℝ)|=(431125077/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6554252539/10000000000 : ℝ)|^39 ≤ (58772519923857/100000000000000 : ℝ)^31
        have hw : |(6554252539/10000000000 : ℝ)|=(6554252539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-228558883/2000000000 : ℝ)|^39 ≤ (408077944089/6250000000000 : ℝ)^31
        have hw : |(-228558883/2000000000 : ℝ)|=(228558883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s2_s2_27 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3590012137/5000000000 : ℝ)*x 0 + (2304539833/10000000000 : ℝ)*x 1 + (162066203/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3590012137/5000000000 : ℝ)^39 ≤ (32958475874217/50000000000000 : ℝ)^31 := by
    have hnat : (3590012137 : ℕ)^39*50000000000000^31 ≤ 32958475874217^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3590012137 5000000000 32958475874217 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2304539833/10000000000 : ℝ)^39 ≤ (15779375968959/100000000000000 : ℝ)^31 := by
    have hnat : (2304539833 : ℕ)^39*100000000000000^31 ≤ 15779375968959^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2304539833 10000000000 15779375968959 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162066203/625000000 : ℝ)^39 ≤ (4575918065599/25000000000000 : ℝ)^31 := by
    have hnat : (162066203 : ℕ)^39*25000000000000^31 ≤ 4575918065599^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162066203 625000000 4575918065599 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3590012137/5000000000 : ℝ), (2304539833/10000000000 : ℝ), (162066203/625000000 : ℝ)] ![(32958475874217/50000000000000 : ℝ), (15779375968959/100000000000000 : ℝ), (4575918065599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3590012137/5000000000 : ℝ)|^39 ≤ (32958475874217/50000000000000 : ℝ)^31
        have hw : |(3590012137/5000000000 : ℝ)|=(3590012137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2304539833/10000000000 : ℝ)|^39 ≤ (15779375968959/100000000000000 : ℝ)^31
        have hw : |(2304539833/10000000000 : ℝ)|=(2304539833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(162066203/625000000 : ℝ)|^39 ≤ (4575918065599/25000000000000 : ℝ)^31
        have hw : |(162066203/625000000 : ℝ)|=(162066203/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317061_s2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((10373/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10373/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27829/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27829/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12637/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12637/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((23299/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23299/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(181/625 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(181/625 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13287/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13287/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s2_pow0 : (10373/20000 : ℝ) ^ (77/16 : ℝ) ≤ (4244562809420203649/100000000000000000000 : ℝ) := by
    have hpowers : (10373/20000 : ℝ)^77 ≤ (4244562809420203649/100000000000000000000 : ℝ)^16 := by
      have hnat : (10373 : ℕ)^77*100000000000000000000^16 ≤ 4244562809420203649^16*20000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10373 20000 4244562809420203649 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10373/20000 : ℝ)) (X := (4244562809420203649/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (104244562809420203649/100000000000000000000 : ℝ) ≤ (10086752355576781/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (104244562809420203649/100000000000000000000 : ℝ)^16 ≤ (10086752355576781/10000000000000000 : ℝ)^77 := by
      have hnat : (104244562809420203649 : ℕ)^16*10000000000000000^77 ≤ 10086752355576781^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104244562809420203649 100000000000000000000 10086752355576781 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10086752355576781/10000000000000000 : ℝ)) (X := (104244562809420203649/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (54244562809420203649/50000000000000000000 : ℝ) ≤ (5085374989784109/5000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (54244562809420203649/50000000000000000000 : ℝ)^16 ≤ (5085374989784109/5000000000000000 : ℝ)^77 := by
      have hnat : (54244562809420203649 : ℕ)^16*5000000000000000^77 ≤ 5085374989784109^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54244562809420203649 50000000000000000000 5085374989784109 5000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5085374989784109/5000000000000000 : ℝ)) (X := (54244562809420203649/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(86752355576781/5186500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(83997623991437/5186500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (10373/20000 : ℝ)) (alpha := (86752355576781/5186500000000000 : ℝ)) (beta := (83997623991437/5186500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (10373/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(86752355576781/5186500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(83997623991437/5186500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (27829/50000 : ℝ) ^ (77/16 : ℝ) ≤ (2980722612603390287/50000000000000000000 : ℝ) := by
    have hpowers : (27829/50000 : ℝ)^77 ≤ (2980722612603390287/50000000000000000000 : ℝ)^16 := by
      have hnat : (27829 : ℕ)^77*50000000000000000000^16 ≤ 2980722612603390287^16*50000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27829 50000 2980722612603390287 50000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27829/50000 : ℝ)) (X := (2980722612603390287/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (52980722612603390287/50000000000000000000 : ℝ) ≤ (10121049107518273/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (52980722612603390287/50000000000000000000 : ℝ)^16 ≤ (10121049107518273/10000000000000000 : ℝ)^77 := by
      have hnat : (52980722612603390287 : ℕ)^16*10000000000000000^77 ≤ 10121049107518273^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52980722612603390287 50000000000000000000 10121049107518273 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10121049107518273/10000000000000000 : ℝ)) (X := (52980722612603390287/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (27980722612603390287/25000000000000000000 : ℝ) ≤ (2047363542526901/2000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (27980722612603390287/25000000000000000000 : ℝ)^16 ≤ (2047363542526901/2000000000000000 : ℝ)^77 := by
      have hnat : (27980722612603390287 : ℕ)^16*2000000000000000^77 ≤ 2047363542526901^77*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27980722612603390287 25000000000000000000 2047363542526901 2000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2047363542526901/2000000000000000 : ℝ)) (X := (27980722612603390287/25000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(7120535736369/327400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(14471075639529/695725000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (27829/50000 : ℝ)) (alpha := (7120535736369/327400000000000 : ℝ)) (beta := (14471075639529/695725000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (27829/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(7120535736369/327400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(14471075639529/695725000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (12637/25000 : ℝ) ^ (77/16 : ℝ) ≤ (3750380988188560479/100000000000000000000 : ℝ) := by
    have hpowers : (12637/25000 : ℝ)^77 ≤ (3750380988188560479/100000000000000000000 : ℝ)^16 := by
      have hnat : (12637 : ℕ)^77*100000000000000000000^16 ≤ 3750380988188560479^16*25000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12637 25000 3750380988188560479 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12637/25000 : ℝ)) (X := (3750380988188560479/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (103750380988188560479/100000000000000000000 : ℝ) ≤ (10076797590337763/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (103750380988188560479/100000000000000000000 : ℝ)^16 ≤ (10076797590337763/10000000000000000 : ℝ)^77 := by
      have hnat : (103750380988188560479 : ℕ)^16*10000000000000000^77 ≤ 10076797590337763^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103750380988188560479 100000000000000000000 10076797590337763 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10076797590337763/10000000000000000 : ℝ)) (X := (103750380988188560479/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (53750380988188560479/50000000000000000000 : ℝ) ≤ (2030285296559967/2000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (53750380988188560479/50000000000000000000 : ℝ)^16 ≤ (2030285296559967/2000000000000000 : ℝ)^77 := by
      have hnat : (53750380988188560479 : ℕ)^16*2000000000000000^77 ≤ 2030285296559967^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53750380988188560479 50000000000000000000 2030285296559967 2000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2030285296559967/2000000000000000 : ℝ)) (X := (53750380988188560479/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(76797590337763/5054800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(9328611557759/631850000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (12637/25000 : ℝ)) (alpha := (76797590337763/5054800000000000 : ℝ)) (beta := (9328611557759/631850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (12637/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(76797590337763/5054800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(9328611557759/631850000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1050781293/5000000000 : ℝ)*X 0 0+(4451698813/10000000000 : ℝ)*X 0 1+(14369189/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((930788431/2000000000 : ℝ)*X 1 0+(-536264933/2500000000 : ℝ)*X 1 1+(276122513/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((4699214021/10000000000 : ℝ)*X 2 0+(6136243831/10000000000 : ℝ)*X 2 1+(-247921231/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((3069028937/5000000000 : ℝ)*X 0 0+(2808709293/10000000000 : ℝ)*X 0 1+(339022719/1000000000 : ℝ)*X 0 2+(3069028937/5000000000 : ℝ)*X 1 0+(2808709293/10000000000 : ℝ)*X 1 1+(339022719/1000000000 : ℝ)*X 1 2+(3069028937/5000000000 : ℝ)*X 2 0+(2808709293/10000000000 : ℝ)*X 2 1+(339022719/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-2126817937/10000000000 : ℝ)*X 0 0+(205526081/500000000 : ℝ)*X 0 1+(1510606233/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((4432525111/10000000000 : ℝ)*X 1 0+(-1775232643/10000000000 : ℝ)*X 1 1+(3005268911/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((895585057/2000000000 : ℝ)*X 2 0+(828759309/1250000000 : ℝ)*X 2 1+(-385270489/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((773537281/1250000000 : ℝ)*X 0 0+(1732893403/5000000000 : ℝ)*X 0 1+(2666688563/10000000000 : ℝ)*X 0 2+(773537281/1250000000 : ℝ)*X 1 0+(1732893403/5000000000 : ℝ)*X 1 1+(2666688563/10000000000 : ℝ)*X 1 2+(773537281/1250000000 : ℝ)*X 2 0+(1732893403/5000000000 : ℝ)*X 2 1+(2666688563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-734612703/5000000000 : ℝ)*X 0 0+(4631681781/10000000000 : ℝ)*X 0 1+(3021768951/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4334474497/10000000000 : ℝ)*X 1 0+(-474116809/2500000000 : ℝ)*X 1 1+(6011650779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1337670419/2500000000 : ℝ)*X 2 0+(5809540849/10000000000 : ℝ)*X 2 1+(-769427477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((875224223/1250000000 : ℝ)*X 0 0+(1234046561/5000000000 : ℝ)*X 0 1+(2663794589/10000000000 : ℝ)*X 0 2+(875224223/1250000000 : ℝ)*X 1 0+(1234046561/5000000000 : ℝ)*X 1 1+(2663794589/10000000000 : ℝ)*X 1 2+(875224223/1250000000 : ℝ)*X 2 0+(1234046561/5000000000 : ℝ)*X 2 1+(2663794589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-1476820721/10000000000 : ℝ)*X 0 0+(977468089/2000000000 : ℝ)*X 0 1+(231863007/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5297687189/10000000000 : ℝ)*X 1 0+(-1521344619/10000000000 : ℝ)*X 1 1+(335255377/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((431125077/1000000000 : ℝ)*X 2 0+(6554252539/10000000000 : ℝ)*X 2 1+(-228558883/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((3590012137/5000000000 : ℝ)*X 0 0+(2304539833/10000000000 : ℝ)*X 0 1+(162066203/625000000 : ℝ)*X 0 2+(3590012137/5000000000 : ℝ)*X 1 0+(2304539833/10000000000 : ℝ)*X 1 1+(162066203/625000000 : ℝ)*X 1 2+(3590012137/5000000000 : ℝ)*X 2 0+(2304539833/10000000000 : ℝ)*X 2 1+(162066203/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((23299/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23299/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (973326341110042175639727352047/53645963709250000000000000000000000 : ℝ) := by norm_num
    linear_combination (684561/500000000000 : ℝ)*(base50) + (373014194181/250000000000 : ℝ)*(base59) + (1874649807677/250000000000 : ℝ)*(major_s2_0) + (1874649807677/250000000000 : ℝ)*(major_s2_1) + (1874649807677/250000000000 : ℝ)*(major_s2_2) + (20542433/125000000000 : ℝ)*(sp_s2_0) + (73204629/1000000000000 : ℝ)*(sp_s2_1) + (39337371/500000000000 : ℝ)*(sp_s2_6) + (676746457143/62500000000 : ℝ)*(sp_s2_7) + (1082745764529/100000000000 : ℝ)*(sp_s2_8) + (5413944141361/500000000000 : ℝ)*(sp_s2_9) + (2084503042539/500000000000 : ℝ)*(sp_s2_13) + (288401917/500000000000 : ℝ)*(sp_s2_15) + (21937103/100000000000 : ℝ)*(sp_s2_23) + (208454237991/50000000000 : ℝ)*(f.failure) + (1353513456719/125000000000 : ℝ)*(f.sum) + (446825452825580269/2068676900000000000000000000000 : ℝ)*base63 + (20255041759291/315925000000000000000000000 : ℝ)*base64 + (188718793020057/695725000000000000000000000 : ℝ)*base67 + (41552919536399/1263700000000000000000000000 : ℝ)*base68 + (3202583720141763821/16385450125000000000000000000000 : ℝ)*base70 + (242776360069401/1296625000000000000000000000 : ℝ)*base72 + (44455882095243/81850000000000000000000000 : ℝ)*base75 + (490835160334687/1296625000000000000000000000 : ℝ)*base77 + (2099497999770786699/36083777125000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1379/2500000000000000 : ℝ)*base86 + (1379/2500000000000000 : ℝ)*base88 + (1379/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(181/625 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(181/625 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (342540205233004170090929640843/26822981854625000000000000000000000 : ℝ) := by norm_num
    linear_combination (176001/250000000000 : ℝ)*(base39) + (340041/500000000000 : ℝ)*(base49) + (247163109491/250000000000 : ℝ)*(base59) + (7133380675507/1000000000000 : ℝ)*(major_s2_0) + (7133380675507/1000000000000 : ℝ)*(major_s2_1) + (7133380675507/1000000000000 : ℝ)*(major_s2_2) + (21200001/500000000000 : ℝ)*(sp_s2_2) + (103105997/1000000000000 : ℝ)*(sp_s2_6) + (17404373/200000000000 : ℝ)*(sp_s2_7) + (643790011579/62500000000 : ℝ)*(sp_s2_14) + (10300727207129/1000000000000 : ℝ)*(sp_s2_15) + (10300684807127/1000000000000 : ℝ)*(sp_s2_16) + (247832641371/62500000000 : ℝ)*(sp_s2_20) + (604519151/1000000000000 : ℝ)*(sp_s2_27) + (991507471771/250000000000 : ℝ)*(f.failure) + (10300727207129/1000000000000 : ℝ)*(f.sum) + (591234157526783661/8274707600000000000000000000000 : ℝ)*base62 + (115190687923887/631850000000000000000000000 : ℝ)*base65 + (1216596938583/20462500000000000000000000 : ℝ)*base66 + (390000925715121/5054800000000000000000000000 : ℝ)*base69 + (944505996772628889/65541800500000000000000000000000 : ℝ)*base71 + (163166322982109/5186500000000000000000000000 : ℝ)*base73 + (25248020826283/327400000000000000000000000 : ℝ)*base75 + (780942070167317/5186500000000000000000000000 : ℝ)*base77 + (2885608200147052427/8490300500000000000000000000000 : ℝ)*base78 + (301/12500000000000000 : ℝ)*base87 + (301/12500000000000000 : ℝ)*base89 + (301/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13287/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13287/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (56667858748670040952403931/18041888562500000000000000000000 : ℝ) := by norm_num
    linear_combination (49421/25000000000 : ℝ)*(base15) + (388243312173/1000000000000 : ℝ)*(base40) + (1015902525309/1000000000000 : ℝ)*(base59) + (6711492316791/1000000000000 : ℝ)*(major_s2_0) + (6711492316791/1000000000000 : ℝ)*(major_s2_1) + (6711492316791/1000000000000 : ℝ)*(major_s2_2) + (87631831/1000000000000 : ℝ)*(sp_s2_0) + (88559787/1000000000000 : ℝ)*(sp_s2_1) + (80349/25000000000 : ℝ)*(sp_s2_2) + (8321913/500000000000 : ℝ)*(sp_s2_9) + (1211428540033/125000000000 : ℝ)*(sp_s2_21) + (2422856353867/250000000000 : ℝ)*(sp_s2_22) + (9691496094309/1000000000000 : ℝ)*(sp_s2_23) + (746293526903/200000000000 : ℝ)*(sp_s2_27) + (746293526903/200000000000 : ℝ)*(f.failure) + (1938303190419/200000000000 : ℝ)*(f.sum) + (116300027001260367/8274707600000000000000000000000 : ℝ)*base63 + (464168936009799/631850000000000000000000000 : ℝ)*base64 + (315607218661261/695725000000000000000000000 : ℝ)*base66 + (2348157396179027/5054800000000000000000000000 : ℝ)*base68 + (40704228360278807/65541800500000000000000000000000 : ℝ)*base71 + (3581545552874733/5186500000000000000000000000 : ℝ)*base72 + (143317200819521/327400000000000000000000000 : ℝ)*base74 + (1012864254839929/5186500000000000000000000000 : ℝ)*base76 + (42202608130632179567/144335108500000000000000000000000 : ℝ)*base78 + (3693/10000000000000000 : ℝ)*base87 + (3693/10000000000000000 : ℝ)*base89 + (3693/10000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((10373/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10373/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27829/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27829/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12637/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12637/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((23299/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23299/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(181/625 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(181/625 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13287/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13287/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c317061_s2 p hpa hpb X hX hprev1

#print axioms solution

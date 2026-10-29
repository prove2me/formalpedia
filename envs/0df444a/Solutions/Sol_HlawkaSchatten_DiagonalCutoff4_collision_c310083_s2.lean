-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310083_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:11.728004+00:00
-- url     : https://prove2.me/submissions/a120f716-1cba-4aed-a670-16bc483266bf

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
theorem collision_support_c310083_s2_s2_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-646359953/2500000000 : ℝ)*x 0 + (1221629689/2500000000 : ℝ)*x 1 + (5189567343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646359953/2500000000 : ℝ)^71 ≤ (109022308817/625000000000 : ℝ)^55 := by
    have hnat : (646359953 : ℕ)^71*625000000000^55 ≤ 109022308817^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646359953 2500000000 109022308817 625000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1221629689/2500000000 : ℝ)^71 ≤ (7935178734507/20000000000000 : ℝ)^55 := by
    have hnat : (1221629689 : ℕ)^71*20000000000000^55 ≤ 7935178734507^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221629689 2500000000 7935178734507 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5189567343/10000000000 : ℝ)^71 ≤ (2680033555919/6250000000000 : ℝ)^55 := by
    have hnat : (5189567343 : ℕ)^71*6250000000000^55 ≤ 2680033555919^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189567343 10000000000 2680033555919 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-646359953/2500000000 : ℝ), (1221629689/2500000000 : ℝ), (5189567343/10000000000 : ℝ)] ![(109022308817/625000000000 : ℝ), (7935178734507/20000000000000 : ℝ), (2680033555919/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-646359953/2500000000 : ℝ)|^71 ≤ (109022308817/625000000000 : ℝ)^55
        have hw : |(-646359953/2500000000 : ℝ)|=(646359953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1221629689/2500000000 : ℝ)|^71 ≤ (7935178734507/20000000000000 : ℝ)^55
        have hw : |(1221629689/2500000000 : ℝ)|=(1221629689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5189567343/10000000000 : ℝ)|^71 ≤ (2680033555919/6250000000000 : ℝ)^55
        have hw : |(5189567343/10000000000 : ℝ)|=(5189567343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s2_s2_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6589225471/10000000000 : ℝ)*x 0 + (-254547539/2000000000 : ℝ)*x 1 + (4399856723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6589225471/10000000000 : ℝ)^71 ≤ (29181098982997/50000000000000 : ℝ)^55 := by
    have hnat : (6589225471 : ℕ)^71*50000000000000^55 ≤ 29181098982997^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6589225471 10000000000 29181098982997 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254547539/2000000000 : ℝ)^71 ≤ (6987137924227/100000000000000 : ℝ)^55 := by
    have hnat : (254547539 : ℕ)^71*100000000000000^55 ≤ 6987137924227^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254547539 2000000000 6987137924227 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4399856723/10000000000 : ℝ)^71 ≤ (8662666024703/25000000000000 : ℝ)^55 := by
    have hnat : (4399856723 : ℕ)^71*25000000000000^55 ≤ 8662666024703^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4399856723 10000000000 8662666024703 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6589225471/10000000000 : ℝ), (-254547539/2000000000 : ℝ), (4399856723/10000000000 : ℝ)] ![(29181098982997/50000000000000 : ℝ), (6987137924227/100000000000000 : ℝ), (8662666024703/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6589225471/10000000000 : ℝ)|^71 ≤ (29181098982997/50000000000000 : ℝ)^55
        have hw : |(6589225471/10000000000 : ℝ)|=(6589225471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-254547539/2000000000 : ℝ)|^71 ≤ (6987137924227/100000000000000 : ℝ)^55
        have hw : |(-254547539/2000000000 : ℝ)|=(254547539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4399856723/10000000000 : ℝ)|^71 ≤ (8662666024703/25000000000000 : ℝ)^55
        have hw : |(4399856723/10000000000 : ℝ)|=(4399856723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s2_s2_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3785163843/10000000000 : ℝ)*x 0 + (1541853371/2500000000 : ℝ)*x 1 + (-2635666249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3785163843/10000000000 : ℝ)^71 ≤ (14266442355447/50000000000000 : ℝ)^55 := by
    have hnat : (3785163843 : ℕ)^71*50000000000000^55 ≤ 14266442355447^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3785163843 10000000000 14266442355447 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1541853371/2500000000 : ℝ)^71 ≤ (837263513283/1562500000000 : ℝ)^55 := by
    have hnat : (1541853371 : ℕ)^71*1562500000000^55 ≤ 837263513283^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1541853371 2500000000 837263513283 1562500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2635666249/10000000000 : ℝ)^71 ≤ (17882250422011/100000000000000 : ℝ)^55 := by
    have hnat : (2635666249 : ℕ)^71*100000000000000^55 ≤ 17882250422011^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635666249 10000000000 17882250422011 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3785163843/10000000000 : ℝ), (1541853371/2500000000 : ℝ), (-2635666249/10000000000 : ℝ)] ![(14266442355447/50000000000000 : ℝ), (837263513283/1562500000000 : ℝ), (17882250422011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3785163843/10000000000 : ℝ)|^71 ≤ (14266442355447/50000000000000 : ℝ)^55
        have hw : |(3785163843/10000000000 : ℝ)|=(3785163843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1541853371/2500000000 : ℝ)|^71 ≤ (837263513283/1562500000000 : ℝ)^55
        have hw : |(1541853371/2500000000 : ℝ)|=(1541853371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2635666249/10000000000 : ℝ)|^71 ≤ (17882250422011/100000000000000 : ℝ)^55
        have hw : |(-2635666249/10000000000 : ℝ)|=(2635666249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s2_s2_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-67083479/250000000 : ℝ)*x 0 + (4842692707/10000000000 : ℝ)*x 1 + (5152163253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67083479/250000000 : ℝ)^71 ≤ (18300885243169/100000000000000 : ℝ)^55 := by
    have hnat : (67083479 : ℕ)^71*100000000000000^55 ≤ 18300885243169^55*250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67083479 250000000 18300885243169 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4842692707/10000000000 : ℝ)^71 ≤ (7843426428659/20000000000000 : ℝ)^55 := by
    have hnat : (4842692707 : ℕ)^71*20000000000000^55 ≤ 7843426428659^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4842692707 10000000000 7843426428659 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152163253/10000000000 : ℝ)^71 ≤ (42481982598241/100000000000000 : ℝ)^55 := by
    have hnat : (5152163253 : ℕ)^71*100000000000000^55 ≤ 42481982598241^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152163253 10000000000 42481982598241 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67083479/250000000 : ℝ), (4842692707/10000000000 : ℝ), (5152163253/10000000000 : ℝ)] ![(18300885243169/100000000000000 : ℝ), (7843426428659/20000000000000 : ℝ), (42481982598241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67083479/250000000 : ℝ)|^71 ≤ (18300885243169/100000000000000 : ℝ)^55
        have hw : |(-67083479/250000000 : ℝ)|=(67083479/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4842692707/10000000000 : ℝ)|^71 ≤ (7843426428659/20000000000000 : ℝ)^55
        have hw : |(4842692707/10000000000 : ℝ)|=(4842692707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152163253/10000000000 : ℝ)|^71 ≤ (42481982598241/100000000000000 : ℝ)^55
        have hw : |(5152163253/10000000000 : ℝ)|=(5152163253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s2_s2_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6365655129/10000000000 : ℝ)*x 0 + (-186133347/5000000000 : ℝ)*x 1 + (1035504893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6365655129/10000000000 : ℝ)^71 ≤ (2232745763077/4000000000000 : ℝ)^55 := by
    have hnat : (6365655129 : ℕ)^71*4000000000000^55 ≤ 2232745763077^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6365655129 10000000000 2232745763077 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186133347/5000000000 : ℝ)^71 ≤ (178653975543/12500000000000 : ℝ)^55 := by
    have hnat : (186133347 : ℕ)^71*12500000000000^55 ≤ 178653975543^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186133347 5000000000 178653975543 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035504893/2000000000 : ℝ)^71 ≤ (42752124096111/100000000000000 : ℝ)^55 := by
    have hnat : (1035504893 : ℕ)^71*100000000000000^55 ≤ 42752124096111^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035504893 2000000000 42752124096111 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6365655129/10000000000 : ℝ), (-186133347/5000000000 : ℝ), (1035504893/2000000000 : ℝ)] ![(2232745763077/4000000000000 : ℝ), (178653975543/12500000000000 : ℝ), (42752124096111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6365655129/10000000000 : ℝ)|^71 ≤ (2232745763077/4000000000000 : ℝ)^55
        have hw : |(6365655129/10000000000 : ℝ)|=(6365655129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-186133347/5000000000 : ℝ)|^71 ≤ (178653975543/12500000000000 : ℝ)^55
        have hw : |(-186133347/5000000000 : ℝ)|=(186133347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035504893/2000000000 : ℝ)|^71 ≤ (42752124096111/100000000000000 : ℝ)^55
        have hw : |(1035504893/2000000000 : ℝ)|=(1035504893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s2_s2_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1656099317/5000000000 : ℝ)*x 0 + (1775604247/2500000000 : ℝ)*x 1 + (-947976563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1656099317/5000000000 : ℝ)^71 ≤ (24016729368091/100000000000000 : ℝ)^55 := by
    have hnat : (1656099317 : ℕ)^71*100000000000000^55 ≤ 24016729368091^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656099317 5000000000 24016729368091 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1775604247/2500000000 : ℝ)^71 ≤ (1607381176317/2500000000000 : ℝ)^55 := by
    have hnat : (1775604247 : ℕ)^71*2500000000000^55 ≤ 1607381176317^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775604247 2500000000 1607381176317 2500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (947976563/5000000000 : ℝ)^71 ≤ (11688023562989/100000000000000 : ℝ)^55 := by
    have hnat : (947976563 : ℕ)^71*100000000000000^55 ≤ 11688023562989^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947976563 5000000000 11688023562989 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1656099317/5000000000 : ℝ), (1775604247/2500000000 : ℝ), (-947976563/5000000000 : ℝ)] ![(24016729368091/100000000000000 : ℝ), (1607381176317/2500000000000 : ℝ), (11688023562989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1656099317/5000000000 : ℝ)|^71 ≤ (24016729368091/100000000000000 : ℝ)^55
        have hw : |(1656099317/5000000000 : ℝ)|=(1656099317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1775604247/2500000000 : ℝ)|^71 ≤ (1607381176317/2500000000000 : ℝ)^55
        have hw : |(1775604247/2500000000 : ℝ)|=(1775604247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-947976563/5000000000 : ℝ)|^71 ≤ (11688023562989/100000000000000 : ℝ)^55
        have hw : |(-947976563/5000000000 : ℝ)|=(947976563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s2_s2_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2864734469/10000000000 : ℝ)*x 0 + (301166929/625000000 : ℝ)*x 1 + (1255944603/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2864734469/10000000000 : ℝ)^71 ≤ (19913393800323/100000000000000 : ℝ)^55 := by
    have hnat : (2864734469 : ℕ)^71*100000000000000^55 ≤ 19913393800323^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2864734469 10000000000 19913393800323 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301166929/625000000 : ℝ)^71 ≤ (38966187996267/100000000000000 : ℝ)^55 := by
    have hnat : (301166929 : ℕ)^71*100000000000000^55 ≤ 38966187996267^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301166929 625000000 38966187996267 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1255944603/2500000000 : ℝ)^71 ≤ (20560209095177/50000000000000 : ℝ)^55 := by
    have hnat : (1255944603 : ℕ)^71*50000000000000^55 ≤ 20560209095177^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255944603 2500000000 20560209095177 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2864734469/10000000000 : ℝ), (301166929/625000000 : ℝ), (1255944603/2500000000 : ℝ)] ![(19913393800323/100000000000000 : ℝ), (38966187996267/100000000000000 : ℝ), (20560209095177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2864734469/10000000000 : ℝ)|^71 ≤ (19913393800323/100000000000000 : ℝ)^55
        have hw : |(2864734469/10000000000 : ℝ)|=(2864734469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(301166929/625000000 : ℝ)|^71 ≤ (38966187996267/100000000000000 : ℝ)^55
        have hw : |(301166929/625000000 : ℝ)|=(301166929/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1255944603/2500000000 : ℝ)|^71 ≤ (20560209095177/50000000000000 : ℝ)^55
        have hw : |(1255944603/2500000000 : ℝ)|=(1255944603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s2_s2_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-185547467/1000000000 : ℝ)*x 0 + (412508887/1000000000 : ℝ)*x 1 + (6447787333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (185547467/1000000000 : ℝ)^71 ≤ (284172440093/2500000000000 : ℝ)^55 := by
    have hnat : (185547467 : ℕ)^71*2500000000000^55 ≤ 284172440093^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185547467 1000000000 284172440093 2500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412508887/1000000000 : ℝ)^71 ≤ (31883013492559/100000000000000 : ℝ)^55 := by
    have hnat : (412508887 : ℕ)^71*100000000000000^55 ≤ 31883013492559^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412508887 1000000000 31883013492559 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6447787333/10000000000 : ℝ)^71 ≤ (28375044443581/50000000000000 : ℝ)^55 := by
    have hnat : (6447787333 : ℕ)^71*50000000000000^55 ≤ 28375044443581^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6447787333 10000000000 28375044443581 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-185547467/1000000000 : ℝ), (412508887/1000000000 : ℝ), (6447787333/10000000000 : ℝ)] ![(284172440093/2500000000000 : ℝ), (31883013492559/100000000000000 : ℝ), (28375044443581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-185547467/1000000000 : ℝ)|^71 ≤ (284172440093/2500000000000 : ℝ)^55
        have hw : |(-185547467/1000000000 : ℝ)|=(185547467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(412508887/1000000000 : ℝ)|^71 ≤ (31883013492559/100000000000000 : ℝ)^55
        have hw : |(412508887/1000000000 : ℝ)|=(412508887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6447787333/10000000000 : ℝ)|^71 ≤ (28375044443581/50000000000000 : ℝ)^55
        have hw : |(6447787333/10000000000 : ℝ)|=(6447787333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s2_s2_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3723599601/5000000000 : ℝ)*x 0 + (-562123101/5000000000 : ℝ)*x 1 + (436255963/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3723599601/5000000000 : ℝ)^71 ≤ (6835252497603/10000000000000 : ℝ)^55 := by
    have hnat : (3723599601 : ℕ)^71*10000000000000^55 ≤ 6835252497603^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3723599601 5000000000 6835252497603 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562123101/5000000000 : ℝ)^71 ≤ (2976585724679/50000000000000 : ℝ)^55 := by
    have hnat : (562123101 : ℕ)^71*50000000000000^55 ≤ 2976585724679^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562123101 5000000000 2976585724679 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436255963/1250000000 : ℝ)^71 ≤ (6423575889471/25000000000000 : ℝ)^55 := by
    have hnat : (436255963 : ℕ)^71*25000000000000^55 ≤ 6423575889471^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436255963 1250000000 6423575889471 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3723599601/5000000000 : ℝ), (-562123101/5000000000 : ℝ), (436255963/1250000000 : ℝ)] ![(6835252497603/10000000000000 : ℝ), (2976585724679/50000000000000 : ℝ), (6423575889471/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3723599601/5000000000 : ℝ)|^71 ≤ (6835252497603/10000000000000 : ℝ)^55
        have hw : |(3723599601/5000000000 : ℝ)|=(3723599601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-562123101/5000000000 : ℝ)|^71 ≤ (2976585724679/50000000000000 : ℝ)^55
        have hw : |(-562123101/5000000000 : ℝ)|=(562123101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(436255963/1250000000 : ℝ)|^71 ≤ (6423575889471/25000000000000 : ℝ)^55
        have hw : |(436255963/1250000000 : ℝ)|=(436255963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s2_s2_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1957986051/5000000000 : ℝ)*x 0 + (6568954319/10000000000 : ℝ)*x 1 + (-971099531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1957986051/5000000000 : ℝ)^71 ≤ (29812124359013/100000000000000 : ℝ)^55 := by
    have hnat : (1957986051 : ℕ)^71*100000000000000^55 ≤ 29812124359013^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957986051 5000000000 29812124359013 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6568954319/10000000000 : ℝ)^71 ≤ (58130524210857/100000000000000 : ℝ)^55 := by
    have hnat : (6568954319 : ℕ)^71*100000000000000^55 ≤ 58130524210857^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6568954319 10000000000 58130524210857 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (971099531/5000000000 : ℝ)^71 ≤ (3014337855323/25000000000000 : ℝ)^55 := by
    have hnat : (971099531 : ℕ)^71*25000000000000^55 ≤ 3014337855323^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971099531 5000000000 3014337855323 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1957986051/5000000000 : ℝ), (6568954319/10000000000 : ℝ), (-971099531/5000000000 : ℝ)] ![(29812124359013/100000000000000 : ℝ), (58130524210857/100000000000000 : ℝ), (3014337855323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1957986051/5000000000 : ℝ)|^71 ≤ (29812124359013/100000000000000 : ℝ)^55
        have hw : |(1957986051/5000000000 : ℝ)|=(1957986051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6568954319/10000000000 : ℝ)|^71 ≤ (58130524210857/100000000000000 : ℝ)^55
        have hw : |(6568954319/10000000000 : ℝ)|=(6568954319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-971099531/5000000000 : ℝ)|^71 ≤ (3014337855323/25000000000000 : ℝ)^55
        have hw : |(-971099531/5000000000 : ℝ)|=(971099531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s2_s2_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2803558571/10000000000 : ℝ)*x 0 + (4053658479/10000000000 : ℝ)*x 1 + (2898253399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2803558571/10000000000 : ℝ)^71 ≤ (77464609619/400000000000 : ℝ)^55 := by
    have hnat : (2803558571 : ℕ)^71*400000000000^55 ≤ 77464609619^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2803558571 10000000000 77464609619 400000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4053658479/10000000000 : ℝ)^71 ≤ (7793029819631/25000000000000 : ℝ)^55 := by
    have hnat : (4053658479 : ℕ)^71*25000000000000^55 ≤ 7793029819631^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4053658479 10000000000 7793029819631 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2898253399/5000000000 : ℝ)^71 ≤ (12365432077709/25000000000000 : ℝ)^55 := by
    have hnat : (2898253399 : ℕ)^71*25000000000000^55 ≤ 12365432077709^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2898253399 5000000000 12365432077709 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2803558571/10000000000 : ℝ), (4053658479/10000000000 : ℝ), (2898253399/5000000000 : ℝ)] ![(77464609619/400000000000 : ℝ), (7793029819631/25000000000000 : ℝ), (12365432077709/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2803558571/10000000000 : ℝ)|^71 ≤ (77464609619/400000000000 : ℝ)^55
        have hw : |(2803558571/10000000000 : ℝ)|=(2803558571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4053658479/10000000000 : ℝ)|^71 ≤ (7793029819631/25000000000000 : ℝ)^55
        have hw : |(4053658479/10000000000 : ℝ)|=(4053658479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2898253399/5000000000 : ℝ)|^71 ≤ (12365432077709/25000000000000 : ℝ)^55
        have hw : |(2898253399/5000000000 : ℝ)|=(2898253399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s2_s2_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-257850597/1250000000 : ℝ)*x 0 + (5441334917/10000000000 : ℝ)*x 1 + (504858581/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257850597/1250000000 : ℝ)^71 ≤ (13032500959279/100000000000000 : ℝ)^55 := by
    have hnat : (257850597 : ℕ)^71*100000000000000^55 ≤ 13032500959279^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257850597 1250000000 13032500959279 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441334917/10000000000 : ℝ)^71 ≤ (22792385256217/50000000000000 : ℝ)^55 := by
    have hnat : (5441334917 : ℕ)^71*50000000000000^55 ≤ 22792385256217^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441334917 10000000000 22792385256217 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504858581/1000000000 : ℝ)^71 ≤ (5172841063977/12500000000000 : ℝ)^55 := by
    have hnat : (504858581 : ℕ)^71*12500000000000^55 ≤ 5172841063977^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504858581 1000000000 5172841063977 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257850597/1250000000 : ℝ), (5441334917/10000000000 : ℝ), (504858581/1000000000 : ℝ)] ![(13032500959279/100000000000000 : ℝ), (22792385256217/50000000000000 : ℝ), (5172841063977/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257850597/1250000000 : ℝ)|^71 ≤ (13032500959279/100000000000000 : ℝ)^55
        have hw : |(-257850597/1250000000 : ℝ)|=(257850597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441334917/10000000000 : ℝ)|^71 ≤ (22792385256217/50000000000000 : ℝ)^55
        have hw : |(5441334917/10000000000 : ℝ)|=(5441334917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(504858581/1000000000 : ℝ)|^71 ≤ (5172841063977/12500000000000 : ℝ)^55
        have hw : |(504858581/1000000000 : ℝ)|=(504858581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s2_s2_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7392797229/10000000000 : ℝ)*x 0 + (-117203883/2500000000 : ℝ)*x 1 + (496533933/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7392797229/10000000000 : ℝ)^71 ≤ (33854319180883/50000000000000 : ℝ)^55 := by
    have hnat : (7392797229 : ℕ)^71*50000000000000^55 ≤ 33854319180883^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7392797229 10000000000 33854319180883 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117203883/2500000000 : ℝ)^71 ≤ (962397294487/50000000000000 : ℝ)^55 := by
    have hnat : (117203883 : ℕ)^71*50000000000000^55 ≤ 962397294487^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117203883 2500000000 962397294487 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496533933/1250000000 : ℝ)^71 ≤ (30366567028407/100000000000000 : ℝ)^55 := by
    have hnat : (496533933 : ℕ)^71*100000000000000^55 ≤ 30366567028407^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496533933 1250000000 30366567028407 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7392797229/10000000000 : ℝ), (-117203883/2500000000 : ℝ), (496533933/1250000000 : ℝ)] ![(33854319180883/50000000000000 : ℝ), (962397294487/50000000000000 : ℝ), (30366567028407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7392797229/10000000000 : ℝ)|^71 ≤ (33854319180883/50000000000000 : ℝ)^55
        have hw : |(7392797229/10000000000 : ℝ)|=(7392797229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117203883/2500000000 : ℝ)|^71 ≤ (962397294487/50000000000000 : ℝ)^55
        have hw : |(-117203883/2500000000 : ℝ)|=(117203883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(496533933/1250000000 : ℝ)|^71 ≤ (30366567028407/100000000000000 : ℝ)^55
        have hw : |(496533933/1250000000 : ℝ)|=(496533933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s2_s2_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1667732601/5000000000 : ℝ)*x 0 + (3242925581/5000000000 : ℝ)*x 1 + (-2715250709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1667732601/5000000000 : ℝ)^71 ≤ (24234735271747/100000000000000 : ℝ)^55 := by
    have hnat : (1667732601 : ℕ)^71*100000000000000^55 ≤ 24234735271747^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1667732601 5000000000 24234735271747 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3242925581/5000000000 : ℝ)^71 ≤ (57182937682991/100000000000000 : ℝ)^55 := by
    have hnat : (3242925581 : ℕ)^71*100000000000000^55 ≤ 57182937682991^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3242925581 5000000000 57182937682991 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715250709/10000000000 : ℝ)^71 ≤ (743293081123/4000000000000 : ℝ)^55 := by
    have hnat : (2715250709 : ℕ)^71*4000000000000^55 ≤ 743293081123^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715250709 10000000000 743293081123 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1667732601/5000000000 : ℝ), (3242925581/5000000000 : ℝ), (-2715250709/10000000000 : ℝ)] ![(24234735271747/100000000000000 : ℝ), (57182937682991/100000000000000 : ℝ), (743293081123/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1667732601/5000000000 : ℝ)|^71 ≤ (24234735271747/100000000000000 : ℝ)^55
        have hw : |(1667732601/5000000000 : ℝ)|=(1667732601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3242925581/5000000000 : ℝ)|^71 ≤ (57182937682991/100000000000000 : ℝ)^55
        have hw : |(3242925581/5000000000 : ℝ)|=(3242925581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2715250709/10000000000 : ℝ)|^71 ≤ (743293081123/4000000000000 : ℝ)^55
        have hw : |(-2715250709/10000000000 : ℝ)|=(2715250709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s2_s2_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3759564593/10000000000 : ℝ)*x 0 + (232143789/500000000 : ℝ)*x 1 + (219621003/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3759564593/10000000000 : ℝ)^71 ≤ (3535503039843/12500000000000 : ℝ)^55 := by
    have hnat : (3759564593 : ℕ)^71*12500000000000^55 ≤ 3535503039843^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3759564593 10000000000 3535503039843 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232143789/500000000 : ℝ)^71 ≤ (37140897323487/100000000000000 : ℝ)^55 := by
    have hnat : (232143789 : ℕ)^71*100000000000000^55 ≤ 37140897323487^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232143789 500000000 37140897323487 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219621003/500000000 : ℝ)^71 ≤ (34575078342579/100000000000000 : ℝ)^55 := by
    have hnat : (219621003 : ℕ)^71*100000000000000^55 ≤ 34575078342579^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219621003 500000000 34575078342579 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3759564593/10000000000 : ℝ), (232143789/500000000 : ℝ), (219621003/500000000 : ℝ)] ![(3535503039843/12500000000000 : ℝ), (37140897323487/100000000000000 : ℝ), (34575078342579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3759564593/10000000000 : ℝ)|^71 ≤ (3535503039843/12500000000000 : ℝ)^55
        have hw : |(3759564593/10000000000 : ℝ)|=(3759564593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(232143789/500000000 : ℝ)|^71 ≤ (37140897323487/100000000000000 : ℝ)^55
        have hw : |(232143789/500000000 : ℝ)|=(232143789/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219621003/500000000 : ℝ)|^71 ≤ (34575078342579/100000000000000 : ℝ)^55
        have hw : |(219621003/500000000 : ℝ)|=(219621003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310083_s2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((54817/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(54817/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((25299/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(25299/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61427/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61427/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((23099/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23099/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((25629/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(25629/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6297/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6297/25000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (54817/100000 : ℝ) ^ (35/8 : ℝ) ≤ (7206995981762673703/100000000000000000000 : ℝ) := by
    have hpowers : (54817/100000 : ℝ)^35 ≤ (7206995981762673703/100000000000000000000 : ℝ)^8 := by
      have hnat : (54817 : ℕ)^35*100000000000000000000^8 ≤ 7206995981762673703^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54817 100000 7206995981762673703 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (54817/100000 : ℝ)) (X := (7206995981762673703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (107206995981762673703/100000000000000000000 : ℝ) ≤ (10160337710042393/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (107206995981762673703/100000000000000000000 : ℝ)^8 ≤ (10160337710042393/10000000000000000 : ℝ)^35 := by
      have hnat : (107206995981762673703 : ℕ)^8*10000000000000000^35 ≤ 10160337710042393^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107206995981762673703 100000000000000000000 10160337710042393 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10160337710042393/10000000000000000 : ℝ)) (X := (107206995981762673703/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (57206995981762673703/50000000000000000000 : ℝ) ≤ (1289070510240139/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (57206995981762673703/50000000000000000000 : ℝ)^8 ≤ (1289070510240139/1250000000000000 : ℝ)^35 := by
      have hnat : (57206995981762673703 : ℕ)^8*1250000000000000^35 ≤ 1289070510240139^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57206995981762673703 50000000000000000000 1289070510240139 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1289070510240139/1250000000000000 : ℝ)) (X := (57206995981762673703/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(160337710042393/5481700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(152226371878719/5481700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (54817/100000 : ℝ)) (alpha := (160337710042393/5481700000000000 : ℝ)) (beta := (152226371878719/5481700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (54817/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(160337710042393/5481700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(152226371878719/5481700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (25299/50000 : ℝ) ^ (35/8 : ℝ) ≤ (50767223174738229/1000000000000000000 : ℝ) := by
    have hpowers : (25299/50000 : ℝ)^35 ≤ (50767223174738229/1000000000000000000 : ℝ)^8 := by
      have hnat : (25299 : ℕ)^35*1000000000000000000^8 ≤ 50767223174738229^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25299 50000 50767223174738229 1000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25299/50000 : ℝ)) (X := (50767223174738229/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (1050767223174738229/1000000000000000000 : ℝ) ≤ (10113832932676373/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (1050767223174738229/1000000000000000000 : ℝ)^8 ≤ (10113832932676373/10000000000000000 : ℝ)^35 := by
      have hnat : (1050767223174738229 : ℕ)^8*10000000000000000^35 ≤ 10113832932676373^35*1000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1050767223174738229 1000000000000000000 10113832932676373 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10113832932676373/10000000000000000 : ℝ)) (X := (1050767223174738229/1000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (550767223174738229/500000000000000000 : ℝ) ≤ (1022349906825413/1000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (550767223174738229/500000000000000000 : ℝ)^8 ≤ (1022349906825413/1000000000000000 : ℝ)^35 := by
      have hnat : (550767223174738229 : ℕ)^8*1000000000000000^35 ≤ 1022349906825413^35*500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        550767223174738229 500000000000000000 1022349906825413 1000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1022349906825413/1000000000000000 : ℝ)) (X := (550767223174738229/500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(113832932676373/5059800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(36555378525919/1686600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (25299/50000 : ℝ)) (alpha := (113832932676373/5059800000000000 : ℝ)) (beta := (36555378525919/1686600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (25299/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(113832932676373/5059800000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(36555378525919/1686600000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (61427/100000 : ℝ) ^ (35/8 : ℝ) ≤ (592982622138029719/5000000000000000000 : ℝ) := by
    have hpowers : (61427/100000 : ℝ)^35 ≤ (592982622138029719/5000000000000000000 : ℝ)^8 := by
      have hnat : (61427 : ℕ)^35*5000000000000000000^8 ≤ 592982622138029719^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61427 100000 592982622138029719 5000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61427/100000 : ℝ)) (X := (592982622138029719/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (5592982622138029719/5000000000000000000 : ℝ) ≤ (10259480339592327/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (5592982622138029719/5000000000000000000 : ℝ)^8 ≤ (10259480339592327/10000000000000000 : ℝ)^35 := by
      have hnat : (5592982622138029719 : ℕ)^8*10000000000000000^35 ≤ 10259480339592327^35*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5592982622138029719 5000000000000000000 10259480339592327 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10259480339592327/10000000000000000 : ℝ)) (X := (5592982622138029719/5000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (3092982622138029719/2500000000000000000 : ℝ) ≤ (5249265861481829/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3092982622138029719/2500000000000000000 : ℝ)^8 ≤ (5249265861481829/5000000000000000 : ℝ)^35 := by
      have hnat : (3092982622138029719 : ℕ)^8*5000000000000000^35 ≤ 5249265861481829^35*2500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3092982622138029719 2500000000000000000 5249265861481829 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5249265861481829/5000000000000000 : ℝ)) (X := (3092982622138029719/2500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(259480339592327/6142700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(239051383371331/6142700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (61427/100000 : ℝ)) (alpha := (259480339592327/6142700000000000 : ℝ)) (beta := (239051383371331/6142700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (61427/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(259480339592327/6142700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(239051383371331/6142700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-646359953/2500000000 : ℝ)*X 0 0+(1221629689/2500000000 : ℝ)*X 0 1+(5189567343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((6589225471/10000000000 : ℝ)*X 1 0+(-254547539/2000000000 : ℝ)*X 1 1+(4399856723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((3785163843/10000000000 : ℝ)*X 2 0+(1541853371/2500000000 : ℝ)*X 2 1+(-2635666249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-67083479/250000000 : ℝ)*X 0 0+(4842692707/10000000000 : ℝ)*X 0 1+(5152163253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((6365655129/10000000000 : ℝ)*X 1 0+(-186133347/5000000000 : ℝ)*X 1 1+(1035504893/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1656099317/5000000000 : ℝ)*X 2 0+(1775604247/2500000000 : ℝ)*X 2 1+(-947976563/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((2864734469/10000000000 : ℝ)*X 0 0+(301166929/625000000 : ℝ)*X 0 1+(1255944603/2500000000 : ℝ)*X 0 2+(2864734469/10000000000 : ℝ)*X 1 0+(301166929/625000000 : ℝ)*X 1 1+(1255944603/2500000000 : ℝ)*X 1 2+(2864734469/10000000000 : ℝ)*X 2 0+(301166929/625000000 : ℝ)*X 2 1+(1255944603/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-185547467/1000000000 : ℝ)*X 0 0+(412508887/1000000000 : ℝ)*X 0 1+(6447787333/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((3723599601/5000000000 : ℝ)*X 1 0+(-562123101/5000000000 : ℝ)*X 1 1+(436255963/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1957986051/5000000000 : ℝ)*X 2 0+(6568954319/10000000000 : ℝ)*X 2 1+(-971099531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((2803558571/10000000000 : ℝ)*X 0 0+(4053658479/10000000000 : ℝ)*X 0 1+(2898253399/5000000000 : ℝ)*X 0 2+(2803558571/10000000000 : ℝ)*X 1 0+(4053658479/10000000000 : ℝ)*X 1 1+(2898253399/5000000000 : ℝ)*X 1 2+(2803558571/10000000000 : ℝ)*X 2 0+(4053658479/10000000000 : ℝ)*X 2 1+(2898253399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-257850597/1250000000 : ℝ)*X 0 0+(5441334917/10000000000 : ℝ)*X 0 1+(504858581/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((7392797229/10000000000 : ℝ)*X 1 0+(-117203883/2500000000 : ℝ)*X 1 1+(496533933/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1667732601/5000000000 : ℝ)*X 2 0+(3242925581/5000000000 : ℝ)*X 2 1+(-2715250709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((3759564593/10000000000 : ℝ)*X 0 0+(232143789/500000000 : ℝ)*X 0 1+(219621003/500000000 : ℝ)*X 0 2+(3759564593/10000000000 : ℝ)*X 1 0+(232143789/500000000 : ℝ)*X 1 1+(219621003/500000000 : ℝ)*X 1 2+(3759564593/10000000000 : ℝ)*X 2 0+(232143789/500000000 : ℝ)*X 2 1+(219621003/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((23099/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23099/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12861488944165540269237/1370425000000000000000000000 : ℝ) := by norm_num
    linear_combination (2192899/250000000000 : ℝ)*(base19) + (3559008947/500000000000 : ℝ)*(base40) + (230503256967/200000000000 : ℝ)*(base49) + (289402135603/1000000000000 : ℝ)*(base60) + (4027169376303/1000000000000 : ℝ)*(major_s2_0) + (4027169376303/1000000000000 : ℝ)*(major_s2_1) + (4027169376303/1000000000000 : ℝ)*(major_s2_2) + (428155701/1000000000000 : ℝ)*(sp_s2_0) + (24887109/1000000000000 : ℝ)*(sp_s2_1) + (5564819057419/1000000000000 : ℝ)*(sp_s2_7) + (5565214442417/1000000000000 : ℝ)*(sp_s2_8) + (2782624050561/500000000000 : ℝ)*(sp_s2_9) + (2489087523133/1000000000000 : ℝ)*(sp_s2_13) + (888001/1000000000000 : ℝ)*(sp_s2_21) + (2489087523133/1000000000000 : ℝ)*(f.failure) + (2782624050561/500000000000 : ℝ)*(f.sum) + (5167781582281952609/34534259400000000000000000000000 : ℝ)*base63 + (1261599672817567/6142700000000000000000000000 : ℝ)*base64 + (399265085064713/1686600000000000000000000000 : ℝ)*base67 + (746997125606349/6142700000000000000000000000 : ℝ)*base68 + (2476264086480196197/10522637059375000000000000000000 : ℝ)*base71 + (3367102726274503/5481700000000000000000000000 : ℝ)*base72 + (296762511085319/562200000000000000000000000 : ℝ)*base74 + (333013299342919/5481700000000000000000000000 : ℝ)*base77 + (13800425683694664277/92454352200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (42531/100000000000000000 : ℝ)*base86 + (42531/100000000000000000 : ℝ)*base88 + (42531/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((25629/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(25629/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (36507719054949777/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (1533203/250000000000 : ℝ)*(base21) + (51587089709/62500000000 : ℝ)*(base40) + (1163491183611/1000000000000 : ℝ)*(base49) + (867051/500000000000 : ℝ)*(base59) + (706270246091/1000000000000 : ℝ)*(base60) + (2204530554067/500000000000 : ℝ)*(major_s2_0) + (2204530554067/500000000000 : ℝ)*(major_s2_1) + (2204530554067/500000000000 : ℝ)*(major_s2_2) + (13898339/500000000000 : ℝ)*(sp_s2_2) + (6092995019211/1000000000000 : ℝ)*(sp_s2_14) + (1218589883943/200000000000 : ℝ)*(sp_s2_15) + (6092961089721/1000000000000 : ℝ)*(sp_s2_16) + (1362562381603/500000000000 : ℝ)*(sp_s2_20) + (5699937/125000000000 : ℝ)*(sp_s2_22) + (1362562381603/500000000000 : ℝ)*(f.failure) + (6092995019211/1000000000000 : ℝ)*(f.sum) + (3078850288431806563/51801389100000000000000000000000 : ℝ)*base63 + (1151827766362763/3071350000000000000000000000 : ℝ)*base64 + (766768491457499/2529900000000000000000000000 : ℝ)*base66 + (412810302992491/3071350000000000000000000000 : ℝ)*base68 + (14328933856660413603/84181096475000000000000000000000 : ℝ)*base71 + (1117101288183647/2740850000000000000000000000 : ℝ)*base72 + (490964240198833/843300000000000000000000000 : ℝ)*base74 + (443321809598897/1370425000000000000000000000 : ℝ)*base76 + (17401546782924187981/138681528300000000000000000000000 : ℝ)*base79 + (5821/50000000000000000 : ℝ)*base86 + (5821/50000000000000000 : ℝ)*base88 + (5821/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6297/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6297/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9693758807824394001240049/1295034727500000000000000000000 : ℝ) := by norm_num
    linear_combination (727302752251/1000000000000 : ℝ)*(base40) + (336496305271/250000000000 : ℝ)*(base49) + (609641/200000000000 : ℝ)*(base50) + (1423031/1000000000000 : ℝ)*(base60) + (472241236171/100000000000 : ℝ)*(major_s2_0) + (472241236171/100000000000 : ℝ)*(major_s2_1) + (472241236171/100000000000 : ℝ)*(major_s2_2) + (3727609/1000000000000 : ℝ)*(sp_s2_2) + (43243643/1000000000000 : ℝ)*(sp_s2_15) + (23721177/500000000000 : ℝ)*(sp_s2_16) + (6526023292809/1000000000000 : ℝ)*(sp_s2_21) + (1305196009833/200000000000 : ℝ)*(sp_s2_22) + (3262986061423/500000000000 : ℝ)*(sp_s2_23) + (1459399467749/500000000000 : ℝ)*(sp_s2_27) + (1459399467749/500000000000 : ℝ)*(f.failure) + (6526023292809/1000000000000 : ℝ)*(f.sum) + (7924105066268239039/10360277820000000000000000000000 : ℝ)*base63 + (9961654143451/61427000000000000000000000 : ℝ)*base64 + (58172365546123/505980000000000000000000000 : ℝ)*base67 + (84662406844161/307135000000000000000000000 : ℝ)*base69 + (250529706007823/802030263671875000000000000 : ℝ)*base71 + (501923142271/2674000000000000000000000 : ℝ)*base72 + (21941838988957/33732000000000000000000000 : ℝ)*base75 + (70628002951/2674000000000000000000000 : ℝ)*base76 + (84080841185660591/676495260000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (13957/50000000000000000 : ℝ)*base87 + (13957/50000000000000000 : ℝ)*base89 + (13957/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((54817/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(54817/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((25299/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(25299/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61427/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61427/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((23099/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23099/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((25629/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(25629/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6297/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6297/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310083_s2 p hpa hpb X hX hprev1

#print axioms solution

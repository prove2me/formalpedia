-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301086_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:44:50.234723+00:00
-- url     : https://prove2.me/submissions/f12825f4-d4be-4e76-8ccd-cff992810f0c

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
theorem collision_support_c301086_s4_s4_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1505712939/2500000000 : ℝ)*x 0 + (-3574112861/10000000000 : ℝ)*x 1 + (-3347697303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1505712939/2500000000 : ℝ)^65 ≤ (51038845578249/100000000000000 : ℝ)^49 := by
    have hnat : (1505712939 : ℕ)^65*100000000000000^49 ≤ 51038845578249^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505712939 2500000000 51038845578249 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3574112861/10000000000 : ℝ)^65 ≤ (25542536423611/100000000000000 : ℝ)^49 := by
    have hnat : (3574112861 : ℕ)^65*100000000000000^49 ≤ 25542536423611^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3574112861 10000000000 25542536423611 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3347697303/10000000000 : ℝ)^65 ≤ (4683723598597/20000000000000 : ℝ)^49 := by
    have hnat : (3347697303 : ℕ)^65*20000000000000^49 ≤ 4683723598597^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3347697303 10000000000 4683723598597 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1505712939/2500000000 : ℝ), (-3574112861/10000000000 : ℝ), (-3347697303/10000000000 : ℝ)] ![(51038845578249/100000000000000 : ℝ), (25542536423611/100000000000000 : ℝ), (4683723598597/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1505712939/2500000000 : ℝ)|^65 ≤ (51038845578249/100000000000000 : ℝ)^49
        have hw : |(1505712939/2500000000 : ℝ)|=(1505712939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3574112861/10000000000 : ℝ)|^65 ≤ (25542536423611/100000000000000 : ℝ)^49
        have hw : |(-3574112861/10000000000 : ℝ)|=(3574112861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3347697303/10000000000 : ℝ)|^65 ≤ (4683723598597/20000000000000 : ℝ)^49
        have hw : |(-3347697303/10000000000 : ℝ)|=(3347697303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s4_s4_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4132062311/10000000000 : ℝ)*x 0 + (-3047288099/10000000000 : ℝ)*x 1 + (289171461/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4132062311/10000000000 : ℝ)^65 ≤ (30962326960617/100000000000000 : ℝ)^49 := by
    have hnat : (4132062311 : ℕ)^65*100000000000000^49 ≤ 30962326960617^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132062311 10000000000 30962326960617 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3047288099/10000000000 : ℝ)^65 ≤ (10336309005869/50000000000000 : ℝ)^49 := by
    have hnat : (3047288099 : ℕ)^65*50000000000000^49 ≤ 10336309005869^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3047288099 10000000000 10336309005869 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (289171461/500000000 : ℝ)^65 ≤ (48365055008457/100000000000000 : ℝ)^49 := by
    have hnat : (289171461 : ℕ)^65*100000000000000^49 ≤ 48365055008457^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289171461 500000000 48365055008457 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4132062311/10000000000 : ℝ), (-3047288099/10000000000 : ℝ), (289171461/500000000 : ℝ)] ![(30962326960617/100000000000000 : ℝ), (10336309005869/50000000000000 : ℝ), (48365055008457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4132062311/10000000000 : ℝ)|^65 ≤ (30962326960617/100000000000000 : ℝ)^49
        have hw : |(4132062311/10000000000 : ℝ)|=(4132062311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3047288099/10000000000 : ℝ)|^65 ≤ (10336309005869/50000000000000 : ℝ)^49
        have hw : |(-3047288099/10000000000 : ℝ)|=(3047288099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(289171461/500000000 : ℝ)|^65 ≤ (48365055008457/100000000000000 : ℝ)^49
        have hw : |(289171461/500000000 : ℝ)|=(289171461/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s4_s4_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (312993/10000000000 : ℝ)*x 0 + (-3858522723/5000000000 : ℝ)*x 1 + (1971183843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (312993/10000000000 : ℝ)^65 ≤ (21169899/20000000000000 : ℝ)^49 := by
    have hnat : (312993 : ℕ)^65*20000000000000^49 ≤ 21169899^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312993 10000000000 21169899 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3858522723/5000000000 : ℝ)^65 ≤ (35454420167193/50000000000000 : ℝ)^49 := by
    have hnat : (3858522723 : ℕ)^65*50000000000000^49 ≤ 35454420167193^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3858522723 5000000000 35454420167193 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1971183843/5000000000 : ℝ)^65 ≤ (14545526897397/50000000000000 : ℝ)^49 := by
    have hnat : (1971183843 : ℕ)^65*50000000000000^49 ≤ 14545526897397^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971183843 5000000000 14545526897397 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(312993/10000000000 : ℝ), (-3858522723/5000000000 : ℝ), (1971183843/5000000000 : ℝ)] ![(21169899/20000000000000 : ℝ), (35454420167193/50000000000000 : ℝ), (14545526897397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(312993/10000000000 : ℝ)|^65 ≤ (21169899/20000000000000 : ℝ)^49
        have hw : |(312993/10000000000 : ℝ)|=(312993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3858522723/5000000000 : ℝ)|^65 ≤ (35454420167193/50000000000000 : ℝ)^49
        have hw : |(-3858522723/5000000000 : ℝ)|=(3858522723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1971183843/5000000000 : ℝ)|^65 ≤ (14545526897397/50000000000000 : ℝ)^49
        have hw : |(1971183843/5000000000 : ℝ)|=(1971183843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s4_s4_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5963743801/10000000000 : ℝ)*x 0 + (1761346731/5000000000 : ℝ)*x 1 + (3470857549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5963743801/10000000000 : ℝ)^65 ≤ (25187731608759/50000000000000 : ℝ)^49 := by
    have hnat : (5963743801 : ℕ)^65*50000000000000^49 ≤ 25187731608759^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5963743801 10000000000 25187731608759 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1761346731/5000000000 : ℝ)^65 ≤ (25056223934047/100000000000000 : ℝ)^49 := by
    have hnat : (1761346731 : ℕ)^65*100000000000000^49 ≤ 25056223934047^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761346731 5000000000 25056223934047 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3470857549/10000000000 : ℝ)^65 ≤ (24568312825699/100000000000000 : ℝ)^49 := by
    have hnat : (3470857549 : ℕ)^65*100000000000000^49 ≤ 24568312825699^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3470857549 10000000000 24568312825699 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5963743801/10000000000 : ℝ), (1761346731/5000000000 : ℝ), (3470857549/10000000000 : ℝ)] ![(25187731608759/50000000000000 : ℝ), (25056223934047/100000000000000 : ℝ), (24568312825699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5963743801/10000000000 : ℝ)|^65 ≤ (25187731608759/50000000000000 : ℝ)^49
        have hw : |(5963743801/10000000000 : ℝ)|=(5963743801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1761346731/5000000000 : ℝ)|^65 ≤ (25056223934047/100000000000000 : ℝ)^49
        have hw : |(1761346731/5000000000 : ℝ)|=(1761346731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3470857549/10000000000 : ℝ)|^65 ≤ (24568312825699/100000000000000 : ℝ)^49
        have hw : |(3470857549/10000000000 : ℝ)|=(3470857549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s4_s4_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2896957271/5000000000 : ℝ)*x 0 + (-3682280831/10000000000 : ℝ)*x 1 + (-54858759/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2896957271/5000000000 : ℝ)^65 ≤ (9696281398283/20000000000000 : ℝ)^49 := by
    have hnat : (2896957271 : ℕ)^65*20000000000000^49 ≤ 9696281398283^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2896957271 5000000000 9696281398283 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3682280831/10000000000 : ℝ)^65 ≤ (26573012704197/100000000000000 : ℝ)^49 := by
    have hnat : (3682280831 : ℕ)^65*100000000000000^49 ≤ 26573012704197^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3682280831 10000000000 26573012704197 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54858759/156250000 : ℝ)^65 ≤ (6236395071033/25000000000000 : ℝ)^49 := by
    have hnat : (54858759 : ℕ)^65*25000000000000^49 ≤ 6236395071033^49*156250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54858759 156250000 6236395071033 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2896957271/5000000000 : ℝ), (-3682280831/10000000000 : ℝ), (-54858759/156250000 : ℝ)] ![(9696281398283/20000000000000 : ℝ), (26573012704197/100000000000000 : ℝ), (6236395071033/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2896957271/5000000000 : ℝ)|^65 ≤ (9696281398283/20000000000000 : ℝ)^49
        have hw : |(2896957271/5000000000 : ℝ)|=(2896957271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3682280831/10000000000 : ℝ)|^65 ≤ (26573012704197/100000000000000 : ℝ)^49
        have hw : |(-3682280831/10000000000 : ℝ)|=(3682280831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54858759/156250000 : ℝ)|^65 ≤ (6236395071033/25000000000000 : ℝ)^49
        have hw : |(-54858759/156250000 : ℝ)|=(54858759/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s4_s4_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2682788183/10000000000 : ℝ)*x 0 + (-1514227771/10000000000 : ℝ)*x 1 + (15998093/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682788183/10000000000 : ℝ)^65 ≤ (3491663175903/20000000000000 : ℝ)^49 := by
    have hnat : (2682788183 : ℕ)^65*20000000000000^49 ≤ 3491663175903^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682788183 10000000000 3491663175903 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1514227771/10000000000 : ℝ)^65 ≤ (8175202891787/100000000000000 : ℝ)^49 := by
    have hnat : (1514227771 : ℕ)^65*100000000000000^49 ≤ 8175202891787^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514227771 10000000000 8175202891787 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15998093/20000000 : ℝ)^65 ≤ (74366481210127/100000000000000 : ℝ)^49 := by
    have hnat : (15998093 : ℕ)^65*100000000000000^49 ≤ 74366481210127^49*20000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15998093 20000000 74366481210127 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682788183/10000000000 : ℝ), (-1514227771/10000000000 : ℝ), (15998093/20000000 : ℝ)] ![(3491663175903/20000000000000 : ℝ), (8175202891787/100000000000000 : ℝ), (74366481210127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682788183/10000000000 : ℝ)|^65 ≤ (3491663175903/20000000000000 : ℝ)^49
        have hw : |(2682788183/10000000000 : ℝ)|=(2682788183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1514227771/10000000000 : ℝ)|^65 ≤ (8175202891787/100000000000000 : ℝ)^49
        have hw : |(-1514227771/10000000000 : ℝ)|=(1514227771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15998093/20000000 : ℝ)|^65 ≤ (74366481210127/100000000000000 : ℝ)^49
        have hw : |(15998093/20000000 : ℝ)|=(15998093/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s4_s4_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-13333/2000000000 : ℝ)*x 0 + (-5039236613/10000000000 : ℝ)*x 1 + (6779283699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13333/2000000000 : ℝ)^65 ≤ (2721273/20000000000000 : ℝ)^49 := by
    have hnat : (13333 : ℕ)^65*20000000000000^49 ≤ 2721273^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13333 2000000000 2721273 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5039236613/10000000000 : ℝ)^65 ≤ (8057637517991/20000000000000 : ℝ)^49 := by
    have hnat : (5039236613 : ℕ)^65*20000000000000^49 ≤ 8057637517991^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5039236613 10000000000 8057637517991 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6779283699/10000000000 : ℝ)^65 ≤ (59711798788477/100000000000000 : ℝ)^49 := by
    have hnat : (6779283699 : ℕ)^65*100000000000000^49 ≤ 59711798788477^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6779283699 10000000000 59711798788477 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13333/2000000000 : ℝ), (-5039236613/10000000000 : ℝ), (6779283699/10000000000 : ℝ)] ![(2721273/20000000000000 : ℝ), (8057637517991/20000000000000 : ℝ), (59711798788477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13333/2000000000 : ℝ)|^65 ≤ (2721273/20000000000000 : ℝ)^49
        have hw : |(-13333/2000000000 : ℝ)|=(13333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5039236613/10000000000 : ℝ)|^65 ≤ (8057637517991/20000000000000 : ℝ)^49
        have hw : |(-5039236613/10000000000 : ℝ)|=(5039236613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6779283699/10000000000 : ℝ)|^65 ≤ (59711798788477/100000000000000 : ℝ)^49
        have hw : |(6779283699/10000000000 : ℝ)|=(6779283699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s4_s4_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7780148511/10000000000 : ℝ)*x 0 + (2532995381/10000000000 : ℝ)*x 1 + (510133841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7780148511/10000000000 : ℝ)^65 ≤ (17919756489993/25000000000000 : ℝ)^49 := by
    have hnat : (7780148511 : ℕ)^65*25000000000000^49 ≤ 17919756489993^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7780148511 10000000000 17919756489993 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2532995381/10000000000 : ℝ)^65 ≤ (2022147289657/12500000000000 : ℝ)^49 := by
    have hnat : (2532995381 : ℕ)^65*12500000000000^49 ≤ 2022147289657^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2532995381 10000000000 2022147289657 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510133841/2500000000 : ℝ)^65 ≤ (12143795708953/100000000000000 : ℝ)^49 := by
    have hnat : (510133841 : ℕ)^65*100000000000000^49 ≤ 12143795708953^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510133841 2500000000 12143795708953 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7780148511/10000000000 : ℝ), (2532995381/10000000000 : ℝ), (510133841/2500000000 : ℝ)] ![(17919756489993/25000000000000 : ℝ), (2022147289657/12500000000000 : ℝ), (12143795708953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7780148511/10000000000 : ℝ)|^65 ≤ (17919756489993/25000000000000 : ℝ)^49
        have hw : |(7780148511/10000000000 : ℝ)|=(7780148511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2532995381/10000000000 : ℝ)|^65 ≤ (2022147289657/12500000000000 : ℝ)^49
        have hw : |(2532995381/10000000000 : ℝ)|=(2532995381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(510133841/2500000000 : ℝ)|^65 ≤ (12143795708953/100000000000000 : ℝ)^49
        have hw : |(510133841/2500000000 : ℝ)|=(510133841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s4_s4_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (14597197/20000000 : ℝ)*x 0 + (-1562691307/5000000000 : ℝ)*x 1 + (-423811487/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14597197/20000000 : ℝ)^65 ≤ (16463530924077/25000000000000 : ℝ)^49 := by
    have hnat : (14597197 : ℕ)^65*25000000000000^49 ≤ 16463530924077^49*20000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14597197 20000000 16463530924077 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1562691307/5000000000 : ℝ)^65 ≤ (10689161192067/50000000000000 : ℝ)^49 := by
    have hnat : (1562691307 : ℕ)^65*50000000000000^49 ≤ 10689161192067^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562691307 5000000000 10689161192067 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423811487/2000000000 : ℝ)^65 ≤ (797972119567/6250000000000 : ℝ)^49 := by
    have hnat : (423811487 : ℕ)^65*6250000000000^49 ≤ 797972119567^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423811487 2000000000 797972119567 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(14597197/20000000 : ℝ), (-1562691307/5000000000 : ℝ), (-423811487/2000000000 : ℝ)] ![(16463530924077/25000000000000 : ℝ), (10689161192067/50000000000000 : ℝ), (797972119567/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(14597197/20000000 : ℝ)|^65 ≤ (16463530924077/25000000000000 : ℝ)^49
        have hw : |(14597197/20000000 : ℝ)|=(14597197/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1562691307/5000000000 : ℝ)|^65 ≤ (10689161192067/50000000000000 : ℝ)^49
        have hw : |(-1562691307/5000000000 : ℝ)|=(1562691307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423811487/2000000000 : ℝ)|^65 ≤ (797972119567/6250000000000 : ℝ)^49
        have hw : |(-423811487/2000000000 : ℝ)|=(423811487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s4_s4_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2604988579/10000000000 : ℝ)*x 0 + (-990825243/5000000000 : ℝ)*x 1 + (310714633/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2604988579/10000000000 : ℝ)^65 ≤ (16789916699937/100000000000000 : ℝ)^49 := by
    have hnat : (2604988579 : ℕ)^65*100000000000000^49 ≤ 16789916699937^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2604988579 10000000000 16789916699937 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (990825243/5000000000 : ℝ)^65 ≤ (11681130424393/100000000000000 : ℝ)^49 := by
    have hnat : (990825243 : ℕ)^65*100000000000000^49 ≤ 11681130424393^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990825243 5000000000 11681130424393 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310714633/400000000 : ℝ)^65 ≤ (14305790572911/20000000000000 : ℝ)^49 := by
    have hnat : (310714633 : ℕ)^65*20000000000000^49 ≤ 14305790572911^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310714633 400000000 14305790572911 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2604988579/10000000000 : ℝ), (-990825243/5000000000 : ℝ), (310714633/400000000 : ℝ)] ![(16789916699937/100000000000000 : ℝ), (11681130424393/100000000000000 : ℝ), (14305790572911/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2604988579/10000000000 : ℝ)|^65 ≤ (16789916699937/100000000000000 : ℝ)^49
        have hw : |(2604988579/10000000000 : ℝ)|=(2604988579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-990825243/5000000000 : ℝ)|^65 ≤ (11681130424393/100000000000000 : ℝ)^49
        have hw : |(-990825243/5000000000 : ℝ)|=(990825243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(310714633/400000000 : ℝ)|^65 ≤ (14305790572911/20000000000000 : ℝ)^49
        have hw : |(310714633/400000000 : ℝ)|=(310714633/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s4_s4_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (51443387/10000000000 : ℝ)*x 0 + (-7483293999/10000000000 : ℝ)*x 1 + (4219467121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51443387/10000000000 : ℝ)^65 ≤ (5752923647/6250000000000 : ℝ)^49 := by
    have hnat : (51443387 : ℕ)^65*6250000000000^49 ≤ 5752923647^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51443387 10000000000 5752923647 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7483293999/10000000000 : ℝ)^65 ≤ (34036920450847/50000000000000 : ℝ)^49 := by
    have hnat : (7483293999 : ℕ)^65*50000000000000^49 ≤ 34036920450847^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7483293999 10000000000 34036920450847 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4219467121/10000000000 : ℝ)^65 ≤ (31834112310799/100000000000000 : ℝ)^49 := by
    have hnat : (4219467121 : ℕ)^65*100000000000000^49 ≤ 31834112310799^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219467121 10000000000 31834112310799 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(51443387/10000000000 : ℝ), (-7483293999/10000000000 : ℝ), (4219467121/10000000000 : ℝ)] ![(5752923647/6250000000000 : ℝ), (34036920450847/50000000000000 : ℝ), (31834112310799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(51443387/10000000000 : ℝ)|^65 ≤ (5752923647/6250000000000 : ℝ)^49
        have hw : |(51443387/10000000000 : ℝ)|=(51443387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7483293999/10000000000 : ℝ)|^65 ≤ (34036920450847/50000000000000 : ℝ)^49
        have hw : |(-7483293999/10000000000 : ℝ)|=(7483293999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4219467121/10000000000 : ℝ)|^65 ≤ (31834112310799/100000000000000 : ℝ)^49
        have hw : |(4219467121/10000000000 : ℝ)|=(4219467121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s4_s4_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (149564491/200000000 : ℝ)*x 0 + (1365303111/5000000000 : ℝ)*x 1 + (457110127/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (149564491/200000000 : ℝ)^65 ≤ (34006336932671/50000000000000 : ℝ)^49 := by
    have hnat : (149564491 : ℕ)^65*50000000000000^49 ≤ 34006336932671^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149564491 200000000 34006336932671 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365303111/5000000000 : ℝ)^65 ≤ (17872298372751/100000000000000 : ℝ)^49 := by
    have hnat : (1365303111 : ℕ)^65*100000000000000^49 ≤ 17872298372751^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365303111 5000000000 17872298372751 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (457110127/2000000000 : ℝ)^65 ≤ (14115027745633/100000000000000 : ℝ)^49 := by
    have hnat : (457110127 : ℕ)^65*100000000000000^49 ≤ 14115027745633^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457110127 2000000000 14115027745633 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(149564491/200000000 : ℝ), (1365303111/5000000000 : ℝ), (457110127/2000000000 : ℝ)] ![(34006336932671/50000000000000 : ℝ), (17872298372751/100000000000000 : ℝ), (14115027745633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(149564491/200000000 : ℝ)|^65 ≤ (34006336932671/50000000000000 : ℝ)^49
        have hw : |(149564491/200000000 : ℝ)|=(149564491/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365303111/5000000000 : ℝ)|^65 ≤ (17872298372751/100000000000000 : ℝ)^49
        have hw : |(1365303111/5000000000 : ℝ)|=(1365303111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(457110127/2000000000 : ℝ)|^65 ≤ (14115027745633/100000000000000 : ℝ)^49
        have hw : |(457110127/2000000000 : ℝ)|=(457110127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s4_s4_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2479149453/5000000000 : ℝ)*x 0 + (-1179059103/2500000000 : ℝ)*x 1 + (-3374637537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2479149453/5000000000 : ℝ)^65 ≤ (39432063598087/100000000000000 : ℝ)^49 := by
    have hnat : (2479149453 : ℕ)^65*100000000000000^49 ≤ 39432063598087^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2479149453 5000000000 39432063598087 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1179059103/2500000000 : ℝ)^65 ≤ (36898994145957/100000000000000 : ℝ)^49 := by
    have hnat : (1179059103 : ℕ)^65*100000000000000^49 ≤ 36898994145957^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1179059103 2500000000 36898994145957 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3374637537/10000000000 : ℝ)^65 ≤ (23668942241941/100000000000000 : ℝ)^49 := by
    have hnat : (3374637537 : ℕ)^65*100000000000000^49 ≤ 23668942241941^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3374637537 10000000000 23668942241941 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2479149453/5000000000 : ℝ), (-1179059103/2500000000 : ℝ), (-3374637537/10000000000 : ℝ)] ![(39432063598087/100000000000000 : ℝ), (36898994145957/100000000000000 : ℝ), (23668942241941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2479149453/5000000000 : ℝ)|^65 ≤ (39432063598087/100000000000000 : ℝ)^49
        have hw : |(2479149453/5000000000 : ℝ)|=(2479149453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1179059103/2500000000 : ℝ)|^65 ≤ (36898994145957/100000000000000 : ℝ)^49
        have hw : |(-1179059103/2500000000 : ℝ)|=(1179059103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3374637537/10000000000 : ℝ)|^65 ≤ (23668942241941/100000000000000 : ℝ)^49
        have hw : |(-3374637537/10000000000 : ℝ)|=(3374637537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s4_s4_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2893437159/5000000000 : ℝ)*x 0 + (-52684709/250000000 : ℝ)*x 1 + (4909905553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2893437159/5000000000 : ℝ)^65 ≤ (24201638237541/50000000000000 : ℝ)^49 := by
    have hnat : (2893437159 : ℕ)^65*50000000000000^49 ≤ 24201638237541^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2893437159 5000000000 24201638237541 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52684709/250000000 : ℝ)^65 ≤ (12674372870677/100000000000000 : ℝ)^49 := by
    have hnat : (52684709 : ℕ)^65*100000000000000^49 ≤ 12674372870677^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52684709 250000000 12674372870677 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4909905553/10000000000 : ℝ)^65 ≤ (9730587659889/25000000000000 : ℝ)^49 := by
    have hnat : (4909905553 : ℕ)^65*25000000000000^49 ≤ 9730587659889^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4909905553 10000000000 9730587659889 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2893437159/5000000000 : ℝ), (-52684709/250000000 : ℝ), (4909905553/10000000000 : ℝ)] ![(24201638237541/50000000000000 : ℝ), (12674372870677/100000000000000 : ℝ), (9730587659889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2893437159/5000000000 : ℝ)|^65 ≤ (24201638237541/50000000000000 : ℝ)^49
        have hw : |(2893437159/5000000000 : ℝ)|=(2893437159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52684709/250000000 : ℝ)|^65 ≤ (12674372870677/100000000000000 : ℝ)^49
        have hw : |(-52684709/250000000 : ℝ)|=(52684709/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4909905553/10000000000 : ℝ)|^65 ≤ (9730587659889/25000000000000 : ℝ)^49
        have hw : |(4909905553/10000000000 : ℝ)|=(4909905553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301086_s4 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((8387/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8387/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-20619/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-20619/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(81293/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(81293/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22163/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22163/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-3589/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3589/5000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16593/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16593/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (8387/12500 : ℝ) ^ (129/32 : ℝ) ≤ (20015700305779128519/100000000000000000000 : ℝ) := by
    have hpowers : (8387/12500 : ℝ)^129 ≤ (20015700305779128519/100000000000000000000 : ℝ)^32 := by
      have hnat : (8387 : ℕ)^129*100000000000000000000^32 ≤ 20015700305779128519^32*12500^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8387 12500 20015700305779128519 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8387/12500 : ℝ)) (X := (20015700305779128519/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner0a : (120015700305779128519/100000000000000000000 : ℝ) ≤ (2615748364457651/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (120015700305779128519/100000000000000000000 : ℝ)^32 ≤ (2615748364457651/2500000000000000 : ℝ)^129 := by
      have hnat : (120015700305779128519 : ℕ)^32*2500000000000000^129 ≤ 2615748364457651^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        120015700305779128519 100000000000000000000 2615748364457651 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2615748364457651/2500000000000000 : ℝ)) (X := (120015700305779128519/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner0b : (70015700305779128519/50000000000000000000 : ℝ) ≤ (5435543552449247/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (70015700305779128519/50000000000000000000 : ℝ)^32 ≤ (5435543552449247/5000000000000000 : ℝ)^129 := by
      have hnat : (70015700305779128519 : ℕ)^32*5000000000000000^129 ≤ 5435543552449247^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70015700305779128519 50000000000000000000 5435543552449247 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5435543552449247/5000000000000000 : ℝ)) (X := (70015700305779128519/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(115748364457651/1677400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(40809364706789/670960000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (8387/12500 : ℝ)) (alpha := (115748364457651/1677400000000000 : ℝ)) (beta := (40809364706789/670960000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (8387/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(115748364457651/1677400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(40809364706789/670960000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (20619/25000 : ℝ) ^ (129/32 : ℝ) ≤ (45993408643746074131/100000000000000000000 : ℝ) := by
    have hpowers : (20619/25000 : ℝ)^129 ≤ (45993408643746074131/100000000000000000000 : ℝ)^32 := by
      have hnat : (20619 : ℕ)^129*100000000000000000000^32 ≤ 45993408643746074131^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20619 25000 45993408643746074131 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20619/25000 : ℝ)) (X := (45993408643746074131/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner1a : (145993408643746074131/100000000000000000000 : ℝ) ≤ (1373013634210727/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (145993408643746074131/100000000000000000000 : ℝ)^32 ≤ (1373013634210727/1250000000000000 : ℝ)^129 := by
      have hnat : (145993408643746074131 : ℕ)^32*1250000000000000^129 ≤ 1373013634210727^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        145993408643746074131 100000000000000000000 1373013634210727 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1373013634210727/1250000000000000 : ℝ)) (X := (145993408643746074131/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner1b : (95993408643746074131/50000000000000000000 : ℝ) ≤ (11756251726132123/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (95993408643746074131/50000000000000000000 : ℝ)^32 ≤ (11756251726132123/10000000000000000 : ℝ)^129 := by
      have hnat : (95993408643746074131 : ℕ)^32*10000000000000000^129 ≤ 11756251726132123^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        95993408643746074131 50000000000000000000 11756251726132123 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11756251726132123/10000000000000000 : ℝ)) (X := (95993408643746074131/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(41004544736909/343650000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(257380884148769/2749200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (20619/25000 : ℝ)) (alpha := (41004544736909/343650000000000 : ℝ)) (beta := (257380884148769/2749200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (20619/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(41004544736909/343650000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(257380884148769/2749200000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (81293/100000 : ℝ) ^ (129/32 : ℝ) ≤ (1084780258553883751/2500000000000000000 : ℝ) := by
    have hpowers : (81293/100000 : ℝ)^129 ≤ (1084780258553883751/2500000000000000000 : ℝ)^32 := by
      have hnat : (81293 : ℕ)^129*2500000000000000000^32 ≤ 1084780258553883751^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81293 100000 1084780258553883751 2500000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (81293/100000 : ℝ)) (X := (1084780258553883751/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner2a : (3584780258553883751/2500000000000000000 : ℝ) ≤ (1093521419868043/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3584780258553883751/2500000000000000000 : ℝ)^32 ≤ (1093521419868043/1000000000000000 : ℝ)^129 := by
      have hnat : (3584780258553883751 : ℕ)^32*1000000000000000^129 ≤ 1093521419868043^129*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3584780258553883751 2500000000000000000 1093521419868043 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1093521419868043/1000000000000000 : ℝ)) (X := (3584780258553883751/2500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner2b : (2334780258553883751/1250000000000000000 : ℝ) ≤ (2335275648064123/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2334780258553883751/1250000000000000000 : ℝ)^32 ≤ (2335275648064123/2000000000000000 : ℝ)^129 := by
      have hnat : (2334780258553883751 : ℕ)^32*2000000000000000^129 ≤ 2335275648064123^129*1250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2334780258553883751 1250000000000000000 2335275648064123 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2335275648064123/2000000000000000 : ℝ)) (X := (2334780258553883751/1250000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(93521419868043/812930000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(148232808328037/1625860000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (81293/100000 : ℝ)) (alpha := (93521419868043/812930000000000 : ℝ)) (beta := (148232808328037/1625860000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (81293/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(93521419868043/812930000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(148232808328037/1625860000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_2 : ((1505712939/2500000000 : ℝ)*X 2 0+(-3574112861/10000000000 : ℝ)*X 2 1+(-3347697303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((4132062311/10000000000 : ℝ)*X 0 0+(-3047288099/10000000000 : ℝ)*X 0 1+(289171461/500000000 : ℝ)*X 0 2+(4132062311/10000000000 : ℝ)*X 1 0+(-3047288099/10000000000 : ℝ)*X 1 1+(289171461/500000000 : ℝ)*X 1 2+(4132062311/10000000000 : ℝ)*X 2 0+(-3047288099/10000000000 : ℝ)*X 2 1+(289171461/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((312993/10000000000 : ℝ)*X 0 0+(-3858522723/5000000000 : ℝ)*X 0 1+(1971183843/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((5963743801/10000000000 : ℝ)*X 1 0+(1761346731/5000000000 : ℝ)*X 1 1+(3470857549/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((2896957271/5000000000 : ℝ)*X 2 0+(-3682280831/10000000000 : ℝ)*X 2 1+(-54858759/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((2682788183/10000000000 : ℝ)*X 0 0+(-1514227771/10000000000 : ℝ)*X 0 1+(15998093/20000000 : ℝ)*X 0 2+(2682788183/10000000000 : ℝ)*X 1 0+(-1514227771/10000000000 : ℝ)*X 1 1+(15998093/20000000 : ℝ)*X 1 2+(2682788183/10000000000 : ℝ)*X 2 0+(-1514227771/10000000000 : ℝ)*X 2 1+(15998093/20000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-13333/2000000000 : ℝ)*X 0 0+(-5039236613/10000000000 : ℝ)*X 0 1+(6779283699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((7780148511/10000000000 : ℝ)*X 1 0+(2532995381/10000000000 : ℝ)*X 1 1+(510133841/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((14597197/20000000 : ℝ)*X 2 0+(-1562691307/5000000000 : ℝ)*X 2 1+(-423811487/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((2604988579/10000000000 : ℝ)*X 0 0+(-990825243/5000000000 : ℝ)*X 0 1+(310714633/400000000 : ℝ)*X 0 2+(2604988579/10000000000 : ℝ)*X 1 0+(-990825243/5000000000 : ℝ)*X 1 1+(310714633/400000000 : ℝ)*X 1 2+(2604988579/10000000000 : ℝ)*X 2 0+(-990825243/5000000000 : ℝ)*X 2 1+(310714633/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((51443387/10000000000 : ℝ)*X 0 0+(-7483293999/10000000000 : ℝ)*X 0 1+(4219467121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((149564491/200000000 : ℝ)*X 1 0+(1365303111/5000000000 : ℝ)*X 1 1+(457110127/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((2479149453/5000000000 : ℝ)*X 2 0+(-1179059103/2500000000 : ℝ)*X 2 1+(-3374637537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((2893437159/5000000000 : ℝ)*X 0 0+(-52684709/250000000 : ℝ)*X 0 1+(4909905553/10000000000 : ℝ)*X 0 2+(2893437159/5000000000 : ℝ)*X 1 0+(-52684709/250000000 : ℝ)*X 1 1+(4909905553/10000000000 : ℝ)*X 1 2+(2893437159/5000000000 : ℝ)*X 2 0+(-52684709/250000000 : ℝ)*X 2 1+(4909905553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((22163/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22163/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (381970367026512644739711/96073085000000000000000000000 : ℝ) := by norm_num
    linear_combination (73042513849/250000000000 : ℝ)*(base7) + (2117/125000000000 : ℝ)*(base24) + (2814490469/1000000000000 : ℝ)*(base40) + (287534393403/100000000000 : ℝ)*(major_s4_0) + (287534393403/100000000000 : ℝ)*(major_s4_1) + (287534393403/100000000000 : ℝ)*(major_s4_2) + (2679841/1000000000000 : ℝ)*(sp_s4_6) + (3626789925197/1000000000000 : ℝ)*(sp_s4_7) + (113341537401/31250000000 : ℝ)*(sp_s4_8) + (906732061233/250000000000 : ℝ)*(sp_s4_9) + (2235896937749/1000000000000 : ℝ)*(sp_s4_13) + (13711967/200000000000 : ℝ)*(sp_s4_20) + (27854327/200000000000 : ℝ)*(sp_s4_21) + (233741/250000000000 : ℝ)*(sp_s4_23) + (1943798122029/1000000000000 : ℝ)*(f.failure) + (113341537401/31250000000 : ℝ)*(f.sum) + (839300802156681871/7449690520000000000000000000000 : ℝ)*base62 + (3201248343187/20323250000000000000000000 : ℝ)*base64 + (1133750908017/11455000000000000000000000 : ℝ)*base66 + (12682900664479/162586000000000000000000000 : ℝ)*base69 + (2635178020518243107/13636087820000000000000000000000 : ℝ)*base71 + (26089509391489/335480000000000000000000000 : ℝ)*base72 + (118017826047/18328000000000000000000000 : ℝ)*base74 + (2393048127331/33548000000000000000000000 : ℝ)*base76 + (271631096665194411/768584680000000000000000000000 : ℝ)*base78 + (4449/25000000000000000 : ℝ)*base87 + (4449/25000000000000000 : ℝ)*base89 + (4449/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-3589/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3589/5000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (305929160641970936971788749613/62480554391240000000000000000000000 : ℝ) := by norm_num
    linear_combination (81462955811/125000000000 : ℝ)*(base7) + (250947/125000000000 : ℝ)*(base33) + (30757130407/125000000000 : ℝ)*(base40) + (87550412107/1000000000000 : ℝ)*(base60) + (252464708881/100000000000 : ℝ)*(major_s4_0) + (504929819277/200000000000 : ℝ)*(major_s4_1) + (504929819277/200000000000 : ℝ)*(major_s4_2) + (15657421/1000000000000 : ℝ)*(sp_s4_2) + (3772001/250000000000 : ℝ)*(sp_s4_6) + (129024981/1000000000000 : ℝ)*(sp_s4_13) + (2941165808577/1000000000000 : ℝ)*(sp_s4_14) + (2941163801001/1000000000000 : ℝ)*(sp_s4_15) + (2941148143581/1000000000000 : ℝ)*(sp_s4_16) + (2358279941541/1000000000000 : ℝ)*(sp_s4_20) + (1706720408037/1000000000000 : ℝ)*(f.failure) + (2941165808577/1000000000000 : ℝ)*(f.sum) + (259583210388083661/14899381040000000000000000000000 : ℝ)*base62 + (716346911640919/1625860000000000000000000000 : ℝ)*base65 + (6933061755217/22910000000000000000000000 : ℝ)*base66 + (313213548924037/406465000000000000000000000 : ℝ)*base69 + (540663948985603507/852255488750000000000000000000 : ℝ)*base71 + (112721670741267/335480000000000000000000000 : ℝ)*base72 + (940336357353/7331200000000000000000000 : ℝ)*base74 + (104423361701843/167740000000000000000000000 : ℝ)*base77 + (149105608516619693/768584680000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (33703/25000000000000000 : ℝ)*base86 + (8703/25000000000000000 : ℝ)*base88 + (8703/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16593/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16593/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1522203108639254274721940531001/156201385978100000000000000000000000 : ℝ) := by norm_num
    linear_combination (587617855217/1000000000000 : ℝ)*(base7) + (820429/1000000000000 : ℝ)*(base17) + (282561/100000000000 : ℝ)*(base39) + (77557263529/125000000000 : ℝ)*(base40) + (906831/250000000000 : ℝ)*(base43) + (1747557012721/500000000000 : ℝ)*(major_s4_0) + (1747555199059/500000000000 : ℝ)*(major_s4_1) + (1747557012721/500000000000 : ℝ)*(major_s4_2) + (1259919/1000000000000 : ℝ)*(sp_s4_14) + (5402239/250000000000 : ℝ)*(sp_s4_16) + (1066376431243/250000000000 : ℝ)*(sp_s4_21) + (2132754895893/500000000000 : ℝ)*(sp_s4_22) + (853097075187/200000000000 : ℝ)*(sp_s4_23) + (2950394703763/1000000000000 : ℝ)*(sp_s4_27) + (472555369709/200000000000 : ℝ)*(f.failure) + (853102122443/200000000000 : ℝ)*(f.sum) + (27120893737792533677/111745357800000000000000000000000 : ℝ)*base62 + (122509481360219/406465000000000000000000000 : ℝ)*base65 + (29777134577959/171825000000000000000000000 : ℝ)*base66 + (36582230368707/101616250000000000000000000 : ℝ)*base68 + (10685240459346588793/68180439100000000000000000000000 : ℝ)*base71 + (19494979017/335480000000000000000000000 : ℝ)*base73 + (344052347921869/1374600000000000000000000000 : ℝ)*base74 + (313217728499451/838700000000000000000000000 : ℝ)*base77 + (156059046864528919/11528770200000000000000000000000 : ℝ)*base78 + (1471/5000000000000000 : ℝ)*base86 + (1471/5000000000000000 : ℝ)*base88 + (1471/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((8387/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8387/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-20619/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-20619/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(81293/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(81293/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22163/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22163/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-3589/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3589/5000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16593/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16593/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301086_s4 p hpa hpb X hX hprev3

#print axioms solution

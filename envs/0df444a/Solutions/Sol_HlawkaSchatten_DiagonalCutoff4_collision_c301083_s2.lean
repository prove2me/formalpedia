-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301083_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:44:13.929206+00:00
-- url     : https://prove2.me/submissions/b317ad9b-42a4-4647-b955-39b6b7cfa0ea

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
theorem collision_support_c301083_s2_s2_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2229822767/10000000000 : ℝ)*x 0 + (1012356533/2000000000 : ℝ)*x 1 + (1387944317/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2229822767/10000000000 : ℝ)^65 ≤ (6830156685049/50000000000000 : ℝ)^49 := by
    have hnat : (2229822767 : ℕ)^65*50000000000000^49 ≤ 6830156685049^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229822767 10000000000 6830156685049 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1012356533/2000000000 : ℝ)^65 ≤ (40527473741111/100000000000000 : ℝ)^49 := by
    have hnat : (1012356533 : ℕ)^65*100000000000000^49 ≤ 40527473741111^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012356533 2000000000 40527473741111 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1387944317/2500000000 : ℝ)^65 ≤ (11453053216901/25000000000000 : ℝ)^49 := by
    have hnat : (1387944317 : ℕ)^65*25000000000000^49 ≤ 11453053216901^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387944317 2500000000 11453053216901 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2229822767/10000000000 : ℝ), (1012356533/2000000000 : ℝ), (1387944317/2500000000 : ℝ)] ![(6830156685049/50000000000000 : ℝ), (40527473741111/100000000000000 : ℝ), (11453053216901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2229822767/10000000000 : ℝ)|^65 ≤ (6830156685049/50000000000000 : ℝ)^49
        have hw : |(-2229822767/10000000000 : ℝ)|=(2229822767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1012356533/2000000000 : ℝ)|^65 ≤ (40527473741111/100000000000000 : ℝ)^49
        have hw : |(1012356533/2000000000 : ℝ)|=(1012356533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1387944317/2500000000 : ℝ)|^65 ≤ (11453053216901/25000000000000 : ℝ)^49
        have hw : |(1387944317/2500000000 : ℝ)|=(1387944317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s2_s2_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (234381847/625000000 : ℝ)*x 0 + (1323230643/2000000000 : ℝ)*x 1 + (-2388242657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (234381847/625000000 : ℝ)^65 ≤ (5444854294763/20000000000000 : ℝ)^49 := by
    have hnat : (234381847 : ℕ)^65*20000000000000^49 ≤ 5444854294763^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234381847 625000000 5444854294763 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1323230643/2000000000 : ℝ)^65 ≤ (57813302114279/100000000000000 : ℝ)^49 := by
    have hnat : (1323230643 : ℕ)^65*100000000000000^49 ≤ 57813302114279^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323230643 2000000000 57813302114279 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2388242657/10000000000 : ℝ)^65 ≤ (14962426395289/100000000000000 : ℝ)^49 := by
    have hnat : (2388242657 : ℕ)^65*100000000000000^49 ≤ 14962426395289^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388242657 10000000000 14962426395289 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(234381847/625000000 : ℝ), (1323230643/2000000000 : ℝ), (-2388242657/10000000000 : ℝ)] ![(5444854294763/20000000000000 : ℝ), (57813302114279/100000000000000 : ℝ), (14962426395289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(234381847/625000000 : ℝ)|^65 ≤ (5444854294763/20000000000000 : ℝ)^49
        have hw : |(234381847/625000000 : ℝ)|=(234381847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1323230643/2000000000 : ℝ)|^65 ≤ (57813302114279/100000000000000 : ℝ)^49
        have hw : |(1323230643/2000000000 : ℝ)|=(1323230643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2388242657/10000000000 : ℝ)|^65 ≤ (14962426395289/100000000000000 : ℝ)^49
        have hw : |(-2388242657/10000000000 : ℝ)|=(2388242657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s2_s2_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1624131453/5000000000 : ℝ)*x 0 + (4724917027/10000000000 : ℝ)*x 1 + (253009137/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1624131453/5000000000 : ℝ)^65 ≤ (2812550597433/12500000000000 : ℝ)^49 := by
    have hnat : (1624131453 : ℕ)^65*12500000000000^49 ≤ 2812550597433^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1624131453 5000000000 2812550597433 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4724917027/10000000000 : ℝ)^65 ≤ (3698911331229/10000000000000 : ℝ)^49 := by
    have hnat : (4724917027 : ℕ)^65*10000000000000^49 ≤ 3698911331229^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4724917027 10000000000 3698911331229 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253009137/500000000 : ℝ)^65 ≤ (506381023707/1250000000000 : ℝ)^49 := by
    have hnat : (253009137 : ℕ)^65*1250000000000^49 ≤ 506381023707^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253009137 500000000 506381023707 1250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1624131453/5000000000 : ℝ), (4724917027/10000000000 : ℝ), (253009137/500000000 : ℝ)] ![(2812550597433/12500000000000 : ℝ), (3698911331229/10000000000000 : ℝ), (506381023707/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1624131453/5000000000 : ℝ)|^65 ≤ (2812550597433/12500000000000 : ℝ)^49
        have hw : |(1624131453/5000000000 : ℝ)|=(1624131453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4724917027/10000000000 : ℝ)|^65 ≤ (3698911331229/10000000000000 : ℝ)^49
        have hw : |(4724917027/10000000000 : ℝ)|=(4724917027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(253009137/500000000 : ℝ)|^65 ≤ (506381023707/1250000000000 : ℝ)^49
        have hw : |(253009137/500000000 : ℝ)|=(253009137/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s2_s2_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2313966019/10000000000 : ℝ)*x 0 + (4824499091/10000000000 : ℝ)*x 1 + (5716584101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2313966019/10000000000 : ℝ)^65 ≤ (14348287544309/100000000000000 : ℝ)^49 := by
    have hnat : (2313966019 : ℕ)^65*100000000000000^49 ≤ 14348287544309^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313966019 10000000000 14348287544309 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4824499091/10000000000 : ℝ)^65 ≤ (7605358438911/20000000000000 : ℝ)^49 := by
    have hnat : (4824499091 : ℕ)^65*20000000000000^49 ≤ 7605358438911^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4824499091 10000000000 7605358438911 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5716584101/10000000000 : ℝ)^65 ≤ (1190623006341/2500000000000 : ℝ)^49 := by
    have hnat : (5716584101 : ℕ)^65*2500000000000^49 ≤ 1190623006341^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5716584101 10000000000 1190623006341 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2313966019/10000000000 : ℝ), (4824499091/10000000000 : ℝ), (5716584101/10000000000 : ℝ)] ![(14348287544309/100000000000000 : ℝ), (7605358438911/20000000000000 : ℝ), (1190623006341/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2313966019/10000000000 : ℝ)|^65 ≤ (14348287544309/100000000000000 : ℝ)^49
        have hw : |(-2313966019/10000000000 : ℝ)|=(2313966019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4824499091/10000000000 : ℝ)|^65 ≤ (7605358438911/20000000000000 : ℝ)^49
        have hw : |(4824499091/10000000000 : ℝ)|=(4824499091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5716584101/10000000000 : ℝ)|^65 ≤ (1190623006341/2500000000000 : ℝ)^49
        have hw : |(5716584101/10000000000 : ℝ)|=(5716584101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s2_s2_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1271671711/2000000000 : ℝ)*x 0 + (13175341/10000000000 : ℝ)*x 1 + (1372578423/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1271671711/2000000000 : ℝ)^65 ≤ (54844255051939/100000000000000 : ℝ)^49 := by
    have hnat : (1271671711 : ℕ)^65*100000000000000^49 ≤ 54844255051939^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271671711 2000000000 54844255051939 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13175341/10000000000 : ℝ)^65 ≤ (15110399353/100000000000000 : ℝ)^49 := by
    have hnat : (13175341 : ℕ)^65*100000000000000^49 ≤ 15110399353^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13175341 10000000000 15110399353 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372578423/2500000000 : ℝ)^65 ≤ (361125076317/800000000000 : ℝ)^49 := by
    have hnat : (1372578423 : ℕ)^65*800000000000^49 ≤ 361125076317^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372578423 2500000000 361125076317 800000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1271671711/2000000000 : ℝ), (13175341/10000000000 : ℝ), (1372578423/2500000000 : ℝ)] ![(54844255051939/100000000000000 : ℝ), (15110399353/100000000000000 : ℝ), (361125076317/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1271671711/2000000000 : ℝ)|^65 ≤ (54844255051939/100000000000000 : ℝ)^49
        have hw : |(1271671711/2000000000 : ℝ)|=(1271671711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13175341/10000000000 : ℝ)|^65 ≤ (15110399353/100000000000000 : ℝ)^49
        have hw : |(13175341/10000000000 : ℝ)|=(13175341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372578423/2500000000 : ℝ)|^65 ≤ (361125076317/800000000000 : ℝ)^49
        have hw : |(1372578423/2500000000 : ℝ)|=(1372578423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s2_s2_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2741535527/10000000000 : ℝ)*x 0 + (7905874387/10000000000 : ℝ)*x 1 + (-1602472507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2741535527/10000000000 : ℝ)^65 ≤ (8983626333001/50000000000000 : ℝ)^49 := by
    have hnat : (2741535527 : ℕ)^65*50000000000000^49 ≤ 8983626333001^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741535527 10000000000 8983626333001 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7905874387/10000000000 : ℝ)^65 ≤ (36609806684921/50000000000000 : ℝ)^49 := by
    have hnat : (7905874387 : ℕ)^65*50000000000000^49 ≤ 36609806684921^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7905874387 10000000000 36609806684921 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1602472507/10000000000 : ℝ)^65 ≤ (8813133946859/100000000000000 : ℝ)^49 := by
    have hnat : (1602472507 : ℕ)^65*100000000000000^49 ≤ 8813133946859^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602472507 10000000000 8813133946859 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2741535527/10000000000 : ℝ), (7905874387/10000000000 : ℝ), (-1602472507/10000000000 : ℝ)] ![(8983626333001/50000000000000 : ℝ), (36609806684921/50000000000000 : ℝ), (8813133946859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2741535527/10000000000 : ℝ)|^65 ≤ (8983626333001/50000000000000 : ℝ)^49
        have hw : |(2741535527/10000000000 : ℝ)|=(2741535527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7905874387/10000000000 : ℝ)|^65 ≤ (36609806684921/50000000000000 : ℝ)^49
        have hw : |(7905874387/10000000000 : ℝ)|=(7905874387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1602472507/10000000000 : ℝ)|^65 ≤ (8813133946859/100000000000000 : ℝ)^49
        have hw : |(-1602472507/10000000000 : ℝ)|=(1602472507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s2_s2_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (797674223/2500000000 : ℝ)*x 0 + (2498328603/5000000000 : ℝ)*x 1 + (4840079387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (797674223/2500000000 : ℝ)^65 ≤ (21972981697231/100000000000000 : ℝ)^49 := by
    have hnat : (797674223 : ℕ)^65*100000000000000^49 ≤ 21972981697231^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797674223 2500000000 21972981697231 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2498328603/5000000000 : ℝ)^65 ≤ (39837236760003/100000000000000 : ℝ)^49 := by
    have hnat : (2498328603 : ℕ)^65*100000000000000^49 ≤ 39837236760003^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498328603 5000000000 39837236760003 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4840079387/10000000000 : ℝ)^65 ≤ (19094890766979/50000000000000 : ℝ)^49 := by
    have hnat : (4840079387 : ℕ)^65*50000000000000^49 ≤ 19094890766979^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4840079387 10000000000 19094890766979 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(797674223/2500000000 : ℝ), (2498328603/5000000000 : ℝ), (4840079387/10000000000 : ℝ)] ![(21972981697231/100000000000000 : ℝ), (39837236760003/100000000000000 : ℝ), (19094890766979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(797674223/2500000000 : ℝ)|^65 ≤ (21972981697231/100000000000000 : ℝ)^49
        have hw : |(797674223/2500000000 : ℝ)|=(797674223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2498328603/5000000000 : ℝ)|^65 ≤ (39837236760003/100000000000000 : ℝ)^49
        have hw : |(2498328603/5000000000 : ℝ)|=(2498328603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4840079387/10000000000 : ℝ)|^65 ≤ (19094890766979/50000000000000 : ℝ)^49
        have hw : |(4840079387/10000000000 : ℝ)|=(4840079387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s2_s2_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-971231259/10000000000 : ℝ)*x 0 + (846910901/2500000000 : ℝ)*x 1 + (7779752651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (971231259/10000000000 : ℝ)^65 ≤ (1133946345791/25000000000000 : ℝ)^49 := by
    have hnat : (971231259 : ℕ)^65*25000000000000^49 ≤ 1133946345791^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971231259 10000000000 1133946345791 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846910901/2500000000 : ℝ)^65 ≤ (5947506642203/25000000000000 : ℝ)^49 := by
    have hnat : (846910901 : ℕ)^65*25000000000000^49 ≤ 5947506642203^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846910901 2500000000 5947506642203 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7779752651/10000000000 : ℝ)^65 ≤ (71674188030897/100000000000000 : ℝ)^49 := by
    have hnat : (7779752651 : ℕ)^65*100000000000000^49 ≤ 71674188030897^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7779752651 10000000000 71674188030897 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-971231259/10000000000 : ℝ), (846910901/2500000000 : ℝ), (7779752651/10000000000 : ℝ)] ![(1133946345791/25000000000000 : ℝ), (5947506642203/25000000000000 : ℝ), (71674188030897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-971231259/10000000000 : ℝ)|^65 ≤ (1133946345791/25000000000000 : ℝ)^49
        have hw : |(-971231259/10000000000 : ℝ)|=(971231259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846910901/2500000000 : ℝ)|^65 ≤ (5947506642203/25000000000000 : ℝ)^49
        have hw : |(846910901/2500000000 : ℝ)|=(846910901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7779752651/10000000000 : ℝ)|^65 ≤ (71674188030897/100000000000000 : ℝ)^49
        have hw : |(7779752651/10000000000 : ℝ)|=(7779752651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s2_s2_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4318544409/5000000000 : ℝ)*x 0 + (-92535329/5000000000 : ℝ)*x 1 + (2648281729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318544409/5000000000 : ℝ)^65 ≤ (82335928819623/100000000000000 : ℝ)^49 := by
    have hnat : (4318544409 : ℕ)^65*100000000000000^49 ≤ 82335928819623^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318544409 5000000000 82335928819623 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92535329/5000000000 : ℝ)^65 ≤ (503002617089/100000000000000 : ℝ)^49 := by
    have hnat : (92535329 : ℕ)^65*100000000000000^49 ≤ 503002617089^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92535329 5000000000 503002617089 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2648281729/10000000000 : ℝ)^65 ≤ (17161068547989/100000000000000 : ℝ)^49 := by
    have hnat : (2648281729 : ℕ)^65*100000000000000^49 ≤ 17161068547989^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648281729 10000000000 17161068547989 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318544409/5000000000 : ℝ), (-92535329/5000000000 : ℝ), (2648281729/10000000000 : ℝ)] ![(82335928819623/100000000000000 : ℝ), (503002617089/100000000000000 : ℝ), (17161068547989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318544409/5000000000 : ℝ)|^65 ≤ (82335928819623/100000000000000 : ℝ)^49
        have hw : |(4318544409/5000000000 : ℝ)|=(4318544409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-92535329/5000000000 : ℝ)|^65 ≤ (503002617089/100000000000000 : ℝ)^49
        have hw : |(-92535329/5000000000 : ℝ)|=(92535329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2648281729/10000000000 : ℝ)|^65 ≤ (17161068547989/100000000000000 : ℝ)^49
        have hw : |(2648281729/10000000000 : ℝ)|=(2648281729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s2_s2_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4124651123/10000000000 : ℝ)*x 0 + (6990959173/10000000000 : ℝ)*x 1 + (-333628853/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4124651123/10000000000 : ℝ)^65 ≤ (30888681735659/100000000000000 : ℝ)^49 := by
    have hnat : (4124651123 : ℕ)^65*100000000000000^49 ≤ 30888681735659^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124651123 10000000000 30888681735659 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6990959173/10000000000 : ℝ)^65 ≤ (777469344473/1250000000000 : ℝ)^49 := by
    have hnat : (6990959173 : ℕ)^65*1250000000000^49 ≤ 777469344473^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6990959173 10000000000 777469344473 1250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (333628853/2500000000 : ℝ)^65 ≤ (6913770691851/100000000000000 : ℝ)^49 := by
    have hnat : (333628853 : ℕ)^65*100000000000000^49 ≤ 6913770691851^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333628853 2500000000 6913770691851 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4124651123/10000000000 : ℝ), (6990959173/10000000000 : ℝ), (-333628853/2500000000 : ℝ)] ![(30888681735659/100000000000000 : ℝ), (777469344473/1250000000000 : ℝ), (6913770691851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4124651123/10000000000 : ℝ)|^65 ≤ (30888681735659/100000000000000 : ℝ)^49
        have hw : |(4124651123/10000000000 : ℝ)|=(4124651123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6990959173/10000000000 : ℝ)|^65 ≤ (777469344473/1250000000000 : ℝ)^49
        have hw : |(6990959173/10000000000 : ℝ)|=(6990959173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-333628853/2500000000 : ℝ)|^65 ≤ (6913770691851/100000000000000 : ℝ)^49
        have hw : |(-333628853/2500000000 : ℝ)|=(333628853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s2_s2_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2689050417/10000000000 : ℝ)*x 0 + (3565616721/10000000000 : ℝ)*x 1 + (6548081861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689050417/10000000000 : ℝ)^65 ≤ (547262337141/3125000000000 : ℝ)^49 := by
    have hnat : (2689050417 : ℕ)^65*3125000000000^49 ≤ 547262337141^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689050417 10000000000 547262337141 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3565616721/10000000000 : ℝ)^65 ≤ (20369618737/80000000000 : ℝ)^49 := by
    have hnat : (3565616721 : ℕ)^65*80000000000^49 ≤ 20369618737^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3565616721 10000000000 20369618737 80000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6548081861/10000000000 : ℝ)^65 ≤ (28512790887547/50000000000000 : ℝ)^49 := by
    have hnat : (6548081861 : ℕ)^65*50000000000000^49 ≤ 28512790887547^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6548081861 10000000000 28512790887547 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689050417/10000000000 : ℝ), (3565616721/10000000000 : ℝ), (6548081861/10000000000 : ℝ)] ![(547262337141/3125000000000 : ℝ), (20369618737/80000000000 : ℝ), (28512790887547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689050417/10000000000 : ℝ)|^65 ≤ (547262337141/3125000000000 : ℝ)^49
        have hw : |(2689050417/10000000000 : ℝ)|=(2689050417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3565616721/10000000000 : ℝ)|^65 ≤ (20369618737/80000000000 : ℝ)^49
        have hw : |(3565616721/10000000000 : ℝ)|=(3565616721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6548081861/10000000000 : ℝ)|^65 ≤ (28512790887547/50000000000000 : ℝ)^49
        have hw : |(6548081861/10000000000 : ℝ)|=(6548081861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s2_s2_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-793567277/5000000000 : ℝ)*x 0 + (5913923591/10000000000 : ℝ)*x 1 + (2575633089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (793567277/5000000000 : ℝ)^65 ≤ (435070531749/5000000000000 : ℝ)^49 := by
    have hnat : (793567277 : ℕ)^65*5000000000000^49 ≤ 435070531749^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793567277 5000000000 435070531749 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5913923591/10000000000 : ℝ)^65 ≤ (49817983523603/100000000000000 : ℝ)^49 := by
    have hnat : (5913923591 : ℕ)^65*100000000000000^49 ≤ 49817983523603^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5913923591 10000000000 49817983523603 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575633089/5000000000 : ℝ)^65 ≤ (5185075729191/12500000000000 : ℝ)^49 := by
    have hnat : (2575633089 : ℕ)^65*12500000000000^49 ≤ 5185075729191^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575633089 5000000000 5185075729191 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-793567277/5000000000 : ℝ), (5913923591/10000000000 : ℝ), (2575633089/5000000000 : ℝ)] ![(435070531749/5000000000000 : ℝ), (49817983523603/100000000000000 : ℝ), (5185075729191/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-793567277/5000000000 : ℝ)|^65 ≤ (435070531749/5000000000000 : ℝ)^49
        have hw : |(-793567277/5000000000 : ℝ)|=(793567277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5913923591/10000000000 : ℝ)|^65 ≤ (49817983523603/100000000000000 : ℝ)^49
        have hw : |(5913923591/10000000000 : ℝ)|=(5913923591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575633089/5000000000 : ℝ)|^65 ≤ (5185075729191/12500000000000 : ℝ)^49
        have hw : |(2575633089/5000000000 : ℝ)|=(2575633089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s2_s2_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1965526441/2500000000 : ℝ)*x 0 + (4571539/5000000000 : ℝ)*x 1 + (469854181/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1965526441/2500000000 : ℝ)^65 ≤ (36341189079983/50000000000000 : ℝ)^49 := by
    have hnat : (1965526441 : ℕ)^65*50000000000000^49 ≤ 36341189079983^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965526441 2500000000 36341189079983 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4571539/5000000000 : ℝ)^65 ≤ (9306707693/100000000000000 : ℝ)^49 := by
    have hnat : (4571539 : ℕ)^65*100000000000000^49 ≤ 9306707693^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4571539 5000000000 9306707693 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (469854181/1250000000 : ℝ)^65 ≤ (27308315122333/100000000000000 : ℝ)^49 := by
    have hnat : (469854181 : ℕ)^65*100000000000000^49 ≤ 27308315122333^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469854181 1250000000 27308315122333 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1965526441/2500000000 : ℝ), (4571539/5000000000 : ℝ), (469854181/1250000000 : ℝ)] ![(36341189079983/50000000000000 : ℝ), (9306707693/100000000000000 : ℝ), (27308315122333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1965526441/2500000000 : ℝ)|^65 ≤ (36341189079983/50000000000000 : ℝ)^49
        have hw : |(1965526441/2500000000 : ℝ)|=(1965526441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4571539/5000000000 : ℝ)|^65 ≤ (9306707693/100000000000000 : ℝ)^49
        have hw : |(4571539/5000000000 : ℝ)|=(4571539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(469854181/1250000000 : ℝ)|^65 ≤ (27308315122333/100000000000000 : ℝ)^49
        have hw : |(469854181/1250000000 : ℝ)|=(469854181/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s2_s2_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3449467157/10000000000 : ℝ)*x 0 + (6992757007/10000000000 : ℝ)*x 1 + (-1099696093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3449467157/10000000000 : ℝ)^65 ≤ (24367663937153/100000000000000 : ℝ)^49 := by
    have hnat : (3449467157 : ℕ)^65*100000000000000^49 ≤ 24367663937153^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3449467157 10000000000 24367663937153 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6992757007/10000000000 : ℝ)^65 ≤ (31109383197843/50000000000000 : ℝ)^49 := by
    have hnat : (6992757007 : ℕ)^65*50000000000000^49 ≤ 31109383197843^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6992757007 10000000000 31109383197843 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099696093/5000000000 : ℝ)^65 ≤ (13413569643129/100000000000000 : ℝ)^49 := by
    have hnat : (1099696093 : ℕ)^65*100000000000000^49 ≤ 13413569643129^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099696093 5000000000 13413569643129 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3449467157/10000000000 : ℝ), (6992757007/10000000000 : ℝ), (-1099696093/5000000000 : ℝ)] ![(24367663937153/100000000000000 : ℝ), (31109383197843/50000000000000 : ℝ), (13413569643129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3449467157/10000000000 : ℝ)|^65 ≤ (24367663937153/100000000000000 : ℝ)^49
        have hw : |(3449467157/10000000000 : ℝ)|=(3449467157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6992757007/10000000000 : ℝ)|^65 ≤ (31109383197843/50000000000000 : ℝ)^49
        have hw : |(6992757007/10000000000 : ℝ)|=(6992757007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1099696093/5000000000 : ℝ)|^65 ≤ (13413569643129/100000000000000 : ℝ)^49
        have hw : |(-1099696093/5000000000 : ℝ)|=(1099696093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s2_s2_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4462359001/10000000000 : ℝ)*x 0 + (4464534091/10000000000 : ℝ)*x 1 + (2088144619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4462359001/10000000000 : ℝ)^65 ≤ (17143780394973/50000000000000 : ℝ)^49 := by
    have hnat : (4462359001 : ℕ)^65*50000000000000^49 ≤ 17143780394973^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4462359001 10000000000 17143780394973 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4464534091/10000000000 : ℝ)^65 ≤ (2144358287497/6250000000000 : ℝ)^49 := by
    have hnat : (4464534091 : ℕ)^65*6250000000000^49 ≤ 2144358287497^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4464534091 10000000000 2144358287497 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2088144619/5000000000 : ℝ)^65 ≤ (31402706589073/100000000000000 : ℝ)^49 := by
    have hnat : (2088144619 : ℕ)^65*100000000000000^49 ≤ 31402706589073^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088144619 5000000000 31402706589073 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4462359001/10000000000 : ℝ), (4464534091/10000000000 : ℝ), (2088144619/5000000000 : ℝ)] ![(17143780394973/50000000000000 : ℝ), (2144358287497/6250000000000 : ℝ), (31402706589073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4462359001/10000000000 : ℝ)|^65 ≤ (17143780394973/50000000000000 : ℝ)^49
        have hw : |(4462359001/10000000000 : ℝ)|=(4462359001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4464534091/10000000000 : ℝ)|^65 ≤ (2144358287497/6250000000000 : ℝ)^49
        have hw : |(4464534091/10000000000 : ℝ)|=(4464534091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2088144619/5000000000 : ℝ)|^65 ≤ (31402706589073/100000000000000 : ℝ)^49
        have hw : |(2088144619/5000000000 : ℝ)|=(2088144619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301083_s2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((69133/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69133/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((37611/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(37611/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19829/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19829/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((48667/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48667/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((11897/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(11897/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27193/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27193/50000 : ℝ)*X 1 2) := by
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
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (69133/100000 : ℝ) ^ (129/32 : ℝ) ≤ (22580407863042297109/100000000000000000000 : ℝ) := by
    have hpowers : (69133/100000 : ℝ)^129 ≤ (22580407863042297109/100000000000000000000 : ℝ)^32 := by
      have hnat : (69133 : ℕ)^129*100000000000000000000^32 ≤ 22580407863042297109^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69133 100000 22580407863042297109 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69133/100000 : ℝ)) (X := (22580407863042297109/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (122580407863042297109/100000000000000000000 : ℝ) ≤ (10518017931166653/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (122580407863042297109/100000000000000000000 : ℝ)^32 ≤ (10518017931166653/10000000000000000 : ℝ)^129 := by
      have hnat : (122580407863042297109 : ℕ)^32*10000000000000000^129 ≤ 10518017931166653^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        122580407863042297109 100000000000000000000 10518017931166653 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10518017931166653/10000000000000000 : ℝ)) (X := (122580407863042297109/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (72580407863042297109/50000000000000000000 : ℝ) ≤ (2193707318153581/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (72580407863042297109/50000000000000000000 : ℝ)^32 ≤ (2193707318153581/2000000000000000 : ℝ)^129 := by
      have hnat : (72580407863042297109 : ℕ)^32*2000000000000000^129 ≤ 2193707318153581^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72580407863042297109 50000000000000000000 2193707318153581 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2193707318153581/2000000000000000 : ℝ)) (X := (72580407863042297109/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(518017931166653/6913300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(112629664900313/1728325000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (69133/100000 : ℝ)) (alpha := (518017931166653/6913300000000000 : ℝ)) (beta := (112629664900313/1728325000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (69133/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(518017931166653/6913300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(112629664900313/1728325000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (37611/50000 : ℝ) ^ (129/32 : ℝ) ≤ (31733303280602708737/100000000000000000000 : ℝ) := by
    have hpowers : (37611/50000 : ℝ)^129 ≤ (31733303280602708737/100000000000000000000 : ℝ)^32 := by
      have hnat : (37611 : ℕ)^129*100000000000000000000^32 ≤ 31733303280602708737^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37611 50000 31733303280602708737 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37611/50000 : ℝ)) (X := (31733303280602708737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (131733303280602708737/100000000000000000000 : ℝ) ≤ (10707594780842203/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (131733303280602708737/100000000000000000000 : ℝ)^32 ≤ (10707594780842203/10000000000000000 : ℝ)^129 := by
      have hnat : (131733303280602708737 : ℕ)^32*10000000000000000^129 ≤ 10707594780842203^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        131733303280602708737 100000000000000000000 10707594780842203 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10707594780842203/10000000000000000 : ℝ)) (X := (131733303280602708737/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (81733303280602708737/50000000000000000000 : ℝ) ≤ (2824123263331019/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (81733303280602708737/50000000000000000000 : ℝ)^32 ≤ (2824123263331019/2500000000000000 : ℝ)^129 := by
      have hnat : (81733303280602708737 : ℕ)^32*2500000000000000^129 ≤ 2824123263331019^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81733303280602708737 50000000000000000000 2824123263331019 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2824123263331019/2500000000000000 : ℝ)) (X := (81733303280602708737/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(235864926947401/2507400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(588898272481873/7522200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (37611/50000 : ℝ)) (alpha := (235864926947401/2507400000000000 : ℝ)) (beta := (588898272481873/7522200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (37611/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(235864926947401/2507400000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(588898272481873/7522200000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (19829/25000 : ℝ) ^ (129/32 : ℝ) ≤ (39291466768408073781/100000000000000000000 : ℝ) := by
    have hpowers : (19829/25000 : ℝ)^129 ≤ (39291466768408073781/100000000000000000000 : ℝ)^32 := by
      have hnat : (19829 : ℕ)^129*100000000000000000000^32 ≤ 39291466768408073781^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19829 25000 39291466768408073781 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19829/25000 : ℝ)) (X := (39291466768408073781/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (139291466768408073781/100000000000000000000 : ℝ) ≤ (217136183463569/200000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (139291466768408073781/100000000000000000000 : ℝ)^32 ≤ (217136183463569/200000000000000 : ℝ)^129 := by
      have hnat : (139291466768408073781 : ℕ)^32*200000000000000^129 ≤ 217136183463569^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        139291466768408073781 100000000000000000000 217136183463569 200000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (217136183463569/200000000000000 : ℝ)) (X := (139291466768408073781/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (89291466768408073781/50000000000000000000 : ℝ) ≤ (5773536697405383/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (89291466768408073781/50000000000000000000 : ℝ)^32 ≤ (5773536697405383/5000000000000000 : ℝ)^129 := by
      have hnat : (89291466768408073781 : ℕ)^32*5000000000000000^129 ≤ 5773536697405383^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89291466768408073781 50000000000000000000 5773536697405383 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5773536697405383/5000000000000000 : ℝ)) (X := (89291466768408073781/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(17136183463569/158632000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(172566055408079/1982900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (19829/25000 : ℝ)) (alpha := (17136183463569/158632000000000 : ℝ)) (beta := (172566055408079/1982900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (19829/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(17136183463569/158632000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(172566055408079/1982900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-2229822767/10000000000 : ℝ)*X 0 0+(1012356533/2000000000 : ℝ)*X 0 1+(1387944317/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((234381847/625000000 : ℝ)*X 2 0+(1323230643/2000000000 : ℝ)*X 2 1+(-2388242657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((1624131453/5000000000 : ℝ)*X 0 0+(4724917027/10000000000 : ℝ)*X 0 1+(253009137/500000000 : ℝ)*X 0 2+(1624131453/5000000000 : ℝ)*X 1 0+(4724917027/10000000000 : ℝ)*X 1 1+(253009137/500000000 : ℝ)*X 1 2+(1624131453/5000000000 : ℝ)*X 2 0+(4724917027/10000000000 : ℝ)*X 2 1+(253009137/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-2313966019/10000000000 : ℝ)*X 0 0+(4824499091/10000000000 : ℝ)*X 0 1+(5716584101/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1271671711/2000000000 : ℝ)*X 1 0+(13175341/10000000000 : ℝ)*X 1 1+(1372578423/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2741535527/10000000000 : ℝ)*X 2 0+(7905874387/10000000000 : ℝ)*X 2 1+(-1602472507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((797674223/2500000000 : ℝ)*X 0 0+(2498328603/5000000000 : ℝ)*X 0 1+(4840079387/10000000000 : ℝ)*X 0 2+(797674223/2500000000 : ℝ)*X 1 0+(2498328603/5000000000 : ℝ)*X 1 1+(4840079387/10000000000 : ℝ)*X 1 2+(797674223/2500000000 : ℝ)*X 2 0+(2498328603/5000000000 : ℝ)*X 2 1+(4840079387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-971231259/10000000000 : ℝ)*X 0 0+(846910901/2500000000 : ℝ)*X 0 1+(7779752651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4318544409/5000000000 : ℝ)*X 1 0+(-92535329/5000000000 : ℝ)*X 1 1+(2648281729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((4124651123/10000000000 : ℝ)*X 2 0+(6990959173/10000000000 : ℝ)*X 2 1+(-333628853/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((2689050417/10000000000 : ℝ)*X 0 0+(3565616721/10000000000 : ℝ)*X 0 1+(6548081861/10000000000 : ℝ)*X 0 2+(2689050417/10000000000 : ℝ)*X 1 0+(3565616721/10000000000 : ℝ)*X 1 1+(6548081861/10000000000 : ℝ)*X 1 2+(2689050417/10000000000 : ℝ)*X 2 0+(3565616721/10000000000 : ℝ)*X 2 1+(6548081861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-793567277/5000000000 : ℝ)*X 0 0+(5913923591/10000000000 : ℝ)*X 0 1+(2575633089/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1965526441/2500000000 : ℝ)*X 1 0+(4571539/5000000000 : ℝ)*X 1 1+(469854181/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((3449467157/10000000000 : ℝ)*X 2 0+(6992757007/10000000000 : ℝ)*X 2 1+(-1099696093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((4462359001/10000000000 : ℝ)*X 0 0+(4464534091/10000000000 : ℝ)*X 0 1+(2088144619/5000000000 : ℝ)*X 0 2+(4462359001/10000000000 : ℝ)*X 1 0+(4464534091/10000000000 : ℝ)*X 1 1+(2088144619/5000000000 : ℝ)*X 1 2+(4462359001/10000000000 : ℝ)*X 2 0+(4464534091/10000000000 : ℝ)*X 2 1+(2088144619/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((48667/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48667/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (458152574132097407769525891791/38191553840020000000000000000000000 : ℝ) := by norm_num
    linear_combination (244239629683/1000000000000 : ℝ)*(base7) + (10602077/1000000000000 : ℝ)*(base23) + (290657660343/500000000000 : ℝ)*(base49) + (306341756277/1000000000000 : ℝ)*(base60) + (644045705367/200000000000 : ℝ)*(major_s2_0) + (644045705367/200000000000 : ℝ)*(major_s2_1) + (644045705367/200000000000 : ℝ)*(major_s2_2) + (183013517/500000000000 : ℝ)*(sp_s2_0) + (80562677/500000000000 : ℝ)*(sp_s2_6) + (4112673232993/1000000000000 : ℝ)*(sp_s2_7) + (4113068119531/1000000000000 : ℝ)*(sp_s2_8) + (2056528758727/500000000000 : ℝ)*(sp_s2_9) + (2421026482233/1000000000000 : ℝ)*(sp_s2_13) + (1803719/62500000000 : ℝ)*(sp_s2_14) + (136059248619/62500000000 : ℝ)*(f.failure) + (4113068119531/1000000000000 : ℝ)*(f.sum) + (104805445130292803/4971923460000000000000000000000 : ℝ)*base62 + (129066515203183/396580000000000000000000000 : ℝ)*base65 + (28122323034149/167160000000000000000000000 : ℝ)*base67 + (28112453167167/158632000000000000000000000 : ℝ)*base69 + (255239367018697247/2741676514000000000000000000000 : ℝ)*base71 + (159151496368203/691330000000000000000000000 : ℝ)*base73 + (89763764760139/501480000000000000000000000 : ℝ)*base75 + (258999260323087/1382660000000000000000000000 : ℝ)*base77 + (65819668672114709/462250891200000000000000000000 : ℝ)*base79 + (897/3125000000000000 : ℝ)*base86 + (897/3125000000000000 : ℝ)*base88 + (897/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((11897/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(11897/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (296532855529594157093055619/43336021050000000000000000000000 : ℝ) := by norm_num
    linear_combination (3894417/1000000000000 : ℝ)*(base21) + (318509/50000000000 : ℝ)*(base33) + (359034179857/500000000000 : ℝ)*(base40) + (511939444479/1000000000000 : ℝ)*(base49) + (17934464867/31250000000 : ℝ)*(base60) + (2641174164519/1000000000000 : ℝ)*(major_s2_0) + (26411805347/10000000000 : ℝ)*(major_s2_1) + (26411805347/10000000000 : ℝ)*(major_s2_2) + (60411/10000000000 : ℝ)*(sp_s2_2) + (437107558579/125000000000 : ℝ)*(sp_s2_14) + (87420218849/25000000000 : ℝ)*(sp_s2_15) + (699368832587/200000000000 : ℝ)*(sp_s2_16) + (44637457997/25000000000 : ℝ)*(sp_s2_20) + (11336123/250000000000 : ℝ)*(sp_s2_22) + (44637457997/25000000000 : ℝ)*(f.failure) + (437107558579/125000000000 : ℝ)*(f.sum) + (2264821819199452481/3728942595000000000000000000000 : ℝ)*base63 + (35025782156349/99145000000000000000000000 : ℝ)*base65 + (66843098881591/125370000000000000000000000 : ℝ)*base67 + (87363574776737/198290000000000000000000000 : ℝ)*base68 + (61410633599905998517/137083825700000000000000000000000 : ℝ)*base70 + (1457539375540727/1728325000000000000000000000 : ℝ)*base73 + (2156377338653/37611000000000000000000000 : ℝ)*base75 + (2507303373202643/6913300000000000000000000000 : ℝ)*base76 + (31727933484843258053/43336021050000000000000000000000 : ℝ)*base79 + (91/312500000000000 : ℝ)*base87 + (443/625000000000000 : ℝ)*base88 + (443/625000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27193/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27193/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1356349948723316411797152949373/95478884600050000000000000000000000 : ℝ) := by norm_num
    linear_combination (115877292197/1000000000000 : ℝ)*(base7) + (327858762791/500000000000 : ℝ)*(base40) + (672355014911/1000000000000 : ℝ)*(base49) + (58721/15625000000 : ℝ)*(base60) + (4282020161049/1000000000000 : ℝ)*(major_s2_0) + (4282020161049/1000000000000 : ℝ)*(major_s2_1) + (4282020161049/1000000000000 : ℝ)*(major_s2_2) + (6140401/500000000000 : ℝ)*(sp_s2_8) + (3830007/200000000000 : ℝ)*(sp_s2_9) + (71669069/1000000000000 : ℝ)*(sp_s2_16) + (5597918772081/1000000000000 : ℝ)*(sp_s2_21) + (5597906491279/1000000000000 : ℝ)*(sp_s2_22) + (5597827952977/1000000000000 : ℝ)*(sp_s2_23) + (1505310323801/500000000000 : ℝ)*(sp_s2_27) + (578948671081/200000000000 : ℝ)*(f.failure) + (5597918772081/1000000000000 : ℝ)*(f.sum) + (3032284147520727917/24859617300000000000000000000000 : ℝ)*base63 + (294655903748499/1982900000000000000000000000 : ℝ)*base64 + (184060642183363/835800000000000000000000000 : ℝ)*base67 + (484832013645117/793160000000000000000000000 : ℝ)*base69 + (765065929759854363/1070967388281250000000000000000 : ℝ)*base70 + (1080457749244547/1728325000000000000000000000 : ℝ)*base73 + (292295266081279/2507400000000000000000000000 : ℝ)*base74 + (1094846392797993/6913300000000000000000000000 : ℝ)*base76 + (25115385076440788683/57781361400000000000000000000000 : ℝ)*base79 + (1461/5000000000000000 : ℝ)*base87 + (1461/5000000000000000 : ℝ)*base89 + (1461/5000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((69133/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69133/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((37611/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(37611/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19829/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19829/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((48667/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48667/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((11897/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(11897/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27193/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27193/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301083_s2 p hpa hpb X hX hprev1

#print axioms solution

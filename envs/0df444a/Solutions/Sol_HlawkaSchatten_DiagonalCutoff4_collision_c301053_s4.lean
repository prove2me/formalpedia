-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301053_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:30:28.207743+00:00
-- url     : https://prove2.me/submissions/feb74908-5d3d-4102-84b1-8457220a64c3

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
theorem collision_support_c301053_s4_s4_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1920232429/10000000000 : ℝ)*x 0 + (2665119889/5000000000 : ℝ)*x 1 + (1102697079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1920232429/10000000000 : ℝ)^65 ≤ (140041543987/1250000000000 : ℝ)^49 := by
    have hnat : (1920232429 : ℕ)^65*1250000000000^49 ≤ 140041543987^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920232429 10000000000 140041543987 1250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2665119889/5000000000 : ℝ)^65 ≤ (2170157219641/5000000000000 : ℝ)^49 := by
    have hnat : (2665119889 : ℕ)^65*5000000000000^49 ≤ 2170157219641^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2665119889 5000000000 2170157219641 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102697079/2000000000 : ℝ)^65 ≤ (177318484671/390625000000 : ℝ)^49 := by
    have hnat : (1102697079 : ℕ)^65*390625000000^49 ≤ 177318484671^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102697079 2000000000 177318484671 390625000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1920232429/10000000000 : ℝ), (2665119889/5000000000 : ℝ), (1102697079/2000000000 : ℝ)] ![(140041543987/1250000000000 : ℝ), (2170157219641/5000000000000 : ℝ), (177318484671/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1920232429/10000000000 : ℝ)|^65 ≤ (140041543987/1250000000000 : ℝ)^49
        have hw : |(-1920232429/10000000000 : ℝ)|=(1920232429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2665119889/5000000000 : ℝ)|^65 ≤ (2170157219641/5000000000000 : ℝ)^49
        have hw : |(2665119889/5000000000 : ℝ)|=(2665119889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1102697079/2000000000 : ℝ)|^65 ≤ (177318484671/390625000000 : ℝ)^49
        have hw : |(1102697079/2000000000 : ℝ)|=(1102697079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s4_s4_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (875286479/2000000000 : ℝ)*x 0 + (-541660791/5000000000 : ℝ)*x 1 + (345919493/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875286479/2000000000 : ℝ)^65 ≤ (33414501863357/100000000000000 : ℝ)^49 := by
    have hnat : (875286479 : ℕ)^65*100000000000000^49 ≤ 33414501863357^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875286479 2000000000 33414501863357 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541660791/5000000000 : ℝ)^65 ≤ (5242955077081/100000000000000 : ℝ)^49 := by
    have hnat : (541660791 : ℕ)^65*100000000000000^49 ≤ 5242955077081^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541660791 5000000000 5242955077081 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345919493/500000000 : ℝ)^65 ≤ (61342543048751/100000000000000 : ℝ)^49 := by
    have hnat : (345919493 : ℕ)^65*100000000000000^49 ≤ 61342543048751^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345919493 500000000 61342543048751 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875286479/2000000000 : ℝ), (-541660791/5000000000 : ℝ), (345919493/500000000 : ℝ)] ![(33414501863357/100000000000000 : ℝ), (5242955077081/100000000000000 : ℝ), (61342543048751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875286479/2000000000 : ℝ)|^65 ≤ (33414501863357/100000000000000 : ℝ)^49
        have hw : |(875286479/2000000000 : ℝ)|=(875286479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-541660791/5000000000 : ℝ)|^65 ≤ (5242955077081/100000000000000 : ℝ)^49
        have hw : |(-541660791/5000000000 : ℝ)|=(541660791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(345919493/500000000 : ℝ)|^65 ≤ (61342543048751/100000000000000 : ℝ)^49
        have hw : |(345919493/500000000 : ℝ)|=(345919493/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s4_s4_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-393417131/2000000000 : ℝ)*x 0 + (453060413/1250000000 : ℝ)*x 1 + (7009077763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393417131/2000000000 : ℝ)^65 ≤ (11567378638929/100000000000000 : ℝ)^49 := by
    have hnat : (393417131 : ℕ)^65*100000000000000^49 ≤ 11567378638929^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393417131 2000000000 11567378638929 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453060413/1250000000 : ℝ)^65 ≤ (26021148661501/100000000000000 : ℝ)^49 := by
    have hnat : (453060413 : ℕ)^65*100000000000000^49 ≤ 26021148661501^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453060413 1250000000 26021148661501 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7009077763/10000000000 : ℝ)^65 ≤ (7801434085073/12500000000000 : ℝ)^49 := by
    have hnat : (7009077763 : ℕ)^65*12500000000000^49 ≤ 7801434085073^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7009077763 10000000000 7801434085073 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393417131/2000000000 : ℝ), (453060413/1250000000 : ℝ), (7009077763/10000000000 : ℝ)] ![(11567378638929/100000000000000 : ℝ), (26021148661501/100000000000000 : ℝ), (7801434085073/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393417131/2000000000 : ℝ)|^65 ≤ (11567378638929/100000000000000 : ℝ)^49
        have hw : |(-393417131/2000000000 : ℝ)|=(393417131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(453060413/1250000000 : ℝ)|^65 ≤ (26021148661501/100000000000000 : ℝ)^49
        have hw : |(453060413/1250000000 : ℝ)|=(453060413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7009077763/10000000000 : ℝ)|^65 ≤ (7801434085073/12500000000000 : ℝ)^49
        have hw : |(7009077763/10000000000 : ℝ)|=(7009077763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s4_s4_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (668644433/2500000000 : ℝ)*x 0 + (-331324961/10000000000 : ℝ)*x 1 + (535797357/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668644433/2500000000 : ℝ)^65 ≤ (8693737573001/50000000000000 : ℝ)^49 := by
    have hnat : (668644433 : ℕ)^65*50000000000000^49 ≤ 8693737573001^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668644433 2500000000 8693737573001 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (331324961/10000000000 : ℝ)^65 ≤ (54455511697/5000000000000 : ℝ)^49 := by
    have hnat : (331324961 : ℕ)^65*5000000000000^49 ≤ 54455511697^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331324961 10000000000 54455511697 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535797357/625000000 : ℝ)^65 ≤ (81523414598991/100000000000000 : ℝ)^49 := by
    have hnat : (535797357 : ℕ)^65*100000000000000^49 ≤ 81523414598991^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535797357 625000000 81523414598991 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668644433/2500000000 : ℝ), (-331324961/10000000000 : ℝ), (535797357/625000000 : ℝ)] ![(8693737573001/50000000000000 : ℝ), (54455511697/5000000000000 : ℝ), (81523414598991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668644433/2500000000 : ℝ)|^65 ≤ (8693737573001/50000000000000 : ℝ)^49
        have hw : |(668644433/2500000000 : ℝ)|=(668644433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-331324961/10000000000 : ℝ)|^65 ≤ (54455511697/5000000000000 : ℝ)^49
        have hw : |(-331324961/10000000000 : ℝ)|=(331324961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(535797357/625000000 : ℝ)|^65 ≤ (81523414598991/100000000000000 : ℝ)^49
        have hw : |(535797357/625000000 : ℝ)|=(535797357/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s4_s4_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1347090037/5000000000 : ℝ)*x 0 + (8560131069/10000000000 : ℝ)*x 1 + (-329027937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347090037/5000000000 : ℝ)^65 ≤ (17556723731717/100000000000000 : ℝ)^49 := by
    have hnat : (1347090037 : ℕ)^65*100000000000000^49 ≤ 17556723731717^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347090037 5000000000 17556723731717 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8560131069/10000000000 : ℝ)^65 ≤ (16272834161571/20000000000000 : ℝ)^49 := by
    have hnat : (8560131069 : ℕ)^65*20000000000000^49 ≤ 16272834161571^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8560131069 10000000000 16272834161571 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329027937/10000000000 : ℝ)^65 ≤ (8632843571/800000000000 : ℝ)^49 := by
    have hnat : (329027937 : ℕ)^65*800000000000^49 ≤ 8632843571^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329027937 10000000000 8632843571 800000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347090037/5000000000 : ℝ), (8560131069/10000000000 : ℝ), (-329027937/10000000000 : ℝ)] ![(17556723731717/100000000000000 : ℝ), (16272834161571/20000000000000 : ℝ), (8632843571/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347090037/5000000000 : ℝ)|^65 ≤ (17556723731717/100000000000000 : ℝ)^49
        have hw : |(1347090037/5000000000 : ℝ)|=(1347090037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8560131069/10000000000 : ℝ)|^65 ≤ (16272834161571/20000000000000 : ℝ)^49
        have hw : |(8560131069/10000000000 : ℝ)|=(8560131069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-329027937/10000000000 : ℝ)|^65 ≤ (8632843571/800000000000 : ℝ)^49
        have hw : |(-329027937/10000000000 : ℝ)|=(329027937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s4_s4_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6204601297/10000000000 : ℝ)*x 0 + (552830173/1000000000 : ℝ)*x 1 + (78023987/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6204601297/10000000000 : ℝ)^65 ≤ (13272985625691/25000000000000 : ℝ)^49 := by
    have hnat : (6204601297 : ℕ)^65*25000000000000^49 ≤ 13272985625691^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6204601297 10000000000 13272985625691 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552830173/1000000000 : ℝ)^65 ≤ (22777710325331/50000000000000 : ℝ)^49 := by
    have hnat : (552830173 : ℕ)^65*50000000000000^49 ≤ 22777710325331^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552830173 1000000000 22777710325331 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78023987/2000000000 : ℝ)^65 ≤ (270527367243/20000000000000 : ℝ)^49 := by
    have hnat : (78023987 : ℕ)^65*20000000000000^49 ≤ 270527367243^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78023987 2000000000 270527367243 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6204601297/10000000000 : ℝ), (552830173/1000000000 : ℝ), (78023987/2000000000 : ℝ)] ![(13272985625691/25000000000000 : ℝ), (22777710325331/50000000000000 : ℝ), (270527367243/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6204601297/10000000000 : ℝ)|^65 ≤ (13272985625691/25000000000000 : ℝ)^49
        have hw : |(6204601297/10000000000 : ℝ)|=(6204601297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552830173/1000000000 : ℝ)|^65 ≤ (22777710325331/50000000000000 : ℝ)^49
        have hw : |(552830173/1000000000 : ℝ)|=(552830173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(78023987/2000000000 : ℝ)|^65 ≤ (270527367243/20000000000000 : ℝ)^49
        have hw : |(78023987/2000000000 : ℝ)|=(78023987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s4_s4_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-965461989/5000000000 : ℝ)*x 0 + (1090696527/2500000000 : ℝ)*x 1 + (6410137201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (965461989/5000000000 : ℝ)^65 ≤ (564307270121/5000000000000 : ℝ)^49 := by
    have hnat : (965461989 : ℕ)^65*5000000000000^49 ≤ 564307270121^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965461989 5000000000 564307270121 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090696527/2500000000 : ℝ)^65 ≤ (1663818001087/5000000000000 : ℝ)^49 := by
    have hnat : (1090696527 : ℕ)^65*5000000000000^49 ≤ 1663818001087^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090696527 2500000000 1663818001087 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6410137201/10000000000 : ℝ)^65 ≤ (55437494563621/100000000000000 : ℝ)^49 := by
    have hnat : (6410137201 : ℕ)^65*100000000000000^49 ≤ 55437494563621^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6410137201 10000000000 55437494563621 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-965461989/5000000000 : ℝ), (1090696527/2500000000 : ℝ), (6410137201/10000000000 : ℝ)] ![(564307270121/5000000000000 : ℝ), (1663818001087/5000000000000 : ℝ), (55437494563621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-965461989/5000000000 : ℝ)|^65 ≤ (564307270121/5000000000000 : ℝ)^49
        have hw : |(-965461989/5000000000 : ℝ)|=(965461989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090696527/2500000000 : ℝ)|^65 ≤ (1663818001087/5000000000000 : ℝ)^49
        have hw : |(1090696527/2500000000 : ℝ)|=(1090696527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6410137201/10000000000 : ℝ)|^65 ≤ (55437494563621/100000000000000 : ℝ)^49
        have hw : |(6410137201/10000000000 : ℝ)|=(6410137201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s4_s4_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (848088233/5000000000 : ℝ)*x 0 + (-940717323/10000000000 : ℝ)*x 1 + (8936941941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848088233/5000000000 : ℝ)^65 ≤ (9503197124417/100000000000000 : ℝ)^49 := by
    have hnat : (848088233 : ℕ)^65*100000000000000^49 ≤ 9503197124417^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848088233 5000000000 9503197124417 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (940717323/10000000000 : ℝ)^65 ≤ (4347725600121/100000000000000 : ℝ)^49 := by
    have hnat : (940717323 : ℕ)^65*100000000000000^49 ≤ 4347725600121^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940717323 10000000000 4347725600121 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8936941941/10000000000 : ℝ)^65 ≤ (86149077262427/100000000000000 : ℝ)^49 := by
    have hnat : (8936941941 : ℕ)^65*100000000000000^49 ≤ 86149077262427^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8936941941 10000000000 86149077262427 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848088233/5000000000 : ℝ), (-940717323/10000000000 : ℝ), (8936941941/10000000000 : ℝ)] ![(9503197124417/100000000000000 : ℝ), (4347725600121/100000000000000 : ℝ), (86149077262427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848088233/5000000000 : ℝ)|^65 ≤ (9503197124417/100000000000000 : ℝ)^49
        have hw : |(848088233/5000000000 : ℝ)|=(848088233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-940717323/10000000000 : ℝ)|^65 ≤ (4347725600121/100000000000000 : ℝ)^49
        have hw : |(-940717323/10000000000 : ℝ)|=(940717323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8936941941/10000000000 : ℝ)|^65 ≤ (86149077262427/100000000000000 : ℝ)^49
        have hw : |(8936941941/10000000000 : ℝ)|=(8936941941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s4_s4_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1380467019/2000000000 : ℝ)*x 0 + (929785381/2000000000 : ℝ)*x 1 + (-646618863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380467019/2000000000 : ℝ)^65 ≤ (3822111349633/6250000000000 : ℝ)^49 := by
    have hnat : (1380467019 : ℕ)^65*6250000000000^49 ≤ 3822111349633^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380467019 2000000000 3822111349633 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (929785381/2000000000 : ℝ)^65 ≤ (18101026386357/50000000000000 : ℝ)^49 := by
    have hnat : (929785381 : ℕ)^65*50000000000000^49 ≤ 18101026386357^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929785381 2000000000 18101026386357 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646618863/10000000000 : ℝ)^65 ≤ (1322082808153/50000000000000 : ℝ)^49 := by
    have hnat : (646618863 : ℕ)^65*50000000000000^49 ≤ 1322082808153^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646618863 10000000000 1322082808153 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1380467019/2000000000 : ℝ), (929785381/2000000000 : ℝ), (-646618863/10000000000 : ℝ)] ![(3822111349633/6250000000000 : ℝ), (18101026386357/50000000000000 : ℝ), (1322082808153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1380467019/2000000000 : ℝ)|^65 ≤ (3822111349633/6250000000000 : ℝ)^49
        have hw : |(1380467019/2000000000 : ℝ)|=(1380467019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(929785381/2000000000 : ℝ)|^65 ≤ (18101026386357/50000000000000 : ℝ)^49
        have hw : |(929785381/2000000000 : ℝ)|=(929785381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-646618863/10000000000 : ℝ)|^65 ≤ (1322082808153/50000000000000 : ℝ)^49
        have hw : |(-646618863/10000000000 : ℝ)|=(646618863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s4_s4_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9348565591/10000000000 : ℝ)*x 0 + (1209399061/10000000000 : ℝ)*x 1 + (616270421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9348565591/10000000000 : ℝ)^65 ≤ (22862953253127/25000000000000 : ℝ)^49 := by
    have hnat : (9348565591 : ℕ)^65*25000000000000^49 ≤ 22862953253127^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9348565591 10000000000 22862953253127 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209399061/10000000000 : ℝ)^65 ≤ (3033685320211/50000000000000 : ℝ)^49 := by
    have hnat : (1209399061 : ℕ)^65*50000000000000^49 ≤ 3033685320211^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209399061 10000000000 3033685320211 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (616270421/10000000000 : ℝ)^65 ≤ (496163266923/20000000000000 : ℝ)^49 := by
    have hnat : (616270421 : ℕ)^65*20000000000000^49 ≤ 496163266923^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      616270421 10000000000 496163266923 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9348565591/10000000000 : ℝ), (1209399061/10000000000 : ℝ), (616270421/10000000000 : ℝ)] ![(22862953253127/25000000000000 : ℝ), (3033685320211/50000000000000 : ℝ), (496163266923/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9348565591/10000000000 : ℝ)|^65 ≤ (22862953253127/25000000000000 : ℝ)^49
        have hw : |(9348565591/10000000000 : ℝ)|=(9348565591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1209399061/10000000000 : ℝ)|^65 ≤ (3033685320211/50000000000000 : ℝ)^49
        have hw : |(1209399061/10000000000 : ℝ)|=(1209399061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(616270421/10000000000 : ℝ)|^65 ≤ (496163266923/20000000000000 : ℝ)^49
        have hw : |(616270421/10000000000 : ℝ)|=(616270421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s4_s4_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-966026483/5000000000 : ℝ)*x 0 + (5788147563/10000000000 : ℝ)*x 1 + (1259797561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (966026483/5000000000 : ℝ)^65 ≤ (11294899845391/100000000000000 : ℝ)^49 := by
    have hnat : (966026483 : ℕ)^65*100000000000000^49 ≤ 11294899845391^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966026483 5000000000 11294899845391 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5788147563/10000000000 : ℝ)^65 ≤ (48417404308517/100000000000000 : ℝ)^49 := by
    have hnat : (5788147563 : ℕ)^65*100000000000000^49 ≤ 48417404308517^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5788147563 10000000000 48417404308517 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1259797561/2500000000 : ℝ)^65 ≤ (20143847912637/50000000000000 : ℝ)^49 := by
    have hnat : (1259797561 : ℕ)^65*50000000000000^49 ≤ 20143847912637^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259797561 2500000000 20143847912637 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-966026483/5000000000 : ℝ), (5788147563/10000000000 : ℝ), (1259797561/2500000000 : ℝ)] ![(11294899845391/100000000000000 : ℝ), (48417404308517/100000000000000 : ℝ), (20143847912637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-966026483/5000000000 : ℝ)|^65 ≤ (11294899845391/100000000000000 : ℝ)^49
        have hw : |(-966026483/5000000000 : ℝ)|=(966026483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5788147563/10000000000 : ℝ)|^65 ≤ (48417404308517/100000000000000 : ℝ)^49
        have hw : |(5788147563/10000000000 : ℝ)|=(5788147563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1259797561/2500000000 : ℝ)|^65 ≤ (20143847912637/50000000000000 : ℝ)^49
        have hw : |(1259797561/2500000000 : ℝ)|=(1259797561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s4_s4_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6965300717/10000000000 : ℝ)*x 0 + (-593954699/10000000000 : ℝ)*x 1 + (115109797/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6965300717/10000000000 : ℝ)^65 ≤ (30947454674101/50000000000000 : ℝ)^49 := by
    have hnat : (6965300717 : ℕ)^65*50000000000000^49 ≤ 30947454674101^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6965300717 10000000000 30947454674101 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (593954699/10000000000 : ℝ)^65 ≤ (2362360890717/100000000000000 : ℝ)^49 := by
    have hnat : (593954699 : ℕ)^65*100000000000000^49 ≤ 2362360890717^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593954699 10000000000 2362360890717 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115109797/250000000 : ℝ)^65 ≤ (7148545950983/20000000000000 : ℝ)^49 := by
    have hnat : (115109797 : ℕ)^65*20000000000000^49 ≤ 7148545950983^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115109797 250000000 7148545950983 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6965300717/10000000000 : ℝ), (-593954699/10000000000 : ℝ), (115109797/250000000 : ℝ)] ![(30947454674101/50000000000000 : ℝ), (2362360890717/100000000000000 : ℝ), (7148545950983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6965300717/10000000000 : ℝ)|^65 ≤ (30947454674101/50000000000000 : ℝ)^49
        have hw : |(6965300717/10000000000 : ℝ)|=(6965300717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-593954699/10000000000 : ℝ)|^65 ≤ (2362360890717/100000000000000 : ℝ)^49
        have hw : |(-593954699/10000000000 : ℝ)|=(593954699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(115109797/250000000 : ℝ)|^65 ≤ (7148545950983/20000000000000 : ℝ)^49
        have hw : |(115109797/250000000 : ℝ)|=(115109797/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s4_s4_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (222287299/1250000000 : ℝ)*x 0 + (2221722899/2500000000 : ℝ)*x 1 + (-944679027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (222287299/1250000000 : ℝ)^65 ≤ (10118314877227/100000000000000 : ℝ)^49 := by
    have hnat : (222287299 : ℕ)^65*100000000000000^49 ≤ 10118314877227^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222287299 1250000000 10118314877227 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2221722899/2500000000 : ℝ)^65 ≤ (85509654243927/100000000000000 : ℝ)^49 := by
    have hnat : (2221722899 : ℕ)^65*100000000000000^49 ≤ 85509654243927^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221722899 2500000000 85509654243927 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (944679027/10000000000 : ℝ)^65 ≤ (874406174687/20000000000000 : ℝ)^49 := by
    have hnat : (944679027 : ℕ)^65*20000000000000^49 ≤ 874406174687^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944679027 10000000000 874406174687 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(222287299/1250000000 : ℝ), (2221722899/2500000000 : ℝ), (-944679027/10000000000 : ℝ)] ![(10118314877227/100000000000000 : ℝ), (85509654243927/100000000000000 : ℝ), (874406174687/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(222287299/1250000000 : ℝ)|^65 ≤ (10118314877227/100000000000000 : ℝ)^49
        have hw : |(222287299/1250000000 : ℝ)|=(222287299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2221722899/2500000000 : ℝ)|^65 ≤ (85509654243927/100000000000000 : ℝ)^49
        have hw : |(2221722899/2500000000 : ℝ)|=(2221722899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-944679027/10000000000 : ℝ)|^65 ≤ (874406174687/20000000000000 : ℝ)^49
        have hw : |(-944679027/10000000000 : ℝ)|=(944679027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s4_s4_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9376642089/10000000000 : ℝ)*x 0 + (229469847/2500000000 : ℝ)*x 1 + (879323403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9376642089/10000000000 : ℝ)^65 ≤ (91816332127857/100000000000000 : ℝ)^49 := by
    have hnat : (9376642089 : ℕ)^65*100000000000000^49 ≤ 91816332127857^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9376642089 10000000000 91816332127857 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229469847/2500000000 : ℝ)^65 ≤ (841653561859/20000000000000 : ℝ)^49 := by
    have hnat : (229469847 : ℕ)^65*20000000000000^49 ≤ 841653561859^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229469847 2500000000 841653561859 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (879323403/10000000000 : ℝ)^65 ≤ (1987700022597/50000000000000 : ℝ)^49 := by
    have hnat : (879323403 : ℕ)^65*50000000000000^49 ≤ 1987700022597^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879323403 10000000000 1987700022597 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9376642089/10000000000 : ℝ), (229469847/2500000000 : ℝ), (879323403/10000000000 : ℝ)] ![(91816332127857/100000000000000 : ℝ), (841653561859/20000000000000 : ℝ), (1987700022597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9376642089/10000000000 : ℝ)|^65 ≤ (91816332127857/100000000000000 : ℝ)^49
        have hw : |(9376642089/10000000000 : ℝ)|=(9376642089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229469847/2500000000 : ℝ)|^65 ≤ (841653561859/20000000000000 : ℝ)^49
        have hw : |(229469847/2500000000 : ℝ)|=(229469847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(879323403/10000000000 : ℝ)|^65 ≤ (1987700022597/50000000000000 : ℝ)^49
        have hw : |(879323403/10000000000 : ℝ)|=(879323403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301053_s4 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((40919/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40919/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8619/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8619/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42773/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42773/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((37181/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37181/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40477/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40477/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80247/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(80247/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
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
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (40919/50000 : ℝ) ^ (129/32 : ℝ) ≤ (44575874625779883499/100000000000000000000 : ℝ) := by
    have hpowers : (40919/50000 : ℝ)^129 ≤ (44575874625779883499/100000000000000000000 : ℝ)^32 := by
      have hnat : (40919 : ℕ)^129*100000000000000000000^32 ≤ 44575874625779883499^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40919 50000 44575874625779883499 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40919/50000 : ℝ)) (X := (44575874625779883499/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner0a : (144575874625779883499/100000000000000000000 : ℝ) ≤ (219151117471843/200000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (144575874625779883499/100000000000000000000 : ℝ)^32 ≤ (219151117471843/200000000000000 : ℝ)^129 := by
      have hnat : (144575874625779883499 : ℕ)^32*200000000000000^129 ≤ 219151117471843^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        144575874625779883499 100000000000000000000 219151117471843 200000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (219151117471843/200000000000000 : ℝ)) (X := (144575874625779883499/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner0b : (94575874625779883499/50000000000000000000 : ℝ) ≤ (5856472935639867/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (94575874625779883499/50000000000000000000 : ℝ)^32 ≤ (5856472935639867/5000000000000000 : ℝ)^129 := by
      have hnat : (94575874625779883499 : ℕ)^32*5000000000000000^129 ≤ 5856472935639867^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        94575874625779883499 50000000000000000000 5856472935639867 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5856472935639867/5000000000000000 : ℝ)) (X := (94575874625779883499/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(19151117471843/163676000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(23605937427737/255743750000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (40919/50000 : ℝ)) (alpha := (19151117471843/163676000000000 : ℝ)) (beta := (23605937427737/255743750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (40919/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(19151117471843/163676000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(23605937427737/255743750000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (8619/10000 : ℝ) ^ (129/32 : ℝ) ≤ (54930120327491184757/100000000000000000000 : ℝ) := by
    have hpowers : (8619/10000 : ℝ)^129 ≤ (54930120327491184757/100000000000000000000 : ℝ)^32 := by
      have hnat : (8619 : ℕ)^129*100000000000000000000^32 ≤ 54930120327491184757^32*10000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8619 10000 54930120327491184757 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8619/10000 : ℝ)) (X := (54930120327491184757/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner1a : (154930120327491184757/100000000000000000000 : ℝ) ≤ (2229438413797293/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (154930120327491184757/100000000000000000000 : ℝ)^32 ≤ (2229438413797293/2000000000000000 : ℝ)^129 := by
      have hnat : (154930120327491184757 : ℕ)^32*2000000000000000^129 ≤ 2229438413797293^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        154930120327491184757 100000000000000000000 2229438413797293 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2229438413797293/2000000000000000 : ℝ)) (X := (154930120327491184757/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner1b : (104930120327491184757/50000000000000000000 : ℝ) ≤ (12018731856346089/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (104930120327491184757/50000000000000000000 : ℝ)^32 ≤ (12018731856346089/10000000000000000 : ℝ)^129 := by
      have hnat : (104930120327491184757 : ℕ)^32*10000000000000000^129 ≤ 12018731856346089^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104930120327491184757 50000000000000000000 12018731856346089 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12018731856346089/10000000000000000 : ℝ)) (X := (104930120327491184757/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(229438413797293/1723800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(2136126929803/21125000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (8619/10000 : ℝ)) (alpha := (229438413797293/1723800000000000 : ℝ)) (beta := (2136126929803/21125000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (8619/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(229438413797293/1723800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(2136126929803/21125000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (42773/50000 : ℝ) ^ (129/32 : ℝ) ≤ (53294215104943098059/100000000000000000000 : ℝ) := by
    have hpowers : (42773/50000 : ℝ)^129 ≤ (53294215104943098059/100000000000000000000 : ℝ)^32 := by
      have hnat : (42773 : ℕ)^129*100000000000000000000^32 ≤ 53294215104943098059^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42773 50000 53294215104943098059 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42773/50000 : ℝ)) (X := (53294215104943098059/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner2a : (153294215104943098059/100000000000000000000 : ℝ) ≤ (2779469444896613/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (153294215104943098059/100000000000000000000 : ℝ)^32 ≤ (2779469444896613/2500000000000000 : ℝ)^129 := by
      have hnat : (153294215104943098059 : ℕ)^32*2500000000000000^129 ≤ 2779469444896613^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        153294215104943098059 100000000000000000000 2779469444896613 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2779469444896613/2500000000000000 : ℝ)) (X := (153294215104943098059/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner2b : (103294215104943098059/50000000000000000000 : ℝ) ≤ (11971975746994377/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (103294215104943098059/50000000000000000000 : ℝ)^32 ≤ (11971975746994377/10000000000000000 : ℝ)^129 := by
      have hnat : (103294215104943098059 : ℕ)^32*10000000000000000^129 ≤ 11971975746994377^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103294215104943098059 50000000000000000000 11971975746994377 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11971975746994377/10000000000000000 : ℝ)) (X := (103294215104943098059/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(279469444896613/2138650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(34163918696317/342184000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (42773/50000 : ℝ)) (alpha := (279469444896613/2138650000000000 : ℝ)) (beta := (34163918696317/342184000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (42773/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(279469444896613/2138650000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(34163918696317/342184000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-1920232429/10000000000 : ℝ)*X 0 0+(2665119889/5000000000 : ℝ)*X 0 1+(1102697079/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((875286479/2000000000 : ℝ)*X 1 0+(-541660791/5000000000 : ℝ)*X 1 1+(345919493/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-393417131/2000000000 : ℝ)*X 0 0+(453060413/1250000000 : ℝ)*X 0 1+(7009077763/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((668644433/2500000000 : ℝ)*X 1 0+(-331324961/10000000000 : ℝ)*X 1 1+(535797357/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((1347090037/5000000000 : ℝ)*X 2 0+(8560131069/10000000000 : ℝ)*X 2 1+(-329027937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((6204601297/10000000000 : ℝ)*X 0 0+(552830173/1000000000 : ℝ)*X 0 1+(78023987/2000000000 : ℝ)*X 0 2+(6204601297/10000000000 : ℝ)*X 1 0+(552830173/1000000000 : ℝ)*X 1 1+(78023987/2000000000 : ℝ)*X 1 2+(6204601297/10000000000 : ℝ)*X 2 0+(552830173/1000000000 : ℝ)*X 2 1+(78023987/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-965461989/5000000000 : ℝ)*X 0 0+(1090696527/2500000000 : ℝ)*X 0 1+(6410137201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((848088233/5000000000 : ℝ)*X 1 0+(-940717323/10000000000 : ℝ)*X 1 1+(8936941941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((1380467019/2000000000 : ℝ)*X 2 0+(929785381/2000000000 : ℝ)*X 2 1+(-646618863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((9348565591/10000000000 : ℝ)*X 0 0+(1209399061/10000000000 : ℝ)*X 0 1+(616270421/10000000000 : ℝ)*X 0 2+(9348565591/10000000000 : ℝ)*X 1 0+(1209399061/10000000000 : ℝ)*X 1 1+(616270421/10000000000 : ℝ)*X 1 2+(9348565591/10000000000 : ℝ)*X 2 0+(1209399061/10000000000 : ℝ)*X 2 1+(616270421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-966026483/5000000000 : ℝ)*X 0 0+(5788147563/10000000000 : ℝ)*X 0 1+(1259797561/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((6965300717/10000000000 : ℝ)*X 1 0+(-593954699/10000000000 : ℝ)*X 1 1+(115109797/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((222287299/1250000000 : ℝ)*X 2 0+(2221722899/2500000000 : ℝ)*X 2 1+(-944679027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((9376642089/10000000000 : ℝ)*X 0 0+(229469847/2500000000 : ℝ)*X 0 1+(879323403/10000000000 : ℝ)*X 0 2+(9376642089/10000000000 : ℝ)*X 1 0+(229469847/2500000000 : ℝ)*X 1 1+(879323403/10000000000 : ℝ)*X 1 2+(9376642089/10000000000 : ℝ)*X 2 0+(229469847/2500000000 : ℝ)*X 2 1+(879323403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((37181/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37181/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11940553400519310039587991/1807159250000000000000000000000 : ℝ) := by norm_num
    linear_combination (358844787533/1000000000000 : ℝ)*(base7) + (201261/1000000000000 : ℝ)*(base49) + (2029507/250000000000 : ℝ)*(base53) + (442067/200000000000 : ℝ)*(base59) + (317521688241/125000000000 : ℝ)*(major_s4_0) + (317521688241/125000000000 : ℝ)*(major_s4_1) + (25401653879/10000000000 : ℝ)*(major_s4_2) + (220627/20000000000 : ℝ)*(sp_s4_1) + (3142045470347/1000000000000 : ℝ)*(sp_s4_7) + (157103791711/50000000000 : ℝ)*(sp_s4_8) + (1571051343883/500000000000 : ℝ)*(sp_s4_9) + (259507506341/125000000000 : ℝ)*(sp_s4_13) + (49099391/1000000000000 : ℝ)*(sp_s4_14) + (7704167/1000000000000 : ℝ)*(sp_s4_15) + (858607631597/500000000000 : ℝ)*(f.failure) + (1571051343883/500000000000 : ℝ)*(f.sum) + (347507499008293619/6144341450000000000000000000000 : ℝ)*base62 + (30086371665963/427730000000000000000000000 : ℝ)*base64 + (1118161888071/5281250000000000000000000 : ℝ)*base66 + (65098691076749/106932500000000000000000000 : ℝ)*base69 + (4657170795108929659/8751141935000000000000000000000 : ℝ)*base70 + (1728120019083623/2045950000000000000000000000 : ℝ)*base73 + (17387768119621/71825000000000000000000000 : ℝ)*base75 + (7779845387037/204595000000000000000000000 : ℝ)*base77 + (123782790115047391/864413875000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (11343/12500000000000000 : ℝ)*base86 + (11343/12500000000000000 : ℝ)*base88 + (11343/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40477/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40477/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12418141705915270484763/2138650000000000000000000000 : ℝ) := by norm_num
    linear_combination (587696357779/1000000000000 : ℝ)*(base7) + (4122621/1000000000000 : ℝ)*(base27) + (23781/125000000000 : ℝ)*(base39) + (292912384869/500000000000 : ℝ)*(base53) + (1697068912907/1000000000000 : ℝ)*(major_s4_0) + (1697068912907/1000000000000 : ℝ)*(major_s4_1) + (1111244143169/1000000000000 : ℝ)*(major_s4_2) + (10906861/500000000000 : ℝ)*(sp_s4_0) + (34631049/1000000000000 : ℝ)*(sp_s4_8) + (649523147849/500000000000 : ℝ)*(sp_s4_14) + (1299033478371/1000000000000 : ℝ)*(sp_s4_15) + (942446439579/500000000000 : ℝ)*(sp_s4_16) + (867458490851/500000000000 : ℝ)*(sp_s4_20) + (8142497/250000000000 : ℝ)*(sp_s4_27) + (286814329133/250000000000 : ℝ)*(f.failure) + (942446439579/500000000000 : ℝ)*(f.sum) + (4911673119478538603/14746419480000000000000000000000 : ℝ)*base63 + (375963948865337/1710920000000000000000000000 : ℝ)*base64 + (2450077369823/10562500000000000000000000 : ℝ)*base66 + (287338066541277/2138650000000000000000000000 : ℝ)*base69 + (4601475088546185083/70009135480000000000000000000000 : ℝ)*base71 + (270574955612803/2045950000000000000000000000 : ℝ)*base72 + (53875362880369/1723800000000000000000000000 : ℝ)*base74 + (163746547208723/818380000000000000000000000 : ℝ)*base76 + (213876921236105021/864413875000000000000000000000 : ℝ)*base79 + (1277/6250000000000000 : ℝ)*base86 + (1277/6250000000000000 : ℝ)*base88 + (1277/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80247/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(80247/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (137824251618940077266646303311/14789429870150000000000000000000000 : ℝ) := by norm_num
    linear_combination (56733334697/100000000000 : ℝ)*(base7) + (7301407/500000000000 : ℝ)*(base27) + (43113/200000000000 : ℝ)*(base34) + (4095066891/250000000000 : ℝ)*(base40) + (160393951631/250000000000 : ℝ)*(base43) + (1672393697839/1000000000000 : ℝ)*(major_s4_0) + (402663323/390625000 : ℝ)*(major_s4_1) + (418098478351/250000000000 : ℝ)*(major_s4_2) + (24077769/1000000000000 : ℝ)*(sp_s4_0) + (8840267/125000000000 : ℝ)*(sp_s4_9) + (1223164865121/1000000000000 : ℝ)*(sp_s4_21) + (1864764964979/1000000000000 : ℝ)*(sp_s4_22) + (1223118436319/1000000000000 : ℝ)*(sp_s4_23) + (848947491157/500000000000 : ℝ)*(sp_s4_27) + (565288226861/500000000000 : ℝ)*(f.failure) + (1864764964979/1000000000000 : ℝ)*(f.sum) + (6355847712232581497/18433024350000000000000000000000 : ℝ)*base62 + (5405801650067/53466250000000000000000000 : ℝ)*base64 + (2590386603399/8450000000000000000000000 : ℝ)*base67 + (1618192310820333/2138650000000000000000000000 : ℝ)*base68 + (13454851818488557639/35004567740000000000000000000000 : ℝ)*base70 + (177457994561427/1022975000000000000000000000 : ℝ)*base73 + (5220569425511/8619000000000000000000000 : ℝ)*base74 + (104365837108907/163676000000000000000000000 : ℝ)*base76 + (93736843832061237/345765550000000000000000000000 : ℝ)*base79 + (3359/12500000000000000 : ℝ)*base86 + (3359/12500000000000000 : ℝ)*base88 + (3359/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((40919/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40919/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8619/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8619/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42773/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42773/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((37181/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37181/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40477/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40477/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80247/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(80247/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301053_s4 p hpa hpb X hX hprev3

#print axioms solution

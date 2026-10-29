-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c311053_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:59:10.589508+00:00
-- url     : https://prove2.me/submissions/e37ed0c9-24e1-41a4-9520-4ec0f5a65280

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
theorem collision_support_c311053_s2_s2_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2055408213/10000000000 : ℝ)*x 0 + (5190258383/10000000000 : ℝ)*x 1 + (1054005153/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055408213/10000000000 : ℝ)^9 ≤ (326981561967/2500000000000 : ℝ)^7 := by
    have hnat : (2055408213 : ℕ)^9*2500000000000^7 ≤ 326981561967^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055408213 10000000000 326981561967 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5190258383/10000000000 : ℝ)^9 ≤ (2689641631503/6250000000000 : ℝ)^7 := by
    have hnat : (5190258383 : ℕ)^9*6250000000000^7 ≤ 2689641631503^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190258383 10000000000 2689641631503 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054005153/2000000000 : ℝ)^9 ≤ (43886471403971/100000000000000 : ℝ)^7 := by
    have hnat : (1054005153 : ℕ)^9*100000000000000^7 ≤ 43886471403971^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054005153 2000000000 43886471403971 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2055408213/10000000000 : ℝ), (5190258383/10000000000 : ℝ), (1054005153/2000000000 : ℝ)] ![(326981561967/2500000000000 : ℝ), (2689641631503/6250000000000 : ℝ), (43886471403971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2055408213/10000000000 : ℝ)|^9 ≤ (326981561967/2500000000000 : ℝ)^7
        have hw : |(-2055408213/10000000000 : ℝ)|=(2055408213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5190258383/10000000000 : ℝ)|^9 ≤ (2689641631503/6250000000000 : ℝ)^7
        have hw : |(5190258383/10000000000 : ℝ)|=(5190258383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054005153/2000000000 : ℝ)|^9 ≤ (43886471403971/100000000000000 : ℝ)^7
        have hw : |(1054005153/2000000000 : ℝ)|=(1054005153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s2_s2_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4530955729/10000000000 : ℝ)*x 0 + (-1484688563/10000000000 : ℝ)*x 1 + (393996367/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4530955729/10000000000 : ℝ)^9 ≤ (36137519452777/100000000000000 : ℝ)^7 := by
    have hnat : (4530955729 : ℕ)^9*100000000000000^7 ≤ 36137519452777^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530955729 10000000000 36137519452777 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1484688563/10000000000 : ℝ)^9 ≤ (4304569823621/50000000000000 : ℝ)^7 := by
    have hnat : (1484688563 : ℕ)^9*50000000000000^7 ≤ 4304569823621^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1484688563 10000000000 4304569823621 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (393996367/625000000 : ℝ)^9 ≤ (55253340890863/100000000000000 : ℝ)^7 := by
    have hnat : (393996367 : ℕ)^9*100000000000000^7 ≤ 55253340890863^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393996367 625000000 55253340890863 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4530955729/10000000000 : ℝ), (-1484688563/10000000000 : ℝ), (393996367/625000000 : ℝ)] ![(36137519452777/100000000000000 : ℝ), (4304569823621/50000000000000 : ℝ), (55253340890863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4530955729/10000000000 : ℝ)|^9 ≤ (36137519452777/100000000000000 : ℝ)^7
        have hw : |(4530955729/10000000000 : ℝ)|=(4530955729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1484688563/10000000000 : ℝ)|^9 ≤ (4304569823621/50000000000000 : ℝ)^7
        have hw : |(-1484688563/10000000000 : ℝ)|=(1484688563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(393996367/625000000 : ℝ)|^9 ≤ (55253340890863/100000000000000 : ℝ)^7
        have hw : |(393996367/625000000 : ℝ)|=(393996367/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s2_s2_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (910705957/2000000000 : ℝ)*x 0 + (6305618977/10000000000 : ℝ)*x 1 + (-29019439/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (910705957/2000000000 : ℝ)^9 ≤ (36369168872473/100000000000000 : ℝ)^7 := by
    have hnat : (910705957 : ℕ)^9*100000000000000^7 ≤ 36369168872473^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910705957 2000000000 36369168872473 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6305618977/10000000000 : ℝ)^9 ≤ (55272241141801/100000000000000 : ℝ)^7 := by
    have hnat : (6305618977 : ℕ)^9*100000000000000^7 ≤ 55272241141801^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6305618977 10000000000 55272241141801 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29019439/200000000 : ℝ)^9 ≤ (4179294986181/50000000000000 : ℝ)^7 := by
    have hnat : (29019439 : ℕ)^9*50000000000000^7 ≤ 4179294986181^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29019439 200000000 4179294986181 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(910705957/2000000000 : ℝ), (6305618977/10000000000 : ℝ), (-29019439/200000000 : ℝ)] ![(36369168872473/100000000000000 : ℝ), (55272241141801/100000000000000 : ℝ), (4179294986181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(910705957/2000000000 : ℝ)|^9 ≤ (36369168872473/100000000000000 : ℝ)^7
        have hw : |(910705957/2000000000 : ℝ)|=(910705957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6305618977/10000000000 : ℝ)|^9 ≤ (55272241141801/100000000000000 : ℝ)^7
        have hw : |(6305618977/10000000000 : ℝ)|=(6305618977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-29019439/200000000 : ℝ)|^9 ≤ (4179294986181/50000000000000 : ℝ)^7
        have hw : |(-29019439/200000000 : ℝ)|=(29019439/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s2_s2_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1400571237/2000000000 : ℝ)*x 0 + (341103877/1250000000 : ℝ)*x 1 + (2625796179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1400571237/2000000000 : ℝ)^9 ≤ (15812776499997/25000000000000 : ℝ)^7 := by
    have hnat : (1400571237 : ℕ)^9*25000000000000^7 ≤ 15812776499997^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400571237 2000000000 15812776499997 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341103877/1250000000 : ℝ)^9 ≤ (18828993779449/100000000000000 : ℝ)^7 := by
    have hnat : (341103877 : ℕ)^9*100000000000000^7 ≤ 18828993779449^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341103877 1250000000 18828993779449 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2625796179/10000000000 : ℝ)^9 ≤ (8959950104733/50000000000000 : ℝ)^7 := by
    have hnat : (2625796179 : ℕ)^9*50000000000000^7 ≤ 8959950104733^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625796179 10000000000 8959950104733 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1400571237/2000000000 : ℝ), (341103877/1250000000 : ℝ), (2625796179/10000000000 : ℝ)] ![(15812776499997/25000000000000 : ℝ), (18828993779449/100000000000000 : ℝ), (8959950104733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1400571237/2000000000 : ℝ)|^9 ≤ (15812776499997/25000000000000 : ℝ)^7
        have hw : |(1400571237/2000000000 : ℝ)|=(1400571237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341103877/1250000000 : ℝ)|^9 ≤ (18828993779449/100000000000000 : ℝ)^7
        have hw : |(341103877/1250000000 : ℝ)|=(341103877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2625796179/10000000000 : ℝ)|^9 ≤ (8959950104733/50000000000000 : ℝ)^7
        have hw : |(2625796179/10000000000 : ℝ)|=(2625796179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s2_s2_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1915365321/10000000000 : ℝ)*x 0 + (2067248783/5000000000 : ℝ)*x 1 + (6364010253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1915365321/10000000000 : ℝ)^9 ≤ (5972424365413/50000000000000 : ℝ)^7 := by
    have hnat : (1915365321 : ℕ)^9*50000000000000^7 ≤ 5972424365413^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915365321 10000000000 5972424365413 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067248783/5000000000 : ℝ)^9 ≤ (16061985970911/50000000000000 : ℝ)^7 := by
    have hnat : (2067248783 : ℕ)^9*50000000000000^7 ≤ 16061985970911^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067248783 5000000000 16061985970911 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6364010253/10000000000 : ℝ)^9 ≤ (13982794828609/25000000000000 : ℝ)^7 := by
    have hnat : (6364010253 : ℕ)^9*25000000000000^7 ≤ 13982794828609^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6364010253 10000000000 13982794828609 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1915365321/10000000000 : ℝ), (2067248783/5000000000 : ℝ), (6364010253/10000000000 : ℝ)] ![(5972424365413/50000000000000 : ℝ), (16061985970911/50000000000000 : ℝ), (13982794828609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1915365321/10000000000 : ℝ)|^9 ≤ (5972424365413/50000000000000 : ℝ)^7
        have hw : |(-1915365321/10000000000 : ℝ)|=(1915365321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2067248783/5000000000 : ℝ)|^9 ≤ (16061985970911/50000000000000 : ℝ)^7
        have hw : |(2067248783/5000000000 : ℝ)|=(2067248783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6364010253/10000000000 : ℝ)|^9 ≤ (13982794828609/25000000000000 : ℝ)^7
        have hw : |(6364010253/10000000000 : ℝ)|=(6364010253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s2_s2_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1989087407/5000000000 : ℝ)*x 0 + (-35319177/400000000 : ℝ)*x 1 + (7154327519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989087407/5000000000 : ℝ)^9 ≤ (30570871849767/100000000000000 : ℝ)^7 := by
    have hnat : (1989087407 : ℕ)^9*100000000000000^7 ≤ 30570871849767^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989087407 5000000000 30570871849767 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35319177/400000000 : ℝ)^9 ≤ (1103401618071/25000000000000 : ℝ)^7 := by
    have hnat : (35319177 : ℕ)^9*25000000000000^7 ≤ 1103401618071^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35319177 400000000 1103401618071 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7154327519/10000000000 : ℝ)^9 ≤ (65015521670553/100000000000000 : ℝ)^7 := by
    have hnat : (7154327519 : ℕ)^9*100000000000000^7 ≤ 65015521670553^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7154327519 10000000000 65015521670553 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1989087407/5000000000 : ℝ), (-35319177/400000000 : ℝ), (7154327519/10000000000 : ℝ)] ![(30570871849767/100000000000000 : ℝ), (1103401618071/25000000000000 : ℝ), (65015521670553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1989087407/5000000000 : ℝ)|^9 ≤ (30570871849767/100000000000000 : ℝ)^7
        have hw : |(1989087407/5000000000 : ℝ)|=(1989087407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35319177/400000000 : ℝ)|^9 ≤ (1103401618071/25000000000000 : ℝ)^7
        have hw : |(-35319177/400000000 : ℝ)|=(35319177/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7154327519/10000000000 : ℝ)|^9 ≤ (65015521670553/100000000000000 : ℝ)^7
        have hw : |(7154327519/10000000000 : ℝ)|=(7154327519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s2_s2_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (100027357/250000000 : ℝ)*x 0 + (3674307259/5000000000 : ℝ)*x 1 + (-229969983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100027357/250000000 : ℝ)^9 ≤ (3079750828607/10000000000000 : ℝ)^7 := by
    have hnat : (100027357 : ℕ)^9*10000000000000^7 ≤ 3079750828607^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100027357 250000000 3079750828607 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3674307259/5000000000 : ℝ)^9 ≤ (67294327415841/100000000000000 : ℝ)^7 := by
    have hnat : (3674307259 : ℕ)^9*100000000000000^7 ≤ 67294327415841^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3674307259 5000000000 67294327415841 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229969983/5000000000 : ℝ)^9 ≤ (1908164284069/100000000000000 : ℝ)^7 := by
    have hnat : (229969983 : ℕ)^9*100000000000000^7 ≤ 1908164284069^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229969983 5000000000 1908164284069 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(100027357/250000000 : ℝ), (3674307259/5000000000 : ℝ), (-229969983/5000000000 : ℝ)] ![(3079750828607/10000000000000 : ℝ), (67294327415841/100000000000000 : ℝ), (1908164284069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(100027357/250000000 : ℝ)|^9 ≤ (3079750828607/10000000000000 : ℝ)^7
        have hw : |(100027357/250000000 : ℝ)|=(100027357/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3674307259/5000000000 : ℝ)|^9 ≤ (67294327415841/100000000000000 : ℝ)^7
        have hw : |(3674307259/5000000000 : ℝ)|=(3674307259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-229969983/5000000000 : ℝ)|^9 ≤ (1908164284069/100000000000000 : ℝ)^7
        have hw : |(-229969983/5000000000 : ℝ)|=(229969983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s2_s2_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3305289733/5000000000 : ℝ)*x 0 + (1147210993/2500000000 : ℝ)*x 1 + (112729593/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3305289733/5000000000 : ℝ)^9 ≤ (58732622889163/100000000000000 : ℝ)^7 := by
    have hnat : (3305289733 : ℕ)^9*100000000000000^7 ≤ 58732622889163^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3305289733 5000000000 58732622889163 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1147210993/2500000000 : ℝ)^9 ≤ (4591526569317/12500000000000 : ℝ)^7 := by
    have hnat : (1147210993 : ℕ)^9*12500000000000^7 ≤ 4591526569317^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147210993 2500000000 4591526569317 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112729593/1250000000 : ℝ)^9 ≤ (907032906837/20000000000000 : ℝ)^7 := by
    have hnat : (112729593 : ℕ)^9*20000000000000^7 ≤ 907032906837^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112729593 1250000000 907032906837 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3305289733/5000000000 : ℝ), (1147210993/2500000000 : ℝ), (112729593/1250000000 : ℝ)] ![(58732622889163/100000000000000 : ℝ), (4591526569317/12500000000000 : ℝ), (907032906837/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3305289733/5000000000 : ℝ)|^9 ≤ (58732622889163/100000000000000 : ℝ)^7
        have hw : |(3305289733/5000000000 : ℝ)|=(3305289733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1147210993/2500000000 : ℝ)|^9 ≤ (4591526569317/12500000000000 : ℝ)^7
        have hw : |(1147210993/2500000000 : ℝ)|=(1147210993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112729593/1250000000 : ℝ)|^9 ≤ (907032906837/20000000000000 : ℝ)^7
        have hw : |(112729593/1250000000 : ℝ)|=(112729593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s2_s2_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-926530823/10000000000 : ℝ)*x 0 + (609195861/1250000000 : ℝ)*x 1 + (253445597/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (926530823/10000000000 : ℝ)^9 ≤ (234772368917/5000000000000 : ℝ)^7 := by
    have hnat : (926530823 : ℕ)^9*5000000000000^7 ≤ 234772368917^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926530823 10000000000 234772368917 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (609195861/1250000000 : ℝ)^9 ≤ (39688102881823/100000000000000 : ℝ)^7 := by
    have hnat : (609195861 : ℕ)^9*100000000000000^7 ≤ 39688102881823^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609195861 1250000000 39688102881823 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253445597/400000000 : ℝ)^9 ≤ (6952056215079/12500000000000 : ℝ)^7 := by
    have hnat : (253445597 : ℕ)^9*12500000000000^7 ≤ 6952056215079^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253445597 400000000 6952056215079 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-926530823/10000000000 : ℝ), (609195861/1250000000 : ℝ), (253445597/400000000 : ℝ)] ![(234772368917/5000000000000 : ℝ), (39688102881823/100000000000000 : ℝ), (6952056215079/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-926530823/10000000000 : ℝ)|^9 ≤ (234772368917/5000000000000 : ℝ)^7
        have hw : |(-926530823/10000000000 : ℝ)|=(926530823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(609195861/1250000000 : ℝ)|^9 ≤ (39688102881823/100000000000000 : ℝ)^7
        have hw : |(609195861/1250000000 : ℝ)|=(609195861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(253445597/400000000 : ℝ)|^9 ≤ (6952056215079/12500000000000 : ℝ)^7
        have hw : |(253445597/400000000 : ℝ)|=(253445597/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s2_s2_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3958093957/10000000000 : ℝ)*x 0 + (-120430561/1250000000 : ℝ)*x 1 + (1781614331/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3958093957/10000000000 : ℝ)^9 ≤ (30372610978581/100000000000000 : ℝ)^7 := by
    have hnat : (3958093957 : ℕ)^9*100000000000000^7 ≤ 30372610978581^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3958093957 10000000000 30372610978581 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120430561/1250000000 : ℝ)^9 ≤ (1234330542807/25000000000000 : ℝ)^7 := by
    have hnat : (120430561 : ℕ)^9*25000000000000^7 ≤ 1234330542807^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120430561 1250000000 1234330542807 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1781614331/2500000000 : ℝ)^9 ≤ (64690066834547/100000000000000 : ℝ)^7 := by
    have hnat : (1781614331 : ℕ)^9*100000000000000^7 ≤ 64690066834547^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781614331 2500000000 64690066834547 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3958093957/10000000000 : ℝ), (-120430561/1250000000 : ℝ), (1781614331/2500000000 : ℝ)] ![(30372610978581/100000000000000 : ℝ), (1234330542807/25000000000000 : ℝ), (64690066834547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3958093957/10000000000 : ℝ)|^9 ≤ (30372610978581/100000000000000 : ℝ)^7
        have hw : |(3958093957/10000000000 : ℝ)|=(3958093957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-120430561/1250000000 : ℝ)|^9 ≤ (1234330542807/25000000000000 : ℝ)^7
        have hw : |(-120430561/1250000000 : ℝ)|=(120430561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1781614331/2500000000 : ℝ)|^9 ≤ (64690066834547/100000000000000 : ℝ)^7
        have hw : |(1781614331/2500000000 : ℝ)|=(1781614331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s2_s2_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5783644167/10000000000 : ℝ)*x 0 + (1423596311/2500000000 : ℝ)*x 1 + (-487810517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5783644167/10000000000 : ℝ)^9 ≤ (6182571801269/12500000000000 : ℝ)^7 := by
    have hnat : (5783644167 : ℕ)^9*12500000000000^7 ≤ 6182571801269^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5783644167 10000000000 6182571801269 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1423596311/2500000000 : ℝ)^9 ≤ (12120332218457/25000000000000 : ℝ)^7 := by
    have hnat : (1423596311 : ℕ)^9*25000000000000^7 ≤ 12120332218457^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423596311 2500000000 12120332218457 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (487810517/10000000000 : ℝ)^9 ≤ (205809669969/10000000000000 : ℝ)^7 := by
    have hnat : (487810517 : ℕ)^9*10000000000000^7 ≤ 205809669969^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487810517 10000000000 205809669969 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5783644167/10000000000 : ℝ), (1423596311/2500000000 : ℝ), (-487810517/10000000000 : ℝ)] ![(6182571801269/12500000000000 : ℝ), (12120332218457/25000000000000 : ℝ), (205809669969/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5783644167/10000000000 : ℝ)|^9 ≤ (6182571801269/12500000000000 : ℝ)^7
        have hw : |(5783644167/10000000000 : ℝ)|=(5783644167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1423596311/2500000000 : ℝ)|^9 ≤ (12120332218457/25000000000000 : ℝ)^7
        have hw : |(1423596311/2500000000 : ℝ)|=(1423596311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-487810517/10000000000 : ℝ)|^9 ≤ (205809669969/10000000000000 : ℝ)^7
        have hw : |(-487810517/10000000000 : ℝ)|=(487810517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s2_s2_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (8471695569/10000000000 : ℝ)*x 0 + (2197433901/10000000000 : ℝ)*x 1 + (965575707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8471695569/10000000000 : ℝ)^9 ≤ (40398053754519/50000000000000 : ℝ)^7 := by
    have hnat : (8471695569 : ℕ)^9*50000000000000^7 ≤ 40398053754519^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8471695569 10000000000 40398053754519 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197433901/10000000000 : ℝ)^9 ≤ (14252523606233/100000000000000 : ℝ)^7 := by
    have hnat : (2197433901 : ℕ)^9*100000000000000^7 ≤ 14252523606233^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197433901 10000000000 14252523606233 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965575707/10000000000 : ℝ)^9 ≤ (1237842219103/25000000000000 : ℝ)^7 := by
    have hnat : (965575707 : ℕ)^9*25000000000000^7 ≤ 1237842219103^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965575707 10000000000 1237842219103 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8471695569/10000000000 : ℝ), (2197433901/10000000000 : ℝ), (965575707/10000000000 : ℝ)] ![(40398053754519/50000000000000 : ℝ), (14252523606233/100000000000000 : ℝ), (1237842219103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8471695569/10000000000 : ℝ)|^9 ≤ (40398053754519/50000000000000 : ℝ)^7
        have hw : |(8471695569/10000000000 : ℝ)|=(8471695569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2197433901/10000000000 : ℝ)|^9 ≤ (14252523606233/100000000000000 : ℝ)^7
        have hw : |(2197433901/10000000000 : ℝ)|=(2197433901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(965575707/10000000000 : ℝ)|^9 ≤ (1237842219103/25000000000000 : ℝ)^7
        have hw : |(965575707/10000000000 : ℝ)|=(965575707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s2_s2_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-176266583/2000000000 : ℝ)*x 0 + (243603651/400000000 : ℝ)*x 1 + (1290699921/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176266583/2000000000 : ℝ)^9 ≤ (4403027679553/100000000000000 : ℝ)^7 := by
    have hnat : (176266583 : ℕ)^9*100000000000000^7 ≤ 4403027679553^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176266583 2000000000 4403027679553 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243603651/400000000 : ℝ)^9 ≤ (52855202979249/100000000000000 : ℝ)^7 := by
    have hnat : (243603651 : ℕ)^9*100000000000000^7 ≤ 52855202979249^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243603651 400000000 52855202979249 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1290699921/2500000000 : ℝ)^9 ≤ (42741769330233/100000000000000 : ℝ)^7 := by
    have hnat : (1290699921 : ℕ)^9*100000000000000^7 ≤ 42741769330233^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290699921 2500000000 42741769330233 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-176266583/2000000000 : ℝ), (243603651/400000000 : ℝ), (1290699921/2500000000 : ℝ)] ![(4403027679553/100000000000000 : ℝ), (52855202979249/100000000000000 : ℝ), (42741769330233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-176266583/2000000000 : ℝ)|^9 ≤ (4403027679553/100000000000000 : ℝ)^7
        have hw : |(-176266583/2000000000 : ℝ)|=(176266583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(243603651/400000000 : ℝ)|^9 ≤ (52855202979249/100000000000000 : ℝ)^7
        have hw : |(243603651/400000000 : ℝ)|=(243603651/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1290699921/2500000000 : ℝ)|^9 ≤ (42741769330233/100000000000000 : ℝ)^7
        have hw : |(1290699921/2500000000 : ℝ)|=(1290699921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s2_s2_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5805921543/10000000000 : ℝ)*x 0 + (-17311747/400000000 : ℝ)*x 1 + (5698807751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5805921543/10000000000 : ℝ)^9 ≤ (24852826333619/50000000000000 : ℝ)^7 := by
    have hnat : (5805921543 : ℕ)^9*50000000000000^7 ≤ 24852826333619^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5805921543 10000000000 24852826333619 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17311747/400000000 : ℝ)^9 ≤ (352920490209/20000000000000 : ℝ)^7 := by
    have hnat : (17311747 : ℕ)^9*20000000000000^7 ≤ 352920490209^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17311747 400000000 352920490209 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5698807751/10000000000 : ℝ)^9 ≤ (12132436216649/25000000000000 : ℝ)^7 := by
    have hnat : (5698807751 : ℕ)^9*25000000000000^7 ≤ 12132436216649^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5698807751 10000000000 12132436216649 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5805921543/10000000000 : ℝ), (-17311747/400000000 : ℝ), (5698807751/10000000000 : ℝ)] ![(24852826333619/50000000000000 : ℝ), (352920490209/20000000000000 : ℝ), (12132436216649/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5805921543/10000000000 : ℝ)|^9 ≤ (24852826333619/50000000000000 : ℝ)^7
        have hw : |(5805921543/10000000000 : ℝ)|=(5805921543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17311747/400000000 : ℝ)|^9 ≤ (352920490209/20000000000000 : ℝ)^7
        have hw : |(-17311747/400000000 : ℝ)|=(17311747/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5698807751/10000000000 : ℝ)|^9 ≤ (12132436216649/25000000000000 : ℝ)^7
        have hw : |(5698807751/10000000000 : ℝ)|=(5698807751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s2_s2_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (490093581/1250000000 : ℝ)*x 0 + (447826183/625000000 : ℝ)*x 1 + (-475275709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490093581/1250000000 : ℝ)^9 ≤ (15002330212703/50000000000000 : ℝ)^7 := by
    have hnat : (490093581 : ℕ)^9*50000000000000^7 ≤ 15002330212703^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490093581 1250000000 15002330212703 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447826183/625000000 : ℝ)^9 ≤ (32571402448533/50000000000000 : ℝ)^7 := by
    have hnat : (447826183 : ℕ)^9*50000000000000^7 ≤ 32571402448533^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447826183 625000000 32571402448533 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (475275709/5000000000 : ℝ)^9 ≤ (1213133666517/25000000000000 : ℝ)^7 := by
    have hnat : (475275709 : ℕ)^9*25000000000000^7 ≤ 1213133666517^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475275709 5000000000 1213133666517 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(490093581/1250000000 : ℝ), (447826183/625000000 : ℝ), (-475275709/5000000000 : ℝ)] ![(15002330212703/50000000000000 : ℝ), (32571402448533/50000000000000 : ℝ), (1213133666517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(490093581/1250000000 : ℝ)|^9 ≤ (15002330212703/50000000000000 : ℝ)^7
        have hw : |(490093581/1250000000 : ℝ)|=(490093581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(447826183/625000000 : ℝ)|^9 ≤ (32571402448533/50000000000000 : ℝ)^7
        have hw : |(447826183/625000000 : ℝ)|=(447826183/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-475275709/5000000000 : ℝ)|^9 ≤ (1213133666517/25000000000000 : ℝ)^7
        have hw : |(-475275709/5000000000 : ℝ)|=(475275709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s2_s2_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (67261889/78125000 : ℝ)*x 0 + (391363133/2500000000 : ℝ)*x 1 + (721125803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67261889/78125000 : ℝ)^9 ≤ (82490058107707/100000000000000 : ℝ)^7 := by
    have hnat : (67261889 : ℕ)^9*100000000000000^7 ≤ 82490058107707^7*78125000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67261889 78125000 82490058107707 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (391363133/2500000000 : ℝ)^9 ≤ (575992775153/6250000000000 : ℝ)^7 := by
    have hnat : (391363133 : ℕ)^9*6250000000000^7 ≤ 575992775153^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391363133 2500000000 575992775153 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (721125803/5000000000 : ℝ)^9 ≤ (1658811493493/20000000000000 : ℝ)^7 := by
    have hnat : (721125803 : ℕ)^9*20000000000000^7 ≤ 1658811493493^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721125803 5000000000 1658811493493 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67261889/78125000 : ℝ), (391363133/2500000000 : ℝ), (721125803/5000000000 : ℝ)] ![(82490058107707/100000000000000 : ℝ), (575992775153/6250000000000 : ℝ), (1658811493493/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67261889/78125000 : ℝ)|^9 ≤ (82490058107707/100000000000000 : ℝ)^7
        have hw : |(67261889/78125000 : ℝ)|=(67261889/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(391363133/2500000000 : ℝ)|^9 ≤ (575992775153/6250000000000 : ℝ)^7
        have hw : |(391363133/2500000000 : ℝ)|=(391363133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(721125803/5000000000 : ℝ)|^9 ≤ (1658811493493/20000000000000 : ℝ)^7
        have hw : |(721125803/5000000000 : ℝ)|=(721125803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311053_s2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((68329/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68329/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72817/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(72817/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71719/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(71719/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9021/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9021/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52157/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(52157/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5057/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5057/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s2_pow0 : (68329/100000 : ℝ) ^ (71/16 : ℝ) ≤ (461317557444589139/2500000000000000000 : ℝ) := by
    have hpowers : (68329/100000 : ℝ)^71 ≤ (461317557444589139/2500000000000000000 : ℝ)^16 := by
      have hnat : (68329 : ℕ)^71*2500000000000000000^16 ≤ 461317557444589139^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68329 100000 461317557444589139 2500000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68329/100000 : ℝ)) (X := (461317557444589139/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (2961317557444589139/2500000000000000000 : ℝ) ≤ (2077798893593259/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2961317557444589139/2500000000000000000 : ℝ)^16 ≤ (2077798893593259/2000000000000000 : ℝ)^71 := by
      have hnat : (2961317557444589139 : ℕ)^16*2000000000000000^71 ≤ 2077798893593259^71*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2961317557444589139 2500000000000000000 2077798893593259 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2077798893593259/2000000000000000 : ℝ)) (X := (2961317557444589139/2500000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (1711317557444589139/1250000000000000000 : ℝ) ≤ (10733532332701133/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (1711317557444589139/1250000000000000000 : ℝ)^16 ≤ (10733532332701133/10000000000000000 : ℝ)^71 := by
      have hnat : (1711317557444589139 : ℕ)^16*10000000000000000^71 ≤ 10733532332701133^71*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1711317557444589139 1250000000000000000 10733532332701133 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10733532332701133/10000000000000000 : ℝ)) (X := (1711317557444589139/1250000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(77798893593259/1366580000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(172268932367419/3416450000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (68329/100000 : ℝ)) (alpha := (77798893593259/1366580000000000 : ℝ)) (beta := (172268932367419/3416450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (68329/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(77798893593259/1366580000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(172268932367419/3416450000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (72817/100000 : ℝ) ^ (71/16 : ℝ) ≤ (24471352441642504621/100000000000000000000 : ℝ) := by
    have hpowers : (72817/100000 : ℝ)^71 ≤ (24471352441642504621/100000000000000000000 : ℝ)^16 := by
      have hnat : (72817 : ℕ)^71*100000000000000000000^16 ≤ 24471352441642504621^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72817 100000 24471352441642504621 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72817/100000 : ℝ)) (X := (24471352441642504621/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (124471352441642504621/100000000000000000000 : ℝ) ≤ (10505678157900097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (124471352441642504621/100000000000000000000 : ℝ)^16 ≤ (10505678157900097/10000000000000000 : ℝ)^71 := by
      have hnat : (124471352441642504621 : ℕ)^16*10000000000000000^71 ≤ 10505678157900097^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        124471352441642504621 100000000000000000000 10505678157900097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10505678157900097/10000000000000000 : ℝ)) (X := (124471352441642504621/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (74471352441642504621/50000000000000000000 : ℝ) ≤ (136741476034087/125000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (74471352441642504621/50000000000000000000 : ℝ)^16 ≤ (136741476034087/125000000000000 : ℝ)^71 := by
      have hnat : (74471352441642504621 : ℕ)^16*125000000000000^71 ≤ 136741476034087^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74471352441642504621 50000000000000000000 136741476034087 125000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (136741476034087/125000000000000 : ℝ)) (X := (74471352441642504621/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(505678157900097/7281700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(433639924826863/7281700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (72817/100000 : ℝ)) (alpha := (505678157900097/7281700000000000 : ℝ)) (beta := (433639924826863/7281700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (72817/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(505678157900097/7281700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(433639924826863/7281700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (71719/100000 : ℝ) ^ (71/16 : ℝ) ≤ (11437915392188135259/50000000000000000000 : ℝ) := by
    have hpowers : (71719/100000 : ℝ)^71 ≤ (11437915392188135259/50000000000000000000 : ℝ)^16 := by
      have hnat : (71719 : ℕ)^71*50000000000000000000^16 ≤ 11437915392188135259^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71719 100000 11437915392188135259 50000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71719/100000 : ℝ)) (X := (11437915392188135259/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (61437915392188135259/50000000000000000000 : ℝ) ≤ (10475179107647129/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (61437915392188135259/50000000000000000000 : ℝ)^16 ≤ (10475179107647129/10000000000000000 : ℝ)^71 := by
      have hnat : (61437915392188135259 : ℕ)^16*10000000000000000^71 ≤ 10475179107647129^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61437915392188135259 50000000000000000000 10475179107647129 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10475179107647129/10000000000000000 : ℝ)) (X := (61437915392188135259/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (36437915392188135259/25000000000000000000 : ℝ) ≤ (2177211636417603/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (36437915392188135259/25000000000000000000 : ℝ)^16 ≤ (2177211636417603/2000000000000000 : ℝ)^71 := by
      have hnat : (36437915392188135259 : ℕ)^16*2000000000000000^71 ≤ 2177211636417603^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36437915392188135259 25000000000000000000 2177211636417603 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2177211636417603/2000000000000000 : ℝ)) (X := (36437915392188135259/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(475179107647129/7171900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(205439537220443/3585950000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (71719/100000 : ℝ)) (alpha := (475179107647129/7171900000000000 : ℝ)) (beta := (205439537220443/3585950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (71719/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(475179107647129/7171900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(205439537220443/3585950000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-2055408213/10000000000 : ℝ)*X 0 0+(5190258383/10000000000 : ℝ)*X 0 1+(1054005153/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((4530955729/10000000000 : ℝ)*X 1 0+(-1484688563/10000000000 : ℝ)*X 1 1+(393996367/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((910705957/2000000000 : ℝ)*X 2 0+(6305618977/10000000000 : ℝ)*X 2 1+(-29019439/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((1400571237/2000000000 : ℝ)*X 0 0+(341103877/1250000000 : ℝ)*X 0 1+(2625796179/10000000000 : ℝ)*X 0 2+(1400571237/2000000000 : ℝ)*X 1 0+(341103877/1250000000 : ℝ)*X 1 1+(2625796179/10000000000 : ℝ)*X 1 2+(1400571237/2000000000 : ℝ)*X 2 0+(341103877/1250000000 : ℝ)*X 2 1+(2625796179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1915365321/10000000000 : ℝ)*X 0 0+(2067248783/5000000000 : ℝ)*X 0 1+(6364010253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1989087407/5000000000 : ℝ)*X 1 0+(-35319177/400000000 : ℝ)*X 1 1+(7154327519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((100027357/250000000 : ℝ)*X 2 0+(3674307259/5000000000 : ℝ)*X 2 1+(-229969983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((3305289733/5000000000 : ℝ)*X 0 0+(1147210993/2500000000 : ℝ)*X 0 1+(112729593/1250000000 : ℝ)*X 0 2+(3305289733/5000000000 : ℝ)*X 1 0+(1147210993/2500000000 : ℝ)*X 1 1+(112729593/1250000000 : ℝ)*X 1 2+(3305289733/5000000000 : ℝ)*X 2 0+(1147210993/2500000000 : ℝ)*X 2 1+(112729593/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-926530823/10000000000 : ℝ)*X 0 0+(609195861/1250000000 : ℝ)*X 0 1+(253445597/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((3958093957/10000000000 : ℝ)*X 1 0+(-120430561/1250000000 : ℝ)*X 1 1+(1781614331/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((5783644167/10000000000 : ℝ)*X 2 0+(1423596311/2500000000 : ℝ)*X 2 1+(-487810517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((8471695569/10000000000 : ℝ)*X 0 0+(2197433901/10000000000 : ℝ)*X 0 1+(965575707/10000000000 : ℝ)*X 0 2+(8471695569/10000000000 : ℝ)*X 1 0+(2197433901/10000000000 : ℝ)*X 1 1+(965575707/10000000000 : ℝ)*X 1 2+(8471695569/10000000000 : ℝ)*X 2 0+(2197433901/10000000000 : ℝ)*X 2 1+(965575707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-176266583/2000000000 : ℝ)*X 0 0+(243603651/400000000 : ℝ)*X 0 1+(1290699921/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5805921543/10000000000 : ℝ)*X 1 0+(-17311747/400000000 : ℝ)*X 1 1+(5698807751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((490093581/1250000000 : ℝ)*X 2 0+(447826183/625000000 : ℝ)*X 2 1+(-475275709/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((67261889/78125000 : ℝ)*X 0 0+(391363133/2500000000 : ℝ)*X 0 1+(721125803/5000000000 : ℝ)*X 0 2+(67261889/78125000 : ℝ)*X 1 0+(391363133/2500000000 : ℝ)*X 1 1+(721125803/5000000000 : ℝ)*X 1 2+(67261889/78125000 : ℝ)*X 2 0+(391363133/2500000000 : ℝ)*X 2 1+(721125803/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((9021/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9021/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2759822011133951241831428773389/557560628126823437500000000000000000 : ℝ) := by norm_num
    linear_combination (3205767/1000000000000 : ℝ)*(base19) + (1175843/200000000000 : ℝ)*(base49) + (180022239017/500000000000 : ℝ)*(base59) + (2041900507203/500000000000 : ℝ)*(major_s2_0) + (2041900507203/500000000000 : ℝ)*(major_s2_1) + (2041900507203/500000000000 : ℝ)*(major_s2_2) + (4607569/100000000000 : ℝ)*(sp_s2_0) + (496893/200000000000 : ℝ)*(sp_s2_6) + (1420676115891/250000000000 : ℝ)*(sp_s2_7) + (1420682324633/250000000000 : ℝ)*(sp_s2_8) + (2841310504507/500000000000 : ℝ)*(sp_s2_9) + (621211838787/250000000000 : ℝ)*(sp_s2_13) + (9017477/500000000000 : ℝ)*(sp_s2_15) + (202391/1562500000 : ℝ)*(sp_s2_23) + (621212459903/250000000000 : ℝ)*(f.failure) + (2841375269627/500000000000 : ℝ)*(f.sum) + (135043479616721383977/261118121150000000000000000000000 : ℝ)*base62 + (290431741087023/896487500000000000000000000 : ℝ)*base65 + (777466318599623/1820425000000000000000000000 : ℝ)*base67 + (275478893914059/1792975000000000000000000000 : ℝ)*base68 + (26945503694151439813/245024377550000000000000000000000 : ℝ)*base71 + (2713364964601719/3416450000000000000000000000 : ℝ)*base73 + (723649685885057/1820425000000000000000000000 : ℝ)*base74 + (30731246369119/136658000000000000000000000 : ℝ)*base76 + (41889914824284518781/124387819825000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (2939/6250000000000000 : ℝ)*base86 + (2939/6250000000000000 : ℝ)*base88 + (2939/6250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52157/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(52157/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8058986118360464936419035695937/713677604002334000000000000000000000 : ℝ) := by norm_num
    linear_combination (2293073/500000000000 : ℝ)*(base27) + (65073/200000000000 : ℝ)*(base39) + (5151077/1000000000000 : ℝ)*(base59) + (797316978927/200000000000 : ℝ)*(major_s2_0) + (797316978927/200000000000 : ℝ)*(major_s2_1) + (797316978927/200000000000 : ℝ)*(major_s2_2) + (555917/100000000000 : ℝ)*(sp_s2_0) + (5706217/200000000000 : ℝ)*(sp_s2_2) + (53128399/1000000000000 : ℝ)*(sp_s2_7) + (5547410100891/1000000000000 : ℝ)*(sp_s2_14) + (277373439423/50000000000 : ℝ)*(sp_s2_15) + (44379522059/8000000000 : ℝ)*(sp_s2_16) + (1212811401751/500000000000 : ℝ)*(sp_s2_20) + (6984709/100000000000 : ℝ)*(sp_s2_27) + (1212848618369/500000000000 : ℝ)*(f.failure) + (277373439423/50000000000 : ℝ)*(f.sum) + (1820861299767354301/6527953028750000000000000000000 : ℝ)*base63 + (495878389710193/717190000000000000000000000 : ℝ)*base65 + (54885550721423/291268000000000000000000000 : ℝ)*base67 + (723793425904139/1434380000000000000000000000 : ℝ)*base69 + (47074683543295911793/98009751020000000000000000000000 : ℝ)*base71 + (74559143067887/683290000000000000000000000 : ℝ)*base73 + (643289086282007/1456340000000000000000000000 : ℝ)*base75 + (448066664549099/1366580000000000000000000000 : ℝ)*base77 + (7678013635422588281/99510255860000000000000000000000 : ℝ)*base78 + (10397/12500000000000000 : ℝ)*base86 + (10397/12500000000000000 : ℝ)*base88 + (10397/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5057/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5057/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (41129175396427294291932083182563/4460485025014587500000000000000000000 : ℝ) := by norm_num
    linear_combination (1603399/250000000000 : ℝ)*(base15) + (26656350531/200000000000 : ℝ)*(base40) + (941560825327/250000000000 : ℝ)*(major_s2_0) + (941560825327/250000000000 : ℝ)*(major_s2_1) + (941560825327/250000000000 : ℝ)*(major_s2_2) + (36100499/1000000000000 : ℝ)*(sp_s2_0) + (18456851/500000000000 : ℝ)*(sp_s2_1) + (22500509/1000000000000 : ℝ)*(sp_s2_9) + (626839/62500000000 : ℝ)*(sp_s2_16) + (20724143/250000000000 : ℝ)*(sp_s2_20) + (131020508289/25000000000 : ℝ)*(sp_s2_21) + (5240813104761/1000000000000 : ℝ)*(sp_s2_22) + (41926591217/8000000000 : ℝ)*(sp_s2_23) + (1145772100193/500000000000 : ℝ)*(sp_s2_27) + (1145813548479/500000000000 : ℝ)*(f.failure) + (5240856432059/1000000000000 : ℝ)*(f.sum) + (55217009326568412751/261118121150000000000000000000000 : ℝ)*base62 + (601510532737839/3585950000000000000000000000 : ℝ)*base64 + (653927438106477/3640850000000000000000000000 : ℝ)*base66 + (1451910397431429/3585950000000000000000000000 : ℝ)*base68 + (29148281707203886229/245024377550000000000000000000000 : ℝ)*base71 + (1076233993879823/3416450000000000000000000000 : ℝ)*base72 + (47904841099129/1820425000000000000000000000 : ℝ)*base75 + (55678498081671/85411250000000000000000000 : ℝ)*base77 + (30093973077461145947/124387819825000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (6673/12500000000000000 : ℝ)*base87 + (6673/12500000000000000 : ℝ)*base89 + (6673/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((68329/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68329/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72817/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(72817/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71719/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(71719/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9021/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9021/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52157/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(52157/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5057/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5057/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c311053_s2 p hpa hpb X hX hprev1

#print axioms solution

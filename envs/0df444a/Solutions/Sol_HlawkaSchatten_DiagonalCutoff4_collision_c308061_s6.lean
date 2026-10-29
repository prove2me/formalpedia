-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308061_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:38:47.578676+00:00
-- url     : https://prove2.me/submissions/ddd9e4e8-4327-4a3e-a75a-0f2988205bbf

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
theorem collision_support_c308061_s6_s6_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2627714483/10000000000 : ℝ)*x 0 + (2262528113/5000000000 : ℝ)*x 1 + (348979979/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627714483/10000000000 : ℝ)^69 ≤ (1755320769807/10000000000000 : ℝ)^53 := by
    have hnat : (2627714483 : ℕ)^69*10000000000000^53 ≤ 1755320769807^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627714483 10000000000 1755320769807 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262528113/5000000000 : ℝ)^69 ≤ (17808666954963/50000000000000 : ℝ)^53 := by
    have hnat : (2262528113 : ℕ)^69*50000000000000^53 ≤ 17808666954963^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262528113 5000000000 17808666954963 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (348979979/625000000 : ℝ)^69 ≤ (11707364593171/25000000000000 : ℝ)^53 := by
    have hnat : (348979979 : ℕ)^69*25000000000000^53 ≤ 11707364593171^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348979979 625000000 11707364593171 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2627714483/10000000000 : ℝ), (2262528113/5000000000 : ℝ), (348979979/625000000 : ℝ)] ![(1755320769807/10000000000000 : ℝ), (17808666954963/50000000000000 : ℝ), (11707364593171/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2627714483/10000000000 : ℝ)|^69 ≤ (1755320769807/10000000000000 : ℝ)^53
        have hw : |(-2627714483/10000000000 : ℝ)|=(2627714483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2262528113/5000000000 : ℝ)|^69 ≤ (17808666954963/50000000000000 : ℝ)^53
        have hw : |(2262528113/5000000000 : ℝ)|=(2262528113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(348979979/625000000 : ℝ)|^69 ≤ (11707364593171/25000000000000 : ℝ)^53
        have hw : |(348979979/625000000 : ℝ)|=(348979979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s6_s6_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (58518819/125000000 : ℝ)*x 0 + (-2646575741/10000000000 : ℝ)*x 1 + (2710162461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58518819/125000000 : ℝ)^69 ≤ (18614410710327/50000000000000 : ℝ)^53 := by
    have hnat : (58518819 : ℕ)^69*50000000000000^53 ≤ 18614410710327^53*125000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58518819 125000000 18614410710327 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2646575741/10000000000 : ℝ)^69 ≤ (17717414706953/100000000000000 : ℝ)^53 := by
    have hnat : (2646575741 : ℕ)^69*100000000000000^53 ≤ 17717414706953^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646575741 10000000000 17717414706953 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710162461/5000000000 : ℝ)^69 ≤ (1126344096571/2500000000000 : ℝ)^53 := by
    have hnat : (2710162461 : ℕ)^69*2500000000000^53 ≤ 1126344096571^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710162461 5000000000 1126344096571 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(58518819/125000000 : ℝ), (-2646575741/10000000000 : ℝ), (2710162461/5000000000 : ℝ)] ![(18614410710327/50000000000000 : ℝ), (17717414706953/100000000000000 : ℝ), (1126344096571/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(58518819/125000000 : ℝ)|^69 ≤ (18614410710327/50000000000000 : ℝ)^53
        have hw : |(58518819/125000000 : ℝ)|=(58518819/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2646575741/10000000000 : ℝ)|^69 ≤ (17717414706953/100000000000000 : ℝ)^53
        have hw : |(-2646575741/10000000000 : ℝ)|=(2646575741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710162461/5000000000 : ℝ)|^69 ≤ (1126344096571/2500000000000 : ℝ)^53
        have hw : |(2710162461/5000000000 : ℝ)|=(2710162461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s6_s6_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (468790329/1000000000 : ℝ)*x 0 + (2993615407/5000000000 : ℝ)*x 1 + (-94450547/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (468790329/1000000000 : ℝ)^69 ≤ (932376782687/2500000000000 : ℝ)^53 := by
    have hnat : (468790329 : ℕ)^69*2500000000000^53 ≤ 932376782687^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468790329 1000000000 932376782687 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2993615407/5000000000 : ℝ)^69 ≤ (512830058989/1000000000000 : ℝ)^53 := by
    have hnat : (2993615407 : ℕ)^69*1000000000000^53 ≤ 512830058989^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2993615407 5000000000 512830058989 1000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94450547/500000000 : ℝ)^69 ≤ (11421922779537/100000000000000 : ℝ)^53 := by
    have hnat : (94450547 : ℕ)^69*100000000000000^53 ≤ 11421922779537^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94450547 500000000 11421922779537 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(468790329/1000000000 : ℝ), (2993615407/5000000000 : ℝ), (-94450547/500000000 : ℝ)] ![(932376782687/2500000000000 : ℝ), (512830058989/1000000000000 : ℝ), (11421922779537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(468790329/1000000000 : ℝ)|^69 ≤ (932376782687/2500000000000 : ℝ)^53
        have hw : |(468790329/1000000000 : ℝ)|=(468790329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2993615407/5000000000 : ℝ)|^69 ≤ (512830058989/1000000000000 : ℝ)^53
        have hw : |(2993615407/5000000000 : ℝ)|=(2993615407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94450547/500000000 : ℝ)|^69 ≤ (11421922779537/100000000000000 : ℝ)^53
        have hw : |(-94450547/500000000 : ℝ)|=(94450547/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s6_s6_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2863036299/5000000000 : ℝ)*x 0 + (3245538889/10000000000 : ℝ)*x 1 + (762634477/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2863036299/5000000000 : ℝ)^69 ≤ (1512192405791/3125000000000 : ℝ)^53 := by
    have hnat : (2863036299 : ℕ)^69*3125000000000^53 ≤ 1512192405791^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2863036299 5000000000 1512192405791 3125000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3245538889/10000000000 : ℝ)^69 ≤ (11553691485547/50000000000000 : ℝ)^53 := by
    have hnat : (3245538889 : ℕ)^69*50000000000000^53 ≤ 11553691485547^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3245538889 10000000000 11553691485547 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (762634477/2000000000 : ℝ)^69 ≤ (14251230016803/50000000000000 : ℝ)^53 := by
    have hnat : (762634477 : ℕ)^69*50000000000000^53 ≤ 14251230016803^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      762634477 2000000000 14251230016803 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2863036299/5000000000 : ℝ), (3245538889/10000000000 : ℝ), (762634477/2000000000 : ℝ)] ![(1512192405791/3125000000000 : ℝ), (11553691485547/50000000000000 : ℝ), (14251230016803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2863036299/5000000000 : ℝ)|^69 ≤ (1512192405791/3125000000000 : ℝ)^53
        have hw : |(2863036299/5000000000 : ℝ)|=(2863036299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3245538889/10000000000 : ℝ)|^69 ≤ (11553691485547/50000000000000 : ℝ)^53
        have hw : |(3245538889/10000000000 : ℝ)|=(3245538889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(762634477/2000000000 : ℝ)|^69 ≤ (14251230016803/50000000000000 : ℝ)^53
        have hw : |(762634477/2000000000 : ℝ)|=(762634477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s6_s6_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1316009931/5000000000 : ℝ)*x 0 + (2217581239/5000000000 : ℝ)*x 1 + (5664187001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316009931/5000000000 : ℝ)^69 ≤ (8795329644831/50000000000000 : ℝ)^53 := by
    have hnat : (1316009931 : ℕ)^69*50000000000000^53 ≤ 8795329644831^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316009931 5000000000 8795329644831 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217581239/5000000000 : ℝ)^69 ≤ (17349469136141/50000000000000 : ℝ)^53 := by
    have hnat : (2217581239 : ℕ)^69*50000000000000^53 ≤ 17349469136141^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217581239 5000000000 17349469136141 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5664187001/10000000000 : ℝ)^69 ≤ (23855201212559/50000000000000 : ℝ)^53 := by
    have hnat : (5664187001 : ℕ)^69*50000000000000^53 ≤ 23855201212559^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664187001 10000000000 23855201212559 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1316009931/5000000000 : ℝ), (2217581239/5000000000 : ℝ), (5664187001/10000000000 : ℝ)] ![(8795329644831/50000000000000 : ℝ), (17349469136141/50000000000000 : ℝ), (23855201212559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1316009931/5000000000 : ℝ)|^69 ≤ (8795329644831/50000000000000 : ℝ)^53
        have hw : |(-1316009931/5000000000 : ℝ)|=(1316009931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2217581239/5000000000 : ℝ)|^69 ≤ (17349469136141/50000000000000 : ℝ)^53
        have hw : |(2217581239/5000000000 : ℝ)|=(2217581239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5664187001/10000000000 : ℝ)|^69 ≤ (23855201212559/50000000000000 : ℝ)^53
        have hw : |(5664187001/10000000000 : ℝ)|=(5664187001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s6_s6_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2304415623/5000000000 : ℝ)*x 0 + (-610400581/2500000000 : ℝ)*x 1 + (1130267673/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2304415623/5000000000 : ℝ)^69 ≤ (7295638556777/20000000000000 : ℝ)^53 := by
    have hnat : (2304415623 : ℕ)^69*20000000000000^53 ≤ 7295638556777^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2304415623 5000000000 7295638556777 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (610400581/2500000000 : ℝ)^69 ≤ (3988063703329/25000000000000 : ℝ)^53 := by
    have hnat : (610400581 : ℕ)^69*25000000000000^53 ≤ 3988063703329^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610400581 2500000000 3988063703329 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130267673/2000000000 : ℝ)^69 ≤ (743274256207/1562500000000 : ℝ)^53 := by
    have hnat : (1130267673 : ℕ)^69*1562500000000^53 ≤ 743274256207^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130267673 2000000000 743274256207 1562500000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2304415623/5000000000 : ℝ), (-610400581/2500000000 : ℝ), (1130267673/2000000000 : ℝ)] ![(7295638556777/20000000000000 : ℝ), (3988063703329/25000000000000 : ℝ), (743274256207/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2304415623/5000000000 : ℝ)|^69 ≤ (7295638556777/20000000000000 : ℝ)^53
        have hw : |(2304415623/5000000000 : ℝ)|=(2304415623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-610400581/2500000000 : ℝ)|^69 ≤ (3988063703329/25000000000000 : ℝ)^53
        have hw : |(-610400581/2500000000 : ℝ)|=(610400581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130267673/2000000000 : ℝ)|^69 ≤ (743274256207/1562500000000 : ℝ)^53
        have hw : |(1130267673/2000000000 : ℝ)|=(1130267673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s6_s6_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (184609359/400000000 : ℝ)*x 0 + (1242207929/2000000000 : ℝ)*x 1 + (-415329187/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (184609359/400000000 : ℝ)^69 ≤ (18272090917209/50000000000000 : ℝ)^53 := by
    have hnat : (184609359 : ℕ)^69*50000000000000^53 ≤ 18272090917209^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184609359 400000000 18272090917209 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1242207929/2000000000 : ℝ)^69 ≤ (53792699069427/100000000000000 : ℝ)^53 := by
    have hnat : (1242207929 : ℕ)^69*100000000000000^53 ≤ 53792699069427^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242207929 2000000000 53792699069427 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415329187/2500000000 : ℝ)^69 ≤ (1207889886051/12500000000000 : ℝ)^53 := by
    have hnat : (415329187 : ℕ)^69*12500000000000^53 ≤ 1207889886051^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415329187 2500000000 1207889886051 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(184609359/400000000 : ℝ), (1242207929/2000000000 : ℝ), (-415329187/2500000000 : ℝ)] ![(18272090917209/50000000000000 : ℝ), (53792699069427/100000000000000 : ℝ), (1207889886051/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(184609359/400000000 : ℝ)|^69 ≤ (18272090917209/50000000000000 : ℝ)^53
        have hw : |(184609359/400000000 : ℝ)|=(184609359/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1242207929/2000000000 : ℝ)|^69 ≤ (53792699069427/100000000000000 : ℝ)^53
        have hw : |(1242207929/2000000000 : ℝ)|=(1242207929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-415329187/2500000000 : ℝ)|^69 ≤ (1207889886051/12500000000000 : ℝ)^53
        have hw : |(-415329187/2500000000 : ℝ)|=(415329187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s6_s6_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5732718627/10000000000 : ℝ)*x 0 + (13639771/40000000 : ℝ)*x 1 + (227923151/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5732718627/10000000000 : ℝ)^69 ≤ (9692657939937/20000000000000 : ℝ)^53 := by
    have hnat : (5732718627 : ℕ)^69*20000000000000^53 ≤ 9692657939937^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5732718627 10000000000 9692657939937 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13639771/40000000 : ℝ)^69 ≤ (6160693649251/25000000000000 : ℝ)^53 := by
    have hnat : (13639771 : ℕ)^69*25000000000000^53 ≤ 6160693649251^53*40000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13639771 40000000 6160693649251 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227923151/625000000 : ℝ)^69 ≤ (1075757427487/4000000000000 : ℝ)^53 := by
    have hnat : (227923151 : ℕ)^69*4000000000000^53 ≤ 1075757427487^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227923151 625000000 1075757427487 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5732718627/10000000000 : ℝ), (13639771/40000000 : ℝ), (227923151/625000000 : ℝ)] ![(9692657939937/20000000000000 : ℝ), (6160693649251/25000000000000 : ℝ), (1075757427487/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5732718627/10000000000 : ℝ)|^69 ≤ (9692657939937/20000000000000 : ℝ)^53
        have hw : |(5732718627/10000000000 : ℝ)|=(5732718627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13639771/40000000 : ℝ)|^69 ≤ (6160693649251/25000000000000 : ℝ)^53
        have hw : |(13639771/40000000 : ℝ)|=(13639771/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(227923151/625000000 : ℝ)|^69 ≤ (1075757427487/4000000000000 : ℝ)^53
        have hw : |(227923151/625000000 : ℝ)|=(227923151/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s6_s6_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-469993381/2000000000 : ℝ)*x 0 + (1159686337/2500000000 : ℝ)*x 1 + (1138770947/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (469993381/2000000000 : ℝ)^69 ≤ (303545353693/2000000000000 : ℝ)^53 := by
    have hnat : (469993381 : ℕ)^69*2000000000000^53 ≤ 303545353693^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469993381 2000000000 303545353693 2000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1159686337/2500000000 : ℝ)^69 ≤ (36786736236329/100000000000000 : ℝ)^53 := by
    have hnat : (1159686337 : ℕ)^69*100000000000000^53 ≤ 36786736236329^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159686337 2500000000 36786736236329 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1138770947/2000000000 : ℝ)^69 ≤ (4803599605383/10000000000000 : ℝ)^53 := by
    have hnat : (1138770947 : ℕ)^69*10000000000000^53 ≤ 4803599605383^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138770947 2000000000 4803599605383 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-469993381/2000000000 : ℝ), (1159686337/2500000000 : ℝ), (1138770947/2000000000 : ℝ)] ![(303545353693/2000000000000 : ℝ), (36786736236329/100000000000000 : ℝ), (4803599605383/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-469993381/2000000000 : ℝ)|^69 ≤ (303545353693/2000000000000 : ℝ)^53
        have hw : |(-469993381/2000000000 : ℝ)|=(469993381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1159686337/2500000000 : ℝ)|^69 ≤ (36786736236329/100000000000000 : ℝ)^53
        have hw : |(1159686337/2500000000 : ℝ)|=(1159686337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1138770947/2000000000 : ℝ)|^69 ≤ (4803599605383/10000000000000 : ℝ)^53
        have hw : |(1138770947/2000000000 : ℝ)|=(1138770947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s6_s6_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1130899901/2500000000 : ℝ)*x 0 + (-639600833/2500000000 : ℝ)*x 1 + (5639945663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1130899901/2500000000 : ℝ)^69 ≤ (17801204075719/50000000000000 : ℝ)^53 := by
    have hnat : (1130899901 : ℕ)^69*50000000000000^53 ≤ 17801204075719^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130899901 2500000000 17801204075719 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639600833/2500000000 : ℝ)^69 ≤ (3390569661603/20000000000000 : ℝ)^53 := by
    have hnat : (639600833 : ℕ)^69*20000000000000^53 ≤ 3390569661603^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639600833 2500000000 3390569661603 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5639945663/10000000000 : ℝ)^69 ≤ (23722371759659/50000000000000 : ℝ)^53 := by
    have hnat : (5639945663 : ℕ)^69*50000000000000^53 ≤ 23722371759659^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5639945663 10000000000 23722371759659 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1130899901/2500000000 : ℝ), (-639600833/2500000000 : ℝ), (5639945663/10000000000 : ℝ)] ![(17801204075719/50000000000000 : ℝ), (3390569661603/20000000000000 : ℝ), (23722371759659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1130899901/2500000000 : ℝ)|^69 ≤ (17801204075719/50000000000000 : ℝ)^53
        have hw : |(1130899901/2500000000 : ℝ)|=(1130899901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-639600833/2500000000 : ℝ)|^69 ≤ (3390569661603/20000000000000 : ℝ)^53
        have hw : |(-639600833/2500000000 : ℝ)|=(639600833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5639945663/10000000000 : ℝ)|^69 ≤ (23722371759659/50000000000000 : ℝ)^53
        have hw : |(5639945663/10000000000 : ℝ)|=(5639945663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s6_s6_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1242243201/2500000000 : ℝ)*x 0 + (5873492713/10000000000 : ℝ)*x 1 + (-1672709363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1242243201/2500000000 : ℝ)^69 ≤ (40232176128673/100000000000000 : ℝ)^53 := by
    have hnat : (1242243201 : ℕ)^69*100000000000000^53 ≤ 40232176128673^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242243201 2500000000 40232176128673 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5873492713/10000000000 : ℝ)^69 ≤ (50018345269509/100000000000000 : ℝ)^53 := by
    have hnat : (5873492713 : ℕ)^69*100000000000000^53 ≤ 50018345269509^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5873492713 10000000000 50018345269509 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1672709363/10000000000 : ℝ)^69 ≤ (304671205923/3125000000000 : ℝ)^53 := by
    have hnat : (1672709363 : ℕ)^69*3125000000000^53 ≤ 304671205923^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1672709363 10000000000 304671205923 3125000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1242243201/2500000000 : ℝ), (5873492713/10000000000 : ℝ), (-1672709363/10000000000 : ℝ)] ![(40232176128673/100000000000000 : ℝ), (50018345269509/100000000000000 : ℝ), (304671205923/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1242243201/2500000000 : ℝ)|^69 ≤ (40232176128673/100000000000000 : ℝ)^53
        have hw : |(1242243201/2500000000 : ℝ)|=(1242243201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5873492713/10000000000 : ℝ)|^69 ≤ (50018345269509/100000000000000 : ℝ)^53
        have hw : |(5873492713/10000000000 : ℝ)|=(5873492713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1672709363/10000000000 : ℝ)|^69 ≤ (304671205923/3125000000000 : ℝ)^53
        have hw : |(-1672709363/10000000000 : ℝ)|=(1672709363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s6_s6_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5925406/9765625 : ℝ)*x 0 + (1537055787/5000000000 : ℝ)*x 1 + (3583446737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5925406/9765625 : ℝ)^69 ≤ (52181203399437/100000000000000 : ℝ)^53 := by
    have hnat : (5925406 : ℕ)^69*100000000000000^53 ≤ 52181203399437^53*9765625^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5925406 9765625 52181203399437 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1537055787/5000000000 : ℝ)^69 ≤ (21531235301547/100000000000000 : ℝ)^53 := by
    have hnat : (1537055787 : ℕ)^69*100000000000000^53 ≤ 21531235301547^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537055787 5000000000 21531235301547 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3583446737/10000000000 : ℝ)^69 ≤ (5257512256843/20000000000000 : ℝ)^53 := by
    have hnat : (3583446737 : ℕ)^69*20000000000000^53 ≤ 5257512256843^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3583446737 10000000000 5257512256843 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5925406/9765625 : ℝ), (1537055787/5000000000 : ℝ), (3583446737/10000000000 : ℝ)] ![(52181203399437/100000000000000 : ℝ), (21531235301547/100000000000000 : ℝ), (5257512256843/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5925406/9765625 : ℝ)|^69 ≤ (52181203399437/100000000000000 : ℝ)^53
        have hw : |(5925406/9765625 : ℝ)|=(5925406/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1537055787/5000000000 : ℝ)|^69 ≤ (21531235301547/100000000000000 : ℝ)^53
        have hw : |(1537055787/5000000000 : ℝ)|=(1537055787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3583446737/10000000000 : ℝ)|^69 ≤ (5257512256843/20000000000000 : ℝ)^53
        have hw : |(3583446737/10000000000 : ℝ)|=(3583446737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s6_s6_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2368228901/10000000000 : ℝ)*x 0 + (1171022369/2500000000 : ℝ)*x 1 + (2818542931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2368228901/10000000000 : ℝ)^69 ≤ (383274967779/2500000000000 : ℝ)^53 := by
    have hnat : (2368228901 : ℕ)^69*2500000000000^53 ≤ 383274967779^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2368228901 10000000000 383274967779 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1171022369/2500000000 : ℝ)^69 ≤ (18627787696057/50000000000000 : ℝ)^53 := by
    have hnat : (1171022369 : ℕ)^69*50000000000000^53 ≤ 18627787696057^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171022369 2500000000 18627787696057 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2818542931/5000000000 : ℝ)^69 ≤ (47413425883243/100000000000000 : ℝ)^53 := by
    have hnat : (2818542931 : ℕ)^69*100000000000000^53 ≤ 47413425883243^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2818542931 5000000000 47413425883243 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2368228901/10000000000 : ℝ), (1171022369/2500000000 : ℝ), (2818542931/5000000000 : ℝ)] ![(383274967779/2500000000000 : ℝ), (18627787696057/50000000000000 : ℝ), (47413425883243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2368228901/10000000000 : ℝ)|^69 ≤ (383274967779/2500000000000 : ℝ)^53
        have hw : |(-2368228901/10000000000 : ℝ)|=(2368228901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1171022369/2500000000 : ℝ)|^69 ≤ (18627787696057/50000000000000 : ℝ)^53
        have hw : |(1171022369/2500000000 : ℝ)|=(1171022369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2818542931/5000000000 : ℝ)|^69 ≤ (47413425883243/100000000000000 : ℝ)^53
        have hw : |(2818542931/5000000000 : ℝ)|=(2818542931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s6_s6_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (247215519/500000000 : ℝ)*x 0 + (-2388548249/10000000000 : ℝ)*x 1 + (5371406369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (247215519/500000000 : ℝ)^69 ≤ (999310137823/2500000000000 : ℝ)^53 := by
    have hnat : (247215519 : ℕ)^69*2500000000000^53 ≤ 999310137823^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247215519 500000000 999310137823 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2388548249/10000000000 : ℝ)^69 ≤ (15502469730357/100000000000000 : ℝ)^53 := by
    have hnat : (2388548249 : ℕ)^69*100000000000000^53 ≤ 15502469730357^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388548249 10000000000 15502469730357 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5371406369/10000000000 : ℝ)^69 ≤ (8905024947417/20000000000000 : ℝ)^53 := by
    have hnat : (5371406369 : ℕ)^69*20000000000000^53 ≤ 8905024947417^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371406369 10000000000 8905024947417 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(247215519/500000000 : ℝ), (-2388548249/10000000000 : ℝ), (5371406369/10000000000 : ℝ)] ![(999310137823/2500000000000 : ℝ), (15502469730357/100000000000000 : ℝ), (8905024947417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(247215519/500000000 : ℝ)|^69 ≤ (999310137823/2500000000000 : ℝ)^53
        have hw : |(247215519/500000000 : ℝ)|=(247215519/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2388548249/10000000000 : ℝ)|^69 ≤ (15502469730357/100000000000000 : ℝ)^53
        have hw : |(-2388548249/10000000000 : ℝ)|=(2388548249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5371406369/10000000000 : ℝ)|^69 ≤ (8905024947417/20000000000000 : ℝ)^53
        have hw : |(5371406369/10000000000 : ℝ)|=(5371406369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s6_s6_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4507852219/10000000000 : ℝ)*x 0 + (1234699761/2000000000 : ℝ)*x 1 + (-18593591/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4507852219/10000000000 : ℝ)^69 ≤ (35441140064171/100000000000000 : ℝ)^53 := by
    have hnat : (4507852219 : ℕ)^69*100000000000000^53 ≤ 35441140064171^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507852219 10000000000 35441140064171 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1234699761/2000000000 : ℝ)^69 ≤ (13342449379139/25000000000000 : ℝ)^53 := by
    have hnat : (1234699761 : ℕ)^69*25000000000000^53 ≤ 13342449379139^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1234699761 2000000000 13342449379139 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18593591/100000000 : ℝ)^69 ≤ (2237812479967/20000000000000 : ℝ)^53 := by
    have hnat : (18593591 : ℕ)^69*20000000000000^53 ≤ 2237812479967^53*100000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18593591 100000000 2237812479967 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4507852219/10000000000 : ℝ), (1234699761/2000000000 : ℝ), (-18593591/100000000 : ℝ)] ![(35441140064171/100000000000000 : ℝ), (13342449379139/25000000000000 : ℝ), (2237812479967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4507852219/10000000000 : ℝ)|^69 ≤ (35441140064171/100000000000000 : ℝ)^53
        have hw : |(4507852219/10000000000 : ℝ)|=(4507852219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1234699761/2000000000 : ℝ)|^69 ≤ (13342449379139/25000000000000 : ℝ)^53
        have hw : |(1234699761/2000000000 : ℝ)|=(1234699761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18593591/100000000 : ℝ)|^69 ≤ (2237812479967/20000000000000 : ℝ)^53
        have hw : |(-18593591/100000000 : ℝ)|=(18593591/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s6_s6_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3057441611/5000000000 : ℝ)*x 0 + (3072029307/10000000000 : ℝ)*x 1 + (176491771/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3057441611/5000000000 : ℝ)^69 ≤ (52711038985593/100000000000000 : ℝ)^53 := by
    have hnat : (3057441611 : ℕ)^69*100000000000000^53 ≤ 52711038985593^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3057441611 5000000000 52711038985593 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3072029307/10000000000 : ℝ)^69 ≤ (2151225012911/10000000000000 : ℝ)^53 := by
    have hnat : (3072029307 : ℕ)^69*10000000000000^53 ≤ 2151225012911^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3072029307 10000000000 2151225012911 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176491771/500000000 : ℝ)^69 ≤ (12888355435791/50000000000000 : ℝ)^53 := by
    have hnat : (176491771 : ℕ)^69*50000000000000^53 ≤ 12888355435791^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176491771 500000000 12888355435791 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3057441611/5000000000 : ℝ), (3072029307/10000000000 : ℝ), (176491771/500000000 : ℝ)] ![(52711038985593/100000000000000 : ℝ), (2151225012911/10000000000000 : ℝ), (12888355435791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3057441611/5000000000 : ℝ)|^69 ≤ (52711038985593/100000000000000 : ℝ)^53
        have hw : |(3057441611/5000000000 : ℝ)|=(3057441611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3072029307/10000000000 : ℝ)|^69 ≤ (2151225012911/10000000000000 : ℝ)^53
        have hw : |(3072029307/10000000000 : ℝ)|=(3072029307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(176491771/500000000 : ℝ)|^69 ≤ (12888355435791/50000000000000 : ℝ)^53
        have hw : |(176491771/500000000 : ℝ)|=(176491771/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308061_s6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((3033/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3033/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14409/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14409/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1339/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1339/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15977/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15977/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19879/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19879/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4623/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4623/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (3033/12500 : ℝ) ^ (17/4 : ℝ) ≤ (194616731959539/80000000000000000 : ℝ) := by
    have hpowers : (3033/12500 : ℝ)^17 ≤ (194616731959539/80000000000000000 : ℝ)^4 := by
      have hnat : (3033 : ℕ)^17*80000000000000000^4 ≤ 194616731959539^4*12500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3033 12500 194616731959539 80000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3033/12500 : ℝ)) (X := (194616731959539/80000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s6_corner0a : (80194616731959539/80000000000000000 : ℝ) ≤ (10005718704915771/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (80194616731959539/80000000000000000 : ℝ)^4 ≤ (10005718704915771/10000000000000000 : ℝ)^17 := by
      have hnat : (80194616731959539 : ℕ)^4*10000000000000000^17 ≤ 10005718704915771^17*80000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80194616731959539 80000000000000000 10005718704915771 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005718704915771/10000000000000000 : ℝ)) (X := (80194616731959539/80000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s6_corner0b : (40194616731959539/40000000000000000 : ℝ) ≤ (10011426806929507/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (40194616731959539/40000000000000000 : ℝ)^4 ≤ (10011426806929507/10000000000000000 : ℝ)^17 := by
      have hnat : (40194616731959539 : ℕ)^4*10000000000000000^17 ≤ 10011426806929507^17*40000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40194616731959539 40000000000000000 10011426806929507 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011426806929507/10000000000000000 : ℝ)) (X := (40194616731959539/40000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(5718704915771/2426400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(713512751717/303300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (3033/12500 : ℝ)) (alpha := (5718704915771/2426400000000000 : ℝ)) (beta := (713512751717/303300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3033/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(5718704915771/2426400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(713512751717/303300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (14409/50000 : ℝ) ^ (17/4 : ℝ) ≤ (101065121632653013/20000000000000000000 : ℝ) := by
    have hpowers : (14409/50000 : ℝ)^17 ≤ (101065121632653013/20000000000000000000 : ℝ)^4 := by
      have hnat : (14409 : ℕ)^17*20000000000000000000^4 ≤ 101065121632653013^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14409 50000 101065121632653013 20000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14409/50000 : ℝ)) (X := (101065121632653013/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s6_corner1a : (20101065121632653013/20000000000000000000 : ℝ) ≤ (2502966777334491/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (20101065121632653013/20000000000000000000 : ℝ)^4 ≤ (2502966777334491/2500000000000000 : ℝ)^17 := by
      have hnat : (20101065121632653013 : ℕ)^4*2500000000000000^17 ≤ 2502966777334491^17*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20101065121632653013 20000000000000000000 2502966777334491 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502966777334491/2500000000000000 : ℝ)) (X := (20101065121632653013/20000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s6_corner1b : (10101065121632653013/10000000000000000000 : ℝ) ≤ (626480542440317/625000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (10101065121632653013/10000000000000000000 : ℝ)^4 ≤ (626480542440317/625000000000000 : ℝ)^17 := by
      have hnat : (10101065121632653013 : ℕ)^4*625000000000000^17 ≤ 626480542440317^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10101065121632653013 10000000000000000000 626480542440317 625000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626480542440317/625000000000000 : ℝ)) (X := (10101065121632653013/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(2966777334491/720450000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(2955392426777/720450000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (14409/50000 : ℝ)) (alpha := (2966777334491/720450000000000 : ℝ)) (beta := (2955392426777/720450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (14409/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(2966777334491/720450000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(2955392426777/720450000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (1339/5000 : ℝ) ^ (17/4 : ℝ) ≤ (36999421509538359/10000000000000000000 : ℝ) := by
    have hpowers : (1339/5000 : ℝ)^17 ≤ (36999421509538359/10000000000000000000 : ℝ)^4 := by
      have hnat : (1339 : ℕ)^17*10000000000000000000^4 ≤ 36999421509538359^4*5000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1339 5000 36999421509538359 10000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1339/5000 : ℝ)) (X := (36999421509538359/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s6_corner2a : (10036999421509538359/10000000000000000000 : ℝ) ≤ (1251086682137007/1250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (10036999421509538359/10000000000000000000 : ℝ)^4 ≤ (1251086682137007/1250000000000000 : ℝ)^17 := by
      have hnat : (10036999421509538359 : ℕ)^4*1250000000000000^17 ≤ 1251086682137007^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10036999421509538359 10000000000000000000 1251086682137007 1250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251086682137007/1250000000000000 : ℝ)) (X := (10036999421509538359/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s6_corner2b : (5036999421509538359/5000000000000000000 : ℝ) ≤ (10017362442310789/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (5036999421509538359/5000000000000000000 : ℝ)^4 ≤ (10017362442310789/10000000000000000 : ℝ)^17 := by
      have hnat : (5036999421509538359 : ℕ)^4*10000000000000000^17 ≤ 10017362442310789^17*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5036999421509538359 5000000000000000000 10017362442310789 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10017362442310789/10000000000000000 : ℝ)) (X := (5036999421509538359/5000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1086682137007/334750000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(8668985214733/2678000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1339/5000 : ℝ)) (alpha := (1086682137007/334750000000000 : ℝ)) (beta := (8668985214733/2678000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1339/5000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1086682137007/334750000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(8668985214733/2678000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-2627714483/10000000000 : ℝ)*X 0 0+(2262528113/5000000000 : ℝ)*X 0 1+(348979979/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_1 : ((58518819/125000000 : ℝ)*X 1 0+(-2646575741/10000000000 : ℝ)*X 1 1+(2710162461/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((468790329/1000000000 : ℝ)*X 2 0+(2993615407/5000000000 : ℝ)*X 2 1+(-94450547/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((2863036299/5000000000 : ℝ)*X 0 0+(3245538889/10000000000 : ℝ)*X 0 1+(762634477/2000000000 : ℝ)*X 0 2+(2863036299/5000000000 : ℝ)*X 1 0+(3245538889/10000000000 : ℝ)*X 1 1+(762634477/2000000000 : ℝ)*X 1 2+(2863036299/5000000000 : ℝ)*X 2 0+(3245538889/10000000000 : ℝ)*X 2 1+(762634477/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-1316009931/5000000000 : ℝ)*X 0 0+(2217581239/5000000000 : ℝ)*X 0 1+(5664187001/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((2304415623/5000000000 : ℝ)*X 1 0+(-610400581/2500000000 : ℝ)*X 1 1+(1130267673/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((184609359/400000000 : ℝ)*X 2 0+(1242207929/2000000000 : ℝ)*X 2 1+(-415329187/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((5732718627/10000000000 : ℝ)*X 0 0+(13639771/40000000 : ℝ)*X 0 1+(227923151/625000000 : ℝ)*X 0 2+(5732718627/10000000000 : ℝ)*X 1 0+(13639771/40000000 : ℝ)*X 1 1+(227923151/625000000 : ℝ)*X 1 2+(5732718627/10000000000 : ℝ)*X 2 0+(13639771/40000000 : ℝ)*X 2 1+(227923151/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-469993381/2000000000 : ℝ)*X 0 0+(1159686337/2500000000 : ℝ)*X 0 1+(1138770947/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((1130899901/2500000000 : ℝ)*X 1 0+(-639600833/2500000000 : ℝ)*X 1 1+(5639945663/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((1242243201/2500000000 : ℝ)*X 2 0+(5873492713/10000000000 : ℝ)*X 2 1+(-1672709363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((5925406/9765625 : ℝ)*X 0 0+(1537055787/5000000000 : ℝ)*X 0 1+(3583446737/10000000000 : ℝ)*X 0 2+(5925406/9765625 : ℝ)*X 1 0+(1537055787/5000000000 : ℝ)*X 1 1+(3583446737/10000000000 : ℝ)*X 1 2+(5925406/9765625 : ℝ)*X 2 0+(1537055787/5000000000 : ℝ)*X 2 1+(3583446737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-2368228901/10000000000 : ℝ)*X 0 0+(1171022369/2500000000 : ℝ)*X 0 1+(2818542931/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((247215519/500000000 : ℝ)*X 1 0+(-2388548249/10000000000 : ℝ)*X 1 1+(5371406369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((4507852219/10000000000 : ℝ)*X 2 0+(1234699761/2000000000 : ℝ)*X 2 1+(-18593591/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((3057441611/5000000000 : ℝ)*X 0 0+(3072029307/10000000000 : ℝ)*X 0 1+(176491771/500000000 : ℝ)*X 0 2+(3057441611/5000000000 : ℝ)*X 1 0+(3072029307/10000000000 : ℝ)*X 1 1+(176491771/500000000 : ℝ)*X 1 2+(3057441611/5000000000 : ℝ)*X 2 0+(3072029307/10000000000 : ℝ)*X 2 1+(176491771/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((15977/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15977/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11646827507096009859091735689/722440043000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3101027/500000000000 : ℝ)*(base50) + (2866267262459/1000000000000 : ℝ)*(base59) + (8182279144701/500000000000 : ℝ)*(major_s6_0) + (8182279144701/500000000000 : ℝ)*(major_s6_1) + (8182279144701/500000000000 : ℝ)*(major_s6_2) + (1226045983/1000000000000 : ℝ)*(sp_s6_0) + (7772089/1000000000000 : ℝ)*(sp_s6_1) + (40705123/200000000000 : ℝ)*(sp_s6_2) + (4457075485713/200000000000 : ℝ)*(sp_s6_7) + (4457234051333/200000000000 : ℝ)*(sp_s6_8) + (22286086945531/1000000000000 : ℝ)*(sp_s6_9) + (1044250773041/100000000000 : ℝ)*(sp_s6_13) + (85089159/200000000000 : ℝ)*(sp_s6_15) + (313003403/1000000000000 : ℝ)*(sp_s6_23) + (1044250773041/100000000000 : ℝ)*(f.failure) + (5571650868637/250000000000 : ℝ)*(f.sum) + (56273155271213599/535934750000000000000000000000 : ℝ)*base63 + (986693810459033/1339000000000000000000000000 : ℝ)*base64 + (49555467135479/80050000000000000000000000 : ℝ)*base66 + (133631933483593/167375000000000000000000000 : ℝ)*base68 + (367868734904217337/902486000000000000000000000000 : ℝ)*base70 + (13277266857667/16850000000000000000000000 : ℝ)*base72 + (8386706562853/20012500000000000000000000 : ℝ)*base74 + (110449982511881/134800000000000000000000000 : ℝ)*base76 + (2055276417853917/5395370000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (8151/10000000000000000 : ℝ)*base87 + (8151/10000000000000000 : ℝ)*base89 + (8151/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19879/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19879/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2006921048633279230518109319/180610010750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1885621/1000000000000 : ℝ)*(base39) + (93553060891/1000000000000 : ℝ)*(base40) + (1312888222961/500000000000 : ℝ)*(base59) + (16727604651521/1000000000000 : ℝ)*(major_s6_0) + (16727604651521/1000000000000 : ℝ)*(major_s6_1) + (16727604651521/1000000000000 : ℝ)*(major_s6_2) + (117368571/250000000000 : ℝ)*(sp_s6_1) + (306405043/500000000000 : ℝ)*(sp_s6_2) + (173771501/1000000000000 : ℝ)*(sp_s6_6) + (713911211/1000000000000 : ℝ)*(sp_s6_7) + (22780317793543/1000000000000 : ℝ)*(sp_s6_14) + (2278056223047/100000000000 : ℝ)*(sp_s6_15) + (5695104723667/250000000000 : ℝ)*(sp_s6_16) + (2134800024563/200000000000 : ℝ)*(sp_s6_20) + (2668543473579/250000000000 : ℝ)*(f.failure) + (11390515852377/500000000000 : ℝ)*(f.sum) + (39042156813922507/4823412750000000000000000000000 : ℝ)*base62 + (1762915123282693/2678000000000000000000000000 : ℝ)*base64 + (403621493152703/720450000000000000000000000 : ℝ)*base66 + (183557094152403/334750000000000000000000000 : ℝ)*base68 + (1171059747554014307/16244748000000000000000000000000 : ℝ)*base71 + (202277732987783/303300000000000000000000000 : ℝ)*base72 + (401557540872839/720450000000000000000000000 : ℝ)*base74 + (914841968607989/2426400000000000000000000000 : ℝ)*base76 + (9838486154311573/97116660000000000000000000000 : ℝ)*base78 + (13669/25000000000000000 : ℝ)*base87 + (13669/25000000000000000 : ℝ)*base89 + (13669/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4623/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4623/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4396692658073709837323180549/361220021500000000000000000000000 : ℝ) := by norm_num
    linear_combination (14273008303/25000000000 : ℝ)*(base40) + (3659217/1000000000000 : ℝ)*(base50) + (168726309483/62500000000 : ℝ)*(base59) + (4145239366849/250000000000 : ℝ)*(major_s6_0) + (4145239366849/250000000000 : ℝ)*(major_s6_1) + (4145239366849/250000000000 : ℝ)*(major_s6_2) + (225954951/200000000000 : ℝ)*(sp_s6_0) + (144724673/125000000000 : ℝ)*(sp_s6_1) + (7672609/25000000000 : ℝ)*(sp_s6_2) + (58695699/500000000000 : ℝ)*(sp_s6_9) + (2822523164181/125000000000 : ℝ)*(sp_s6_21) + (1129007864541/50000000000 : ℝ)*(sp_s6_22) + (11290445396223/500000000000 : ℝ)*(sp_s6_23) + (2645148947329/250000000000 : ℝ)*(sp_s6_27) + (2645148947329/250000000000 : ℝ)*(f.failure) + (22581315088203/1000000000000 : ℝ)*(f.sum) + (1614331788559604957/4823412750000000000000000000000 : ℝ)*base62 + (362924233378183/669500000000000000000000000 : ℝ)*base65 + (234517421896493/180112500000000000000000000 : ℝ)*base67 + (37413769184393/83687500000000000000000000 : ℝ)*base69 + (1693696802720616883/4061187000000000000000000000000 : ℝ)*base71 + (9883412251477/75825000000000000000000000 : ℝ)*base72 + (222263180047/5628515625000000000000000 : ℝ)*base75 + (449023840852859/606600000000000000000000000 : ℝ)*base77 + (3941265947363563/24279165000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (25081/25000000000000000 : ℝ)*base86 + (25081/25000000000000000 : ℝ)*base88 + (25081/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((3033/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3033/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14409/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14409/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1339/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1339/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15977/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15977/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19879/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19879/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4623/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4623/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308061_s6 p hpa hpb X hX hprev5

#print axioms solution

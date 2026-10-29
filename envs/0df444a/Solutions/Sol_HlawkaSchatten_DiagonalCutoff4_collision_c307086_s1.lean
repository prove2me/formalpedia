-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307086_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:17:50.865815+00:00
-- url     : https://prove2.me/submissions/1b1d241c-5599-4fb3-b621-675211efce66

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
theorem collision_support_c307086_s1_s1_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (325812551/500000000 : ℝ)*x 0 + (24529543/78125000 : ℝ)*x 1 + (755161699/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (325812551/500000000 : ℝ)^17 ≤ (11423425593121/20000000000000 : ℝ)^13 := by
    have hnat : (325812551 : ℕ)^17*20000000000000^13 ≤ 11423425593121^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325812551 500000000 11423425593121 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24529543/78125000 : ℝ)^17 ≤ (21983622124979/100000000000000 : ℝ)^13 := by
    have hnat : (24529543 : ℕ)^17*100000000000000^13 ≤ 21983622124979^13*78125000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24529543 78125000 21983622124979 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (755161699/2500000000 : ℝ)^17 ≤ (20899249894303/100000000000000 : ℝ)^13 := by
    have hnat : (755161699 : ℕ)^17*100000000000000^13 ≤ 20899249894303^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755161699 2500000000 20899249894303 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(325812551/500000000 : ℝ), (24529543/78125000 : ℝ), (755161699/2500000000 : ℝ)] ![(11423425593121/20000000000000 : ℝ), (21983622124979/100000000000000 : ℝ), (20899249894303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(325812551/500000000 : ℝ)|^17 ≤ (11423425593121/20000000000000 : ℝ)^13
        have hw : |(325812551/500000000 : ℝ)|=(325812551/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(24529543/78125000 : ℝ)|^17 ≤ (21983622124979/100000000000000 : ℝ)^13
        have hw : |(24529543/78125000 : ℝ)|=(24529543/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(755161699/2500000000 : ℝ)|^17 ≤ (20899249894303/100000000000000 : ℝ)^13
        have hw : |(755161699/2500000000 : ℝ)|=(755161699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s1_s1_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3106950759/5000000000 : ℝ)*x 0 + (-3380424187/10000000000 : ℝ)*x 1 + (-788421631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3106950759/5000000000 : ℝ)^17 ≤ (26838248837509/50000000000000 : ℝ)^13 := by
    have hnat : (3106950759 : ℕ)^17*50000000000000^13 ≤ 26838248837509^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3106950759 5000000000 26838248837509 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3380424187/10000000000 : ℝ)^17 ≤ (2421247928133/10000000000000 : ℝ)^13 := by
    have hnat : (3380424187 : ℕ)^17*10000000000000^13 ≤ 2421247928133^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3380424187 10000000000 2421247928133 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (788421631/2500000000 : ℝ)^17 ≤ (22111023028181/100000000000000 : ℝ)^13 := by
    have hnat : (788421631 : ℕ)^17*100000000000000^13 ≤ 22111023028181^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788421631 2500000000 22111023028181 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3106950759/5000000000 : ℝ), (-3380424187/10000000000 : ℝ), (-788421631/2500000000 : ℝ)] ![(26838248837509/50000000000000 : ℝ), (2421247928133/10000000000000 : ℝ), (22111023028181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3106950759/5000000000 : ℝ)|^17 ≤ (26838248837509/50000000000000 : ℝ)^13
        have hw : |(3106950759/5000000000 : ℝ)|=(3106950759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3380424187/10000000000 : ℝ)|^17 ≤ (2421247928133/10000000000000 : ℝ)^13
        have hw : |(-3380424187/10000000000 : ℝ)|=(3380424187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-788421631/2500000000 : ℝ)|^17 ≤ (22111023028181/100000000000000 : ℝ)^13
        have hw : |(-788421631/2500000000 : ℝ)|=(788421631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s1_s1_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (28625623/80000000 : ℝ)*x 0 + (-3241621/12500000 : ℝ)*x 1 + (1622114707/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28625623/80000000 : ℝ)^17 ≤ (3260176517663/12500000000000 : ℝ)^13 := by
    have hnat : (28625623 : ℕ)^17*12500000000000^13 ≤ 3260176517663^13*80000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28625623 80000000 3260176517663 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3241621/12500000 : ℝ)^17 ≤ (8559907402371/50000000000000 : ℝ)^13 := by
    have hnat : (3241621 : ℕ)^17*50000000000000^13 ≤ 8559907402371^13*12500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3241621 12500000 8559907402371 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1622114707/2500000000 : ℝ)^17 ≤ (2839938651639/5000000000000 : ℝ)^13 := by
    have hnat : (1622114707 : ℕ)^17*5000000000000^13 ≤ 2839938651639^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1622114707 2500000000 2839938651639 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(28625623/80000000 : ℝ), (-3241621/12500000 : ℝ), (1622114707/2500000000 : ℝ)] ![(3260176517663/12500000000000 : ℝ), (8559907402371/50000000000000 : ℝ), (2839938651639/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(28625623/80000000 : ℝ)|^17 ≤ (3260176517663/12500000000000 : ℝ)^13
        have hw : |(28625623/80000000 : ℝ)|=(28625623/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3241621/12500000 : ℝ)|^17 ≤ (8559907402371/50000000000000 : ℝ)^13
        have hw : |(-3241621/12500000 : ℝ)|=(3241621/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1622114707/2500000000 : ℝ)|^17 ≤ (2839938651639/5000000000000 : ℝ)^13
        have hw : |(1622114707/2500000000 : ℝ)|=(1622114707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s1_s1_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7158957/1250000000 : ℝ)*x 0 + (-830767243/1000000000 : ℝ)*x 1 + (192329221/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7158957/1250000000 : ℝ)^17 ≤ (116970149699/100000000000000 : ℝ)^13 := by
    have hnat : (7158957 : ℕ)^17*100000000000000^13 ≤ 116970149699^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7158957 1250000000 116970149699 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (830767243/1000000000 : ℝ)^17 ≤ (78470023696153/100000000000000 : ℝ)^13 := by
    have hnat : (830767243 : ℕ)^17*100000000000000^13 ≤ 78470023696153^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830767243 1000000000 78470023696153 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (192329221/625000000 : ℝ)^17 ≤ (21413006135657/100000000000000 : ℝ)^13 := by
    have hnat : (192329221 : ℕ)^17*100000000000000^13 ≤ 21413006135657^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192329221 625000000 21413006135657 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7158957/1250000000 : ℝ), (-830767243/1000000000 : ℝ), (192329221/625000000 : ℝ)] ![(116970149699/100000000000000 : ℝ), (78470023696153/100000000000000 : ℝ), (21413006135657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7158957/1250000000 : ℝ)|^17 ≤ (116970149699/100000000000000 : ℝ)^13
        have hw : |(7158957/1250000000 : ℝ)|=(7158957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-830767243/1000000000 : ℝ)|^17 ≤ (78470023696153/100000000000000 : ℝ)^13
        have hw : |(-830767243/1000000000 : ℝ)|=(830767243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(192329221/625000000 : ℝ)|^17 ≤ (21413006135657/100000000000000 : ℝ)^13
        have hw : |(192329221/625000000 : ℝ)|=(192329221/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s1_s1_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4012808317/10000000000 : ℝ)*x 0 + (782173569/1250000000 : ℝ)*x 1 + (2407334237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4012808317/10000000000 : ℝ)^17 ≤ (151496481663/500000000000 : ℝ)^13 := by
    have hnat : (4012808317 : ℕ)^17*500000000000^13 ≤ 151496481663^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4012808317 10000000000 151496481663 500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (782173569/1250000000 : ℝ)^17 ≤ (54168256032497/100000000000000 : ℝ)^13 := by
    have hnat : (782173569 : ℕ)^17*100000000000000^13 ≤ 54168256032497^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782173569 1250000000 54168256032497 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2407334237/10000000000 : ℝ)^17 ≤ (124259580969/800000000000 : ℝ)^13 := by
    have hnat : (2407334237 : ℕ)^17*800000000000^13 ≤ 124259580969^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2407334237 10000000000 124259580969 800000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4012808317/10000000000 : ℝ), (782173569/1250000000 : ℝ), (2407334237/10000000000 : ℝ)] ![(151496481663/500000000000 : ℝ), (54168256032497/100000000000000 : ℝ), (124259580969/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4012808317/10000000000 : ℝ)|^17 ≤ (151496481663/500000000000 : ℝ)^13
        have hw : |(4012808317/10000000000 : ℝ)|=(4012808317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(782173569/1250000000 : ℝ)|^17 ≤ (54168256032497/100000000000000 : ℝ)^13
        have hw : |(782173569/1250000000 : ℝ)|=(782173569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2407334237/10000000000 : ℝ)|^17 ≤ (124259580969/800000000000 : ℝ)^13
        have hw : |(2407334237/10000000000 : ℝ)|=(2407334237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s1_s1_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4258547879/5000000000 : ℝ)*x 0 + (-19412879/200000000 : ℝ)*x 1 + (-2247460587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4258547879/5000000000 : ℝ)^17 ≤ (810667514487/1000000000000 : ℝ)^13 := by
    have hnat : (4258547879 : ℕ)^17*1000000000000^13 ≤ 810667514487^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258547879 5000000000 810667514487 1000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19412879/200000000 : ℝ)^17 ≤ (4735720809499/100000000000000 : ℝ)^13 := by
    have hnat : (19412879 : ℕ)^17*100000000000000^13 ≤ 4735720809499^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19412879 200000000 4735720809499 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247460587/10000000000 : ℝ)^17 ≤ (1419752773447/10000000000000 : ℝ)^13 := by
    have hnat : (2247460587 : ℕ)^17*10000000000000^13 ≤ 1419752773447^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247460587 10000000000 1419752773447 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4258547879/5000000000 : ℝ), (-19412879/200000000 : ℝ), (-2247460587/10000000000 : ℝ)] ![(810667514487/1000000000000 : ℝ), (4735720809499/100000000000000 : ℝ), (1419752773447/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4258547879/5000000000 : ℝ)|^17 ≤ (810667514487/1000000000000 : ℝ)^13
        have hw : |(4258547879/5000000000 : ℝ)|=(4258547879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19412879/200000000 : ℝ)|^17 ≤ (4735720809499/100000000000000 : ℝ)^13
        have hw : |(-19412879/200000000 : ℝ)|=(19412879/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2247460587/10000000000 : ℝ)|^17 ≤ (1419752773447/10000000000000 : ℝ)^13
        have hw : |(-2247460587/10000000000 : ℝ)|=(2247460587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s1_s1_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1760917967/5000000000 : ℝ)*x 0 + (-580184399/5000000000 : ℝ)*x 1 + (7485537689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1760917967/5000000000 : ℝ)^17 ≤ (3193180570519/12500000000000 : ℝ)^13 := by
    have hnat : (1760917967 : ℕ)^17*12500000000000^13 ≤ 3193180570519^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760917967 5000000000 3193180570519 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (580184399/5000000000 : ℝ)^17 ≤ (1495269409441/25000000000000 : ℝ)^13 := by
    have hnat : (580184399 : ℕ)^17*25000000000000^13 ≤ 1495269409441^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580184399 5000000000 1495269409441 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7485537689/10000000000 : ℝ)^17 ≤ (34236738893311/50000000000000 : ℝ)^13 := by
    have hnat : (7485537689 : ℕ)^17*50000000000000^13 ≤ 34236738893311^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7485537689 10000000000 34236738893311 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1760917967/5000000000 : ℝ), (-580184399/5000000000 : ℝ), (7485537689/10000000000 : ℝ)] ![(3193180570519/12500000000000 : ℝ), (1495269409441/25000000000000 : ℝ), (34236738893311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1760917967/5000000000 : ℝ)|^17 ≤ (3193180570519/12500000000000 : ℝ)^13
        have hw : |(1760917967/5000000000 : ℝ)|=(1760917967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-580184399/5000000000 : ℝ)|^17 ≤ (1495269409441/25000000000000 : ℝ)^13
        have hw : |(-580184399/5000000000 : ℝ)|=(580184399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7485537689/10000000000 : ℝ)|^17 ≤ (34236738893311/50000000000000 : ℝ)^13
        have hw : |(7485537689/10000000000 : ℝ)|=(7485537689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s1_s1_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-559449/10000000000 : ℝ)*x 0 + (-260445713/625000000 : ℝ)*x 1 + (7459963353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (559449/10000000000 : ℝ)^17 ≤ (137514699/50000000000000 : ℝ)^13 := by
    have hnat : (559449 : ℕ)^17*50000000000000^13 ≤ 137514699^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559449 10000000000 137514699 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260445713/625000000 : ℝ)^17 ≤ (7958001818777/25000000000000 : ℝ)^13 := by
    have hnat : (260445713 : ℕ)^17*25000000000000^13 ≤ 7958001818777^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260445713 625000000 7958001818777 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7459963353/10000000000 : ℝ)^17 ≤ (68167717688811/100000000000000 : ℝ)^13 := by
    have hnat : (7459963353 : ℕ)^17*100000000000000^13 ≤ 68167717688811^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7459963353 10000000000 68167717688811 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-559449/10000000000 : ℝ), (-260445713/625000000 : ℝ), (7459963353/10000000000 : ℝ)] ![(137514699/50000000000000 : ℝ), (7958001818777/25000000000000 : ℝ), (68167717688811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-559449/10000000000 : ℝ)|^17 ≤ (137514699/50000000000000 : ℝ)^13
        have hw : |(-559449/10000000000 : ℝ)|=(559449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-260445713/625000000 : ℝ)|^17 ≤ (7958001818777/25000000000000 : ℝ)^13
        have hw : |(-260445713/625000000 : ℝ)|=(260445713/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7459963353/10000000000 : ℝ)|^17 ≤ (68167717688811/100000000000000 : ℝ)^13
        have hw : |(7459963353/10000000000 : ℝ)|=(7459963353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s1_s1_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (874763307/1000000000 : ℝ)*x 0 + (243503739/1250000000 : ℝ)*x 1 + (897668227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874763307/1000000000 : ℝ)^17 ≤ (83948072584867/100000000000000 : ℝ)^13 := by
    have hnat : (874763307 : ℕ)^17*100000000000000^13 ≤ 83948072584867^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874763307 1000000000 83948072584867 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243503739/1250000000 : ℝ)^17 ≤ (117763216313/1000000000000 : ℝ)^13 := by
    have hnat : (243503739 : ℕ)^17*1000000000000^13 ≤ 117763216313^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243503739 1250000000 117763216313 1000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897668227/10000000000 : ℝ)^17 ≤ (4275605772001/100000000000000 : ℝ)^13 := by
    have hnat : (897668227 : ℕ)^17*100000000000000^13 ≤ 4275605772001^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897668227 10000000000 4275605772001 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874763307/1000000000 : ℝ), (243503739/1250000000 : ℝ), (897668227/10000000000 : ℝ)] ![(83948072584867/100000000000000 : ℝ), (117763216313/1000000000000 : ℝ), (4275605772001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874763307/1000000000 : ℝ)|^17 ≤ (83948072584867/100000000000000 : ℝ)^13
        have hw : |(874763307/1000000000 : ℝ)|=(874763307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(243503739/1250000000 : ℝ)|^17 ≤ (117763216313/1000000000000 : ℝ)^13
        have hw : |(243503739/1250000000 : ℝ)|=(243503739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897668227/10000000000 : ℝ)|^17 ≤ (4275605772001/100000000000000 : ℝ)^13
        have hw : |(897668227/10000000000 : ℝ)|=(897668227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s1_s1_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2077518039/2500000000 : ℝ)*x 0 + (-1996466367/10000000000 : ℝ)*x 1 + (-407892547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077518039/2500000000 : ℝ)^17 ≤ (19624916482751/25000000000000 : ℝ)^13 := by
    have hnat : (2077518039 : ℕ)^17*25000000000000^13 ≤ 19624916482751^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077518039 2500000000 19624916482751 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1996466367/10000000000 : ℝ)^17 ≤ (12160683846867/100000000000000 : ℝ)^13 := by
    have hnat : (1996466367 : ℕ)^17*100000000000000^13 ≤ 12160683846867^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996466367 10000000000 12160683846867 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407892547/2500000000 : ℝ)^17 ≤ (9339650202731/100000000000000 : ℝ)^13 := by
    have hnat : (407892547 : ℕ)^17*100000000000000^13 ≤ 9339650202731^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407892547 2500000000 9339650202731 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2077518039/2500000000 : ℝ), (-1996466367/10000000000 : ℝ), (-407892547/2500000000 : ℝ)] ![(19624916482751/25000000000000 : ℝ), (12160683846867/100000000000000 : ℝ), (9339650202731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2077518039/2500000000 : ℝ)|^17 ≤ (19624916482751/25000000000000 : ℝ)^13
        have hw : |(2077518039/2500000000 : ℝ)|=(2077518039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1996466367/10000000000 : ℝ)|^17 ≤ (12160683846867/100000000000000 : ℝ)^13
        have hw : |(-1996466367/10000000000 : ℝ)|=(1996466367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-407892547/2500000000 : ℝ)|^17 ≤ (9339650202731/100000000000000 : ℝ)^13
        have hw : |(-407892547/2500000000 : ℝ)|=(407892547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s1_s1_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2151903437/10000000000 : ℝ)*x 0 + (-276921769/2000000000 : ℝ)*x 1 + (261083367/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151903437/10000000000 : ℝ)^17 ≤ (1341335690421/10000000000000 : ℝ)^13 := by
    have hnat : (2151903437 : ℕ)^17*10000000000000^13 ≤ 1341335690421^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151903437 10000000000 1341335690421 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276921769/2000000000 : ℝ)^17 ≤ (7535638493789/100000000000000 : ℝ)^13 := by
    have hnat : (276921769 : ℕ)^17*100000000000000^13 ≤ 7535638493789^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276921769 2000000000 7535638493789 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261083367/312500000 : ℝ)^17 ≤ (79051004587547/100000000000000 : ℝ)^13 := by
    have hnat : (261083367 : ℕ)^17*100000000000000^13 ≤ 79051004587547^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261083367 312500000 79051004587547 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151903437/10000000000 : ℝ), (-276921769/2000000000 : ℝ), (261083367/312500000 : ℝ)] ![(1341335690421/10000000000000 : ℝ), (7535638493789/100000000000000 : ℝ), (79051004587547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151903437/10000000000 : ℝ)|^17 ≤ (1341335690421/10000000000000 : ℝ)^13
        have hw : |(2151903437/10000000000 : ℝ)|=(2151903437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-276921769/2000000000 : ℝ)|^17 ≤ (7535638493789/100000000000000 : ℝ)^13
        have hw : |(-276921769/2000000000 : ℝ)|=(276921769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261083367/312500000 : ℝ)|^17 ≤ (79051004587547/100000000000000 : ℝ)^13
        have hw : |(261083367/312500000 : ℝ)|=(261083367/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s1_s1_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (22698227/10000000000 : ℝ)*x 0 + (-4221963899/5000000000 : ℝ)*x 1 + (2899264517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22698227/10000000000 : ℝ)^17 ≤ (8717480821/25000000000000 : ℝ)^13 := by
    have hnat : (22698227 : ℕ)^17*25000000000000^13 ≤ 8717480821^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22698227 10000000000 8717480821 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4221963899/5000000000 : ℝ)^17 ≤ (80157252402993/100000000000000 : ℝ)^13 := by
    have hnat : (4221963899 : ℕ)^17*100000000000000^13 ≤ 80157252402993^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221963899 5000000000 80157252402993 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2899264517/10000000000 : ℝ)^17 ≤ (3961575533357/20000000000000 : ℝ)^13 := by
    have hnat : (2899264517 : ℕ)^17*20000000000000^13 ≤ 3961575533357^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2899264517 10000000000 3961575533357 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(22698227/10000000000 : ℝ), (-4221963899/5000000000 : ℝ), (2899264517/10000000000 : ℝ)] ![(8717480821/25000000000000 : ℝ), (80157252402993/100000000000000 : ℝ), (3961575533357/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(22698227/10000000000 : ℝ)|^17 ≤ (8717480821/25000000000000 : ℝ)^13
        have hw : |(22698227/10000000000 : ℝ)|=(22698227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4221963899/5000000000 : ℝ)|^17 ≤ (80157252402993/100000000000000 : ℝ)^13
        have hw : |(-4221963899/5000000000 : ℝ)|=(4221963899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2899264517/10000000000 : ℝ)|^17 ≤ (3961575533357/20000000000000 : ℝ)^13
        have hw : |(2899264517/10000000000 : ℝ)|=(2899264517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s1_s1_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8687673601/10000000000 : ℝ)*x 0 + (294085497/2000000000 : ℝ)*x 1 + (769405307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8687673601/10000000000 : ℝ)^17 ≤ (83196407151987/100000000000000 : ℝ)^13 := by
    have hnat : (8687673601 : ℕ)^17*100000000000000^13 ≤ 83196407151987^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8687673601 10000000000 83196407151987 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (294085497/2000000000 : ℝ)^17 ≤ (8152154757039/100000000000000 : ℝ)^13 := by
    have hnat : (294085497 : ℕ)^17*100000000000000^13 ≤ 8152154757039^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294085497 2000000000 8152154757039 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (769405307/5000000000 : ℝ)^17 ≤ (8651438072511/100000000000000 : ℝ)^13 := by
    have hnat : (769405307 : ℕ)^17*100000000000000^13 ≤ 8651438072511^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769405307 5000000000 8651438072511 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8687673601/10000000000 : ℝ), (294085497/2000000000 : ℝ), (769405307/5000000000 : ℝ)] ![(83196407151987/100000000000000 : ℝ), (8152154757039/100000000000000 : ℝ), (8651438072511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8687673601/10000000000 : ℝ)|^17 ≤ (83196407151987/100000000000000 : ℝ)^13
        have hw : |(8687673601/10000000000 : ℝ)|=(8687673601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(294085497/2000000000 : ℝ)|^17 ≤ (8152154757039/100000000000000 : ℝ)^13
        have hw : |(294085497/2000000000 : ℝ)|=(294085497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(769405307/5000000000 : ℝ)|^17 ≤ (8651438072511/100000000000000 : ℝ)^13
        have hw : |(769405307/5000000000 : ℝ)|=(769405307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s1_s1_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4546754403/10000000000 : ℝ)*x 0 + (-791235157/2000000000 : ℝ)*x 1 + (-277485487/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4546754403/10000000000 : ℝ)^17 ≤ (4459527972967/12500000000000 : ℝ)^13 := by
    have hnat : (4546754403 : ℕ)^17*12500000000000^13 ≤ 4459527972967^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4546754403 10000000000 4459527972967 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (791235157/2000000000 : ℝ)^17 ≤ (7435332304043/25000000000000 : ℝ)^13 := by
    have hnat : (791235157 : ℕ)^17*25000000000000^13 ≤ 7435332304043^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791235157 2000000000 7435332304043 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277485487/625000000 : ℝ)^17 ≤ (17291223490663/50000000000000 : ℝ)^13 := by
    have hnat : (277485487 : ℕ)^17*50000000000000^13 ≤ 17291223490663^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277485487 625000000 17291223490663 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4546754403/10000000000 : ℝ), (-791235157/2000000000 : ℝ), (-277485487/625000000 : ℝ)] ![(4459527972967/12500000000000 : ℝ), (7435332304043/25000000000000 : ℝ), (17291223490663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4546754403/10000000000 : ℝ)|^17 ≤ (4459527972967/12500000000000 : ℝ)^13
        have hw : |(4546754403/10000000000 : ℝ)|=(4546754403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-791235157/2000000000 : ℝ)|^17 ≤ (7435332304043/25000000000000 : ℝ)^13
        have hw : |(-791235157/2000000000 : ℝ)|=(791235157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-277485487/625000000 : ℝ)|^17 ≤ (17291223490663/50000000000000 : ℝ)^13
        have hw : |(-277485487/625000000 : ℝ)|=(277485487/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s1_s1_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7304622069/10000000000 : ℝ)*x 0 + (-1017371583/10000000000 : ℝ)*x 1 + (3844320563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7304622069/10000000000 : ℝ)^17 ≤ (129526272419/195312500000 : ℝ)^13 := by
    have hnat : (7304622069 : ℕ)^17*195312500000^13 ≤ 129526272419^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7304622069 10000000000 129526272419 195312500000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1017371583/10000000000 : ℝ)^17 ≤ (1259008667843/25000000000000 : ℝ)^13 := by
    have hnat : (1017371583 : ℕ)^17*25000000000000^13 ≤ 1259008667843^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017371583 10000000000 1259008667843 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3844320563/10000000000 : ℝ)^17 ≤ (28646513833169/100000000000000 : ℝ)^13 := by
    have hnat : (3844320563 : ℕ)^17*100000000000000^13 ≤ 28646513833169^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3844320563 10000000000 28646513833169 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7304622069/10000000000 : ℝ), (-1017371583/10000000000 : ℝ), (3844320563/10000000000 : ℝ)] ![(129526272419/195312500000 : ℝ), (1259008667843/25000000000000 : ℝ), (28646513833169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7304622069/10000000000 : ℝ)|^17 ≤ (129526272419/195312500000 : ℝ)^13
        have hw : |(7304622069/10000000000 : ℝ)|=(7304622069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1017371583/10000000000 : ℝ)|^17 ≤ (1259008667843/25000000000000 : ℝ)^13
        have hw : |(-1017371583/10000000000 : ℝ)|=(1017371583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3844320563/10000000000 : ℝ)|^17 ≤ (28646513833169/100000000000000 : ℝ)^13
        have hw : |(3844320563/10000000000 : ℝ)|=(3844320563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307086_s1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((88571/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(88571/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-94087/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-94087/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(93053/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(93053/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((72857/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72857/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-42861/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-42861/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8459/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8459/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92559/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s1_pow0 : (88571/100000 : ℝ) ^ (135/32 : ℝ) ≤ (59928887869856160057/100000000000000000000 : ℝ) := by
    have hpowers : (88571/100000 : ℝ)^135 ≤ (59928887869856160057/100000000000000000000 : ℝ)^32 := by
      have hnat : (88571 : ℕ)^135*100000000000000000000^32 ≤ 59928887869856160057^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88571 100000 59928887869856160057 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88571/100000 : ℝ)) (X := (59928887869856160057/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (159928887869856160057/100000000000000000000 : ℝ) ≤ (2794333522892573/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (159928887869856160057/100000000000000000000 : ℝ)^32 ≤ (2794333522892573/2500000000000000 : ℝ)^135 := by
      have hnat : (159928887869856160057 : ℕ)^32*2500000000000000^135 ≤ 2794333522892573^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        159928887869856160057 100000000000000000000 2794333522892573 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2794333522892573/2500000000000000 : ℝ)) (X := (159928887869856160057/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (109928887869856160057/50000000000000000000 : ℝ) ≤ (12053142348033243/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (109928887869856160057/50000000000000000000 : ℝ)^32 ≤ (12053142348033243/10000000000000000 : ℝ)^135 := by
      have hnat : (109928887869856160057 : ℕ)^32*10000000000000000^135 ≤ 12053142348033243^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109928887869856160057 50000000000000000000 12053142348033243 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12053142348033243/10000000000000000 : ℝ)) (X := (109928887869856160057/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(294333522892573/2214275000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(125115465208993/1265300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (88571/100000 : ℝ)) (alpha := (294333522892573/2214275000000000 : ℝ)) (beta := (125115465208993/1265300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (88571/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(294333522892573/2214275000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(125115465208993/1265300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (94087/100000 : ℝ) ^ (135/32 : ℝ) ≤ (7732645294661659493/10000000000000000000 : ℝ) := by
    have hpowers : (94087/100000 : ℝ)^135 ≤ (7732645294661659493/10000000000000000000 : ℝ)^32 := by
      have hnat : (94087 : ℕ)^135*10000000000000000000^32 ≤ 7732645294661659493^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        94087 100000 7732645294661659493 10000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (94087/100000 : ℝ)) (X := (7732645294661659493/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (17732645294661659493/10000000000000000000 : ℝ) ≤ (5727149817748071/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (17732645294661659493/10000000000000000000 : ℝ)^32 ≤ (5727149817748071/5000000000000000 : ℝ)^135 := by
      have hnat : (17732645294661659493 : ℕ)^32*5000000000000000^135 ≤ 5727149817748071^135*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17732645294661659493 10000000000000000000 5727149817748071 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5727149817748071/5000000000000000 : ℝ)) (X := (17732645294661659493/10000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12732645294661659493/5000000000000000000 : ℝ) ≤ (12480295314712437/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (12732645294661659493/5000000000000000000 : ℝ)^32 ≤ (12480295314712437/10000000000000000 : ℝ)^135 := by
      have hnat : (12732645294661659493 : ℕ)^32*10000000000000000^135 ≤ 12480295314712437^135*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12732645294661659493 5000000000000000000 12480295314712437 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12480295314712437/10000000000000000 : ℝ)) (X := (12732645294661659493/5000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(727149817748071/4704350000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(205199135843259/1881740000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (94087/100000 : ℝ)) (alpha := (727149817748071/4704350000000000 : ℝ)) (beta := (205199135843259/1881740000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (94087/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(727149817748071/4704350000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(205199135843259/1881740000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (93053/100000 : ℝ) ^ (135/32 : ℝ) ≤ (18451058931946700581/25000000000000000000 : ℝ) := by
    have hpowers : (93053/100000 : ℝ)^135 ≤ (18451058931946700581/25000000000000000000 : ℝ)^32 := by
      have hnat : (93053 : ℕ)^135*25000000000000000000^32 ≤ 18451058931946700581^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93053 100000 18451058931946700581 25000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (93053/100000 : ℝ)) (X := (18451058931946700581/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (43451058931946700581/25000000000000000000 : ℝ) ≤ (5699978268493759/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (43451058931946700581/25000000000000000000 : ℝ)^32 ≤ (5699978268493759/5000000000000000 : ℝ)^135 := by
      have hnat : (43451058931946700581 : ℕ)^32*5000000000000000^135 ≤ 5699978268493759^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43451058931946700581 25000000000000000000 5699978268493759 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5699978268493759/5000000000000000 : ℝ)) (X := (43451058931946700581/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (30951058931946700581/12500000000000000000 : ℝ) ≤ (12397582506120677/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (30951058931946700581/12500000000000000000 : ℝ)^32 ≤ (12397582506120677/10000000000000000 : ℝ)^135 := by
      have hnat : (30951058931946700581 : ℕ)^32*10000000000000000^135 ≤ 12397582506120677^135*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30951058931946700581 12500000000000000000 12397582506120677 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12397582506120677/10000000000000000 : ℝ)) (X := (30951058931946700581/12500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(699978268493759/4652650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(997625969133159/9305300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (93053/100000 : ℝ)) (alpha := (699978268493759/4652650000000000 : ℝ)) (beta := (997625969133159/9305300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (93053/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(699978268493759/4652650000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(997625969133159/9305300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((325812551/500000000 : ℝ)*X 1 0+(24529543/78125000 : ℝ)*X 1 1+(755161699/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3106950759/5000000000 : ℝ)*X 2 0+(-3380424187/10000000000 : ℝ)*X 2 1+(-788421631/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((28625623/80000000 : ℝ)*X 0 0+(-3241621/12500000 : ℝ)*X 0 1+(1622114707/2500000000 : ℝ)*X 0 2+(28625623/80000000 : ℝ)*X 1 0+(-3241621/12500000 : ℝ)*X 1 1+(1622114707/2500000000 : ℝ)*X 1 2+(28625623/80000000 : ℝ)*X 2 0+(-3241621/12500000 : ℝ)*X 2 1+(1622114707/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((7158957/1250000000 : ℝ)*X 0 0+(-830767243/1000000000 : ℝ)*X 0 1+(192329221/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4012808317/10000000000 : ℝ)*X 1 0+(782173569/1250000000 : ℝ)*X 1 1+(2407334237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4258547879/5000000000 : ℝ)*X 2 0+(-19412879/200000000 : ℝ)*X 2 1+(-2247460587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1760917967/5000000000 : ℝ)*X 0 0+(-580184399/5000000000 : ℝ)*X 0 1+(7485537689/10000000000 : ℝ)*X 0 2+(1760917967/5000000000 : ℝ)*X 1 0+(-580184399/5000000000 : ℝ)*X 1 1+(7485537689/10000000000 : ℝ)*X 1 2+(1760917967/5000000000 : ℝ)*X 2 0+(-580184399/5000000000 : ℝ)*X 2 1+(7485537689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-559449/10000000000 : ℝ)*X 0 0+(-260445713/625000000 : ℝ)*X 0 1+(7459963353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((874763307/1000000000 : ℝ)*X 1 0+(243503739/1250000000 : ℝ)*X 1 1+(897668227/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((2077518039/2500000000 : ℝ)*X 2 0+(-1996466367/10000000000 : ℝ)*X 2 1+(-407892547/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2151903437/10000000000 : ℝ)*X 0 0+(-276921769/2000000000 : ℝ)*X 0 1+(261083367/312500000 : ℝ)*X 0 2+(2151903437/10000000000 : ℝ)*X 1 0+(-276921769/2000000000 : ℝ)*X 1 1+(261083367/312500000 : ℝ)*X 1 2+(2151903437/10000000000 : ℝ)*X 2 0+(-276921769/2000000000 : ℝ)*X 2 1+(261083367/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((22698227/10000000000 : ℝ)*X 0 0+(-4221963899/5000000000 : ℝ)*X 0 1+(2899264517/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((8687673601/10000000000 : ℝ)*X 1 0+(294085497/2000000000 : ℝ)*X 1 1+(769405307/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4546754403/10000000000 : ℝ)*X 2 0+(-791235157/2000000000 : ℝ)*X 2 1+(-277485487/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((7304622069/10000000000 : ℝ)*X 0 0+(-1017371583/10000000000 : ℝ)*X 0 1+(3844320563/10000000000 : ℝ)*X 0 2+(7304622069/10000000000 : ℝ)*X 1 0+(-1017371583/10000000000 : ℝ)*X 1 1+(3844320563/10000000000 : ℝ)*X 1 2+(7304622069/10000000000 : ℝ)*X 2 0+(-1017371583/10000000000 : ℝ)*X 2 1+(3844320563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((72857/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72857/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13362744919561401380157/4428550000000000000000000000 : ℝ) := by norm_num
    linear_combination (241499772931/500000000000 : ℝ)*(base7) + (49817937663/200000000000 : ℝ)*(base43) + (756368716309/1000000000000 : ℝ)*(base54) + (412739058037/250000000000 : ℝ)*(major_s1_0) + (1401866543833/1000000000000 : ℝ)*(major_s1_1) + (894587515839/1000000000000 : ℝ)*(major_s1_2) + (3184801/125000000000 : ℝ)*(sp_s1_2) + (619081/40000000000 : ℝ)*(sp_s1_6) + (169268780471/100000000000 : ℝ)*(sp_s1_7) + (1941808411397/1000000000000 : ℝ)*(sp_s1_8) + (187264905673/200000000000 : ℝ)*(sp_s1_9) + (788669269253/1000000000000 : ℝ)*(sp_s1_13) + (9430599/1000000000000 : ℝ)*(sp_s1_20) + (7729593/250000000000 : ℝ)*(sp_s1_21) + (265515836831/250000000000 : ℝ)*(f.failure) + (1941808411397/1000000000000 : ℝ)*(f.sum) + (2009355516209086073/125072537300000000000000000000000 : ℝ)*base62 + (4169100062266751/9305300000000000000000000000 : ℝ)*base64 + (37514801407033/84006250000000000000000000 : ℝ)*base67 + (353498154047429/1163162500000000000000000000 : ℝ)*base69 + (159349725683735188627/824179726300000000000000000000000 : ℝ)*base71 + (15578779215347/39540625000000000000000000 : ℝ)*base73 + (102275736211393/268820000000000000000000000 : ℝ)*base75 + (77895340004833/4428550000000000000000000000 : ℝ)*base77 + (946447618003710731/8503448650000000000000000000000 : ℝ)*base78 + (661/3125000000000000 : ℝ)*base87 + (661/3125000000000000 : ℝ)*base89 + (661/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-42861/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-42861/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34166897552565033402842682217443/5538899850599150000000000000000000000 : ℝ) := by norm_num
    linear_combination (92859080311/100000000000 : ℝ)*(base7) + (104348966367/1000000000000 : ℝ)*(base33) + (20207/8000000000 : ℝ)*(base40) + (772740442643/500000000000 : ℝ)*(major_s1_0) + (1649829851653/1000000000000 : ℝ)*(major_s1_1) + (1649829851653/1000000000000 : ℝ)*(major_s1_2) + (4149923/200000000000 : ℝ)*(sp_s1_1) + (5967363/250000000000 : ℝ)*(sp_s1_2) + (643751/50000000000 : ℝ)*(sp_s1_13) + (166532266159/100000000000 : ℝ)*(sp_s1_14) + (97558879249/62500000000 : ℝ)*(sp_s1_15) + (390237456443/250000000000 : ℝ)*(sp_s1_16) + (124369792041/62500000000 : ℝ)*(sp_s1_20) + (87021/8000000000 : ℝ)*(sp_s1_22) + (530669372283/500000000000 : ℝ)*(f.failure) + (166532266159/100000000000 : ℝ)*(f.sum) + (72407045838734449867/875507761100000000000000000000000 : ℝ)*base62 + (2145208727151827/9305300000000000000000000000 : ℝ)*base64 + (1112328046901773/4704350000000000000000000000 : ℝ)*base67 + (1234997737628989/2326325000000000000000000000 : ℝ)*base68 + (58759668296580722729/824179726300000000000000000000000 : ℝ)*base71 + (198147271610531/632650000000000000000000000 : ℝ)*base72 + (905772918568953/1881740000000000000000000000 : ℝ)*base74 + (235114359979299/1107137500000000000000000000 : ℝ)*base77 + (1725765274897666981/7440517568750000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (277/6250000000000000 : ℝ)*base86 + (277/6250000000000000 : ℝ)*base88 + (277/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8459/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8459/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16328982746633931695229753988299/1107779970119830000000000000000000000 : ℝ) := by norm_num
    linear_combination (185799235393/250000000000 : ℝ)*(base7) + (7810061/1000000000000 : ℝ)*(base15) + (43016514211/1000000000000 : ℝ)*(base40) + (856699814407/1000000000000 : ℝ)*(base43) + (2164243/1000000000000 : ℝ)*(base50) + (429388424687/250000000000 : ℝ)*(major_s1_0) + (860853884341/1000000000000 : ℝ)*(major_s1_1) + (429388424687/250000000000 : ℝ)*(major_s1_2) + (38294207/1000000000000 : ℝ)*(sp_s1_2) + (87280091/1000000000000 : ℝ)*(sp_s1_7) + (1014812658003/1000000000000 : ℝ)*(sp_s1_21) + (46789798561/25000000000 : ℝ)*(sp_s1_22) + (1014861643887/1000000000000 : ℝ)*(sp_s1_23) + (462025642093/250000000000 : ℝ)*(sp_s1_27) + (2762264067/2500000000 : ℝ)*(f.failure) + (1871599752501/1000000000000 : ℝ)*(f.sum) + (93588449573511324953/875507761100000000000000000000000 : ℝ)*base63 + (674368730235733/2326325000000000000000000000 : ℝ)*base64 + (732681050192153/2352175000000000000000000000 : ℝ)*base67 + (285728464993139/581581250000000000000000000 : ℝ)*base69 + (49876255743411694561/206044931575000000000000000000000 : ℝ)*base70 + (98847283199721/316325000000000000000000000 : ℝ)*base73 + (132936300102451/1881740000000000000000000000 : ℝ)*base74 + (21193154881839/34598046875000000000000000 : ℝ)*base76 + (40171201785689752497/59524140550000000000000000000000 : ℝ)*base79 + (1/15625000000000 : ℝ)*base87 + (1/15625000000000 : ℝ)*base89 + (1/15625000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((88571/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(88571/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-94087/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-94087/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(93053/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(93053/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((72857/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72857/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-42861/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-42861/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8459/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8459/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307086_s1 p hpa hpb X hX hprev0

#print axioms solution

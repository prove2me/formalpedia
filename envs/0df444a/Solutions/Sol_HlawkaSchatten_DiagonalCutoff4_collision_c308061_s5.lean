-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308061_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:38:46.564423+00:00
-- url     : https://prove2.me/submissions/5f6a1c62-b929-4758-8ad1-98e0a4296597

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
theorem collision_support_c308061_s5_s5_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2480110843/10000000000 : ℝ)*x 0 + (906082741/2000000000 : ℝ)*x 1 + (2847436259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2480110843/10000000000 : ℝ)^69 ≤ (8140290718677/50000000000000 : ℝ)^53 := by
    have hnat : (2480110843 : ℕ)^69*50000000000000^53 ≤ 8140290718677^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2480110843 10000000000 8140290718677 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906082741/2000000000 : ℝ)^69 ≤ (17836121782221/50000000000000 : ℝ)^53 := by
    have hnat : (906082741 : ℕ)^69*50000000000000^53 ≤ 17836121782221^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906082741 2000000000 17836121782221 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2847436259/5000000000 : ℝ)^69 ≤ (24023587495927/50000000000000 : ℝ)^53 := by
    have hnat : (2847436259 : ℕ)^69*50000000000000^53 ≤ 24023587495927^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2847436259 5000000000 24023587495927 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2480110843/10000000000 : ℝ), (906082741/2000000000 : ℝ), (2847436259/5000000000 : ℝ)] ![(8140290718677/50000000000000 : ℝ), (17836121782221/50000000000000 : ℝ), (24023587495927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2480110843/10000000000 : ℝ)|^69 ≤ (8140290718677/50000000000000 : ℝ)^53
        have hw : |(-2480110843/10000000000 : ℝ)|=(2480110843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906082741/2000000000 : ℝ)|^69 ≤ (17836121782221/50000000000000 : ℝ)^53
        have hw : |(906082741/2000000000 : ℝ)|=(906082741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2847436259/5000000000 : ℝ)|^69 ≤ (24023587495927/50000000000000 : ℝ)^53
        have hw : |(2847436259/5000000000 : ℝ)|=(2847436259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s5_s5_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (587183831/1250000000 : ℝ)*x 0 + (-2540014637/10000000000 : ℝ)*x 1 + (5490204691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (587183831/1250000000 : ℝ)^69 ≤ (18697096846639/50000000000000 : ℝ)^53 := by
    have hnat : (587183831 : ℕ)^69*50000000000000^53 ≤ 18697096846639^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587183831 1250000000 18697096846639 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2540014637/10000000000 : ℝ)^69 ≤ (16794386146877/100000000000000 : ℝ)^53 := by
    have hnat : (2540014637 : ℕ)^69*100000000000000^53 ≤ 16794386146877^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540014637 10000000000 16794386146877 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490204691/10000000000 : ℝ)^69 ≤ (9162284030603/20000000000000 : ℝ)^53 := by
    have hnat : (5490204691 : ℕ)^69*20000000000000^53 ≤ 9162284030603^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490204691 10000000000 9162284030603 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(587183831/1250000000 : ℝ), (-2540014637/10000000000 : ℝ), (5490204691/10000000000 : ℝ)] ![(18697096846639/50000000000000 : ℝ), (16794386146877/100000000000000 : ℝ), (9162284030603/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(587183831/1250000000 : ℝ)|^69 ≤ (18697096846639/50000000000000 : ℝ)^53
        have hw : |(587183831/1250000000 : ℝ)|=(587183831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2540014637/10000000000 : ℝ)|^69 ≤ (16794386146877/100000000000000 : ℝ)^53
        have hw : |(-2540014637/10000000000 : ℝ)|=(2540014637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490204691/10000000000 : ℝ)|^69 ≤ (9162284030603/20000000000000 : ℝ)^53
        have hw : |(5490204691/10000000000 : ℝ)|=(5490204691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s5_s5_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1183213369/2500000000 : ℝ)*x 0 + (6082556853/10000000000 : ℝ)*x 1 + (-422804087/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1183213369/2500000000 : ℝ)^69 ≤ (37761305617249/100000000000000 : ℝ)^53 := by
    have hnat : (1183213369 : ℕ)^69*100000000000000^53 ≤ 37761305617249^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183213369 2500000000 37761305617249 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6082556853/10000000000 : ℝ)^69 ≤ (52348548644179/100000000000000 : ℝ)^53 := by
    have hnat : (6082556853 : ℕ)^69*100000000000000^53 ≤ 52348548644179^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6082556853 10000000000 52348548644179 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422804087/2500000000 : ℝ)^69 ≤ (9890145720199/100000000000000 : ℝ)^53 := by
    have hnat : (422804087 : ℕ)^69*100000000000000^53 ≤ 9890145720199^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422804087 2500000000 9890145720199 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1183213369/2500000000 : ℝ), (6082556853/10000000000 : ℝ), (-422804087/2500000000 : ℝ)] ![(37761305617249/100000000000000 : ℝ), (52348548644179/100000000000000 : ℝ), (9890145720199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1183213369/2500000000 : ℝ)|^69 ≤ (37761305617249/100000000000000 : ℝ)^53
        have hw : |(1183213369/2500000000 : ℝ)|=(1183213369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6082556853/10000000000 : ℝ)|^69 ≤ (52348548644179/100000000000000 : ℝ)^53
        have hw : |(6082556853/10000000000 : ℝ)|=(6082556853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-422804087/2500000000 : ℝ)|^69 ≤ (9890145720199/100000000000000 : ℝ)^53
        have hw : |(-422804087/2500000000 : ℝ)|=(422804087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s5_s5_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1166447691/2000000000 : ℝ)*x 0 + (3170918169/10000000000 : ℝ)*x 1 + (376353901/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1166447691/2000000000 : ℝ)^69 ≤ (49561453378939/100000000000000 : ℝ)^53 := by
    have hnat : (1166447691 : ℕ)^69*100000000000000^53 ≤ 49561453378939^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166447691 2000000000 49561453378939 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3170918169/10000000000 : ℝ)^69 ≤ (22418130063123/100000000000000 : ℝ)^53 := by
    have hnat : (3170918169 : ℕ)^69*100000000000000^53 ≤ 22418130063123^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3170918169 10000000000 22418130063123 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (376353901/1000000000 : ℝ)^69 ≤ (28020416542669/100000000000000 : ℝ)^53 := by
    have hnat : (376353901 : ℕ)^69*100000000000000^53 ≤ 28020416542669^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376353901 1000000000 28020416542669 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1166447691/2000000000 : ℝ), (3170918169/10000000000 : ℝ), (376353901/1000000000 : ℝ)] ![(49561453378939/100000000000000 : ℝ), (22418130063123/100000000000000 : ℝ), (28020416542669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1166447691/2000000000 : ℝ)|^69 ≤ (49561453378939/100000000000000 : ℝ)^53
        have hw : |(1166447691/2000000000 : ℝ)|=(1166447691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3170918169/10000000000 : ℝ)|^69 ≤ (22418130063123/100000000000000 : ℝ)^53
        have hw : |(3170918169/10000000000 : ℝ)|=(3170918169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(376353901/1000000000 : ℝ)|^69 ≤ (28020416542669/100000000000000 : ℝ)^53
        have hw : |(376353901/1000000000 : ℝ)|=(376353901/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s5_s5_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2491276947/10000000000 : ℝ)*x 0 + (816296483/2000000000 : ℝ)*x 1 + (1218913841/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2491276947/10000000000 : ℝ)^69 ≤ (8188036878331/50000000000000 : ℝ)^53 := by
    have hnat : (2491276947 : ℕ)^69*50000000000000^53 ≤ 8188036878331^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491276947 10000000000 8188036878331 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (816296483/2000000000 : ℝ)^69 ≤ (31140745325597/100000000000000 : ℝ)^53 := by
    have hnat : (816296483 : ℕ)^69*100000000000000^53 ≤ 31140745325597^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      816296483 2000000000 31140745325597 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1218913841/2000000000 : ℝ)^69 ≤ (419865447199/800000000000 : ℝ)^53 := by
    have hnat : (1218913841 : ℕ)^69*800000000000^53 ≤ 419865447199^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1218913841 2000000000 419865447199 800000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2491276947/10000000000 : ℝ), (816296483/2000000000 : ℝ), (1218913841/2000000000 : ℝ)] ![(8188036878331/50000000000000 : ℝ), (31140745325597/100000000000000 : ℝ), (419865447199/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2491276947/10000000000 : ℝ)|^69 ≤ (8188036878331/50000000000000 : ℝ)^53
        have hw : |(-2491276947/10000000000 : ℝ)|=(2491276947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(816296483/2000000000 : ℝ)|^69 ≤ (31140745325597/100000000000000 : ℝ)^53
        have hw : |(816296483/2000000000 : ℝ)|=(816296483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1218913841/2000000000 : ℝ)|^69 ≤ (419865447199/800000000000 : ℝ)^53
        have hw : |(1218913841/2000000000 : ℝ)|=(1218913841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s5_s5_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4453456161/10000000000 : ℝ)*x 0 + (-2106826509/10000000000 : ℝ)*x 1 + (6046865389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4453456161/10000000000 : ℝ)^69 ≤ (17442691706479/50000000000000 : ℝ)^53 := by
    have hnat : (4453456161 : ℕ)^69*50000000000000^53 ≤ 17442691706479^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4453456161 10000000000 17442691706479 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106826509/10000000000 : ℝ)^69 ≤ (3291404382063/25000000000000 : ℝ)^53 := by
    have hnat : (2106826509 : ℕ)^69*25000000000000^53 ≤ 3291404382063^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106826509 10000000000 3291404382063 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6046865389/10000000000 : ℝ)^69 ≤ (51948999049127/100000000000000 : ℝ)^53 := by
    have hnat : (6046865389 : ℕ)^69*100000000000000^53 ≤ 51948999049127^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6046865389 10000000000 51948999049127 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4453456161/10000000000 : ℝ), (-2106826509/10000000000 : ℝ), (6046865389/10000000000 : ℝ)] ![(17442691706479/50000000000000 : ℝ), (3291404382063/25000000000000 : ℝ), (51948999049127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4453456161/10000000000 : ℝ)|^69 ≤ (17442691706479/50000000000000 : ℝ)^53
        have hw : |(4453456161/10000000000 : ℝ)|=(4453456161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2106826509/10000000000 : ℝ)|^69 ≤ (3291404382063/25000000000000 : ℝ)^53
        have hw : |(-2106826509/10000000000 : ℝ)|=(2106826509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6046865389/10000000000 : ℝ)|^69 ≤ (51948999049127/100000000000000 : ℝ)^53
        have hw : |(6046865389/10000000000 : ℝ)|=(6046865389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s5_s5_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2244483269/5000000000 : ℝ)*x 0 + (207549913/312500000 : ℝ)*x 1 + (-1160117777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2244483269/5000000000 : ℝ)^69 ≤ (4405994633877/12500000000000 : ℝ)^53 := by
    have hnat : (2244483269 : ℕ)^69*12500000000000^53 ≤ 4405994633877^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244483269 5000000000 4405994633877 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207549913/312500000 : ℝ)^69 ≤ (11739482560773/20000000000000 : ℝ)^53 := by
    have hnat : (207549913 : ℕ)^69*20000000000000^53 ≤ 11739482560773^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207549913 312500000 11739482560773 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1160117777/10000000000 : ℝ)^69 ≤ (6054630103113/100000000000000 : ℝ)^53 := by
    have hnat : (1160117777 : ℕ)^69*100000000000000^53 ≤ 6054630103113^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1160117777 10000000000 6054630103113 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2244483269/5000000000 : ℝ), (207549913/312500000 : ℝ), (-1160117777/10000000000 : ℝ)] ![(4405994633877/12500000000000 : ℝ), (11739482560773/20000000000000 : ℝ), (6054630103113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2244483269/5000000000 : ℝ)|^69 ≤ (4405994633877/12500000000000 : ℝ)^53
        have hw : |(2244483269/5000000000 : ℝ)|=(2244483269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207549913/312500000 : ℝ)|^69 ≤ (11739482560773/20000000000000 : ℝ)^53
        have hw : |(207549913/312500000 : ℝ)|=(207549913/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1160117777/10000000000 : ℝ)|^69 ≤ (6054630103113/100000000000000 : ℝ)^53
        have hw : |(-1160117777/10000000000 : ℝ)|=(1160117777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s5_s5_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (583722707/1000000000 : ℝ)*x 0 + (1980174197/5000000000 : ℝ)*x 1 + (369220749/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (583722707/1000000000 : ℝ)^69 ≤ (49616650703477/100000000000000 : ℝ)^53 := by
    have hnat : (583722707 : ℕ)^69*100000000000000^53 ≤ 49616650703477^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583722707 1000000000 49616650703477 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1980174197/5000000000 : ℝ)^69 ≤ (7485734601533/25000000000000 : ℝ)^53 := by
    have hnat : (1980174197 : ℕ)^69*25000000000000^53 ≤ 7485734601533^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980174197 5000000000 7485734601533 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (369220749/1250000000 : ℝ)^69 ≤ (5110102718693/25000000000000 : ℝ)^53 := by
    have hnat : (369220749 : ℕ)^69*25000000000000^53 ≤ 5110102718693^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369220749 1250000000 5110102718693 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(583722707/1000000000 : ℝ), (1980174197/5000000000 : ℝ), (369220749/1250000000 : ℝ)] ![(49616650703477/100000000000000 : ℝ), (7485734601533/25000000000000 : ℝ), (5110102718693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(583722707/1000000000 : ℝ)|^69 ≤ (49616650703477/100000000000000 : ℝ)^53
        have hw : |(583722707/1000000000 : ℝ)|=(583722707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1980174197/5000000000 : ℝ)|^69 ≤ (7485734601533/25000000000000 : ℝ)^53
        have hw : |(1980174197/5000000000 : ℝ)|=(1980174197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(369220749/1250000000 : ℝ)|^69 ≤ (5110102718693/25000000000000 : ℝ)^53
        have hw : |(369220749/1250000000 : ℝ)|=(369220749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s5_s5_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-71980479/400000000 : ℝ)*x 0 + (2319031947/5000000000 : ℝ)*x 1 + (6095873641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71980479/400000000 : ℝ)^69 ≤ (2680623395411/25000000000000 : ℝ)^53 := by
    have hnat : (71980479 : ℕ)^69*25000000000000^53 ≤ 2680623395411^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71980479 400000000 2680623395411 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2319031947/5000000000 : ℝ)^69 ≤ (2298731300177/6250000000000 : ℝ)^53 := by
    have hnat : (2319031947 : ℕ)^69*6250000000000^53 ≤ 2298731300177^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2319031947 5000000000 2298731300177 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6095873641/10000000000 : ℝ)^69 ≤ (52497805606503/100000000000000 : ℝ)^53 := by
    have hnat : (6095873641 : ℕ)^69*100000000000000^53 ≤ 52497805606503^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6095873641 10000000000 52497805606503 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-71980479/400000000 : ℝ), (2319031947/5000000000 : ℝ), (6095873641/10000000000 : ℝ)] ![(2680623395411/25000000000000 : ℝ), (2298731300177/6250000000000 : ℝ), (52497805606503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-71980479/400000000 : ℝ)|^69 ≤ (2680623395411/25000000000000 : ℝ)^53
        have hw : |(-71980479/400000000 : ℝ)|=(71980479/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2319031947/5000000000 : ℝ)|^69 ≤ (2298731300177/6250000000000 : ℝ)^53
        have hw : |(2319031947/5000000000 : ℝ)|=(2319031947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6095873641/10000000000 : ℝ)|^69 ≤ (52497805606503/100000000000000 : ℝ)^53
        have hw : |(6095873641/10000000000 : ℝ)|=(6095873641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s5_s5_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (171912941/400000000 : ℝ)*x 0 + (-287069783/1250000000 : ℝ)*x 1 + (6048169873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171912941/400000000 : ℝ)^69 ≤ (832666662661/2500000000000 : ℝ)^53 := by
    have hnat : (171912941 : ℕ)^69*2500000000000^53 ≤ 832666662661^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171912941 400000000 832666662661 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287069783/1250000000 : ℝ)^69 ≤ (3682435959619/25000000000000 : ℝ)^53 := by
    have hnat : (287069783 : ℕ)^69*25000000000000^53 ≤ 3682435959619^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287069783 1250000000 3682435959619 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6048169873/10000000000 : ℝ)^69 ≤ (10392717928821/20000000000000 : ℝ)^53 := by
    have hnat : (6048169873 : ℕ)^69*20000000000000^53 ≤ 10392717928821^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6048169873 10000000000 10392717928821 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171912941/400000000 : ℝ), (-287069783/1250000000 : ℝ), (6048169873/10000000000 : ℝ)] ![(832666662661/2500000000000 : ℝ), (3682435959619/25000000000000 : ℝ), (10392717928821/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171912941/400000000 : ℝ)|^69 ≤ (832666662661/2500000000000 : ℝ)^53
        have hw : |(171912941/400000000 : ℝ)|=(171912941/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-287069783/1250000000 : ℝ)|^69 ≤ (3682435959619/25000000000000 : ℝ)^53
        have hw : |(-287069783/1250000000 : ℝ)|=(287069783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6048169873/10000000000 : ℝ)|^69 ≤ (10392717928821/20000000000000 : ℝ)^53
        have hw : |(6048169873/10000000000 : ℝ)|=(6048169873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s5_s5_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2719562403/5000000000 : ℝ)*x 0 + (5753934693/10000000000 : ℝ)*x 1 + (-1158813379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2719562403/5000000000 : ℝ)^69 ≤ (45257309253837/100000000000000 : ℝ)^53 := by
    have hnat : (2719562403 : ℕ)^69*100000000000000^53 ≤ 45257309253837^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719562403 5000000000 45257309253837 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5753934693/10000000000 : ℝ)^69 ≤ (4869692188639/10000000000000 : ℝ)^53 := by
    have hnat : (5753934693 : ℕ)^69*10000000000000^53 ≤ 4869692188639^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5753934693 10000000000 4869692188639 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1158813379/10000000000 : ℝ)^69 ≤ (604576884989/10000000000000 : ℝ)^53 := by
    have hnat : (1158813379 : ℕ)^69*10000000000000^53 ≤ 604576884989^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158813379 10000000000 604576884989 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2719562403/5000000000 : ℝ), (5753934693/10000000000 : ℝ), (-1158813379/10000000000 : ℝ)] ![(45257309253837/100000000000000 : ℝ), (4869692188639/10000000000000 : ℝ), (604576884989/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2719562403/5000000000 : ℝ)|^69 ≤ (45257309253837/100000000000000 : ℝ)^53
        have hw : |(2719562403/5000000000 : ℝ)|=(2719562403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5753934693/10000000000 : ℝ)|^69 ≤ (4869692188639/10000000000000 : ℝ)^53
        have hw : |(5753934693/10000000000 : ℝ)|=(5753934693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1158813379/10000000000 : ℝ)|^69 ≤ (604576884989/10000000000000 : ℝ)^53
        have hw : |(-1158813379/10000000000 : ℝ)|=(1158813379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s5_s5_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1680214643/2500000000 : ℝ)*x 0 + (2901821141/10000000000 : ℝ)*x 1 + (2950978523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1680214643/2500000000 : ℝ)^69 ≤ (29805511153351/50000000000000 : ℝ)^53 := by
    have hnat : (1680214643 : ℕ)^69*50000000000000^53 ≤ 29805511153351^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680214643 2500000000 29805511153351 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2901821141/10000000000 : ℝ)^69 ≤ (19973676128091/100000000000000 : ℝ)^53 := by
    have hnat : (2901821141 : ℕ)^69*100000000000000^53 ≤ 19973676128091^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2901821141 10000000000 19973676128091 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2950978523/10000000000 : ℝ)^69 ≤ (4083060311301/20000000000000 : ℝ)^53 := by
    have hnat : (2950978523 : ℕ)^69*20000000000000^53 ≤ 4083060311301^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2950978523 10000000000 4083060311301 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1680214643/2500000000 : ℝ), (2901821141/10000000000 : ℝ), (2950978523/10000000000 : ℝ)] ![(29805511153351/50000000000000 : ℝ), (19973676128091/100000000000000 : ℝ), (4083060311301/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1680214643/2500000000 : ℝ)|^69 ≤ (29805511153351/50000000000000 : ℝ)^53
        have hw : |(1680214643/2500000000 : ℝ)|=(1680214643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2901821141/10000000000 : ℝ)|^69 ≤ (19973676128091/100000000000000 : ℝ)^53
        have hw : |(2901821141/10000000000 : ℝ)|=(2901821141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2950978523/10000000000 : ℝ)|^69 ≤ (4083060311301/20000000000000 : ℝ)^53
        have hw : |(2950978523/10000000000 : ℝ)|=(2950978523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s5_s5_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1792207759/10000000000 : ℝ)*x 0 + (2495923039/5000000000 : ℝ)*x 1 + (1153758351/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1792207759/10000000000 : ℝ)^69 ≤ (10665866853887/100000000000000 : ℝ)^53 := by
    have hnat : (1792207759 : ℕ)^69*100000000000000^53 ≤ 10665866853887^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792207759 10000000000 10665866853887 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2495923039/5000000000 : ℝ)^69 ≤ (40473449720417/100000000000000 : ℝ)^53 := by
    have hnat : (2495923039 : ℕ)^69*100000000000000^53 ≤ 40473449720417^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495923039 5000000000 40473449720417 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1153758351/2000000000 : ℝ)^69 ≤ (48860683409587/100000000000000 : ℝ)^53 := by
    have hnat : (1153758351 : ℕ)^69*100000000000000^53 ≤ 48860683409587^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153758351 2000000000 48860683409587 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1792207759/10000000000 : ℝ), (2495923039/5000000000 : ℝ), (1153758351/2000000000 : ℝ)] ![(10665866853887/100000000000000 : ℝ), (40473449720417/100000000000000 : ℝ), (48860683409587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1792207759/10000000000 : ℝ)|^69 ≤ (10665866853887/100000000000000 : ℝ)^53
        have hw : |(-1792207759/10000000000 : ℝ)|=(1792207759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2495923039/5000000000 : ℝ)|^69 ≤ (40473449720417/100000000000000 : ℝ)^53
        have hw : |(2495923039/5000000000 : ℝ)|=(2495923039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1153758351/2000000000 : ℝ)|^69 ≤ (48860683409587/100000000000000 : ℝ)^53
        have hw : |(1153758351/2000000000 : ℝ)|=(1153758351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s5_s5_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1352729581/2500000000 : ℝ)*x 0 + (-463474119/2500000000 : ℝ)*x 1 + (1062708933/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352729581/2500000000 : ℝ)^69 ≤ (44951999026667/100000000000000 : ℝ)^53 := by
    have hnat : (1352729581 : ℕ)^69*100000000000000^53 ≤ 44951999026667^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352729581 2500000000 44951999026667 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (463474119/2500000000 : ℝ)^69 ≤ (5573142608203/50000000000000 : ℝ)^53 := by
    have hnat : (463474119 : ℕ)^69*50000000000000^53 ≤ 5573142608203^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463474119 2500000000 5573142608203 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062708933/2000000000 : ℝ)^69 ≤ (43901715745509/100000000000000 : ℝ)^53 := by
    have hnat : (1062708933 : ℕ)^69*100000000000000^53 ≤ 43901715745509^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062708933 2000000000 43901715745509 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1352729581/2500000000 : ℝ), (-463474119/2500000000 : ℝ), (1062708933/2000000000 : ℝ)] ![(44951999026667/100000000000000 : ℝ), (5573142608203/50000000000000 : ℝ), (43901715745509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1352729581/2500000000 : ℝ)|^69 ≤ (44951999026667/100000000000000 : ℝ)^53
        have hw : |(1352729581/2500000000 : ℝ)|=(1352729581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-463474119/2500000000 : ℝ)|^69 ≤ (5573142608203/50000000000000 : ℝ)^53
        have hw : |(-463474119/2500000000 : ℝ)|=(463474119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1062708933/2000000000 : ℝ)|^69 ≤ (43901715745509/100000000000000 : ℝ)^53
        have hw : |(1062708933/2000000000 : ℝ)|=(1062708933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s5_s5_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (170594467/400000000 : ℝ)*x 0 + (1316106287/2000000000 : ℝ)*x 1 + (-1577019907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170594467/400000000 : ℝ)^69 ≤ (4121811773633/12500000000000 : ℝ)^53 := by
    have hnat : (170594467 : ℕ)^69*12500000000000^53 ≤ 4121811773633^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170594467 400000000 4121811773633 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316106287/2000000000 : ℝ)^69 ≤ (57995774781341/100000000000000 : ℝ)^53 := by
    have hnat : (1316106287 : ℕ)^69*100000000000000^53 ≤ 57995774781341^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316106287 2000000000 57995774781341 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577019907/10000000000 : ℝ)^69 ≤ (4514865508023/50000000000000 : ℝ)^53 := by
    have hnat : (1577019907 : ℕ)^69*50000000000000^53 ≤ 4514865508023^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577019907 10000000000 4514865508023 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170594467/400000000 : ℝ), (1316106287/2000000000 : ℝ), (-1577019907/10000000000 : ℝ)] ![(4121811773633/12500000000000 : ℝ), (57995774781341/100000000000000 : ℝ), (4514865508023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170594467/400000000 : ℝ)|^69 ≤ (4121811773633/12500000000000 : ℝ)^53
        have hw : |(170594467/400000000 : ℝ)|=(170594467/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316106287/2000000000 : ℝ)|^69 ≤ (57995774781341/100000000000000 : ℝ)^53
        have hw : |(1316106287/2000000000 : ℝ)|=(1316106287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1577019907/10000000000 : ℝ)|^69 ≤ (4514865508023/50000000000000 : ℝ)^53
        have hw : |(-1577019907/10000000000 : ℝ)|=(1577019907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308061_s5_s5_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (343349219/500000000 : ℝ)*x 0 + (1343789601/5000000000 : ℝ)*x 1 + (743434321/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343349219/500000000 : ℝ)^69 ≤ (30651934804201/50000000000000 : ℝ)^53 := by
    have hnat : (343349219 : ℕ)^69*50000000000000^53 ≤ 30651934804201^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343349219 500000000 30651934804201 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343789601/5000000000 : ℝ)^69 ≤ (18075610576329/100000000000000 : ℝ)^53 := by
    have hnat : (1343789601 : ℕ)^69*100000000000000^53 ≤ 18075610576329^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343789601 5000000000 18075610576329 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (743434321/2500000000 : ℝ)^69 ≤ (5155129949177/25000000000000 : ℝ)^53 := by
    have hnat : (743434321 : ℕ)^69*25000000000000^53 ≤ 5155129949177^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743434321 2500000000 5155129949177 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(343349219/500000000 : ℝ), (1343789601/5000000000 : ℝ), (743434321/2500000000 : ℝ)] ![(30651934804201/50000000000000 : ℝ), (18075610576329/100000000000000 : ℝ), (5155129949177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(343349219/500000000 : ℝ)|^69 ≤ (30651934804201/50000000000000 : ℝ)^53
        have hw : |(343349219/500000000 : ℝ)|=(343349219/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1343789601/5000000000 : ℝ)|^69 ≤ (18075610576329/100000000000000 : ℝ)^53
        have hw : |(1343789601/5000000000 : ℝ)|=(1343789601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(743434321/2500000000 : ℝ)|^69 ≤ (5155129949177/25000000000000 : ℝ)^53
        have hw : |(743434321/2500000000 : ℝ)|=(743434321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308061_s5 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((8063/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8063/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46321/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46321/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42263/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42263/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3033/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3033/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14409/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14409/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1339/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1339/5000 : ℝ)*X 1 2) := by
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (8063/20000 : ℝ) ^ (17/4 : ℝ) ≤ (1052454494027118029/50000000000000000000 : ℝ) := by
    have hpowers : (8063/20000 : ℝ)^17 ≤ (1052454494027118029/50000000000000000000 : ℝ)^4 := by
      have hnat : (8063 : ℕ)^17*50000000000000000000^4 ≤ 1052454494027118029^4*20000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8063 20000 1052454494027118029 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8063/20000 : ℝ)) (X := (1052454494027118029/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s5_corner0a : (51052454494027118029/50000000000000000000 : ℝ) ≤ (10049133530613191/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (51052454494027118029/50000000000000000000 : ℝ)^4 ≤ (10049133530613191/10000000000000000 : ℝ)^17 := by
      have hnat : (51052454494027118029 : ℕ)^4*10000000000000000^17 ≤ 10049133530613191^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51052454494027118029 50000000000000000000 10049133530613191 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10049133530613191/10000000000000000 : ℝ)) (X := (51052454494027118029/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s5_corner0b : (26052454494027118029/25000000000000000000 : ℝ) ≤ (5048749246371483/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (26052454494027118029/25000000000000000000 : ℝ)^4 ≤ (5048749246371483/5000000000000000 : ℝ)^17 := by
      have hnat : (26052454494027118029 : ℕ)^4*5000000000000000^17 ≤ 5048749246371483^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26052454494027118029 25000000000000000000 5048749246371483 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5048749246371483/5000000000000000 : ℝ)) (X := (26052454494027118029/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(49133530613191/4031500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1934598485191/161260000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (8063/20000 : ℝ)) (alpha := (49133530613191/4031500000000000 : ℝ)) (beta := (1934598485191/161260000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (8063/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(49133530613191/4031500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1934598485191/161260000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (46321/100000 : ℝ) ^ (17/4 : ℝ) ≤ (3798010735274078659/100000000000000000000 : ℝ) := by
    have hpowers : (46321/100000 : ℝ)^17 ≤ (3798010735274078659/100000000000000000000 : ℝ)^4 := by
      have hnat : (46321 : ℕ)^17*100000000000000000000^4 ≤ 3798010735274078659^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46321 100000 3798010735274078659 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (46321/100000 : ℝ)) (X := (3798010735274078659/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s5_corner1a : (103798010735274078659/100000000000000000000 : ℝ) ≤ (10088095471072863/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (103798010735274078659/100000000000000000000 : ℝ)^4 ≤ (10088095471072863/10000000000000000 : ℝ)^17 := by
      have hnat : (103798010735274078659 : ℕ)^4*10000000000000000^17 ≤ 10088095471072863^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103798010735274078659 100000000000000000000 10088095471072863 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10088095471072863/10000000000000000 : ℝ)) (X := (103798010735274078659/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s5_corner1b : (53798010735274078659/50000000000000000000 : ℝ) ≤ (2543439844780357/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (53798010735274078659/50000000000000000000 : ℝ)^4 ≤ (2543439844780357/2500000000000000 : ℝ)^17 := by
      have hnat : (53798010735274078659 : ℕ)^4*2500000000000000^17 ≤ 2543439844780357^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53798010735274078659 50000000000000000000 2543439844780357 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2543439844780357/2500000000000000 : ℝ)) (X := (53798010735274078659/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(88095471072863/4632100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1557525600883/84220000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (46321/100000 : ℝ)) (alpha := (88095471072863/4632100000000000 : ℝ)) (beta := (1557525600883/84220000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (46321/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(88095471072863/4632100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1557525600883/84220000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (42263/100000 : ℝ) ^ (17/4 : ℝ) ≤ (2572357748906388629/100000000000000000000 : ℝ) := by
    have hpowers : (42263/100000 : ℝ)^17 ≤ (2572357748906388629/100000000000000000000 : ℝ)^4 := by
      have hnat : (42263 : ℕ)^17*100000000000000000000^4 ≤ 2572357748906388629^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42263 100000 2572357748906388629 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42263/100000 : ℝ)) (X := (2572357748906388629/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s5_corner2a : (102572357748906388629/100000000000000000000 : ℝ) ≤ (10059939612173169/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (102572357748906388629/100000000000000000000 : ℝ)^4 ≤ (10059939612173169/10000000000000000 : ℝ)^17 := by
      have hnat : (102572357748906388629 : ℕ)^4*10000000000000000^17 ≤ 10059939612173169^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102572357748906388629 100000000000000000000 10059939612173169 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059939612173169/10000000000000000 : ℝ)) (X := (102572357748906388629/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s5_corner2b : (52572357748906388629/50000000000000000000 : ℝ) ≤ (5059370256021967/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (52572357748906388629/50000000000000000000 : ℝ)^4 ≤ (5059370256021967/5000000000000000 : ℝ)^17 := by
      have hnat : (52572357748906388629 : ℕ)^4*5000000000000000^17 ≤ 5059370256021967^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52572357748906388629 50000000000000000000 5059370256021967 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059370256021967/5000000000000000 : ℝ)) (X := (52572357748906388629/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(59939612173169/4226300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(904629228781/65020000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (42263/100000 : ℝ)) (alpha := (59939612173169/4226300000000000 : ℝ)) (beta := (904629228781/65020000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (42263/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(59939612173169/4226300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(904629228781/65020000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-2480110843/10000000000 : ℝ)*X 0 0+(906082741/2000000000 : ℝ)*X 0 1+(2847436259/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((587183831/1250000000 : ℝ)*X 1 0+(-2540014637/10000000000 : ℝ)*X 1 1+(5490204691/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((1183213369/2500000000 : ℝ)*X 2 0+(6082556853/10000000000 : ℝ)*X 2 1+(-422804087/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((1166447691/2000000000 : ℝ)*X 0 0+(3170918169/10000000000 : ℝ)*X 0 1+(376353901/1000000000 : ℝ)*X 0 2+(1166447691/2000000000 : ℝ)*X 1 0+(3170918169/10000000000 : ℝ)*X 1 1+(376353901/1000000000 : ℝ)*X 1 2+(1166447691/2000000000 : ℝ)*X 2 0+(3170918169/10000000000 : ℝ)*X 2 1+(376353901/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-2491276947/10000000000 : ℝ)*X 0 0+(816296483/2000000000 : ℝ)*X 0 1+(1218913841/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((4453456161/10000000000 : ℝ)*X 1 0+(-2106826509/10000000000 : ℝ)*X 1 1+(6046865389/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((2244483269/5000000000 : ℝ)*X 2 0+(207549913/312500000 : ℝ)*X 2 1+(-1160117777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((583722707/1000000000 : ℝ)*X 0 0+(1980174197/5000000000 : ℝ)*X 0 1+(369220749/1250000000 : ℝ)*X 0 2+(583722707/1000000000 : ℝ)*X 1 0+(1980174197/5000000000 : ℝ)*X 1 1+(369220749/1250000000 : ℝ)*X 1 2+(583722707/1000000000 : ℝ)*X 2 0+(1980174197/5000000000 : ℝ)*X 2 1+(369220749/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-71980479/400000000 : ℝ)*X 0 0+(2319031947/5000000000 : ℝ)*X 0 1+(6095873641/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((171912941/400000000 : ℝ)*X 1 0+(-287069783/1250000000 : ℝ)*X 1 1+(6048169873/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((2719562403/5000000000 : ℝ)*X 2 0+(5753934693/10000000000 : ℝ)*X 2 1+(-1158813379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((1680214643/2500000000 : ℝ)*X 0 0+(2901821141/10000000000 : ℝ)*X 0 1+(2950978523/10000000000 : ℝ)*X 0 2+(1680214643/2500000000 : ℝ)*X 1 0+(2901821141/10000000000 : ℝ)*X 1 1+(2950978523/10000000000 : ℝ)*X 1 2+(1680214643/2500000000 : ℝ)*X 2 0+(2901821141/10000000000 : ℝ)*X 2 1+(2950978523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-1792207759/10000000000 : ℝ)*X 0 0+(2495923039/5000000000 : ℝ)*X 0 1+(1153758351/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((1352729581/2500000000 : ℝ)*X 1 0+(-463474119/2500000000 : ℝ)*X 1 1+(1062708933/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((170594467/400000000 : ℝ)*X 2 0+(1316106287/2000000000 : ℝ)*X 2 1+(-1577019907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((343349219/500000000 : ℝ)*X 0 0+(1343789601/5000000000 : ℝ)*X 0 1+(743434321/2500000000 : ℝ)*X 0 2+(343349219/500000000 : ℝ)*X 1 0+(1343789601/5000000000 : ℝ)*X 1 1+(743434321/2500000000 : ℝ)*X 1 2+(343349219/500000000 : ℝ)*X 2 0+(1343789601/5000000000 : ℝ)*X 2 1+(743434321/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308061_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((3033/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3033/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2649540647810542226555841496539/179371002757375000000000000000000000 : ℝ) := by norm_num
    linear_combination (45337/125000000000 : ℝ)*(base50) + (1223981150591/1000000000000 : ℝ)*(base59) + (3447435401441/500000000000 : ℝ)*(major_s5_0) + (3447435401441/500000000000 : ℝ)*(major_s5_1) + (3447435401441/500000000000 : ℝ)*(major_s5_2) + (16465903/125000000000 : ℝ)*(sp_s5_0) + (24523351/250000000000 : ℝ)*(sp_s5_1) + (78967887/1000000000000 : ℝ)*(sp_s5_6) + (9389868623001/1000000000000 : ℝ)*(sp_s5_7) + (3667771049/390625000 : ℝ)*(sp_s5_8) + (9389794398363/1000000000000 : ℝ)*(sp_s5_9) + (1099914340971/250000000000 : ℝ)*(sp_s5_13) + (20418569/50000000000 : ℝ)*(sp_s5_15) + (102975931/500000000000 : ℝ)*(sp_s5_23) + (4399736331771/1000000000000 : ℝ)*(f.failure) + (375600014009/40000000000 : ℝ)*(f.sum) + (3552049576471388953/6117701321875000000000000000000 : ℝ)*base63 + (2439882226491/6502000000000000000000000 : ℝ)*base64 + (12974826691991/21055000000000000000000000 : ℝ)*base66 + (272483686865737/1056575000000000000000000000 : ℝ)*base69 + (951772627749709669/6553203250000000000000000000000 : ℝ)*base70 + (826875413237/3225200000000000000000000 : ℝ)*base73 + (93531961824069/1158025000000000000000000000 : ℝ)*base75 + (21189613743767/62992187500000000000000000 : ℝ)*base76 + (39388863987822379/339532930000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (34819/100000000000000000 : ℝ)*base86 + (34819/100000000000000000 : ℝ)*base88 + (34819/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14409/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14409/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15763366923622547459439/4765966000000000000000000000 : ℝ) := by norm_num
    linear_combination (148911/1000000000000 : ℝ)*(base39) + (167160384747/200000000000 : ℝ)*(base59) + (6640292915927/1000000000000 : ℝ)*(major_s5_0) + (6640292915927/1000000000000 : ℝ)*(major_s5_1) + (6640292915927/1000000000000 : ℝ)*(major_s5_2) + (3283401/500000000000 : ℝ)*(sp_s5_1) + (443703/62500000000 : ℝ)*(sp_s5_2) + (2184717/250000000000 : ℝ)*(sp_s5_6) + (23786869/1000000000000 : ℝ)*(sp_s5_7) + (328803/50000000000 : ℝ)*(sp_s5_13) + (9043275164253/1000000000000 : ℝ)*(sp_s5_14) + (28260288701/3125000000 : ℝ)*(sp_s5_15) + (4521645925937/500000000000 : ℝ)*(sp_s5_16) + (847454092661/200000000000 : ℝ)*(sp_s5_20) + (4237285778233/1000000000000 : ℝ)*(f.failure) + (4521649475561/500000000000 : ℝ)*(f.sum) + (2119339966694991283/8898474650000000000000000000000 : ℝ)*base63 + (998731576341/13004000000000000000000000 : ℝ)*base65 + (4435404168877/16844000000000000000000000 : ℝ)*base66 + (465138605405817/4226300000000000000000000000 : ℝ)*base68 + (35037499055289857/74468218750000000000000000000 : ℝ)*base71 + (62857000337/586400000000000000000000 : ℝ)*base73 + (48077417226029/421100000000000000000000000 : ℝ)*base74 + (102692029552763/366500000000000000000000000 : ℝ)*base76 + (1581356568509361/3086663000000000000000000000 : ℝ)*base79 + (28337/100000000000000000 : ℝ)*base86 + (28337/100000000000000000 : ℝ)*base88 + (28337/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1339/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1339/5000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (163256511449606780639689760463/35874200551475000000000000000000000 : ℝ) := by norm_num
    linear_combination (68985013913/200000000000 : ℝ)*(base40) + (2514927/1000000000000 : ℝ)*(base50) + (837433995013/1000000000000 : ℝ)*(base59) + (776817178331/125000000000 : ℝ)*(major_s5_0) + (776817178331/125000000000 : ℝ)*(major_s5_1) + (776817178331/125000000000 : ℝ)*(major_s5_2) + (762941/500000000000 : ℝ)*(sp_s5_0) + (70931803/200000000000 : ℝ)*(sp_s5_2) + (2854219/100000000000 : ℝ)*(sp_s5_9) + (220892339/250000000000 : ℝ)*(sp_s5_20) + (8463467974971/1000000000000 : ℝ)*(sp_s5_21) + (4231734750427/500000000000 : ℝ)*(sp_s5_22) + (8463086299649/1000000000000 : ℝ)*(sp_s5_23) + (3964720266143/1000000000000 : ℝ)*(sp_s5_27) + (1982801917749/500000000000 : ℝ)*(f.failure) + (4231734750427/500000000000 : ℝ)*(f.sum) + (26991163221915326923/97883221150000000000000000000000 : ℝ)*base62 + (4468223292413/16255000000000000000000000 : ℝ)*base65 + (1143190724699/42110000000000000000000000 : ℝ)*base66 + (148261022745583/264143750000000000000000000 : ℝ)*base68 + (1165391748106356367/3276601625000000000000000000000 : ℝ)*base71 + (26748075809923/40315000000000000000000000 : ℝ)*base72 + (632727317246623/2316050000000000000000000000 : ℝ)*base74 + (35796730139629/503937500000000000000000000 : ℝ)*base76 + (225341561630972631/339532930000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (36461/50000000000000000 : ℝ)*base86 + (36461/50000000000000000 : ℝ)*base88 + (36461/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((8063/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8063/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46321/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46321/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42263/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42263/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3033/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3033/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14409/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14409/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1339/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1339/5000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308061_s5 p hpa hpb X hX hprev4

#print axioms solution

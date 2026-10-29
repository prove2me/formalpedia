-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310053_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:26:21.041211+00:00
-- url     : https://prove2.me/submissions/5694dfa5-4377-481b-8f3e-afa8da4dcd92

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
theorem collision_support_c310053_s1_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1635687137/10000000000 : ℝ)*x 0 + (2647007087/5000000000 : ℝ)*x 1 + (1377818491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1635687137/10000000000 : ℝ)^71 ≤ (9659585470467/100000000000000 : ℝ)^55 := by
    have hnat : (1635687137 : ℕ)^71*100000000000000^55 ≤ 9659585470467^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1635687137 10000000000 9659585470467 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2647007087/5000000000 : ℝ)^71 ≤ (21998936115513/50000000000000 : ℝ)^55 := by
    have hnat : (2647007087 : ℕ)^71*50000000000000^55 ≤ 21998936115513^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647007087 5000000000 21998936115513 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1377818491/2500000000 : ℝ)^71 ≤ (46342542281151/100000000000000 : ℝ)^55 := by
    have hnat : (1377818491 : ℕ)^71*100000000000000^55 ≤ 46342542281151^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377818491 2500000000 46342542281151 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1635687137/10000000000 : ℝ), (2647007087/5000000000 : ℝ), (1377818491/2500000000 : ℝ)] ![(9659585470467/100000000000000 : ℝ), (21998936115513/50000000000000 : ℝ), (46342542281151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1635687137/10000000000 : ℝ)|^71 ≤ (9659585470467/100000000000000 : ℝ)^55
        have hw : |(-1635687137/10000000000 : ℝ)|=(1635687137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2647007087/5000000000 : ℝ)|^71 ≤ (21998936115513/50000000000000 : ℝ)^55
        have hw : |(2647007087/5000000000 : ℝ)|=(2647007087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1377818491/2500000000 : ℝ)|^71 ≤ (46342542281151/100000000000000 : ℝ)^55
        have hw : |(1377818491/2500000000 : ℝ)|=(1377818491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s1_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4455385321/10000000000 : ℝ)*x 0 + (-410179631/5000000000 : ℝ)*x 1 + (6803205281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4455385321/10000000000 : ℝ)^71 ≤ (35216225217861/100000000000000 : ℝ)^55 := by
    have hnat : (4455385321 : ℕ)^71*100000000000000^55 ≤ 35216225217861^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4455385321 10000000000 35216225217861 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410179631/5000000000 : ℝ)^71 ≤ (3963492142587/100000000000000 : ℝ)^55 := by
    have hnat : (410179631 : ℕ)^71*100000000000000^55 ≤ 3963492142587^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410179631 5000000000 3963492142587 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6803205281/10000000000 : ℝ)^71 ≤ (190063383231/312500000000 : ℝ)^55 := by
    have hnat : (6803205281 : ℕ)^71*312500000000^55 ≤ 190063383231^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6803205281 10000000000 190063383231 312500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4455385321/10000000000 : ℝ), (-410179631/5000000000 : ℝ), (6803205281/10000000000 : ℝ)] ![(35216225217861/100000000000000 : ℝ), (3963492142587/100000000000000 : ℝ), (190063383231/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4455385321/10000000000 : ℝ)|^71 ≤ (35216225217861/100000000000000 : ℝ)^55
        have hw : |(4455385321/10000000000 : ℝ)|=(4455385321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410179631/5000000000 : ℝ)|^71 ≤ (3963492142587/100000000000000 : ℝ)^55
        have hw : |(-410179631/5000000000 : ℝ)|=(410179631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6803205281/10000000000 : ℝ)|^71 ≤ (190063383231/312500000000 : ℝ)^55
        have hw : |(6803205281/10000000000 : ℝ)|=(6803205281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s1_s1_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-60770301/312500000 : ℝ)*x 0 + (3293851751/10000000000 : ℝ)*x 1 + (1416761729/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60770301/312500000 : ℝ)^71 ≤ (12076994095997/100000000000000 : ℝ)^55 := by
    have hnat : (60770301 : ℕ)^71*100000000000000^55 ≤ 12076994095997^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60770301 312500000 12076994095997 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3293851751/10000000000 : ℝ)^71 ≤ (11922567124667/50000000000000 : ℝ)^55 := by
    have hnat : (3293851751 : ℕ)^71*50000000000000^55 ≤ 11922567124667^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3293851751 10000000000 11922567124667 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1416761729/2000000000 : ℝ)^71 ≤ (64077871637319/100000000000000 : ℝ)^55 := by
    have hnat : (1416761729 : ℕ)^71*100000000000000^55 ≤ 64077871637319^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1416761729 2000000000 64077871637319 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-60770301/312500000 : ℝ), (3293851751/10000000000 : ℝ), (1416761729/2000000000 : ℝ)] ![(12076994095997/100000000000000 : ℝ), (11922567124667/50000000000000 : ℝ), (64077871637319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-60770301/312500000 : ℝ)|^71 ≤ (12076994095997/100000000000000 : ℝ)^55
        have hw : |(-60770301/312500000 : ℝ)|=(60770301/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3293851751/10000000000 : ℝ)|^71 ≤ (11922567124667/50000000000000 : ℝ)^55
        have hw : |(3293851751/10000000000 : ℝ)|=(3293851751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1416761729/2000000000 : ℝ)|^71 ≤ (64077871637319/100000000000000 : ℝ)^55
        have hw : |(1416761729/2000000000 : ℝ)|=(1416761729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s1_s1_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (509062377/2000000000 : ℝ)*x 0 + (-24710799/1000000000 : ℝ)*x 1 + (4290072311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (509062377/2000000000 : ℝ)^71 ≤ (17094864450029/100000000000000 : ℝ)^55 := by
    have hnat : (509062377 : ℕ)^71*100000000000000^55 ≤ 17094864450029^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509062377 2000000000 17094864450029 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24710799/1000000000 : ℝ)^71 ≤ (842098598713/100000000000000 : ℝ)^55 := by
    have hnat : (24710799 : ℕ)^71*100000000000000^55 ≤ 842098598713^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24710799 1000000000 842098598713 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4290072311/5000000000 : ℝ)^71 ≤ (41031518469977/50000000000000 : ℝ)^55 := by
    have hnat : (4290072311 : ℕ)^71*50000000000000^55 ≤ 41031518469977^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4290072311 5000000000 41031518469977 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(509062377/2000000000 : ℝ), (-24710799/1000000000 : ℝ), (4290072311/5000000000 : ℝ)] ![(17094864450029/100000000000000 : ℝ), (842098598713/100000000000000 : ℝ), (41031518469977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(509062377/2000000000 : ℝ)|^71 ≤ (17094864450029/100000000000000 : ℝ)^55
        have hw : |(509062377/2000000000 : ℝ)|=(509062377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24710799/1000000000 : ℝ)|^71 ≤ (842098598713/100000000000000 : ℝ)^55
        have hw : |(-24710799/1000000000 : ℝ)|=(24710799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4290072311/5000000000 : ℝ)|^71 ≤ (41031518469977/50000000000000 : ℝ)^55
        have hw : |(4290072311/5000000000 : ℝ)|=(4290072311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s1_s1_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (256997531/1000000000 : ℝ)*x 0 + (8564056291/10000000000 : ℝ)*x 1 + (-30445711/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256997531/1000000000 : ℝ)^71 ≤ (17308997636279/100000000000000 : ℝ)^55 := by
    have hnat : (256997531 : ℕ)^71*100000000000000^55 ≤ 17308997636279^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256997531 1000000000 17308997636279 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8564056291/10000000000 : ℝ)^71 ≤ (81864454376693/100000000000000 : ℝ)^55 := by
    have hnat : (8564056291 : ℕ)^71*100000000000000^55 ≤ 81864454376693^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8564056291 10000000000 81864454376693 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30445711/1250000000 : ℝ)^71 ≤ (103318496863/12500000000000 : ℝ)^55 := by
    have hnat : (30445711 : ℕ)^71*12500000000000^55 ≤ 103318496863^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30445711 1250000000 103318496863 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(256997531/1000000000 : ℝ), (8564056291/10000000000 : ℝ), (-30445711/1250000000 : ℝ)] ![(17308997636279/100000000000000 : ℝ), (81864454376693/100000000000000 : ℝ), (103318496863/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(256997531/1000000000 : ℝ)|^71 ≤ (17308997636279/100000000000000 : ℝ)^55
        have hw : |(256997531/1000000000 : ℝ)|=(256997531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8564056291/10000000000 : ℝ)|^71 ≤ (81864454376693/100000000000000 : ℝ)^55
        have hw : |(8564056291/10000000000 : ℝ)|=(8564056291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30445711/1250000000 : ℝ)|^71 ≤ (103318496863/12500000000000 : ℝ)^55
        have hw : |(-30445711/1250000000 : ℝ)|=(30445711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s1_s1_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5727658573/10000000000 : ℝ)*x 0 + (2925170353/5000000000 : ℝ)*x 1 + (333444689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5727658573/10000000000 : ℝ)^71 ≤ (48704654417659/100000000000000 : ℝ)^55 := by
    have hnat : (5727658573 : ℕ)^71*100000000000000^55 ≤ 48704654417659^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5727658573 10000000000 48704654417659 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2925170353/5000000000 : ℝ)^71 ≤ (50055527374077/100000000000000 : ℝ)^55 := by
    have hnat : (2925170353 : ℕ)^71*100000000000000^55 ≤ 50055527374077^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2925170353 5000000000 50055527374077 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (333444689/10000000000 : ℝ)^71 ≤ (1239818185333/100000000000000 : ℝ)^55 := by
    have hnat : (333444689 : ℕ)^71*100000000000000^55 ≤ 1239818185333^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333444689 10000000000 1239818185333 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5727658573/10000000000 : ℝ), (2925170353/5000000000 : ℝ), (333444689/10000000000 : ℝ)] ![(48704654417659/100000000000000 : ℝ), (50055527374077/100000000000000 : ℝ), (1239818185333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5727658573/10000000000 : ℝ)|^71 ≤ (48704654417659/100000000000000 : ℝ)^55
        have hw : |(5727658573/10000000000 : ℝ)|=(5727658573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2925170353/5000000000 : ℝ)|^71 ≤ (50055527374077/100000000000000 : ℝ)^55
        have hw : |(2925170353/5000000000 : ℝ)|=(2925170353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(333444689/10000000000 : ℝ)|^71 ≤ (1239818185333/100000000000000 : ℝ)^55
        have hw : |(333444689/10000000000 : ℝ)|=(333444689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s1_s1_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1603492549/10000000000 : ℝ)*x 0 + (1902606361/5000000000 : ℝ)*x 1 + (3446433431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1603492549/10000000000 : ℝ)^71 ≤ (9414856267307/100000000000000 : ℝ)^55 := by
    have hnat : (1603492549 : ℕ)^71*100000000000000^55 ≤ 9414856267307^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1603492549 10000000000 9414856267307 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1902606361/5000000000 : ℝ)^71 ≤ (14364065052907/50000000000000 : ℝ)^55 := by
    have hnat : (1902606361 : ℕ)^71*50000000000000^55 ≤ 14364065052907^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902606361 5000000000 14364065052907 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3446433431/5000000000 : ℝ)^71 ≤ (7732126702129/12500000000000 : ℝ)^55 := by
    have hnat : (3446433431 : ℕ)^71*12500000000000^55 ≤ 7732126702129^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3446433431 5000000000 7732126702129 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1603492549/10000000000 : ℝ), (1902606361/5000000000 : ℝ), (3446433431/5000000000 : ℝ)] ![(9414856267307/100000000000000 : ℝ), (14364065052907/50000000000000 : ℝ), (7732126702129/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1603492549/10000000000 : ℝ)|^71 ≤ (9414856267307/100000000000000 : ℝ)^55
        have hw : |(-1603492549/10000000000 : ℝ)|=(1603492549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1902606361/5000000000 : ℝ)|^71 ≤ (14364065052907/50000000000000 : ℝ)^55
        have hw : |(1902606361/5000000000 : ℝ)|=(1902606361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3446433431/5000000000 : ℝ)|^71 ≤ (7732126702129/12500000000000 : ℝ)^55
        have hw : |(3446433431/5000000000 : ℝ)|=(3446433431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s1_s1_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (701980271/5000000000 : ℝ)*x 0 + (-891268513/10000000000 : ℝ)*x 1 + (9029920193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (701980271/5000000000 : ℝ)^71 ≤ (7930721367643/100000000000000 : ℝ)^55 := by
    have hnat : (701980271 : ℕ)^71*100000000000000^55 ≤ 7930721367643^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701980271 5000000000 7930721367643 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (891268513/10000000000 : ℝ)^71 ≤ (2205598786281/50000000000000 : ℝ)^55 := by
    have hnat : (891268513 : ℕ)^71*50000000000000^55 ≤ 2205598786281^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891268513 10000000000 2205598786281 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9029920193/10000000000 : ℝ)^71 ≤ (10957260131009/12500000000000 : ℝ)^55 := by
    have hnat : (9029920193 : ℕ)^71*12500000000000^55 ≤ 10957260131009^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9029920193 10000000000 10957260131009 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(701980271/5000000000 : ℝ), (-891268513/10000000000 : ℝ), (9029920193/10000000000 : ℝ)] ![(7930721367643/100000000000000 : ℝ), (2205598786281/50000000000000 : ℝ), (10957260131009/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(701980271/5000000000 : ℝ)|^71 ≤ (7930721367643/100000000000000 : ℝ)^55
        have hw : |(701980271/5000000000 : ℝ)|=(701980271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-891268513/10000000000 : ℝ)|^71 ≤ (2205598786281/50000000000000 : ℝ)^55
        have hw : |(-891268513/10000000000 : ℝ)|=(891268513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9029920193/10000000000 : ℝ)|^71 ≤ (10957260131009/12500000000000 : ℝ)^55
        have hw : |(9029920193/10000000000 : ℝ)|=(9029920193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s1_s1_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6835945111/10000000000 : ℝ)*x 0 + (2311747883/5000000000 : ℝ)*x 1 + (-114170323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6835945111/10000000000 : ℝ)^71 ≤ (61198385950663/100000000000000 : ℝ)^55 := by
    have hnat : (6835945111 : ℕ)^71*100000000000000^55 ≤ 61198385950663^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6835945111 10000000000 61198385950663 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2311747883/5000000000 : ℝ)^71 ≤ (36940887626573/100000000000000 : ℝ)^55 := by
    have hnat : (2311747883 : ℕ)^71*100000000000000^55 ≤ 36940887626573^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2311747883 5000000000 36940887626573 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114170323/2500000000 : ℝ)^71 ≤ (1860726409733/100000000000000 : ℝ)^55 := by
    have hnat : (114170323 : ℕ)^71*100000000000000^55 ≤ 1860726409733^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114170323 2500000000 1860726409733 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6835945111/10000000000 : ℝ), (2311747883/5000000000 : ℝ), (-114170323/2500000000 : ℝ)] ![(61198385950663/100000000000000 : ℝ), (36940887626573/100000000000000 : ℝ), (1860726409733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6835945111/10000000000 : ℝ)|^71 ≤ (61198385950663/100000000000000 : ℝ)^55
        have hw : |(6835945111/10000000000 : ℝ)|=(6835945111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2311747883/5000000000 : ℝ)|^71 ≤ (36940887626573/100000000000000 : ℝ)^55
        have hw : |(2311747883/5000000000 : ℝ)|=(2311747883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-114170323/2500000000 : ℝ)|^71 ≤ (1860726409733/100000000000000 : ℝ)^55
        have hw : |(-114170323/2500000000 : ℝ)|=(114170323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s1_s1_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1163103763/1250000000 : ℝ)*x 0 + (15774031/125000000 : ℝ)*x 1 + (477537637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1163103763/1250000000 : ℝ)^71 ≤ (91118266914851/100000000000000 : ℝ)^55 := by
    have hnat : (1163103763 : ℕ)^71*100000000000000^55 ≤ 91118266914851^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163103763 1250000000 91118266914851 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15774031/125000000 : ℝ)^71 ≤ (3455293272819/50000000000000 : ℝ)^55 := by
    have hnat : (15774031 : ℕ)^71*50000000000000^55 ≤ 3455293272819^55*125000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15774031 125000000 3455293272819 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477537637/10000000000 : ℝ)^71 ≤ (1971146529243/100000000000000 : ℝ)^55 := by
    have hnat : (477537637 : ℕ)^71*100000000000000^55 ≤ 1971146529243^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477537637 10000000000 1971146529243 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1163103763/1250000000 : ℝ), (15774031/125000000 : ℝ), (477537637/10000000000 : ℝ)] ![(91118266914851/100000000000000 : ℝ), (3455293272819/50000000000000 : ℝ), (1971146529243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1163103763/1250000000 : ℝ)|^71 ≤ (91118266914851/100000000000000 : ℝ)^55
        have hw : |(1163103763/1250000000 : ℝ)|=(1163103763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15774031/125000000 : ℝ)|^71 ≤ (3455293272819/50000000000000 : ℝ)^55
        have hw : |(15774031/125000000 : ℝ)|=(15774031/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(477537637/10000000000 : ℝ)|^71 ≤ (1971146529243/100000000000000 : ℝ)^55
        have hw : |(477537637/10000000000 : ℝ)|=(477537637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s1_s1_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-322139597/2000000000 : ℝ)*x 0 + (608563697/1000000000 : ℝ)*x 1 + (471246199/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (322139597/2000000000 : ℝ)^71 ≤ (1183688220071/12500000000000 : ℝ)^55 := by
    have hnat : (322139597 : ℕ)^71*12500000000000^55 ≤ 1183688220071^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322139597 2000000000 1183688220071 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (608563697/1000000000 : ℝ)^71 ≤ (5266944089823/10000000000000 : ℝ)^55 := by
    have hnat : (608563697 : ℕ)^71*10000000000000^55 ≤ 5266944089823^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608563697 1000000000 5266944089823 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (471246199/1000000000 : ℝ)^71 ≤ (18930526668459/50000000000000 : ℝ)^55 := by
    have hnat : (471246199 : ℕ)^71*50000000000000^55 ≤ 18930526668459^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471246199 1000000000 18930526668459 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-322139597/2000000000 : ℝ), (608563697/1000000000 : ℝ), (471246199/1000000000 : ℝ)] ![(1183688220071/12500000000000 : ℝ), (5266944089823/10000000000000 : ℝ), (18930526668459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-322139597/2000000000 : ℝ)|^71 ≤ (1183688220071/12500000000000 : ℝ)^55
        have hw : |(-322139597/2000000000 : ℝ)|=(322139597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(608563697/1000000000 : ℝ)|^71 ≤ (5266944089823/10000000000000 : ℝ)^55
        have hw : |(608563697/1000000000 : ℝ)|=(608563697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(471246199/1000000000 : ℝ)|^71 ≤ (18930526668459/50000000000000 : ℝ)^55
        have hw : |(471246199/1000000000 : ℝ)|=(471246199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s1_s1_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6928330637/10000000000 : ℝ)*x 0 + (-92649303/2500000000 : ℝ)*x 1 + (1140573869/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6928330637/10000000000 : ℝ)^71 ≤ (62268157823981/100000000000000 : ℝ)^55 := by
    have hnat : (6928330637 : ℕ)^71*100000000000000^55 ≤ 62268157823981^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6928330637 10000000000 62268157823981 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92649303/2500000000 : ℝ)^71 ≤ (1420963009803/100000000000000 : ℝ)^55 := by
    have hnat : (92649303 : ℕ)^71*100000000000000^55 ≤ 1420963009803^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92649303 2500000000 1420963009803 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140573869/2500000000 : ℝ)^71 ≤ (36310879154869/100000000000000 : ℝ)^55 := by
    have hnat : (1140573869 : ℕ)^71*100000000000000^55 ≤ 36310879154869^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140573869 2500000000 36310879154869 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6928330637/10000000000 : ℝ), (-92649303/2500000000 : ℝ), (1140573869/2500000000 : ℝ)] ![(62268157823981/100000000000000 : ℝ), (1420963009803/100000000000000 : ℝ), (36310879154869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6928330637/10000000000 : ℝ)|^71 ≤ (62268157823981/100000000000000 : ℝ)^55
        have hw : |(6928330637/10000000000 : ℝ)|=(6928330637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-92649303/2500000000 : ℝ)|^71 ≤ (1420963009803/100000000000000 : ℝ)^55
        have hw : |(-92649303/2500000000 : ℝ)|=(92649303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1140573869/2500000000 : ℝ)|^71 ≤ (36310879154869/100000000000000 : ℝ)^55
        have hw : |(1140573869/2500000000 : ℝ)|=(1140573869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s1_s1_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1499957059/10000000000 : ℝ)*x 0 + (8758131/9765625 : ℝ)*x 1 + (-180261007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1499957059/10000000000 : ℝ)^71 ≤ (269924737819/3125000000000 : ℝ)^55 := by
    have hnat : (1499957059 : ℕ)^71*3125000000000^55 ≤ 269924737819^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499957059 10000000000 269924737819 3125000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8758131/9765625 : ℝ)^71 ≤ (86886981126101/100000000000000 : ℝ)^55 := by
    have hnat : (8758131 : ℕ)^71*100000000000000^55 ≤ 86886981126101^55*9765625^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8758131 9765625 86886981126101 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180261007/2000000000 : ℝ)^71 ≤ (4475427249501/100000000000000 : ℝ)^55 := by
    have hnat : (180261007 : ℕ)^71*100000000000000^55 ≤ 4475427249501^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180261007 2000000000 4475427249501 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1499957059/10000000000 : ℝ), (8758131/9765625 : ℝ), (-180261007/2000000000 : ℝ)] ![(269924737819/3125000000000 : ℝ), (86886981126101/100000000000000 : ℝ), (4475427249501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1499957059/10000000000 : ℝ)|^71 ≤ (269924737819/3125000000000 : ℝ)^55
        have hw : |(1499957059/10000000000 : ℝ)|=(1499957059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8758131/9765625 : ℝ)|^71 ≤ (86886981126101/100000000000000 : ℝ)^55
        have hw : |(8758131/9765625 : ℝ)|=(8758131/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-180261007/2000000000 : ℝ)|^71 ≤ (4475427249501/100000000000000 : ℝ)^55
        have hw : |(-180261007/2000000000 : ℝ)|=(180261007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s1_s1_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (584784781/625000000 : ℝ)*x 0 + (881157169/10000000000 : ℝ)*x 1 + (807039241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (584784781/625000000 : ℝ)^71 ≤ (91772685184823/100000000000000 : ℝ)^55 := by
    have hnat : (584784781 : ℕ)^71*100000000000000^55 ≤ 91772685184823^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584784781 625000000 91772685184823 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (881157169/10000000000 : ℝ)^71 ≤ (4346701494459/100000000000000 : ℝ)^55 := by
    have hnat : (881157169 : ℕ)^71*100000000000000^55 ≤ 4346701494459^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881157169 10000000000 4346701494459 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (807039241/10000000000 : ℝ)^71 ≤ (970153327889/25000000000000 : ℝ)^55 := by
    have hnat : (807039241 : ℕ)^71*25000000000000^55 ≤ 970153327889^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807039241 10000000000 970153327889 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(584784781/625000000 : ℝ), (881157169/10000000000 : ℝ), (807039241/10000000000 : ℝ)] ![(91772685184823/100000000000000 : ℝ), (4346701494459/100000000000000 : ℝ), (970153327889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(584784781/625000000 : ℝ)|^71 ≤ (91772685184823/100000000000000 : ℝ)^55
        have hw : |(584784781/625000000 : ℝ)|=(584784781/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(881157169/10000000000 : ℝ)|^71 ≤ (4346701494459/100000000000000 : ℝ)^55
        have hw : |(881157169/10000000000 : ℝ)|=(881157169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(807039241/10000000000 : ℝ)|^71 ≤ (970153327889/25000000000000 : ℝ)^55
        have hw : |(807039241/10000000000 : ℝ)|=(807039241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310053_s1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((87631/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(87631/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8851/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8851/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(87707/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(87707/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((72437/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72437/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1533/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1533/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3023/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3023/4000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (18111/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (87631/100000 : ℝ) ^ (35/8 : ℝ) ≤ (5612130142481399821/10000000000000000000 : ℝ) := by
    have hpowers : (87631/100000 : ℝ)^35 ≤ (5612130142481399821/10000000000000000000 : ℝ)^8 := by
      have hnat : (87631 : ℕ)^35*10000000000000000000^8 ≤ 5612130142481399821^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87631 100000 5612130142481399821 10000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (87631/100000 : ℝ)) (X := (5612130142481399821/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (15612130142481399821/10000000000000000000 : ℝ) ≤ (2767960776366137/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (15612130142481399821/10000000000000000000 : ℝ)^8 ≤ (2767960776366137/2500000000000000 : ℝ)^35 := by
      have hnat : (15612130142481399821 : ℕ)^8*2500000000000000^35 ≤ 2767960776366137^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15612130142481399821 10000000000000000000 2767960776366137 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2767960776366137/2500000000000000 : ℝ)) (X := (15612130142481399821/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (10612130142481399821/5000000000000000000 : ℝ) ≤ (11876940637840431/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (10612130142481399821/5000000000000000000 : ℝ)^8 ≤ (11876940637840431/10000000000000000 : ℝ)^35 := by
      have hnat : (10612130142481399821 : ℕ)^8*10000000000000000^35 ≤ 11876940637840431^35*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10612130142481399821 5000000000000000000 11876940637840431 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876940637840431/10000000000000000 : ℝ)) (X := (10612130142481399821/5000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(267960776366137/2190775000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(805097532375883/8763100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (87631/100000 : ℝ)) (alpha := (267960776366137/2190775000000000 : ℝ)) (beta := (805097532375883/8763100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (87631/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(267960776366137/2190775000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(805097532375883/8763100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (8851/10000 : ℝ) ^ (35/8 : ℝ) ≤ (29313082824463631531/50000000000000000000 : ℝ) := by
    have hpowers : (8851/10000 : ℝ)^35 ≤ (29313082824463631531/50000000000000000000 : ℝ)^8 := by
      have hnat : (8851 : ℕ)^35*50000000000000000000^8 ≤ 29313082824463631531^8*10000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8851 10000 29313082824463631531 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8851/10000 : ℝ)) (X := (29313082824463631531/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (79313082824463631531/50000000000000000000 : ℝ) ≤ (11112197722902033/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (79313082824463631531/50000000000000000000 : ℝ)^8 ≤ (11112197722902033/10000000000000000 : ℝ)^35 := by
      have hnat : (79313082824463631531 : ℕ)^8*10000000000000000^35 ≤ 11112197722902033^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79313082824463631531 50000000000000000000 11112197722902033 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11112197722902033/10000000000000000 : ℝ)) (X := (79313082824463631531/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (54313082824463631531/25000000000000000000 : ℝ) ≤ (11940443135190131/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (54313082824463631531/25000000000000000000 : ℝ)^8 ≤ (11940443135190131/10000000000000000 : ℝ)^35 := by
      have hnat : (54313082824463631531 : ℕ)^8*10000000000000000^35 ≤ 11940443135190131^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54313082824463631531 25000000000000000000 11940443135190131 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11940443135190131/10000000000000000 : ℝ)) (X := (54313082824463631531/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1112197722902033/8851000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(414122706144049/4425500000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (8851/10000 : ℝ)) (alpha := (1112197722902033/8851000000000000 : ℝ)) (beta := (414122706144049/4425500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (8851/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1112197722902033/8851000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(414122706144049/4425500000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (87707/100000 : ℝ) ^ (35/8 : ℝ) ≤ (28167277712609899641/50000000000000000000 : ℝ) := by
    have hpowers : (87707/100000 : ℝ)^35 ≤ (28167277712609899641/50000000000000000000 : ℝ)^8 := by
      have hnat : (87707 : ℕ)^35*50000000000000000000^8 ≤ 28167277712609899641^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87707 100000 28167277712609899641 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (87707/100000 : ℝ)) (X := (28167277712609899641/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (78167277712609899641/50000000000000000000 : ℝ) ≤ (2215059621326249/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (78167277712609899641/50000000000000000000 : ℝ)^8 ≤ (2215059621326249/2000000000000000 : ℝ)^35 := by
      have hnat : (78167277712609899641 : ℕ)^8*2000000000000000^35 ≤ 2215059621326249^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78167277712609899641 50000000000000000000 2215059621326249 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2215059621326249/2000000000000000 : ℝ)) (X := (78167277712609899641/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (53167277712609899641/25000000000000000000 : ℝ) ≤ (1485298968240007/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (53167277712609899641/25000000000000000000 : ℝ)^8 ≤ (1485298968240007/1250000000000000 : ℝ)^35 := by
      have hnat : (53167277712609899641 : ℕ)^8*1250000000000000^35 ≤ 1485298968240007^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53167277712609899641 25000000000000000000 1485298968240007 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1485298968240007/1250000000000000 : ℝ)) (X := (53167277712609899641/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(215059621326249/1754140000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(807093639288811/8770700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (87707/100000 : ℝ)) (alpha := (215059621326249/1754140000000000 : ℝ)) (beta := (807093639288811/8770700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (87707/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(215059621326249/1754140000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(807093639288811/8770700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1635687137/10000000000 : ℝ)*X 0 0+(2647007087/5000000000 : ℝ)*X 0 1+(1377818491/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4455385321/10000000000 : ℝ)*X 1 0+(-410179631/5000000000 : ℝ)*X 1 1+(6803205281/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-60770301/312500000 : ℝ)*X 0 0+(3293851751/10000000000 : ℝ)*X 0 1+(1416761729/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((509062377/2000000000 : ℝ)*X 1 0+(-24710799/1000000000 : ℝ)*X 1 1+(4290072311/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((256997531/1000000000 : ℝ)*X 2 0+(8564056291/10000000000 : ℝ)*X 2 1+(-30445711/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((5727658573/10000000000 : ℝ)*X 0 0+(2925170353/5000000000 : ℝ)*X 0 1+(333444689/10000000000 : ℝ)*X 0 2+(5727658573/10000000000 : ℝ)*X 1 0+(2925170353/5000000000 : ℝ)*X 1 1+(333444689/10000000000 : ℝ)*X 1 2+(5727658573/10000000000 : ℝ)*X 2 0+(2925170353/5000000000 : ℝ)*X 2 1+(333444689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1603492549/10000000000 : ℝ)*X 0 0+(1902606361/5000000000 : ℝ)*X 0 1+(3446433431/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((701980271/5000000000 : ℝ)*X 1 0+(-891268513/10000000000 : ℝ)*X 1 1+(9029920193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6835945111/10000000000 : ℝ)*X 2 0+(2311747883/5000000000 : ℝ)*X 2 1+(-114170323/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1163103763/1250000000 : ℝ)*X 0 0+(15774031/125000000 : ℝ)*X 0 1+(477537637/10000000000 : ℝ)*X 0 2+(1163103763/1250000000 : ℝ)*X 1 0+(15774031/125000000 : ℝ)*X 1 1+(477537637/10000000000 : ℝ)*X 1 2+(1163103763/1250000000 : ℝ)*X 2 0+(15774031/125000000 : ℝ)*X 2 1+(477537637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-322139597/2000000000 : ℝ)*X 0 0+(608563697/1000000000 : ℝ)*X 0 1+(471246199/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((6928330637/10000000000 : ℝ)*X 1 0+(-92649303/2500000000 : ℝ)*X 1 1+(1140573869/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1499957059/10000000000 : ℝ)*X 2 0+(8758131/9765625 : ℝ)*X 2 1+(-180261007/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((584784781/625000000 : ℝ)*X 0 0+(881157169/10000000000 : ℝ)*X 0 1+(807039241/10000000000 : ℝ)*X 0 2+(584784781/625000000 : ℝ)*X 1 0+(881157169/10000000000 : ℝ)*X 1 1+(807039241/10000000000 : ℝ)*X 1 2+(584784781/625000000 : ℝ)*X 2 0+(881157169/10000000000 : ℝ)*X 2 1+(807039241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((72437/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72437/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11752448718331944806143657075443/680274770875670000000000000000000000 : ℝ) := by norm_num
    linear_combination (538127657263/1000000000000 : ℝ)*(base7) + (1498237/200000000000 : ℝ)*(base13) + (96413/250000000000 : ℝ)*(base49) + (236793/200000000000 : ℝ)*(base59) + (113938963383/50000000000 : ℝ)*(major_s1_0) + (113938963383/50000000000 : ℝ)*(major_s1_1) + (113938963383/50000000000 : ℝ)*(major_s1_2) + (3024673/1000000000000 : ℝ)*(sp_s1_1) + (88252507631/31250000000 : ℝ)*(sp_s1_7) + (706055878959/250000000000 : ℝ)*(sp_s1_8) + (1412115775179/500000000000 : ℝ)*(sp_s1_9) + (121661326053/62500000000 : ℝ)*(sp_s1_13) + (143814981/1000000000000 : ℝ)*(sp_s1_14) + (100197/20000000000 : ℝ)*(sp_s1_15) + (281690711917/200000000000 : ℝ)*(f.failure) + (1412115775179/500000000000 : ℝ)*(f.sum) + (3344285644928644797/9703683212500000000000000000000 : ℝ)*base63 + (21449965209881/21926750000000000000000000 : ℝ)*base65 + (57299308744537/55318750000000000000000000 : ℝ)*base67 + (475599436629291/877070000000000000000000000 : ℝ)*base69 + (25623583976762441873/38429260585000000000000000000000 : ℝ)*base71 + (73444943822941/876310000000000000000000000 : ℝ)*base73 + (378337203146219/442550000000000000000000000 : ℝ)*base75 + (491843558353661/438155000000000000000000000 : ℝ)*base77 + (1512183506037646349/9695274762500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (12819/20000000000000000 : ℝ)*base86 + (12819/20000000000000000 : ℝ)*base88 + (12819/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1533/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1533/2000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (106123831839088069593587571204777/6802747708756700000000000000000000000 : ℝ) := by norm_num
    linear_combination (690283313979/1000000000000 : ℝ)*(base7) + (18238727/1000000000000 : ℝ)*(base27) + (105381494913/250000000000 : ℝ)*(base53) + (326075751057/200000000000 : ℝ)*(major_s1_0) + (326075751057/200000000000 : ℝ)*(major_s1_1) + (1208852775633/1000000000000 : ℝ)*(major_s1_2) + (11922407/250000000000 : ℝ)*(sp_s1_0) + (16336233/1000000000000 : ℝ)*(sp_s1_7) + (98613313/1000000000000 : ℝ)*(sp_s1_8) + (1414744019973/1000000000000 : ℝ)*(sp_s1_14) + (1414709432521/1000000000000 : ℝ)*(sp_s1_15) + (918167012743/500000000000 : ℝ)*(sp_s1_16) + (1697909190473/1000000000000 : ℝ)*(sp_s1_20) + (25066581/500000000000 : ℝ)*(sp_s1_27) + (503847124191/500000000000 : ℝ)*(f.failure) + (918167012743/500000000000 : ℝ)*(f.sum) + (52833301662265198963/155258931400000000000000000000000 : ℝ)*base62 + (3265373882767893/8770700000000000000000000000 : ℝ)*base64 + (179073557598253/885100000000000000000000000 : ℝ)*base66 + (1156638558039817/1754140000000000000000000000 : ℝ)*base68 + (30076480276304124543/768585211700000000000000000000000 : ℝ)*base70 + (542576736286153/1752620000000000000000000000 : ℝ)*base72 + (1182988117900919/1770200000000000000000000000 : ℝ)*base74 + (8416130673603/27384687500000000000000000 : ℝ)*base76 + (136016129250313761/9695274762500000000000000000000 : ℝ)*base78 + (15537/50000000000000000 : ℝ)*base86 + (15537/50000000000000000 : ℝ)*base88 + (15537/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3023/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3023/4000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2045607696002305615343447811/193905495250000000000000000000000 : ℝ) := by norm_num
    linear_combination (8219814071/12500000000 : ℝ)*(base7) + (7882279/500000000000 : ℝ)*(base27) + (322283/1000000000000 : ℝ)*(base34) + (29467647863/1000000000000 : ℝ)*(base40) + (260139445901/500000000000 : ℝ)*(base43) + (1596941114671/1000000000000 : ℝ)*(major_s1_0) + (4205713067/3906250000 : ℝ)*(major_s1_1) + (798470718477/500000000000 : ℝ)*(major_s1_2) + (1628169/62500000000 : ℝ)*(sp_s1_0) + (71180857/1000000000000 : ℝ)*(sp_s1_9) + (644781215649/500000000000 : ℝ)*(sp_s1_21) + (1809867696087/1000000000000 : ℝ)*(sp_s1_22) + (1289517623427/1000000000000 : ℝ)*(sp_s1_23) + (1644596559779/1000000000000 : ℝ)*(sp_s1_27) + (49351376047/50000000000 : ℝ)*(f.failure) + (1809867696087/1000000000000 : ℝ)*(f.sum) + (31317283077786417353/194073664250000000000000000000000 : ℝ)*base63 + (27362080356603/68521093750000000000000000 : ℝ)*base64 + (1508602145404349/2212750000000000000000000000 : ℝ)*base66 + (126612153740737/219267500000000000000000000 : ℝ)*base68 + (40698312355684527113/192146302925000000000000000000000 : ℝ)*base71 + (6918983864343317/8763100000000000000000000000 : ℝ)*base72 + (516251981781421/2212750000000000000000000000 : ℝ)*base74 + (404170261828081/1095387500000000000000000000 : ℝ)*base77 + (88729072787146426873/387810990500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (2271/5000000000000000 : ℝ)*base87 + (2271/5000000000000000 : ℝ)*base89 + (2271/5000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((87631/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(87631/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8851/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8851/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(87707/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(87707/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((72437/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72437/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1533/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1533/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3023/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3023/4000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310053_s1 p hpa hpb X hX hprev0

#print axioms solution

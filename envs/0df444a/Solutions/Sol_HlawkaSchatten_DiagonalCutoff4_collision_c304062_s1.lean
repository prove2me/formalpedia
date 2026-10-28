-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304062_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:48:29.130549+00:00
-- url     : https://prove2.me/submissions/f7c8c6df-5e4e-46cb-9f67-a4691fa85380

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
theorem collision_support_c304062_s1_s1_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-471719899/5000000000 : ℝ)*x 0 + (5026216203/10000000000 : ℝ)*x 1 + (-1272195851/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (471719899/5000000000 : ℝ)^133 ≤ (1116377752387/25000000000000 : ℝ)^101 := by
    have hnat : (471719899 : ℕ)^133*25000000000000^101 ≤ 1116377752387^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471719899 5000000000 1116377752387 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5026216203/10000000000 : ℝ)^133 ≤ (40418938303191/100000000000000 : ℝ)^101 := by
    have hnat : (5026216203 : ℕ)^133*100000000000000^101 ≤ 40418938303191^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026216203 10000000000 40418938303191 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1272195851/2000000000 : ℝ)^133 ≤ (55115550665119/100000000000000 : ℝ)^101 := by
    have hnat : (1272195851 : ℕ)^133*100000000000000^101 ≤ 55115550665119^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272195851 2000000000 55115550665119 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-471719899/5000000000 : ℝ), (5026216203/10000000000 : ℝ), (-1272195851/2000000000 : ℝ)] ![(1116377752387/25000000000000 : ℝ), (40418938303191/100000000000000 : ℝ), (55115550665119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-471719899/5000000000 : ℝ)|^133 ≤ (1116377752387/25000000000000 : ℝ)^101
        have hw : |(-471719899/5000000000 : ℝ)|=(471719899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5026216203/10000000000 : ℝ)|^133 ≤ (40418938303191/100000000000000 : ℝ)^101
        have hw : |(5026216203/10000000000 : ℝ)|=(5026216203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1272195851/2000000000 : ℝ)|^133 ≤ (55115550665119/100000000000000 : ℝ)^101
        have hw : |(-1272195851/2000000000 : ℝ)|=(1272195851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s1_s1_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5046254113/10000000000 : ℝ)*x 0 + (-186513289/2000000000 : ℝ)*x 1 + (-3174147643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5046254113/10000000000 : ℝ)^133 ≤ (40631262930069/100000000000000 : ℝ)^101 := by
    have hnat : (5046254113 : ℕ)^133*100000000000000^101 ≤ 40631262930069^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5046254113 10000000000 40631262930069 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186513289/2000000000 : ℝ)^133 ≤ (4397863006387/100000000000000 : ℝ)^101 := by
    have hnat : (186513289 : ℕ)^133*100000000000000^101 ≤ 4397863006387^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186513289 2000000000 4397863006387 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3174147643/5000000000 : ℝ)^133 ≤ (54970874050011/100000000000000 : ℝ)^101 := by
    have hnat : (3174147643 : ℕ)^133*100000000000000^101 ≤ 54970874050011^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3174147643 5000000000 54970874050011 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5046254113/10000000000 : ℝ), (-186513289/2000000000 : ℝ), (-3174147643/5000000000 : ℝ)] ![(40631262930069/100000000000000 : ℝ), (4397863006387/100000000000000 : ℝ), (54970874050011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5046254113/10000000000 : ℝ)|^133 ≤ (40631262930069/100000000000000 : ℝ)^101
        have hw : |(5046254113/10000000000 : ℝ)|=(5046254113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-186513289/2000000000 : ℝ)|^133 ≤ (4397863006387/100000000000000 : ℝ)^101
        have hw : |(-186513289/2000000000 : ℝ)|=(186513289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3174147643/5000000000 : ℝ)|^133 ≤ (54970874050011/100000000000000 : ℝ)^101
        have hw : |(-3174147643/5000000000 : ℝ)|=(3174147643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s1_s1_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5354336859/10000000000 : ℝ)*x 0 + (1115943029/2000000000 : ℝ)*x 1 + (1699225129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354336859/10000000000 : ℝ)^133 ≤ (43928973785433/100000000000000 : ℝ)^101 := by
    have hnat : (5354336859 : ℕ)^133*100000000000000^101 ≤ 43928973785433^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354336859 10000000000 43928973785433 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115943029/2000000000 : ℝ)^133 ≤ (46379994229757/100000000000000 : ℝ)^101 := by
    have hnat : (1115943029 : ℕ)^133*100000000000000^101 ≤ 46379994229757^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115943029 2000000000 46379994229757 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1699225129/10000000000 : ℝ)^133 ≤ (121137899553/1250000000000 : ℝ)^101 := by
    have hnat : (1699225129 : ℕ)^133*1250000000000^101 ≤ 121137899553^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699225129 10000000000 121137899553 1250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354336859/10000000000 : ℝ), (1115943029/2000000000 : ℝ), (1699225129/10000000000 : ℝ)] ![(43928973785433/100000000000000 : ℝ), (46379994229757/100000000000000 : ℝ), (121137899553/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354336859/10000000000 : ℝ)|^133 ≤ (43928973785433/100000000000000 : ℝ)^101
        have hw : |(5354336859/10000000000 : ℝ)|=(5354336859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1115943029/2000000000 : ℝ)|^133 ≤ (46379994229757/100000000000000 : ℝ)^101
        have hw : |(1115943029/2000000000 : ℝ)|=(1115943029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1699225129/10000000000 : ℝ)|^133 ≤ (121137899553/1250000000000 : ℝ)^101
        have hw : |(1699225129/10000000000 : ℝ)|=(1699225129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s1_s1_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-94966211/1000000000 : ℝ)*x 0 + (95841847/500000000 : ℝ)*x 1 + (-4385403483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94966211/1000000000 : ℝ)^133 ≤ (563041782137/12500000000000 : ℝ)^101 := by
    have hnat : (94966211 : ℕ)^133*12500000000000^101 ≤ 563041782137^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94966211 1000000000 563041782137 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (95841847/500000000 : ℝ)^133 ≤ (5678784999957/50000000000000 : ℝ)^101 := by
    have hnat : (95841847 : ℕ)^133*50000000000000^101 ≤ 5678784999957^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95841847 500000000 5678784999957 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4385403483/5000000000 : ℝ)^133 ≤ (4206904786217/5000000000000 : ℝ)^101 := by
    have hnat : (4385403483 : ℕ)^133*5000000000000^101 ≤ 4206904786217^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4385403483 5000000000 4206904786217 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94966211/1000000000 : ℝ), (95841847/500000000 : ℝ), (-4385403483/5000000000 : ℝ)] ![(563041782137/12500000000000 : ℝ), (5678784999957/50000000000000 : ℝ), (4206904786217/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94966211/1000000000 : ℝ)|^133 ≤ (563041782137/12500000000000 : ℝ)^101
        have hw : |(-94966211/1000000000 : ℝ)|=(94966211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(95841847/500000000 : ℝ)|^133 ≤ (5678784999957/50000000000000 : ℝ)^101
        have hw : |(95841847/500000000 : ℝ)|=(95841847/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4385403483/5000000000 : ℝ)|^133 ≤ (4206904786217/5000000000000 : ℝ)^101
        have hw : |(-4385403483/5000000000 : ℝ)|=(4385403483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s1_s1_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2130002019/10000000000 : ℝ)*x 0 + (-703328131/10000000000 : ℝ)*x 1 + (-4376666563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130002019/10000000000 : ℝ)^133 ≤ (521974775491/4000000000000 : ℝ)^101 := by
    have hnat : (2130002019 : ℕ)^133*4000000000000^101 ≤ 521974775491^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130002019 10000000000 521974775491 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (703328131/10000000000 : ℝ)^133 ≤ (1516600230117/50000000000000 : ℝ)^101 := by
    have hnat : (703328131 : ℕ)^133*50000000000000^101 ≤ 1516600230117^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      703328131 10000000000 1516600230117 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4376666563/5000000000 : ℝ)^133 ≤ (20979357535953/25000000000000 : ℝ)^101 := by
    have hnat : (4376666563 : ℕ)^133*25000000000000^101 ≤ 20979357535953^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376666563 5000000000 20979357535953 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2130002019/10000000000 : ℝ), (-703328131/10000000000 : ℝ), (-4376666563/5000000000 : ℝ)] ![(521974775491/4000000000000 : ℝ), (1516600230117/50000000000000 : ℝ), (20979357535953/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2130002019/10000000000 : ℝ)|^133 ≤ (521974775491/4000000000000 : ℝ)^101
        have hw : |(2130002019/10000000000 : ℝ)|=(2130002019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-703328131/10000000000 : ℝ)|^133 ≤ (1516600230117/50000000000000 : ℝ)^101
        have hw : |(-703328131/10000000000 : ℝ)|=(703328131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4376666563/5000000000 : ℝ)|^133 ≤ (20979357535953/25000000000000 : ℝ)^101
        have hw : |(-4376666563/5000000000 : ℝ)|=(4376666563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s1_s1_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2390740881/10000000000 : ℝ)*x 0 + (483588127/625000000 : ℝ)*x 1 + (545576973/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2390740881/10000000000 : ℝ)^133 ≤ (15192593449653/100000000000000 : ℝ)^101 := by
    have hnat : (2390740881 : ℕ)^133*100000000000000^101 ≤ 15192593449653^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2390740881 10000000000 15192593449653 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (483588127/625000000 : ℝ)^133 ≤ (1426688525063/2000000000000 : ℝ)^101 := by
    have hnat : (483588127 : ℕ)^133*2000000000000^101 ≤ 1426688525063^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483588127 625000000 1426688525063 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545576973/2500000000 : ℝ)^133 ≤ (6736490140533/50000000000000 : ℝ)^101 := by
    have hnat : (545576973 : ℕ)^133*50000000000000^101 ≤ 6736490140533^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545576973 2500000000 6736490140533 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2390740881/10000000000 : ℝ), (483588127/625000000 : ℝ), (545576973/2500000000 : ℝ)] ![(15192593449653/100000000000000 : ℝ), (1426688525063/2000000000000 : ℝ), (6736490140533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2390740881/10000000000 : ℝ)|^133 ≤ (15192593449653/100000000000000 : ℝ)^101
        have hw : |(2390740881/10000000000 : ℝ)|=(2390740881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(483588127/625000000 : ℝ)|^133 ≤ (1426688525063/2000000000000 : ℝ)^101
        have hw : |(483588127/625000000 : ℝ)|=(483588127/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545576973/2500000000 : ℝ)|^133 ≤ (6736490140533/50000000000000 : ℝ)^101
        have hw : |(545576973/2500000000 : ℝ)|=(545576973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s1_s1_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1740092787/5000000000 : ℝ)*x 0 + (1608969181/2000000000 : ℝ)*x 1 + (54651/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1740092787/5000000000 : ℝ)^133 ≤ (1556852747391/6250000000000 : ℝ)^101 := by
    have hnat : (1740092787 : ℕ)^133*6250000000000^101 ≤ 1556852747391^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740092787 5000000000 1556852747391 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1608969181/2000000000 : ℝ)^133 ≤ (37545056089413/50000000000000 : ℝ)^101 := by
    have hnat : (1608969181 : ℕ)^133*50000000000000^101 ≤ 37545056089413^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1608969181 2000000000 37545056089413 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54651/1000000000 : ℝ)^133 ≤ (48771279/20000000000000 : ℝ)^101 := by
    have hnat : (54651 : ℕ)^133*20000000000000^101 ≤ 48771279^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54651 1000000000 48771279 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1740092787/5000000000 : ℝ), (1608969181/2000000000 : ℝ), (54651/1000000000 : ℝ)] ![(1556852747391/6250000000000 : ℝ), (37545056089413/50000000000000 : ℝ), (48771279/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1740092787/5000000000 : ℝ)|^133 ≤ (1556852747391/6250000000000 : ℝ)^101
        have hw : |(1740092787/5000000000 : ℝ)|=(1740092787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1608969181/2000000000 : ℝ)|^133 ≤ (37545056089413/50000000000000 : ℝ)^101
        have hw : |(1608969181/2000000000 : ℝ)|=(1608969181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54651/1000000000 : ℝ)|^133 ≤ (48771279/20000000000000 : ℝ)^101
        have hw : |(54651/1000000000 : ℝ)|=(54651/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s1_s1_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-26761767/312500000 : ℝ)*x 0 + (954096791/5000000000 : ℝ)*x 1 + (-2205371129/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26761767/312500000 : ℝ)^133 ≤ (786192940333/20000000000000 : ℝ)^101 := by
    have hnat : (26761767 : ℕ)^133*20000000000000^101 ≤ 786192940333^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26761767 312500000 786192940333 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (954096791/5000000000 : ℝ)^133 ≤ (2258035785643/20000000000000 : ℝ)^101 := by
    have hnat : (954096791 : ℕ)^133*20000000000000^101 ≤ 2258035785643^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954096791 5000000000 2258035785643 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205371129/2500000000 : ℝ)^133 ≤ (84778856355531/100000000000000 : ℝ)^101 := by
    have hnat : (2205371129 : ℕ)^133*100000000000000^101 ≤ 84778856355531^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205371129 2500000000 84778856355531 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26761767/312500000 : ℝ), (954096791/5000000000 : ℝ), (-2205371129/2500000000 : ℝ)] ![(786192940333/20000000000000 : ℝ), (2258035785643/20000000000000 : ℝ), (84778856355531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26761767/312500000 : ℝ)|^133 ≤ (786192940333/20000000000000 : ℝ)^101
        have hw : |(-26761767/312500000 : ℝ)|=(26761767/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(954096791/5000000000 : ℝ)|^133 ≤ (2258035785643/20000000000000 : ℝ)^101
        have hw : |(954096791/5000000000 : ℝ)|=(954096791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2205371129/2500000000 : ℝ)|^133 ≤ (84778856355531/100000000000000 : ℝ)^101
        have hw : |(-2205371129/2500000000 : ℝ)|=(2205371129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s1_s1_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (868886967/5000000000 : ℝ)*x 0 + (-10993627/100000000 : ℝ)*x 1 + (-550244409/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868886967/5000000000 : ℝ)^133 ≤ (4990787449381/50000000000000 : ℝ)^101 := by
    have hnat : (868886967 : ℕ)^133*50000000000000^101 ≤ 4990787449381^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868886967 5000000000 4990787449381 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10993627/100000000 : ℝ)^133 ≤ (341369018583/6250000000000 : ℝ)^101 := by
    have hnat : (10993627 : ℕ)^133*6250000000000^101 ≤ 341369018583^101*100000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10993627 100000000 341369018583 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550244409/625000000 : ℝ)^133 ≤ (84556520794383/100000000000000 : ℝ)^101 := by
    have hnat : (550244409 : ℕ)^133*100000000000000^101 ≤ 84556520794383^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550244409 625000000 84556520794383 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868886967/5000000000 : ℝ), (-10993627/100000000 : ℝ), (-550244409/625000000 : ℝ)] ![(4990787449381/50000000000000 : ℝ), (341369018583/6250000000000 : ℝ), (84556520794383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868886967/5000000000 : ℝ)|^133 ≤ (4990787449381/50000000000000 : ℝ)^101
        have hw : |(868886967/5000000000 : ℝ)|=(868886967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10993627/100000000 : ℝ)|^133 ≤ (341369018583/6250000000000 : ℝ)^101
        have hw : |(-10993627/100000000 : ℝ)|=(10993627/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-550244409/625000000 : ℝ)|^133 ≤ (84556520794383/100000000000000 : ℝ)^101
        have hw : |(-550244409/625000000 : ℝ)|=(550244409/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s1_s1_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7455033889/10000000000 : ℝ)*x 0 + (1356967787/5000000000 : ℝ)*x 1 + (282686299/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7455033889/10000000000 : ℝ)^133 ≤ (67926247164197/100000000000000 : ℝ)^101 := by
    have hnat : (7455033889 : ℕ)^133*100000000000000^101 ≤ 67926247164197^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7455033889 10000000000 67926247164197 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356967787/5000000000 : ℝ)^133 ≤ (17953367492767/100000000000000 : ℝ)^101 := by
    have hnat : (1356967787 : ℕ)^133*100000000000000^101 ≤ 17953367492767^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356967787 5000000000 17953367492767 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282686299/1250000000 : ℝ)^133 ≤ (441262041251/3125000000000 : ℝ)^101 := by
    have hnat : (282686299 : ℕ)^133*3125000000000^101 ≤ 441262041251^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282686299 1250000000 441262041251 3125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7455033889/10000000000 : ℝ), (1356967787/5000000000 : ℝ), (282686299/1250000000 : ℝ)] ![(67926247164197/100000000000000 : ℝ), (17953367492767/100000000000000 : ℝ), (441262041251/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7455033889/10000000000 : ℝ)|^133 ≤ (67926247164197/100000000000000 : ℝ)^101
        have hw : |(7455033889/10000000000 : ℝ)|=(7455033889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356967787/5000000000 : ℝ)|^133 ≤ (17953367492767/100000000000000 : ℝ)^101
        have hw : |(1356967787/5000000000 : ℝ)|=(1356967787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282686299/1250000000 : ℝ)|^133 ≤ (441262041251/3125000000000 : ℝ)^101
        have hw : |(282686299/1250000000 : ℝ)|=(282686299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s1_s1_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (66386583/80000000 : ℝ)*x 0 + (785668509/2500000000 : ℝ)*x 1 + (202711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66386583/80000000 : ℝ)^133 ≤ (39110548107289/50000000000000 : ℝ)^101 := by
    have hnat : (66386583 : ℕ)^133*50000000000000^101 ≤ 39110548107289^101*80000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66386583 80000000 39110548107289 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (785668509/2500000000 : ℝ)^133 ≤ (5444623447921/25000000000000 : ℝ)^101 := by
    have hnat : (785668509 : ℕ)^133*25000000000000^101 ≤ 5444623447921^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      785668509 2500000000 5444623447921 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202711/2500000000 : ℝ)^133 ≤ (204988281/50000000000000 : ℝ)^101 := by
    have hnat : (202711 : ℕ)^133*50000000000000^101 ≤ 204988281^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202711 2500000000 204988281 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66386583/80000000 : ℝ), (785668509/2500000000 : ℝ), (202711/2500000000 : ℝ)] ![(39110548107289/50000000000000 : ℝ), (5444623447921/25000000000000 : ℝ), (204988281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66386583/80000000 : ℝ)|^133 ≤ (39110548107289/50000000000000 : ℝ)^101
        have hw : |(66386583/80000000 : ℝ)|=(66386583/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(785668509/2500000000 : ℝ)|^133 ≤ (5444623447921/25000000000000 : ℝ)^101
        have hw : |(785668509/2500000000 : ℝ)|=(785668509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(202711/2500000000 : ℝ)|^133 ≤ (204988281/50000000000000 : ℝ)^101
        have hw : |(202711/2500000000 : ℝ)|=(202711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s1_s1_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-384917489/10000000000 : ℝ)*x 0 + (1299948907/2000000000 : ℝ)*x 1 + (-5167745599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (384917489/10000000000 : ℝ)^133 ≤ (21428280347/1562500000000 : ℝ)^101 := by
    have hnat : (384917489 : ℕ)^133*1562500000000^101 ≤ 21428280347^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384917489 10000000000 21428280347 1562500000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1299948907/2000000000 : ℝ)^133 ≤ (11340857645277/20000000000000 : ℝ)^101 := by
    have hnat : (1299948907 : ℕ)^133*20000000000000^101 ≤ 11340857645277^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299948907 2000000000 11340857645277 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5167745599/10000000000 : ℝ)^133 ≤ (10481075455861/25000000000000 : ℝ)^101 := by
    have hnat : (5167745599 : ℕ)^133*25000000000000^101 ≤ 10481075455861^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167745599 10000000000 10481075455861 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-384917489/10000000000 : ℝ), (1299948907/2000000000 : ℝ), (-5167745599/10000000000 : ℝ)] ![(21428280347/1562500000000 : ℝ), (11340857645277/20000000000000 : ℝ), (10481075455861/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-384917489/10000000000 : ℝ)|^133 ≤ (21428280347/1562500000000 : ℝ)^101
        have hw : |(-384917489/10000000000 : ℝ)|=(384917489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1299948907/2000000000 : ℝ)|^133 ≤ (11340857645277/20000000000000 : ℝ)^101
        have hw : |(1299948907/2000000000 : ℝ)|=(1299948907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5167745599/10000000000 : ℝ)|^133 ≤ (10481075455861/25000000000000 : ℝ)^101
        have hw : |(-5167745599/10000000000 : ℝ)|=(5167745599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s1_s1_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7967458993/10000000000 : ℝ)*x 0 + (-40873727/1250000000 : ℝ)*x 1 + (-1731790953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7967458993/10000000000 : ℝ)^133 ≤ (74140384629587/100000000000000 : ℝ)^101 := by
    have hnat : (7967458993 : ℕ)^133*100000000000000^101 ≤ 74140384629587^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7967458993 10000000000 74140384629587 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40873727/1250000000 : ℝ)^133 ≤ (1106347619471/100000000000000 : ℝ)^101 := by
    have hnat : (40873727 : ℕ)^133*100000000000000^101 ≤ 1106347619471^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40873727 1250000000 1106347619471 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1731790953/5000000000 : ℝ)^133 ≤ (24753267738897/100000000000000 : ℝ)^101 := by
    have hnat : (1731790953 : ℕ)^133*100000000000000^101 ≤ 24753267738897^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1731790953 5000000000 24753267738897 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7967458993/10000000000 : ℝ), (-40873727/1250000000 : ℝ), (-1731790953/5000000000 : ℝ)] ![(74140384629587/100000000000000 : ℝ), (1106347619471/100000000000000 : ℝ), (24753267738897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7967458993/10000000000 : ℝ)|^133 ≤ (74140384629587/100000000000000 : ℝ)^101
        have hw : |(7967458993/10000000000 : ℝ)|=(7967458993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40873727/1250000000 : ℝ)|^133 ≤ (1106347619471/100000000000000 : ℝ)^101
        have hw : |(-40873727/1250000000 : ℝ)|=(40873727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1731790953/5000000000 : ℝ)|^133 ≤ (24753267738897/100000000000000 : ℝ)^101
        have hw : |(-1731790953/5000000000 : ℝ)|=(1731790953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s1_s1_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (461487553/2000000000 : ℝ)*x 0 + (1870578989/2500000000 : ℝ)*x 1 + (658110029/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (461487553/2000000000 : ℝ)^133 ≤ (226552796357/1562500000000 : ℝ)^101 := by
    have hnat : (461487553 : ℕ)^133*1562500000000^101 ≤ 226552796357^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461487553 2000000000 226552796357 1562500000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1870578989/2500000000 : ℝ)^133 ≤ (68253774105061/100000000000000 : ℝ)^101 := by
    have hnat : (1870578989 : ℕ)^133*100000000000000^101 ≤ 68253774105061^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870578989 2500000000 68253774105061 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658110029/2500000000 : ℝ)^133 ≤ (17246846913227/100000000000000 : ℝ)^101 := by
    have hnat : (658110029 : ℕ)^133*100000000000000^101 ≤ 17246846913227^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658110029 2500000000 17246846913227 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(461487553/2000000000 : ℝ), (1870578989/2500000000 : ℝ), (658110029/2500000000 : ℝ)] ![(226552796357/1562500000000 : ℝ), (68253774105061/100000000000000 : ℝ), (17246846913227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(461487553/2000000000 : ℝ)|^133 ≤ (226552796357/1562500000000 : ℝ)^101
        have hw : |(461487553/2000000000 : ℝ)|=(461487553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1870578989/2500000000 : ℝ)|^133 ≤ (68253774105061/100000000000000 : ℝ)^101
        have hw : |(1870578989/2500000000 : ℝ)|=(1870578989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658110029/2500000000 : ℝ)|^133 ≤ (17246846913227/100000000000000 : ℝ)^101
        have hw : |(658110029/2500000000 : ℝ)|=(658110029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s1_s1_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8560172401/10000000000 : ℝ)*x 0 + (2771063477/10000000000 : ℝ)*x 1 + (-35691431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8560172401/10000000000 : ℝ)^133 ≤ (40743734784081/50000000000000 : ℝ)^101 := by
    have hnat : (8560172401 : ℕ)^133*50000000000000^101 ≤ 40743734784081^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8560172401 10000000000 40743734784081 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2771063477/10000000000 : ℝ)^133 ≤ (9226335076257/50000000000000 : ℝ)^101 := by
    have hnat : (2771063477 : ℕ)^133*50000000000000^101 ≤ 9226335076257^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2771063477 10000000000 9226335076257 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35691431/10000000000 : ℝ)^133 ≤ (14965067831/25000000000000 : ℝ)^101 := by
    have hnat : (35691431 : ℕ)^133*25000000000000^101 ≤ 14965067831^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35691431 10000000000 14965067831 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8560172401/10000000000 : ℝ), (2771063477/10000000000 : ℝ), (-35691431/10000000000 : ℝ)] ![(40743734784081/50000000000000 : ℝ), (9226335076257/50000000000000 : ℝ), (14965067831/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8560172401/10000000000 : ℝ)|^133 ≤ (40743734784081/50000000000000 : ℝ)^101
        have hw : |(8560172401/10000000000 : ℝ)|=(8560172401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2771063477/10000000000 : ℝ)|^133 ≤ (9226335076257/50000000000000 : ℝ)^101
        have hw : |(2771063477/10000000000 : ℝ)|=(2771063477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35691431/10000000000 : ℝ)|^133 ≤ (14965067831/25000000000000 : ℝ)^101
        have hw : |(-35691431/10000000000 : ℝ)|=(35691431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304062_s1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((24401/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(24401/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3017/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3017/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10701/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10701/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((92539/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(92539/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46001/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46001/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38341/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38341/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (24401/25000 : ℝ) ^ (33/8 : ℝ) ≤ (45240138038569267351/50000000000000000000 : ℝ) := by
    have hpowers : (24401/25000 : ℝ)^33 ≤ (45240138038569267351/50000000000000000000 : ℝ)^8 := by
      have hnat : (24401 : ℕ)^33*50000000000000000000^8 ≤ 45240138038569267351^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24401 25000 45240138038569267351 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24401/25000 : ℝ)) (X := (45240138038569267351/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (95240138038569267351/50000000000000000000 : ℝ) ≤ (1169075144401559/1000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (95240138038569267351/50000000000000000000 : ℝ)^8 ≤ (1169075144401559/1000000000000000 : ℝ)^33 := by
      have hnat : (95240138038569267351 : ℕ)^8*1000000000000000^33 ≤ 1169075144401559^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        95240138038569267351 50000000000000000000 1169075144401559 1000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1169075144401559/1000000000000000 : ℝ)) (X := (95240138038569267351/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (70240138038569267351/25000000000000000000 : ℝ) ≤ (2569168000798891/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (70240138038569267351/25000000000000000000 : ℝ)^8 ≤ (2569168000798891/2000000000000000 : ℝ)^33 := by
      have hnat : (70240138038569267351 : ℕ)^8*2000000000000000^33 ≤ 2569168000798891^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70240138038569267351 25000000000000000000 2569168000798891 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2569168000798891/2000000000000000 : ℝ)) (X := (70240138038569267351/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(169075144401559/976040000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(231017711995773/1952080000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (24401/25000 : ℝ)) (alpha := (169075144401559/976040000000000 : ℝ)) (beta := (231017711995773/1952080000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (24401/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(169075144401559/976040000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(231017711995773/1952080000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (3017/3125 : ℝ) ^ (33/8 : ℝ) ≤ (43247580862822089809/50000000000000000000 : ℝ) := by
    have hpowers : (3017/3125 : ℝ)^33 ≤ (43247580862822089809/50000000000000000000 : ℝ)^8 := by
      have hnat : (3017 : ℕ)^33*50000000000000000000^8 ≤ 43247580862822089809^8*3125^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3017 3125 43247580862822089809 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3017/3125 : ℝ)) (X := (43247580862822089809/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (93247580862822089809/50000000000000000000 : ℝ) ≤ (5815490957465133/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (93247580862822089809/50000000000000000000 : ℝ)^8 ≤ (5815490957465133/5000000000000000 : ℝ)^33 := by
      have hnat : (93247580862822089809 : ℕ)^8*5000000000000000^33 ≤ 5815490957465133^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93247580862822089809 50000000000000000000 5815490957465133 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5815490957465133/5000000000000000 : ℝ)) (X := (93247580862822089809/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (68247580862822089809/25000000000000000000 : ℝ) ≤ (12756533309979209/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (68247580862822089809/25000000000000000000 : ℝ)^8 ≤ (12756533309979209/10000000000000000 : ℝ)^33 := by
      have hnat : (68247580862822089809 : ℕ)^8*10000000000000000^33 ≤ 12756533309979209^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68247580862822089809 25000000000000000000 12756533309979209 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12756533309979209/10000000000000000 : ℝ)) (X := (68247580862822089809/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(815490957465133/4827200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1125551395048943/9654400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (3017/3125 : ℝ)) (alpha := (815490957465133/4827200000000000 : ℝ)) (beta := (1125551395048943/9654400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (3017/3125 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(815490957465133/4827200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1125551395048943/9654400000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (10701/12500 : ℝ) ^ (33/8 : ℝ) ≤ (1646158768837128431/3125000000000000000 : ℝ) := by
    have hpowers : (10701/12500 : ℝ)^33 ≤ (1646158768837128431/3125000000000000000 : ℝ)^8 := by
      have hnat : (10701 : ℕ)^33*3125000000000000000^8 ≤ 1646158768837128431^8*12500^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10701 12500 1646158768837128431 3125000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10701/12500 : ℝ)) (X := (1646158768837128431/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (4771158768837128431/3125000000000000000 : ℝ) ≤ (5540146383971841/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (4771158768837128431/3125000000000000000 : ℝ)^8 ≤ (5540146383971841/5000000000000000 : ℝ)^33 := by
      have hnat : (4771158768837128431 : ℕ)^8*5000000000000000^33 ≤ 5540146383971841^33*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4771158768837128431 3125000000000000000 5540146383971841 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5540146383971841/5000000000000000 : ℝ)) (X := (4771158768837128431/3125000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (3208658768837128431/1562500000000000000 : ℝ) ≤ (5952897852462107/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3208658768837128431/1562500000000000000 : ℝ)^8 ≤ (5952897852462107/5000000000000000 : ℝ)^33 := by
      have hnat : (3208658768837128431 : ℕ)^8*5000000000000000^33 ≤ 5952897852462107^33*1562500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3208658768837128431 1562500000000000000 5952897852462107 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5952897852462107/5000000000000000 : ℝ)) (X := (3208658768837128431/1562500000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(540146383971841/4280400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(206375734245133/2140200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (10701/12500 : ℝ)) (alpha := (540146383971841/4280400000000000 : ℝ)) (beta := (206375734245133/2140200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (10701/12500 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(540146383971841/4280400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(206375734245133/2140200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-471719899/5000000000 : ℝ)*X 0 0+(5026216203/10000000000 : ℝ)*X 0 1+(-1272195851/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5046254113/10000000000 : ℝ)*X 1 0+(-186513289/2000000000 : ℝ)*X 1 1+(-3174147643/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5354336859/10000000000 : ℝ)*X 2 0+(1115943029/2000000000 : ℝ)*X 2 1+(1699225129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-94966211/1000000000 : ℝ)*X 0 0+(95841847/500000000 : ℝ)*X 0 1+(-4385403483/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2130002019/10000000000 : ℝ)*X 1 0+(-703328131/10000000000 : ℝ)*X 1 1+(-4376666563/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2390740881/10000000000 : ℝ)*X 2 0+(483588127/625000000 : ℝ)*X 2 1+(545576973/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1740092787/5000000000 : ℝ)*X 0 0+(1608969181/2000000000 : ℝ)*X 0 1+(54651/1000000000 : ℝ)*X 0 2+(1740092787/5000000000 : ℝ)*X 1 0+(1608969181/2000000000 : ℝ)*X 1 1+(54651/1000000000 : ℝ)*X 1 2+(1740092787/5000000000 : ℝ)*X 2 0+(1608969181/2000000000 : ℝ)*X 2 1+(54651/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-26761767/312500000 : ℝ)*X 0 0+(954096791/5000000000 : ℝ)*X 0 1+(-2205371129/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((868886967/5000000000 : ℝ)*X 1 0+(-10993627/100000000 : ℝ)*X 1 1+(-550244409/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((7455033889/10000000000 : ℝ)*X 2 0+(1356967787/5000000000 : ℝ)*X 2 1+(282686299/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((66386583/80000000 : ℝ)*X 0 0+(785668509/2500000000 : ℝ)*X 0 1+(202711/2500000000 : ℝ)*X 0 2+(66386583/80000000 : ℝ)*X 1 0+(785668509/2500000000 : ℝ)*X 1 1+(202711/2500000000 : ℝ)*X 1 2+(66386583/80000000 : ℝ)*X 2 0+(785668509/2500000000 : ℝ)*X 2 1+(202711/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-384917489/10000000000 : ℝ)*X 0 0+(1299948907/2000000000 : ℝ)*X 0 1+(-5167745599/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7967458993/10000000000 : ℝ)*X 1 0+(-40873727/1250000000 : ℝ)*X 1 1+(-1731790953/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((461487553/2000000000 : ℝ)*X 2 0+(1870578989/2500000000 : ℝ)*X 2 1+(658110029/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((8560172401/10000000000 : ℝ)*X 0 0+(2771063477/10000000000 : ℝ)*X 0 1+(-35691431/10000000000 : ℝ)*X 0 2+(8560172401/10000000000 : ℝ)*X 1 0+(2771063477/10000000000 : ℝ)*X 1 1+(-35691431/10000000000 : ℝ)*X 1 2+(8560172401/10000000000 : ℝ)*X 2 0+(2771063477/10000000000 : ℝ)*X 2 1+(-35691431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((92539/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(92539/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13027917690712840754618064869/2500902411800000000000000000000000 : ℝ) := by norm_num
    linear_combination (122483603353/1000000000000 : ℝ)*(base5) + (946102983349/1000000000000 : ℝ)*(base7) + (444171658819/250000000000 : ℝ)*(major_s1_0) + (444171658819/250000000000 : ℝ)*(major_s1_1) + (444171658819/250000000000 : ℝ)*(major_s1_2) + (3341443/1000000000000 : ℝ)*(sp_s1_0) + (577451/200000000000 : ℝ)*(sp_s1_1) + (894795639113/500000000000 : ℝ)*(sp_s1_7) + (1789601925383/1000000000000 : ℝ)*(sp_s1_8) + (1912118201831/1000000000000 : ℝ)*(sp_s1_9) + (1995019925433/1000000000000 : ℝ)*(sp_s1_13) + (24837111/500000000000 : ℝ)*(sp_s1_14) + (39481253/1000000000000 : ℝ)*(sp_s1_15) + (2423853/250000000000 : ℝ)*(sp_s1_23) + (1171400545437/1000000000000 : ℝ)*(f.failure) + (1789644293891/1000000000000 : ℝ)*(f.sum) + (397945366258272257/1844852400000000000000000000000 : ℝ)*base63 + (293676519272737/535050000000000000000000000 : ℝ)*base65 + (178785119928229/344800000000000000000000000 : ℝ)*base66 + (543877237754419/1070100000000000000000000000 : ℝ)*base69 + (3915774348111625247/13055755050000000000000000000000 : ℝ)*base71 + (240516328795933/488020000000000000000000000 : ℝ)*base72 + (134517268961641/172400000000000000000000000 : ℝ)*base75 + (72703726726723/61002500000000000000000000 : ℝ)*base77 + (2238413693028321091/8413464800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (9917/12500000000000000 : ℝ)*base86 + (9917/12500000000000000 : ℝ)*base88 + (9917/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46001/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46001/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (567659609062240618729265570401/42015160518240000000000000000000000 : ℝ) := by norm_num
    linear_combination (6452551379/100000000000 : ℝ)*(base5) + (4741314501/5000000000 : ℝ)*(base7) + (16669/50000000000 : ℝ)*(base40) + (24340665379/1000000000000 : ℝ)*(base60) + (175056486317/100000000000 : ℝ)*(major_s1_0) + (175056486317/100000000000 : ℝ)*(major_s1_1) + (175056486317/100000000000 : ℝ)*(major_s1_2) + (1291723/1000000000000 : ℝ)*(sp_s1_1) + (225838501/1000000000000 : ℝ)*(sp_s1_7) + (2300449/25000000000 : ℝ)*(sp_s1_8) + (1753042425677/1000000000000 : ℝ)*(sp_s1_14) + (350634990899/200000000000 : ℝ)*(sp_s1_15) + (113612111123/62500000000 : ℝ)*(sp_s1_16) + (254739423879/125000000000 : ℝ)*(sp_s1_20) + (577089002311/500000000000 : ℝ)*(f.failure) + (876634132089/500000000000 : ℝ)*(f.sum) + (1799767403653484087/5165586720000000000000000000000 : ℝ)*base62 + (28705127877451/214020000000000000000000000 : ℝ)*base64 + (160162745973309/965440000000000000000000000 : ℝ)*base66 + (157428077946679/428040000000000000000000000 : ℝ)*base68 + (267048609355775681/2611151010000000000000000000000 : ℝ)*base71 + (104018908742751/195208000000000000000000000 : ℝ)*base72 + (7786267368983/482720000000000000000000000 : ℝ)*base74 + (145998247624247/488020000000000000000000000 : ℝ)*base77 + (900085152714385121/4711540288000000000000000000000 : ℝ)*base78 + (1749/6250000000000000 : ℝ)*base87 + (1749/6250000000000000 : ℝ)*base89 + (1749/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38341/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38341/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2336548900231077021448741983/350126337652000000000000000000000 : ℝ) := by norm_num
    linear_combination (165638865029/250000000000 : ℝ)*(base7) + (10076761/1000000000000 : ℝ)*(base11) + (372979/1000000000000 : ℝ)*(base40) + (427981401187/1000000000000 : ℝ)*(base43) + (1785829/250000000000 : ℝ)*(base59) + (1507452298011/1000000000000 : ℝ)*(major_s1_0) + (134933862103/125000000000 : ℝ)*(major_s1_1) + (1507452298011/1000000000000 : ℝ)*(major_s1_2) + (511793/25000000000 : ℝ)*(sp_s1_2) + (208344353/1000000000000 : ℝ)*(sp_s1_20) + (589107577271/500000000000 : ℝ)*(sp_s1_21) + (1606206632489/1000000000000 : ℝ)*(sp_s1_22) + (1178204759583/1000000000000 : ℝ)*(sp_s1_23) + (414059189473/250000000000 : ℝ)*(sp_s1_27) + (99388964213/100000000000 : ℝ)*(f.failure) + (1606206632489/1000000000000 : ℝ)*(f.sum) + (86470302048039501/286977040000000000000000000000 : ℝ)*base63 + (62760794386753/237800000000000000000000000 : ℝ)*base64 + (345621636988169/1206800000000000000000000000 : ℝ)*base67 + (254411970354499/475600000000000000000000000 : ℝ)*base69 + (950089670350511543/1450639450000000000000000000000 : ℝ)*base71 + (123675420224653/390416000000000000000000000 : ℝ)*base72 + (9893190400419/603400000000000000000000000 : ℝ)*base75 + (214730233284611/976040000000000000000000000 : ℝ)*base76 + (3387363449754307589/7361781700000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (517/1250000000000000 : ℝ)*base87 + (517/1250000000000000 : ℝ)*base89 + (517/1250000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((24401/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(24401/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3017/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3017/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10701/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10701/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((92539/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(92539/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46001/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46001/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38341/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38341/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304062_s1 p hpa hpb X hX hprev0

#print axioms solution

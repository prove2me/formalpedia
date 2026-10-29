-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310061_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:28:05.816213+00:00
-- url     : https://prove2.me/submissions/ce9c9ad3-ef02-49f5-b9ca-5f9f2cc29250

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
theorem collision_support_c310061_s4_s4_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-245551661/1000000000 : ℝ)*x 0 + (4506697323/10000000000 : ℝ)*x 1 + (1414445323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (245551661/1000000000 : ℝ)^71 ≤ (2040045753441/12500000000000 : ℝ)^55 := by
    have hnat : (245551661 : ℕ)^71*12500000000000^55 ≤ 2040045753441^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245551661 1000000000 2040045753441 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506697323/10000000000 : ℝ)^71 ≤ (35740666772583/100000000000000 : ℝ)^55 := by
    have hnat : (4506697323 : ℕ)^71*100000000000000^55 ≤ 35740666772583^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506697323 10000000000 35740666772583 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414445323/2500000000 : ℝ)^71 ≤ (47938967185479/100000000000000 : ℝ)^55 := by
    have hnat : (1414445323 : ℕ)^71*100000000000000^55 ≤ 47938967185479^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414445323 2500000000 47938967185479 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-245551661/1000000000 : ℝ), (4506697323/10000000000 : ℝ), (1414445323/2500000000 : ℝ)] ![(2040045753441/12500000000000 : ℝ), (35740666772583/100000000000000 : ℝ), (47938967185479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-245551661/1000000000 : ℝ)|^71 ≤ (2040045753441/12500000000000 : ℝ)^55
        have hw : |(-245551661/1000000000 : ℝ)|=(245551661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506697323/10000000000 : ℝ)|^71 ≤ (35740666772583/100000000000000 : ℝ)^55
        have hw : |(4506697323/10000000000 : ℝ)|=(4506697323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1414445323/2500000000 : ℝ)|^71 ≤ (47938967185479/100000000000000 : ℝ)^55
        have hw : |(1414445323/2500000000 : ℝ)|=(1414445323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s4_s4_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1169895583/2500000000 : ℝ)*x 0 + (-1249772207/5000000000 : ℝ)*x 1 + (1364856413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1169895583/2500000000 : ℝ)^71 ≤ (37520389463149/100000000000000 : ℝ)^55 := by
    have hnat : (1169895583 : ℕ)^71*100000000000000^55 ≤ 37520389463149^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1169895583 2500000000 37520389463149 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249772207/5000000000 : ℝ)^71 ≤ (667964064997/4000000000000 : ℝ)^55 := by
    have hnat : (1249772207 : ℕ)^71*4000000000000^55 ≤ 667964064997^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249772207 5000000000 667964064997 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364856413/2500000000 : ℝ)^71 ≤ (22890254446643/50000000000000 : ℝ)^55 := by
    have hnat : (1364856413 : ℕ)^71*50000000000000^55 ≤ 22890254446643^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364856413 2500000000 22890254446643 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1169895583/2500000000 : ℝ), (-1249772207/5000000000 : ℝ), (1364856413/2500000000 : ℝ)] ![(37520389463149/100000000000000 : ℝ), (667964064997/4000000000000 : ℝ), (22890254446643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1169895583/2500000000 : ℝ)|^71 ≤ (37520389463149/100000000000000 : ℝ)^55
        have hw : |(1169895583/2500000000 : ℝ)|=(1169895583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1249772207/5000000000 : ℝ)|^71 ≤ (667964064997/4000000000000 : ℝ)^55
        have hw : |(-1249772207/5000000000 : ℝ)|=(1249772207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364856413/2500000000 : ℝ)|^71 ≤ (22890254446643/50000000000000 : ℝ)^55
        have hw : |(1364856413/2500000000 : ℝ)|=(1364856413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s4_s4_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4702763317/10000000000 : ℝ)*x 0 + (1209831657/2000000000 : ℝ)*x 1 + (-1677205957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4702763317/10000000000 : ℝ)^71 ≤ (37760493927137/100000000000000 : ℝ)^55 := by
    have hnat : (4702763317 : ℕ)^71*100000000000000^55 ≤ 37760493927137^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4702763317 10000000000 37760493927137 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209831657/2000000000 : ℝ)^71 ≤ (1633195017187/3125000000000 : ℝ)^55 := by
    have hnat : (1209831657 : ℕ)^71*3125000000000^55 ≤ 1633195017187^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209831657 2000000000 1633195017187 3125000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1677205957/10000000000 : ℝ)^71 ≤ (498863275599/5000000000000 : ℝ)^55 := by
    have hnat : (1677205957 : ℕ)^71*5000000000000^55 ≤ 498863275599^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677205957 10000000000 498863275599 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4702763317/10000000000 : ℝ), (1209831657/2000000000 : ℝ), (-1677205957/10000000000 : ℝ)] ![(37760493927137/100000000000000 : ℝ), (1633195017187/3125000000000 : ℝ), (498863275599/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4702763317/10000000000 : ℝ)|^71 ≤ (37760493927137/100000000000000 : ℝ)^55
        have hw : |(4702763317/10000000000 : ℝ)|=(4702763317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1209831657/2000000000 : ℝ)|^71 ≤ (1633195017187/3125000000000 : ℝ)^55
        have hw : |(1209831657/2000000000 : ℝ)|=(1209831657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1677205957/10000000000 : ℝ)|^71 ≤ (498863275599/5000000000000 : ℝ)^55
        have hw : |(-1677205957/10000000000 : ℝ)|=(1677205957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s4_s4_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (292339273/500000000 : ℝ)*x 0 + (3120013193/10000000000 : ℝ)*x 1 + (926128801/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (292339273/500000000 : ℝ)^71 ≤ (62520328849/125000000000 : ℝ)^55 := by
    have hnat : (292339273 : ℕ)^71*125000000000^55 ≤ 62520328849^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292339273 500000000 62520328849 125000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3120013193/10000000000 : ℝ)^71 ≤ (22233198093161/100000000000000 : ℝ)^55 := by
    have hnat : (3120013193 : ℕ)^71*100000000000000^55 ≤ 22233198093161^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3120013193 10000000000 22233198093161 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (926128801/2500000000 : ℝ)^71 ≤ (27750538805139/100000000000000 : ℝ)^55 := by
    have hnat : (926128801 : ℕ)^71*100000000000000^55 ≤ 27750538805139^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926128801 2500000000 27750538805139 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(292339273/500000000 : ℝ), (3120013193/10000000000 : ℝ), (926128801/2500000000 : ℝ)] ![(62520328849/125000000000 : ℝ), (22233198093161/100000000000000 : ℝ), (27750538805139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(292339273/500000000 : ℝ)|^71 ≤ (62520328849/125000000000 : ℝ)^55
        have hw : |(292339273/500000000 : ℝ)|=(292339273/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3120013193/10000000000 : ℝ)|^71 ≤ (22233198093161/100000000000000 : ℝ)^55
        have hw : |(3120013193/10000000000 : ℝ)|=(3120013193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(926128801/2500000000 : ℝ)|^71 ≤ (27750538805139/100000000000000 : ℝ)^55
        have hw : |(926128801/2500000000 : ℝ)|=(926128801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s4_s4_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-494228401/2000000000 : ℝ)*x 0 + (4242800459/10000000000 : ℝ)*x 1 + (5889017407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (494228401/2000000000 : ℝ)^71 ≤ (3290910879037/20000000000000 : ℝ)^55 := by
    have hnat : (494228401 : ℕ)^71*20000000000000^55 ≤ 3290910879037^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494228401 2000000000 3290910879037 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242800459/10000000000 : ℝ)^71 ≤ (4132790386721/12500000000000 : ℝ)^55 := by
    have hnat : (4242800459 : ℕ)^71*12500000000000^55 ≤ 4132790386721^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242800459 10000000000 4132790386721 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5889017407/10000000000 : ℝ)^71 ≤ (25241561243391/50000000000000 : ℝ)^55 := by
    have hnat : (5889017407 : ℕ)^71*50000000000000^55 ≤ 25241561243391^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5889017407 10000000000 25241561243391 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-494228401/2000000000 : ℝ), (4242800459/10000000000 : ℝ), (5889017407/10000000000 : ℝ)] ![(3290910879037/20000000000000 : ℝ), (4132790386721/12500000000000 : ℝ), (25241561243391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-494228401/2000000000 : ℝ)|^71 ≤ (3290910879037/20000000000000 : ℝ)^55
        have hw : |(-494228401/2000000000 : ℝ)|=(494228401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242800459/10000000000 : ℝ)|^71 ≤ (4132790386721/12500000000000 : ℝ)^55
        have hw : |(4242800459/10000000000 : ℝ)|=(4242800459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5889017407/10000000000 : ℝ)|^71 ≤ (25241561243391/50000000000000 : ℝ)^55
        have hw : |(5889017407/10000000000 : ℝ)|=(5889017407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s4_s4_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (904587169/2000000000 : ℝ)*x 0 + (-544783689/2500000000 : ℝ)*x 1 + (5854734171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (904587169/2000000000 : ℝ)^71 ≤ (561046843663/1562500000000 : ℝ)^55 := by
    have hnat : (904587169 : ℕ)^71*1562500000000^55 ≤ 561046843663^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904587169 2000000000 561046843663 1562500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544783689/2500000000 : ℝ)^71 ≤ (1398894339897/10000000000000 : ℝ)^55 := by
    have hnat : (544783689 : ℕ)^71*10000000000000^55 ≤ 1398894339897^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544783689 2500000000 1398894339897 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5854734171/10000000000 : ℝ)^71 ≤ (10020811717297/20000000000000 : ℝ)^55 := by
    have hnat : (5854734171 : ℕ)^71*20000000000000^55 ≤ 10020811717297^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5854734171 10000000000 10020811717297 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(904587169/2000000000 : ℝ), (-544783689/2500000000 : ℝ), (5854734171/10000000000 : ℝ)] ![(561046843663/1562500000000 : ℝ), (1398894339897/10000000000000 : ℝ), (10020811717297/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(904587169/2000000000 : ℝ)|^71 ≤ (561046843663/1562500000000 : ℝ)^55
        have hw : |(904587169/2000000000 : ℝ)|=(904587169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544783689/2500000000 : ℝ)|^71 ≤ (1398894339897/10000000000000 : ℝ)^55
        have hw : |(-544783689/2500000000 : ℝ)|=(544783689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5854734171/10000000000 : ℝ)|^71 ≤ (10020811717297/20000000000000 : ℝ)^55
        have hw : |(5854734171/10000000000 : ℝ)|=(5854734171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s4_s4_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (284134707/625000000 : ℝ)*x 0 + (805624201/1250000000 : ℝ)*x 1 + (-1293765181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (284134707/625000000 : ℝ)^71 ≤ (18072568451653/50000000000000 : ℝ)^55 := by
    have hnat : (284134707 : ℕ)^71*50000000000000^55 ≤ 18072568451653^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284134707 625000000 18072568451653 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805624201/1250000000 : ℝ)^71 ≤ (14179587206113/25000000000000 : ℝ)^55 := by
    have hnat : (805624201 : ℕ)^71*25000000000000^55 ≤ 14179587206113^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805624201 1250000000 14179587206113 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293765181/10000000000 : ℝ)^71 ≤ (3568257128647/50000000000000 : ℝ)^55 := by
    have hnat : (1293765181 : ℕ)^71*50000000000000^55 ≤ 3568257128647^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293765181 10000000000 3568257128647 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(284134707/625000000 : ℝ), (805624201/1250000000 : ℝ), (-1293765181/10000000000 : ℝ)] ![(18072568451653/50000000000000 : ℝ), (14179587206113/25000000000000 : ℝ), (3568257128647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(284134707/625000000 : ℝ)|^71 ≤ (18072568451653/50000000000000 : ℝ)^55
        have hw : |(284134707/625000000 : ℝ)|=(284134707/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805624201/1250000000 : ℝ)|^71 ≤ (14179587206113/25000000000000 : ℝ)^55
        have hw : |(805624201/1250000000 : ℝ)|=(805624201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1293765181/10000000000 : ℝ)|^71 ≤ (3568257128647/50000000000000 : ℝ)^55
        have hw : |(-1293765181/10000000000 : ℝ)|=(1293765181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s4_s4_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (734074057/1250000000 : ℝ)*x 0 + (224371889/625000000 : ℝ)*x 1 + (802134393/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (734074057/1250000000 : ℝ)^71 ≤ (50301434265077/100000000000000 : ℝ)^55 := by
    have hnat : (734074057 : ℕ)^71*100000000000000^55 ≤ 50301434265077^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734074057 1250000000 50301434265077 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224371889/625000000 : ℝ)^71 ≤ (26647692348473/100000000000000 : ℝ)^55 := by
    have hnat : (224371889 : ℕ)^71*100000000000000^55 ≤ 26647692348473^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224371889 625000000 26647692348473 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (802134393/2500000000 : ℝ)^71 ≤ (23050873375029/100000000000000 : ℝ)^55 := by
    have hnat : (802134393 : ℕ)^71*100000000000000^55 ≤ 23050873375029^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802134393 2500000000 23050873375029 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(734074057/1250000000 : ℝ), (224371889/625000000 : ℝ), (802134393/2500000000 : ℝ)] ![(50301434265077/100000000000000 : ℝ), (26647692348473/100000000000000 : ℝ), (23050873375029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(734074057/1250000000 : ℝ)|^71 ≤ (50301434265077/100000000000000 : ℝ)^55
        have hw : |(734074057/1250000000 : ℝ)|=(734074057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224371889/625000000 : ℝ)|^71 ≤ (26647692348473/100000000000000 : ℝ)^55
        have hw : |(224371889/625000000 : ℝ)|=(224371889/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(802134393/2500000000 : ℝ)|^71 ≤ (23050873375029/100000000000000 : ℝ)^55
        have hw : |(802134393/2500000000 : ℝ)|=(802134393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s4_s4_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1953421783/10000000000 : ℝ)*x 0 + (4661426829/10000000000 : ℝ)*x 1 + (5892354439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1953421783/10000000000 : ℝ)^71 ≤ (12147366729697/100000000000000 : ℝ)^55 := by
    have hnat : (1953421783 : ℕ)^71*100000000000000^55 ≤ 12147366729697^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953421783 10000000000 12147366729697 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4661426829/10000000000 : ℝ)^71 ≤ (2333286213743/6250000000000 : ℝ)^55 := by
    have hnat : (4661426829 : ℕ)^71*6250000000000^55 ≤ 2333286213743^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4661426829 10000000000 2333286213743 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5892354439/10000000000 : ℝ)^71 ≤ (50520053837427/100000000000000 : ℝ)^55 := by
    have hnat : (5892354439 : ℕ)^71*100000000000000^55 ≤ 50520053837427^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5892354439 10000000000 50520053837427 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1953421783/10000000000 : ℝ), (4661426829/10000000000 : ℝ), (5892354439/10000000000 : ℝ)] ![(12147366729697/100000000000000 : ℝ), (2333286213743/6250000000000 : ℝ), (50520053837427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1953421783/10000000000 : ℝ)|^71 ≤ (12147366729697/100000000000000 : ℝ)^55
        have hw : |(-1953421783/10000000000 : ℝ)|=(1953421783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4661426829/10000000000 : ℝ)|^71 ≤ (2333286213743/6250000000000 : ℝ)^55
        have hw : |(4661426829/10000000000 : ℝ)|=(4661426829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5892354439/10000000000 : ℝ)|^71 ≤ (50520053837427/100000000000000 : ℝ)^55
        have hw : |(5892354439/10000000000 : ℝ)|=(5892354439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s4_s4_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2199810493/5000000000 : ℝ)*x 0 + (-290646783/1250000000 : ℝ)*x 1 + (366129559/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2199810493/5000000000 : ℝ)^71 ≤ (34648267512607/100000000000000 : ℝ)^55 := by
    have hnat : (2199810493 : ℕ)^71*100000000000000^55 ≤ 34648267512607^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199810493 5000000000 34648267512607 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (290646783/1250000000 : ℝ)^71 ≤ (7605392976341/50000000000000 : ℝ)^55 := by
    have hnat : (290646783 : ℕ)^71*50000000000000^55 ≤ 7605392976341^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290646783 1250000000 7605392976341 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (366129559/625000000 : ℝ)^71 ≤ (5014094651733/10000000000000 : ℝ)^55 := by
    have hnat : (366129559 : ℕ)^71*10000000000000^55 ≤ 5014094651733^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366129559 625000000 5014094651733 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2199810493/5000000000 : ℝ), (-290646783/1250000000 : ℝ), (366129559/625000000 : ℝ)] ![(34648267512607/100000000000000 : ℝ), (7605392976341/50000000000000 : ℝ), (5014094651733/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2199810493/5000000000 : ℝ)|^71 ≤ (34648267512607/100000000000000 : ℝ)^55
        have hw : |(2199810493/5000000000 : ℝ)|=(2199810493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-290646783/1250000000 : ℝ)|^71 ≤ (7605392976341/50000000000000 : ℝ)^55
        have hw : |(-290646783/1250000000 : ℝ)|=(290646783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(366129559/625000000 : ℝ)|^71 ≤ (5014094651733/10000000000000 : ℝ)^55
        have hw : |(366129559/625000000 : ℝ)|=(366129559/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s4_s4_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1304190053/2500000000 : ℝ)*x 0 + (2909808457/5000000000 : ℝ)*x 1 + (-322606501/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1304190053/2500000000 : ℝ)^71 ≤ (21585406144291/50000000000000 : ℝ)^55 := by
    have hnat : (1304190053 : ℕ)^71*50000000000000^55 ≤ 21585406144291^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304190053 2500000000 21585406144291 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2909808457/5000000000 : ℝ)^71 ≤ (49716441988271/100000000000000 : ℝ)^55 := by
    have hnat : (2909808457 : ℕ)^71*100000000000000^55 ≤ 49716441988271^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2909808457 5000000000 49716441988271 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (322606501/2500000000 : ℝ)^71 ≤ (7112745711709/100000000000000 : ℝ)^55 := by
    have hnat : (322606501 : ℕ)^71*100000000000000^55 ≤ 7112745711709^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322606501 2500000000 7112745711709 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1304190053/2500000000 : ℝ), (2909808457/5000000000 : ℝ), (-322606501/2500000000 : ℝ)] ![(21585406144291/50000000000000 : ℝ), (49716441988271/100000000000000 : ℝ), (7112745711709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1304190053/2500000000 : ℝ)|^71 ≤ (21585406144291/50000000000000 : ℝ)^55
        have hw : |(1304190053/2500000000 : ℝ)|=(1304190053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2909808457/5000000000 : ℝ)|^71 ≤ (49716441988271/100000000000000 : ℝ)^55
        have hw : |(2909808457/5000000000 : ℝ)|=(2909808457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-322606501/2500000000 : ℝ)|^71 ≤ (7112745711709/100000000000000 : ℝ)^55
        have hw : |(-322606501/2500000000 : ℝ)|=(322606501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s4_s4_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6490134449/10000000000 : ℝ)*x 0 + (1425300447/5000000000 : ℝ)*x 1 + (3201070851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6490134449/10000000000 : ℝ)^71 ≤ (28615846053401/50000000000000 : ℝ)^55 := by
    have hnat : (6490134449 : ℕ)^71*50000000000000^55 ≤ 28615846053401^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6490134449 10000000000 28615846053401 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1425300447/5000000000 : ℝ)^71 ≤ (9893329415989/50000000000000 : ℝ)^55 := by
    have hnat : (1425300447 : ℕ)^71*50000000000000^55 ≤ 9893329415989^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1425300447 5000000000 9893329415989 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3201070851/10000000000 : ℝ)^71 ≤ (1436353065651/6250000000000 : ℝ)^55 := by
    have hnat : (3201070851 : ℕ)^71*6250000000000^55 ≤ 1436353065651^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3201070851 10000000000 1436353065651 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6490134449/10000000000 : ℝ), (1425300447/5000000000 : ℝ), (3201070851/10000000000 : ℝ)] ![(28615846053401/50000000000000 : ℝ), (9893329415989/50000000000000 : ℝ), (1436353065651/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6490134449/10000000000 : ℝ)|^71 ≤ (28615846053401/50000000000000 : ℝ)^55
        have hw : |(6490134449/10000000000 : ℝ)|=(6490134449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1425300447/5000000000 : ℝ)|^71 ≤ (9893329415989/50000000000000 : ℝ)^55
        have hw : |(1425300447/5000000000 : ℝ)|=(1425300447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3201070851/10000000000 : ℝ)|^71 ≤ (1436353065651/6250000000000 : ℝ)^55
        have hw : |(3201070851/10000000000 : ℝ)|=(3201070851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s4_s4_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-492375923/2500000000 : ℝ)*x 0 + (4822040963/10000000000 : ℝ)*x 1 + (5729239501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (492375923/2500000000 : ℝ)^71 ≤ (12276618981377/100000000000000 : ℝ)^55 := by
    have hnat : (492375923 : ℕ)^71*100000000000000^55 ≤ 12276618981377^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492375923 2500000000 12276618981377 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4822040963/10000000000 : ℝ)^71 ≤ (2437585739311/6250000000000 : ℝ)^55 := by
    have hnat : (4822040963 : ℕ)^71*6250000000000^55 ≤ 2437585739311^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4822040963 10000000000 2437585739311 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5729239501/10000000000 : ℝ)^71 ≤ (24361004587179/50000000000000 : ℝ)^55 := by
    have hnat : (5729239501 : ℕ)^71*50000000000000^55 ≤ 24361004587179^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5729239501 10000000000 24361004587179 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-492375923/2500000000 : ℝ), (4822040963/10000000000 : ℝ), (5729239501/10000000000 : ℝ)] ![(12276618981377/100000000000000 : ℝ), (2437585739311/6250000000000 : ℝ), (24361004587179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-492375923/2500000000 : ℝ)|^71 ≤ (12276618981377/100000000000000 : ℝ)^55
        have hw : |(-492375923/2500000000 : ℝ)|=(492375923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4822040963/10000000000 : ℝ)|^71 ≤ (2437585739311/6250000000000 : ℝ)^55
        have hw : |(4822040963/10000000000 : ℝ)|=(4822040963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5729239501/10000000000 : ℝ)|^71 ≤ (24361004587179/50000000000000 : ℝ)^55
        have hw : |(5729239501/10000000000 : ℝ)|=(5729239501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s4_s4_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (647182227/1250000000 : ℝ)*x 0 + (-1007722819/5000000000 : ℝ)*x 1 + (1337537093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (647182227/1250000000 : ℝ)^71 ≤ (42751413661647/100000000000000 : ℝ)^55 := by
    have hnat : (647182227 : ℕ)^71*100000000000000^55 ≤ 42751413661647^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647182227 1250000000 42751413661647 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007722819/5000000000 : ℝ)^71 ≤ (12647547359223/100000000000000 : ℝ)^55 := by
    have hnat : (1007722819 : ℕ)^71*100000000000000^55 ≤ 12647547359223^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007722819 5000000000 12647547359223 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1337537093/2500000000 : ℝ)^71 ≤ (11150259742573/25000000000000 : ℝ)^55 := by
    have hnat : (1337537093 : ℕ)^71*25000000000000^55 ≤ 11150259742573^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337537093 2500000000 11150259742573 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(647182227/1250000000 : ℝ), (-1007722819/5000000000 : ℝ), (1337537093/2500000000 : ℝ)] ![(42751413661647/100000000000000 : ℝ), (12647547359223/100000000000000 : ℝ), (11150259742573/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(647182227/1250000000 : ℝ)|^71 ≤ (42751413661647/100000000000000 : ℝ)^55
        have hw : |(647182227/1250000000 : ℝ)|=(647182227/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1007722819/5000000000 : ℝ)|^71 ≤ (12647547359223/100000000000000 : ℝ)^55
        have hw : |(-1007722819/5000000000 : ℝ)|=(1007722819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1337537093/2500000000 : ℝ)|^71 ≤ (11150259742573/25000000000000 : ℝ)^55
        have hw : |(1337537093/2500000000 : ℝ)|=(1337537093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s4_s4_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (546940333/1250000000 : ℝ)*x 0 + (6393792491/10000000000 : ℝ)*x 1 + (-100583533/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546940333/1250000000 : ℝ)^71 ≤ (34403472746337/100000000000000 : ℝ)^55 := by
    have hnat : (546940333 : ℕ)^71*100000000000000^55 ≤ 34403472746337^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546940333 1250000000 34403472746337 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6393792491/10000000000 : ℝ)^71 ≤ (56137352877809/100000000000000 : ℝ)^55 := by
    have hnat : (6393792491 : ℕ)^71*100000000000000^55 ≤ 56137352877809^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6393792491 10000000000 56137352877809 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100583533/625000000 : ℝ)^71 ≤ (4729587177903/50000000000000 : ℝ)^55 := by
    have hnat : (100583533 : ℕ)^71*50000000000000^55 ≤ 4729587177903^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100583533 625000000 4729587177903 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546940333/1250000000 : ℝ), (6393792491/10000000000 : ℝ), (-100583533/625000000 : ℝ)] ![(34403472746337/100000000000000 : ℝ), (56137352877809/100000000000000 : ℝ), (4729587177903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546940333/1250000000 : ℝ)|^71 ≤ (34403472746337/100000000000000 : ℝ)^55
        have hw : |(546940333/1250000000 : ℝ)|=(546940333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6393792491/10000000000 : ℝ)|^71 ≤ (56137352877809/100000000000000 : ℝ)^55
        have hw : |(6393792491/10000000000 : ℝ)|=(6393792491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-100583533/625000000 : ℝ)|^71 ≤ (4729587177903/50000000000000 : ℝ)^55
        have hw : |(-100583533/625000000 : ℝ)|=(100583533/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s4_s4_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3297967977/5000000000 : ℝ)*x 0 + (2775312983/10000000000 : ℝ)*x 1 + (3143166333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3297967977/5000000000 : ℝ)^71 ≤ (3652433503913/6250000000000 : ℝ)^55 := by
    have hnat : (3297967977 : ℕ)^71*6250000000000^55 ≤ 3652433503913^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3297967977 5000000000 3652433503913 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2775312983/10000000000 : ℝ)^71 ≤ (3822930066603/20000000000000 : ℝ)^55 := by
    have hnat : (2775312983 : ℕ)^71*20000000000000^55 ≤ 3822930066603^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2775312983 10000000000 3822930066603 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3143166333/10000000000 : ℝ)^71 ≤ (22446413590729/100000000000000 : ℝ)^55 := by
    have hnat : (3143166333 : ℕ)^71*100000000000000^55 ≤ 22446413590729^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3143166333 10000000000 22446413590729 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3297967977/5000000000 : ℝ), (2775312983/10000000000 : ℝ), (3143166333/10000000000 : ℝ)] ![(3652433503913/6250000000000 : ℝ), (3822930066603/20000000000000 : ℝ), (22446413590729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3297967977/5000000000 : ℝ)|^71 ≤ (3652433503913/6250000000000 : ℝ)^55
        have hw : |(3297967977/5000000000 : ℝ)|=(3297967977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2775312983/10000000000 : ℝ)|^71 ≤ (3822930066603/20000000000000 : ℝ)^55
        have hw : |(2775312983/10000000000 : ℝ)|=(2775312983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3143166333/10000000000 : ℝ)|^71 ≤ (22446413590729/100000000000000 : ℝ)^55
        have hw : |(3143166333/10000000000 : ℝ)|=(3143166333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310061_s4 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((1453/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1453/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21111/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21111/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19293/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19293/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5027/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5027/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(493/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(493/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22907/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22907/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (1453/4000 : ℝ) ^ (35/8 : ℝ) ≤ (297741662607145441/25000000000000000000 : ℝ) := by
    have hpowers : (1453/4000 : ℝ)^35 ≤ (297741662607145441/25000000000000000000 : ℝ)^8 := by
      have hnat : (1453 : ℕ)^35*25000000000000000000^8 ≤ 297741662607145441^8*4000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1453 4000 297741662607145441 25000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1453/4000 : ℝ)) (X := (297741662607145441/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner0a : (25297741662607145441/25000000000000000000 : ℝ) ≤ (78336702470051/78125000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25297741662607145441/25000000000000000000 : ℝ)^8 ≤ (78336702470051/78125000000000 : ℝ)^35 := by
      have hnat : (25297741662607145441 : ℕ)^8*78125000000000^35 ≤ 78336702470051^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25297741662607145441 25000000000000000000 78336702470051 78125000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78336702470051/78125000000000 : ℝ)) (X := (25297741662607145441/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner0b : (12797741662607145441/12500000000000000000 : ℝ) ≤ (2010790181452323/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (12797741662607145441/12500000000000000000 : ℝ)^8 ≤ (2010790181452323/2000000000000000 : ℝ)^35 := by
      have hnat : (12797741662607145441 : ℕ)^8*2000000000000000^35 ≤ 2010790181452323^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12797741662607145441 12500000000000000000 2010790181452323 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2010790181452323/2000000000000000 : ℝ)) (X := (12797741662607145441/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(211702470051/28378906250000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(26852991095087/3632500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1453/4000 : ℝ)) (alpha := (211702470051/28378906250000 : ℝ)) (beta := (26852991095087/3632500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1453/4000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(211702470051/28378906250000 : ℝ)*((1 : ℝ)*pair X 0 1)+(26852991095087/3632500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (21111/50000 : ℝ) ^ (35/8 : ℝ) ≤ (143751463063985951/6250000000000000000 : ℝ) := by
    have hpowers : (21111/50000 : ℝ)^35 ≤ (143751463063985951/6250000000000000000 : ℝ)^8 := by
      have hnat : (21111 : ℕ)^35*6250000000000000000^8 ≤ 143751463063985951^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21111 50000 143751463063985951 6250000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21111/50000 : ℝ)) (X := (143751463063985951/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner1a : (6393751463063985951/6250000000000000000 : ℝ) ≤ (2010422361075097/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (6393751463063985951/6250000000000000000 : ℝ)^8 ≤ (2010422361075097/2000000000000000 : ℝ)^35 := by
      have hnat : (6393751463063985951 : ℕ)^8*2000000000000000^35 ≤ 2010422361075097^35*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6393751463063985951 6250000000000000000 2010422361075097 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2010422361075097/2000000000000000 : ℝ)) (X := (6393751463063985951/6250000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner1b : (3268751463063985951/3125000000000000000 : ℝ) ≤ (10103327466648863/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3268751463063985951/3125000000000000000 : ℝ)^8 ≤ (10103327466648863/10000000000000000 : ℝ)^35 := by
      have hnat : (3268751463063985951 : ℕ)^8*10000000000000000^35 ≤ 10103327466648863^35*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3268751463063985951 3125000000000000000 10103327466648863 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10103327466648863/10000000000000000 : ℝ)) (X := (3268751463063985951/3125000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(10422361075097/844440000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(8535943545563/703700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (21111/50000 : ℝ)) (alpha := (10422361075097/844440000000000 : ℝ)) (beta := (8535943545563/703700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (21111/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(10422361075097/844440000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(8535943545563/703700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (19293/50000 : ℝ) ^ (35/8 : ℝ) ≤ (1551065720770266833/100000000000000000000 : ℝ) := by
    have hpowers : (19293/50000 : ℝ)^35 ≤ (1551065720770266833/100000000000000000000 : ℝ)^8 := by
      have hnat : (19293 : ℕ)^35*100000000000000000000^8 ≤ 1551065720770266833^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19293 50000 1551065720770266833 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19293/50000 : ℝ)) (X := (1551065720770266833/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner2a : (101551065720770266833/100000000000000000000 : ℝ) ≤ (501762137455007/500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (101551065720770266833/100000000000000000000 : ℝ)^8 ≤ (501762137455007/500000000000000 : ℝ)^35 := by
      have hnat : (101551065720770266833 : ℕ)^8*500000000000000^35 ≤ 501762137455007^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101551065720770266833 100000000000000000000 501762137455007 500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (501762137455007/500000000000000 : ℝ)) (X := (101551065720770266833/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner2b : (51551065720770266833/50000000000000000000 : ℝ) ≤ (10070072661377311/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (51551065720770266833/50000000000000000000 : ℝ)^8 ≤ (10070072661377311/10000000000000000 : ℝ)^35 := by
      have hnat : (51551065720770266833 : ℕ)^8*10000000000000000^35 ≤ 10070072661377311^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51551065720770266833 50000000000000000000 10070072661377311 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10070072661377311/10000000000000000 : ℝ)) (X := (51551065720770266833/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(587379151669/64310000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(11609970759057/1286200000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (19293/50000 : ℝ)) (alpha := (587379151669/64310000000000 : ℝ)) (beta := (11609970759057/1286200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (19293/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(587379151669/64310000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(11609970759057/1286200000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-245551661/1000000000 : ℝ)*X 0 0+(4506697323/10000000000 : ℝ)*X 0 1+(1414445323/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((1169895583/2500000000 : ℝ)*X 1 0+(-1249772207/5000000000 : ℝ)*X 1 1+(1364856413/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((4702763317/10000000000 : ℝ)*X 2 0+(1209831657/2000000000 : ℝ)*X 2 1+(-1677205957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((292339273/500000000 : ℝ)*X 0 0+(3120013193/10000000000 : ℝ)*X 0 1+(926128801/2500000000 : ℝ)*X 0 2+(292339273/500000000 : ℝ)*X 1 0+(3120013193/10000000000 : ℝ)*X 1 1+(926128801/2500000000 : ℝ)*X 1 2+(292339273/500000000 : ℝ)*X 2 0+(3120013193/10000000000 : ℝ)*X 2 1+(926128801/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-494228401/2000000000 : ℝ)*X 0 0+(4242800459/10000000000 : ℝ)*X 0 1+(5889017407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((904587169/2000000000 : ℝ)*X 1 0+(-544783689/2500000000 : ℝ)*X 1 1+(5854734171/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((284134707/625000000 : ℝ)*X 2 0+(805624201/1250000000 : ℝ)*X 2 1+(-1293765181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((734074057/1250000000 : ℝ)*X 0 0+(224371889/625000000 : ℝ)*X 0 1+(802134393/2500000000 : ℝ)*X 0 2+(734074057/1250000000 : ℝ)*X 1 0+(224371889/625000000 : ℝ)*X 1 1+(802134393/2500000000 : ℝ)*X 1 2+(734074057/1250000000 : ℝ)*X 2 0+(224371889/625000000 : ℝ)*X 2 1+(802134393/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-1953421783/10000000000 : ℝ)*X 0 0+(4661426829/10000000000 : ℝ)*X 0 1+(5892354439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((2199810493/5000000000 : ℝ)*X 1 0+(-290646783/1250000000 : ℝ)*X 1 1+(366129559/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((1304190053/2500000000 : ℝ)*X 2 0+(2909808457/5000000000 : ℝ)*X 2 1+(-322606501/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((6490134449/10000000000 : ℝ)*X 0 0+(1425300447/5000000000 : ℝ)*X 0 1+(3201070851/10000000000 : ℝ)*X 0 2+(6490134449/10000000000 : ℝ)*X 1 0+(1425300447/5000000000 : ℝ)*X 1 1+(3201070851/10000000000 : ℝ)*X 1 2+(6490134449/10000000000 : ℝ)*X 2 0+(1425300447/5000000000 : ℝ)*X 2 1+(3201070851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-492375923/2500000000 : ℝ)*X 0 0+(4822040963/10000000000 : ℝ)*X 0 1+(5729239501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((647182227/1250000000 : ℝ)*X 1 0+(-1007722819/5000000000 : ℝ)*X 1 1+(1337537093/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((546940333/1250000000 : ℝ)*X 2 0+(6393792491/10000000000 : ℝ)*X 2 1+(-100583533/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((3297967977/5000000000 : ℝ)*X 0 0+(2775312983/10000000000 : ℝ)*X 0 1+(3143166333/10000000000 : ℝ)*X 0 2+(3297967977/5000000000 : ℝ)*X 1 0+(2775312983/10000000000 : ℝ)*X 1 1+(3143166333/10000000000 : ℝ)*X 1 2+(3297967977/5000000000 : ℝ)*X 2 0+(2775312983/10000000000 : ℝ)*X 2 1+(3143166333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((5027/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5027/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (77445572685268594564985433/4672121500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1289213/1000000000000 : ℝ)*(base50) + (869685959099/500000000000 : ℝ)*(base59) + (9517001939641/1000000000000 : ℝ)*(major_s4_0) + (9517001939641/1000000000000 : ℝ)*(major_s4_1) + (9517001939641/1000000000000 : ℝ)*(major_s4_2) + (4461991/31250000000 : ℝ)*(sp_s4_0) + (9717181/200000000000 : ℝ)*(sp_s4_1) + (54961131/500000000000 : ℝ)*(sp_s4_6) + (13151646859289/1000000000000 : ℝ)*(sp_s4_7) + (6575628327983/500000000000 : ℝ)*(sp_s4_8) + (13151569905261/1000000000000 : ℝ)*(sp_s4_9) + (5882098788647/1000000000000 : ℝ)*(sp_s4_13) + (484401131/1000000000000 : ℝ)*(sp_s4_15) + (219737741/1000000000000 : ℝ)*(sp_s4_23) + (5882208710909/1000000000000 : ℝ)*(f.failure) + (6575894821501/500000000000 : ℝ)*(f.sum) + (37668242774691779/1086118728000000000000000000000 : ℝ)*base63 + (342474781761557/1286200000000000000000000000 : ℝ)*base64 + (43164670091053/703700000000000000000000000 : ℝ)*base67 + (19438673814259/64310000000000000000000000 : ℝ)*base68 + (11042636786521258349/46721215000000000000000000000000 : ℝ)*base70 + (1480006481162733/3632500000000000000000000000 : ℝ)*base72 + (52393292147/270220800000000000000000 : ℝ)*base74 + (714542166092901/1816250000000000000000000000 : ℝ)*base76 + (249743270265816849/6390475625000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (163/100000000000000000 : ℝ)*base86 + (163/100000000000000000 : ℝ)*base88 + (163/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(493/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(493/2000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (57353116502060218225384397059/8219429748875000000000000000000000 : ℝ) := by norm_num
    linear_combination (163572077373/125000000000 : ℝ)*(base59) + (9114688225139/1000000000000 : ℝ)*(major_s4_0) + (9114688225139/1000000000000 : ℝ)*(major_s4_1) + (9114688225139/1000000000000 : ℝ)*(major_s4_2) + (1554261/31250000000 : ℝ)*(sp_s4_1) + (21225493/200000000000 : ℝ)*(sp_s4_2) + (35756819/100000000000 : ℝ)*(sp_s4_6) + (81304827/500000000000 : ℝ)*(sp_s4_7) + (2147151/62500000000 : ℝ)*(sp_s4_8) + (2519132466899/200000000000 : ℝ)*(sp_s4_14) + (12595740853381/1000000000000 : ℝ)*(sp_s4_15) + (3148929704171/250000000000 : ℝ)*(sp_s4_16) + (5630902849351/1000000000000 : ℝ)*(sp_s4_20) + (228876267/100000000000 : ℝ)*(sp_s4_27) + (5633549180211/1000000000000 : ℝ)*(f.failure) + (12595824944149/1000000000000 : ℝ)*(f.sum) + (202784407839709241/5430593640000000000000000000000 : ℝ)*base63 + (69148290524777/1286200000000000000000000000 : ℝ)*base65 + (65998678648277/703700000000000000000000000 : ℝ)*base67 + (1365950877323/16077500000000000000000000 : ℝ)*base69 + (976780310852283929/46721215000000000000000000000000 : ℝ)*base71 + (411985964198343/3632500000000000000000000000 : ℝ)*base73 + (15301803354527/168888000000000000000000000 : ℝ)*base75 + (151158973589321/1816250000000000000000000000 : ℝ)*base77 + (688023462636618233/12780951250000000000000000000000 : ℝ)*base79 + (21677/100000000000000000 : ℝ)*base86 + (21677/100000000000000000 : ℝ)*base88 + (21677/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22907/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22907/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (393875190291512613577132640867/82194297488750000000000000000000000 : ℝ) := by norm_num
    linear_combination (417873394341/1000000000000 : ℝ)*(base40) + (2262979/1000000000000 : ℝ)*(base50) + (335592470437/250000000000 : ℝ)*(base59) + (4384848469523/500000000000 : ℝ)*(major_s4_0) + (4384848469523/500000000000 : ℝ)*(major_s4_1) + (4384848469523/500000000000 : ℝ)*(major_s4_2) + (128787797/500000000000 : ℝ)*(sp_s4_0) + (113532237/500000000000 : ℝ)*(sp_s4_1) + (4852621/125000000000 : ℝ)*(sp_s4_2) + (44416359/1000000000000 : ℝ)*(sp_s4_9) + (2423763113913/200000000000 : ℝ)*(sp_s4_21) + (2423769216137/200000000000 : ℝ)*(sp_s4_22) + (1514873738479/125000000000 : ℝ)*(sp_s4_23) + (542031913559/100000000000 : ℝ)*(sp_s4_27) + (542031913559/100000000000 : ℝ)*(f.failure) + (12119073145159/1000000000000 : ℝ)*(f.sum) + (342990746731970609/2715296820000000000000000000000 : ℝ)*base63 + (556871618764819/643100000000000000000000000 : ℝ)*base65 + (110075960882297/175925000000000000000000000 : ℝ)*base67 + (21713192499373/32155000000000000000000000 : ℝ)*base69 + (14717187735380261553/23360607500000000000000000000000 : ℝ)*base71 + (581929432019251/1816250000000000000000000000 : ℝ)*base73 + (268950775392547/422220000000000000000000000 : ℝ)*base75 + (740879444600447/908125000000000000000000000 : ℝ)*base77 + (1794016202245775913/12780951250000000000000000000000 : ℝ)*base78 + (8713/10000000000000000 : ℝ)*base86 + (8713/10000000000000000 : ℝ)*base88 + (8713/10000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((1453/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1453/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21111/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21111/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19293/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19293/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5027/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5027/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(493/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(493/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22907/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22907/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310061_s4 p hpa hpb X hX hprev3

#print axioms solution

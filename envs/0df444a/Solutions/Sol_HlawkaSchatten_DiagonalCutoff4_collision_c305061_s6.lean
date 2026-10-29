-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305061_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:31:39.126827+00:00
-- url     : https://prove2.me/submissions/5add23a3-2fbd-49f7-972c-7b662a0ec59d

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
theorem collision_support_c305061_s6_s6_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-11981773/50000000 : ℝ)*x 0 + (4564977311/10000000000 : ℝ)*x 1 + (181559749/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11981773/50000000 : ℝ)^67 ≤ (15307365159979/100000000000000 : ℝ)^51 := by
    have hnat : (11981773 : ℕ)^67*100000000000000^51 ≤ 15307365159979^51*50000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11981773 50000000 15307365159979 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4564977311/10000000000 : ℝ)^67 ≤ (35694050889911/100000000000000 : ℝ)^51 := by
    have hnat : (4564977311 : ℕ)^67*100000000000000^51 ≤ 35694050889911^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4564977311 10000000000 35694050889911 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181559749/312500000 : ℝ)^67 ≤ (48998583939919/100000000000000 : ℝ)^51 := by
    have hnat : (181559749 : ℕ)^67*100000000000000^51 ≤ 48998583939919^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181559749 312500000 48998583939919 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11981773/50000000 : ℝ), (4564977311/10000000000 : ℝ), (181559749/312500000 : ℝ)] ![(15307365159979/100000000000000 : ℝ), (35694050889911/100000000000000 : ℝ), (48998583939919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11981773/50000000 : ℝ)|^67 ≤ (15307365159979/100000000000000 : ℝ)^51
        have hw : |(-11981773/50000000 : ℝ)|=(11981773/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4564977311/10000000000 : ℝ)|^67 ≤ (35694050889911/100000000000000 : ℝ)^51
        have hw : |(4564977311/10000000000 : ℝ)|=(4564977311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181559749/312500000 : ℝ)|^67 ≤ (48998583939919/100000000000000 : ℝ)^51
        have hw : |(181559749/312500000 : ℝ)|=(181559749/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305061_s6_s6_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2364310311/5000000000 : ℝ)*x 0 + (-155774581/625000000 : ℝ)*x 1 + (2791372833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2364310311/5000000000 : ℝ)^67 ≤ (747687948021/2000000000000 : ℝ)^51 := by
    have hnat : (2364310311 : ℕ)^67*2000000000000^51 ≤ 747687948021^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364310311 5000000000 747687948021 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155774581/625000000 : ℝ)^67 ≤ (2014790184691/12500000000000 : ℝ)^51 := by
    have hnat : (155774581 : ℕ)^67*12500000000000^51 ≤ 2014790184691^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155774581 625000000 2014790184691 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2791372833/5000000000 : ℝ)^67 ≤ (23248640551513/50000000000000 : ℝ)^51 := by
    have hnat : (2791372833 : ℕ)^67*50000000000000^51 ≤ 23248640551513^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2791372833 5000000000 23248640551513 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2364310311/5000000000 : ℝ), (-155774581/625000000 : ℝ), (2791372833/5000000000 : ℝ)] ![(747687948021/2000000000000 : ℝ), (2014790184691/12500000000000 : ℝ), (23248640551513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2364310311/5000000000 : ℝ)|^67 ≤ (747687948021/2000000000000 : ℝ)^51
        have hw : |(2364310311/5000000000 : ℝ)|=(2364310311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-155774581/625000000 : ℝ)|^67 ≤ (2014790184691/12500000000000 : ℝ)^51
        have hw : |(-155774581/625000000 : ℝ)|=(155774581/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2791372833/5000000000 : ℝ)|^67 ≤ (23248640551513/50000000000000 : ℝ)^51
        have hw : |(2791372833/5000000000 : ℝ)|=(2791372833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305061_s6_s6_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2398628853/5000000000 : ℝ)*x 0 + (3093215341/5000000000 : ℝ)*x 1 + (-311446757/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2398628853/5000000000 : ℝ)^67 ≤ (9524725006771/25000000000000 : ℝ)^51 := by
    have hnat : (2398628853 : ℕ)^67*25000000000000^51 ≤ 9524725006771^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2398628853 5000000000 9524725006771 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3093215341/5000000000 : ℝ)^67 ≤ (53212003411267/100000000000000 : ℝ)^51 := by
    have hnat : (3093215341 : ℕ)^67*100000000000000^51 ≤ 53212003411267^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3093215341 5000000000 53212003411267 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (311446757/2000000000 : ℝ)^67 ≤ (1737819309531/20000000000000 : ℝ)^51 := by
    have hnat : (311446757 : ℕ)^67*20000000000000^51 ≤ 1737819309531^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311446757 2000000000 1737819309531 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2398628853/5000000000 : ℝ), (3093215341/5000000000 : ℝ), (-311446757/2000000000 : ℝ)] ![(9524725006771/25000000000000 : ℝ), (53212003411267/100000000000000 : ℝ), (1737819309531/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2398628853/5000000000 : ℝ)|^67 ≤ (9524725006771/25000000000000 : ℝ)^51
        have hw : |(2398628853/5000000000 : ℝ)|=(2398628853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3093215341/5000000000 : ℝ)|^67 ≤ (53212003411267/100000000000000 : ℝ)^51
        have hw : |(3093215341/5000000000 : ℝ)|=(3093215341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-311446757/2000000000 : ℝ)|^67 ≤ (1737819309531/20000000000000 : ℝ)^51
        have hw : |(-311446757/2000000000 : ℝ)|=(311446757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305061_s6_s6_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (590536387/1000000000 : ℝ)*x 0 + (3169579863/10000000000 : ℝ)*x 1 + (3778003073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (590536387/1000000000 : ℝ)^67 ≤ (50058854770029/100000000000000 : ℝ)^51 := by
    have hnat : (590536387 : ℕ)^67*100000000000000^51 ≤ 50058854770029^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590536387 1000000000 50058854770029 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3169579863/10000000000 : ℝ)^67 ≤ (2210310121719/10000000000000 : ℝ)^51 := by
    have hnat : (3169579863 : ℕ)^67*10000000000000^51 ≤ 2210310121719^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169579863 10000000000 2210310121719 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3778003073/10000000000 : ℝ)^67 ≤ (27838043993011/100000000000000 : ℝ)^51 := by
    have hnat : (3778003073 : ℕ)^67*100000000000000^51 ≤ 27838043993011^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3778003073 10000000000 27838043993011 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(590536387/1000000000 : ℝ), (3169579863/10000000000 : ℝ), (3778003073/10000000000 : ℝ)] ![(50058854770029/100000000000000 : ℝ), (2210310121719/10000000000000 : ℝ), (27838043993011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(590536387/1000000000 : ℝ)|^67 ≤ (50058854770029/100000000000000 : ℝ)^51
        have hw : |(590536387/1000000000 : ℝ)|=(590536387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3169579863/10000000000 : ℝ)|^67 ≤ (2210310121719/10000000000000 : ℝ)^51
        have hw : |(3169579863/10000000000 : ℝ)|=(3169579863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3778003073/10000000000 : ℝ)|^67 ≤ (27838043993011/100000000000000 : ℝ)^51
        have hw : |(3778003073/10000000000 : ℝ)|=(3778003073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305061_s6_s6_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-597199969/2500000000 : ℝ)*x 0 + (1993281493/5000000000 : ℝ)*x 1 + (395853469/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (597199969/2500000000 : ℝ)^67 ≤ (762199948381/5000000000000 : ℝ)^51 := by
    have hnat : (597199969 : ℕ)^67*5000000000000^51 ≤ 762199948381^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597199969 2500000000 762199948381 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1993281493/5000000000 : ℝ)^67 ≤ (29874196935751/100000000000000 : ℝ)^51 := by
    have hnat : (1993281493 : ℕ)^67*100000000000000^51 ≤ 29874196935751^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993281493 5000000000 29874196935751 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (395853469/625000000 : ℝ)^67 ≤ (54881804079149/100000000000000 : ℝ)^51 := by
    have hnat : (395853469 : ℕ)^67*100000000000000^51 ≤ 54881804079149^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395853469 625000000 54881804079149 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-597199969/2500000000 : ℝ), (1993281493/5000000000 : ℝ), (395853469/625000000 : ℝ)] ![(762199948381/5000000000000 : ℝ), (29874196935751/100000000000000 : ℝ), (54881804079149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-597199969/2500000000 : ℝ)|^67 ≤ (762199948381/5000000000000 : ℝ)^51
        have hw : |(-597199969/2500000000 : ℝ)|=(597199969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1993281493/5000000000 : ℝ)|^67 ≤ (29874196935751/100000000000000 : ℝ)^51
        have hw : |(1993281493/5000000000 : ℝ)|=(1993281493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(395853469/625000000 : ℝ)|^67 ≤ (54881804079149/100000000000000 : ℝ)^51
        have hw : |(395853469/625000000 : ℝ)|=(395853469/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305061_s6_s6_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4405139157/10000000000 : ℝ)*x 0 + (-1980759899/10000000000 : ℝ)*x 1 + (6257807493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4405139157/10000000000 : ℝ)^67 ≤ (8515314683449/25000000000000 : ℝ)^51 := by
    have hnat : (4405139157 : ℕ)^67*25000000000000^51 ≤ 8515314683449^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4405139157 10000000000 8515314683449 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1980759899/10000000000 : ℝ)^67 ≤ (11918732089737/100000000000000 : ℝ)^51 := by
    have hnat : (1980759899 : ℕ)^67*100000000000000^51 ≤ 11918732089737^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980759899 10000000000 11918732089737 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6257807493/10000000000 : ℝ)^67 ≤ (54020009163401/100000000000000 : ℝ)^51 := by
    have hnat : (6257807493 : ℕ)^67*100000000000000^51 ≤ 54020009163401^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6257807493 10000000000 54020009163401 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4405139157/10000000000 : ℝ), (-1980759899/10000000000 : ℝ), (6257807493/10000000000 : ℝ)] ![(8515314683449/25000000000000 : ℝ), (11918732089737/100000000000000 : ℝ), (54020009163401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4405139157/10000000000 : ℝ)|^67 ≤ (8515314683449/25000000000000 : ℝ)^51
        have hw : |(4405139157/10000000000 : ℝ)|=(4405139157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1980759899/10000000000 : ℝ)|^67 ≤ (11918732089737/100000000000000 : ℝ)^51
        have hw : |(-1980759899/10000000000 : ℝ)|=(1980759899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6257807493/10000000000 : ℝ)|^67 ≤ (54020009163401/100000000000000 : ℝ)^51
        have hw : |(6257807493/10000000000 : ℝ)|=(6257807493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305061_s6_s6_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4474161243/10000000000 : ℝ)*x 0 + (6853137521/10000000000 : ℝ)*x 1 + (-922204671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4474161243/10000000000 : ℝ)^67 ≤ (543189032857/1562500000000 : ℝ)^51 := by
    have hnat : (4474161243 : ℕ)^67*1562500000000^51 ≤ 543189032857^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474161243 10000000000 543189032857 1562500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6853137521/10000000000 : ℝ)^67 ≤ (30435033732161/50000000000000 : ℝ)^51 := by
    have hnat : (6853137521 : ℕ)^67*50000000000000^51 ≤ 30435033732161^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6853137521 10000000000 30435033732161 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (922204671/10000000000 : ℝ)^67 ≤ (1091458604717/25000000000000 : ℝ)^51 := by
    have hnat : (922204671 : ℕ)^67*25000000000000^51 ≤ 1091458604717^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922204671 10000000000 1091458604717 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4474161243/10000000000 : ℝ), (6853137521/10000000000 : ℝ), (-922204671/10000000000 : ℝ)] ![(543189032857/1562500000000 : ℝ), (30435033732161/50000000000000 : ℝ), (1091458604717/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4474161243/10000000000 : ℝ)|^67 ≤ (543189032857/1562500000000 : ℝ)^51
        have hw : |(4474161243/10000000000 : ℝ)|=(4474161243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6853137521/10000000000 : ℝ)|^67 ≤ (30435033732161/50000000000000 : ℝ)^51
        have hw : |(6853137521/10000000000 : ℝ)|=(6853137521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-922204671/10000000000 : ℝ)|^67 ≤ (1091458604717/25000000000000 : ℝ)^51
        have hw : |(-922204671/10000000000 : ℝ)|=(922204671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305061_s6_s6_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (586215253/1000000000 : ℝ)*x 0 + (4193912433/10000000000 : ℝ)*x 1 + (2766904419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (586215253/1000000000 : ℝ)^67 ≤ (24789097931247/50000000000000 : ℝ)^51 := by
    have hnat : (586215253 : ℕ)^67*50000000000000^51 ≤ 24789097931247^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586215253 1000000000 24789097931247 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4193912433/10000000000 : ℝ)^67 ≤ (31931949337603/100000000000000 : ℝ)^51 := by
    have hnat : (4193912433 : ℕ)^67*100000000000000^51 ≤ 31931949337603^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193912433 10000000000 31931949337603 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2766904419/10000000000 : ℝ)^67 ≤ (18489854785121/100000000000000 : ℝ)^51 := by
    have hnat : (2766904419 : ℕ)^67*100000000000000^51 ≤ 18489854785121^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2766904419 10000000000 18489854785121 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(586215253/1000000000 : ℝ), (4193912433/10000000000 : ℝ), (2766904419/10000000000 : ℝ)] ![(24789097931247/50000000000000 : ℝ), (31931949337603/100000000000000 : ℝ), (18489854785121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(586215253/1000000000 : ℝ)|^67 ≤ (24789097931247/50000000000000 : ℝ)^51
        have hw : |(586215253/1000000000 : ℝ)|=(586215253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4193912433/10000000000 : ℝ)|^67 ≤ (31931949337603/100000000000000 : ℝ)^51
        have hw : |(4193912433/10000000000 : ℝ)|=(4193912433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2766904419/10000000000 : ℝ)|^67 ≤ (18489854785121/100000000000000 : ℝ)^51
        have hw : |(2766904419/10000000000 : ℝ)|=(2766904419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305061_s6_s6_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-791498287/5000000000 : ℝ)*x 0 + (4620427913/10000000000 : ℝ)*x 1 + (1266292371/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (791498287/5000000000 : ℝ)^67 ≤ (1775687074197/20000000000000 : ℝ)^51 := by
    have hnat : (791498287 : ℕ)^67*20000000000000^51 ≤ 1775687074197^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791498287 5000000000 1775687074197 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4620427913/10000000000 : ℝ)^67 ≤ (36264730746763/100000000000000 : ℝ)^51 := by
    have hnat : (4620427913 : ℕ)^67*100000000000000^51 ≤ 36264730746763^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4620427913 10000000000 36264730746763 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1266292371/2000000000 : ℝ)^67 ≤ (54856833874081/100000000000000 : ℝ)^51 := by
    have hnat : (1266292371 : ℕ)^67*100000000000000^51 ≤ 54856833874081^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266292371 2000000000 54856833874081 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-791498287/5000000000 : ℝ), (4620427913/10000000000 : ℝ), (1266292371/2000000000 : ℝ)] ![(1775687074197/20000000000000 : ℝ), (36264730746763/100000000000000 : ℝ), (54856833874081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-791498287/5000000000 : ℝ)|^67 ≤ (1775687074197/20000000000000 : ℝ)^51
        have hw : |(-791498287/5000000000 : ℝ)|=(791498287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4620427913/10000000000 : ℝ)|^67 ≤ (36264730746763/100000000000000 : ℝ)^51
        have hw : |(4620427913/10000000000 : ℝ)|=(4620427913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1266292371/2000000000 : ℝ)|^67 ≤ (54856833874081/100000000000000 : ℝ)^51
        have hw : |(1266292371/2000000000 : ℝ)|=(1266292371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305061_s6_s6_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4251450993/10000000000 : ℝ)*x 0 + (-108865639/500000000 : ℝ)*x 1 + (1563903601/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251450993/10000000000 : ℝ)^67 ≤ (260069730793/800000000000 : ℝ)^51 := by
    have hnat : (4251450993 : ℕ)^67*800000000000^51 ≤ 260069730793^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251450993 10000000000 260069730793 800000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108865639/500000000 : ℝ)^67 ≤ (13496144110847/100000000000000 : ℝ)^51 := by
    have hnat : (108865639 : ℕ)^67*100000000000000^51 ≤ 13496144110847^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108865639 500000000 13496144110847 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1563903601/2500000000 : ℝ)^67 ≤ (5399513952559/10000000000000 : ℝ)^51 := by
    have hnat : (1563903601 : ℕ)^67*10000000000000^51 ≤ 5399513952559^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1563903601 2500000000 5399513952559 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251450993/10000000000 : ℝ), (-108865639/500000000 : ℝ), (1563903601/2500000000 : ℝ)] ![(260069730793/800000000000 : ℝ), (13496144110847/100000000000000 : ℝ), (5399513952559/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251450993/10000000000 : ℝ)|^67 ≤ (260069730793/800000000000 : ℝ)^51
        have hw : |(4251450993/10000000000 : ℝ)|=(4251450993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-108865639/500000000 : ℝ)|^67 ≤ (13496144110847/100000000000000 : ℝ)^51
        have hw : |(-108865639/500000000 : ℝ)|=(108865639/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1563903601/2500000000 : ℝ)|^67 ≤ (5399513952559/10000000000000 : ℝ)^51
        have hw : |(1563903601/2500000000 : ℝ)|=(1563903601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305061_s6_s6_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2825474263/5000000000 : ℝ)*x 0 + (5753593473/10000000000 : ℝ)*x 1 + (-924398231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2825474263/5000000000 : ℝ)^67 ≤ (23622480825863/50000000000000 : ℝ)^51 := by
    have hnat : (2825474263 : ℕ)^67*50000000000000^51 ≤ 23622480825863^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2825474263 5000000000 23622480825863 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5753593473/10000000000 : ℝ)^67 ≤ (9675111263527/20000000000000 : ℝ)^51 := by
    have hnat : (5753593473 : ℕ)^67*20000000000000^51 ≤ 9675111263527^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5753593473 10000000000 9675111263527 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (924398231/10000000000 : ℝ)^67 ≤ (2189741005121/50000000000000 : ℝ)^51 := by
    have hnat : (924398231 : ℕ)^67*50000000000000^51 ≤ 2189741005121^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924398231 10000000000 2189741005121 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2825474263/5000000000 : ℝ), (5753593473/10000000000 : ℝ), (-924398231/10000000000 : ℝ)] ![(23622480825863/50000000000000 : ℝ), (9675111263527/20000000000000 : ℝ), (2189741005121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2825474263/5000000000 : ℝ)|^67 ≤ (23622480825863/50000000000000 : ℝ)^51
        have hw : |(2825474263/5000000000 : ℝ)|=(2825474263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5753593473/10000000000 : ℝ)|^67 ≤ (9675111263527/20000000000000 : ℝ)^51
        have hw : |(5753593473/10000000000 : ℝ)|=(5753593473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-924398231/10000000000 : ℝ)|^67 ≤ (2189741005121/50000000000000 : ℝ)^51
        have hw : |(-924398231/10000000000 : ℝ)|=(924398231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305061_s6_s6_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6942222569/10000000000 : ℝ)*x 0 + (2887846583/10000000000 : ℝ)*x 1 + (138571011/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6942222569/10000000000 : ℝ)^67 ≤ (12382335822983/20000000000000 : ℝ)^51 := by
    have hnat : (6942222569 : ℕ)^67*20000000000000^51 ≤ 12382335822983^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6942222569 10000000000 12382335822983 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2887846583/10000000000 : ℝ)^67 ≤ (391176236357/2000000000000 : ℝ)^51 := by
    have hnat : (2887846583 : ℕ)^67*2000000000000^51 ≤ 391176236357^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2887846583 10000000000 391176236357 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138571011/500000000 : ℝ)^67 ≤ (9264754524593/50000000000000 : ℝ)^51 := by
    have hnat : (138571011 : ℕ)^67*50000000000000^51 ≤ 9264754524593^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138571011 500000000 9264754524593 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6942222569/10000000000 : ℝ), (2887846583/10000000000 : ℝ), (138571011/500000000 : ℝ)] ![(12382335822983/20000000000000 : ℝ), (391176236357/2000000000000 : ℝ), (9264754524593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6942222569/10000000000 : ℝ)|^67 ≤ (12382335822983/20000000000000 : ℝ)^51
        have hw : |(6942222569/10000000000 : ℝ)|=(6942222569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2887846583/10000000000 : ℝ)|^67 ≤ (391176236357/2000000000000 : ℝ)^51
        have hw : |(2887846583/10000000000 : ℝ)|=(2887846583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(138571011/500000000 : ℝ)|^67 ≤ (9264754524593/50000000000000 : ℝ)^51
        have hw : |(138571011/500000000 : ℝ)|=(138571011/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305061_s6_s6_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1563018003/10000000000 : ℝ)*x 0 + (5143870253/10000000000 : ℝ)*x 1 + (1171255259/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1563018003/10000000000 : ℝ)^67 ≤ (8731521644249/100000000000000 : ℝ)^51 := by
    have hnat : (1563018003 : ℕ)^67*100000000000000^51 ≤ 8731521644249^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1563018003 10000000000 8731521644249 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5143870253/10000000000 : ℝ)^67 ≤ (20877780408707/50000000000000 : ℝ)^51 := by
    have hnat : (5143870253 : ℕ)^67*50000000000000^51 ≤ 20877780408707^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143870253 10000000000 20877780408707 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1171255259/2000000000 : ℝ)^67 ≤ (12378229381547/25000000000000 : ℝ)^51 := by
    have hnat : (1171255259 : ℕ)^67*25000000000000^51 ≤ 12378229381547^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171255259 2000000000 12378229381547 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1563018003/10000000000 : ℝ), (5143870253/10000000000 : ℝ), (1171255259/2000000000 : ℝ)] ![(8731521644249/100000000000000 : ℝ), (20877780408707/50000000000000 : ℝ), (12378229381547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1563018003/10000000000 : ℝ)|^67 ≤ (8731521644249/100000000000000 : ℝ)^51
        have hw : |(-1563018003/10000000000 : ℝ)|=(1563018003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5143870253/10000000000 : ℝ)|^67 ≤ (20877780408707/50000000000000 : ℝ)^51
        have hw : |(5143870253/10000000000 : ℝ)|=(5143870253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1171255259/2000000000 : ℝ)|^67 ≤ (12378229381547/25000000000000 : ℝ)^51
        have hw : |(1171255259/2000000000 : ℝ)|=(1171255259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305061_s6_s6_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2800952649/5000000000 : ℝ)*x 0 + (-415544681/2500000000 : ℝ)*x 1 + (5336945359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2800952649/5000000000 : ℝ)^67 ≤ (46707032595021/100000000000000 : ℝ)^51 := by
    have hnat : (2800952649 : ℕ)^67*100000000000000^51 ≤ 46707032595021^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2800952649 5000000000 46707032595021 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415544681/2500000000 : ℝ)^67 ≤ (1893278268779/20000000000000 : ℝ)^51 := by
    have hnat : (415544681 : ℕ)^67*20000000000000^51 ≤ 1893278268779^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415544681 2500000000 1893278268779 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5336945359/10000000000 : ℝ)^67 ≤ (43826576049851/100000000000000 : ℝ)^51 := by
    have hnat : (5336945359 : ℕ)^67*100000000000000^51 ≤ 43826576049851^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5336945359 10000000000 43826576049851 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2800952649/5000000000 : ℝ), (-415544681/2500000000 : ℝ), (5336945359/10000000000 : ℝ)] ![(46707032595021/100000000000000 : ℝ), (1893278268779/20000000000000 : ℝ), (43826576049851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2800952649/5000000000 : ℝ)|^67 ≤ (46707032595021/100000000000000 : ℝ)^51
        have hw : |(2800952649/5000000000 : ℝ)|=(2800952649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415544681/2500000000 : ℝ)|^67 ≤ (1893278268779/20000000000000 : ℝ)^51
        have hw : |(-415544681/2500000000 : ℝ)|=(415544681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5336945359/10000000000 : ℝ)|^67 ≤ (43826576049851/100000000000000 : ℝ)^51
        have hw : |(5336945359/10000000000 : ℝ)|=(5336945359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305061_s6_s6_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4233064479/10000000000 : ℝ)*x 0 + (6792540639/10000000000 : ℝ)*x 1 + (-696942551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4233064479/10000000000 : ℝ)^67 ≤ (16162070934843/50000000000000 : ℝ)^51 := by
    have hnat : (4233064479 : ℕ)^67*50000000000000^51 ≤ 16162070934843^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233064479 10000000000 16162070934843 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6792540639/10000000000 : ℝ)^67 ≤ (60163969066603/100000000000000 : ℝ)^51 := by
    have hnat : (6792540639 : ℕ)^67*100000000000000^51 ≤ 60163969066603^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6792540639 10000000000 60163969066603 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (696942551/5000000000 : ℝ)^67 ≤ (469493065807/6250000000000 : ℝ)^51 := by
    have hnat : (696942551 : ℕ)^67*6250000000000^51 ≤ 469493065807^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696942551 5000000000 469493065807 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4233064479/10000000000 : ℝ), (6792540639/10000000000 : ℝ), (-696942551/5000000000 : ℝ)] ![(16162070934843/50000000000000 : ℝ), (60163969066603/100000000000000 : ℝ), (469493065807/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4233064479/10000000000 : ℝ)|^67 ≤ (16162070934843/50000000000000 : ℝ)^51
        have hw : |(4233064479/10000000000 : ℝ)|=(4233064479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6792540639/10000000000 : ℝ)|^67 ≤ (60163969066603/100000000000000 : ℝ)^51
        have hw : |(6792540639/10000000000 : ℝ)|=(6792540639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-696942551/5000000000 : ℝ)|^67 ≤ (469493065807/6250000000000 : ℝ)^51
        have hw : |(-696942551/5000000000 : ℝ)|=(696942551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305061_s6_s6_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7122158059/10000000000 : ℝ)*x 0 + (518417481/2000000000 : ℝ)*x 1 + (2824949821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7122158059/10000000000 : ℝ)^67 ≤ (8003540094023/12500000000000 : ℝ)^51 := by
    have hnat : (7122158059 : ℕ)^67*12500000000000^51 ≤ 8003540094023^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7122158059 10000000000 8003540094023 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518417481/2000000000 : ℝ)^67 ≤ (678823048251/4000000000000 : ℝ)^51 := by
    have hnat : (518417481 : ℕ)^67*4000000000000^51 ≤ 678823048251^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518417481 2000000000 678823048251 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2824949821/10000000000 : ℝ)^67 ≤ (4750275754707/25000000000000 : ℝ)^51 := by
    have hnat : (2824949821 : ℕ)^67*25000000000000^51 ≤ 4750275754707^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2824949821 10000000000 4750275754707 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7122158059/10000000000 : ℝ), (518417481/2000000000 : ℝ), (2824949821/10000000000 : ℝ)] ![(8003540094023/12500000000000 : ℝ), (678823048251/4000000000000 : ℝ), (4750275754707/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7122158059/10000000000 : ℝ)|^67 ≤ (8003540094023/12500000000000 : ℝ)^51
        have hw : |(7122158059/10000000000 : ℝ)|=(7122158059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518417481/2000000000 : ℝ)|^67 ≤ (678823048251/4000000000000 : ℝ)^51
        have hw : |(518417481/2000000000 : ℝ)|=(518417481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2824949821/10000000000 : ℝ)|^67 ≤ (4750275754707/25000000000000 : ℝ)^51
        have hw : |(2824949821/10000000000 : ℝ)|=(2824949821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305061_s6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((48549/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48549/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3443/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3443/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(24941/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(24941/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14467/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14467/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16979/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16979/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(781/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(781/2500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s6_pow0 : (48549/100000 : ℝ) ^ (133/32 : ℝ) ≤ (4962343524103952171/100000000000000000000 : ℝ) := by
    have hpowers : (48549/100000 : ℝ)^133 ≤ (4962343524103952171/100000000000000000000 : ℝ)^32 := by
      have hnat : (48549 : ℕ)^133*100000000000000000000^32 ≤ 4962343524103952171^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48549 100000 4962343524103952171 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48549/100000 : ℝ)) (X := (4962343524103952171/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s6_corner0a : (104962343524103952171/100000000000000000000 : ℝ) ≤ (2529302101815821/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (104962343524103952171/100000000000000000000 : ℝ)^32 ≤ (2529302101815821/2500000000000000 : ℝ)^133 := by
      have hnat : (104962343524103952171 : ℕ)^32*2500000000000000^133 ≤ 2529302101815821^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104962343524103952171 100000000000000000000 2529302101815821 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2529302101815821/2500000000000000 : ℝ)) (X := (104962343524103952171/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s6_corner0b : (54962343524103952171/50000000000000000000 : ℝ) ≤ (10230281310470093/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (54962343524103952171/50000000000000000000 : ℝ)^32 ≤ (10230281310470093/10000000000000000 : ℝ)^133 := by
      have hnat : (54962343524103952171 : ℕ)^32*10000000000000000^133 ≤ 10230281310470093^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54962343524103952171 50000000000000000000 10230281310470093 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10230281310470093/10000000000000000 : ℝ)) (X := (54962343524103952171/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(29302101815821/1213725000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(37690967735603/1618300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (48549/100000 : ℝ)) (alpha := (29302101815821/1213725000000000 : ℝ)) (beta := (37690967735603/1618300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (48549/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(29302101815821/1213725000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(37690967735603/1618300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (3443/6250 : ℝ) ^ (133/32 : ℝ) ≤ (2097530029674217123/25000000000000000000 : ℝ) := by
    have hpowers : (3443/6250 : ℝ)^133 ≤ (2097530029674217123/25000000000000000000 : ℝ)^32 := by
      have hnat : (3443 : ℕ)^133*25000000000000000000^32 ≤ 2097530029674217123^32*6250^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3443 6250 2097530029674217123 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3443/6250 : ℝ)) (X := (2097530029674217123/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s6_corner1a : (27097530029674217123/25000000000000000000 : ℝ) ≤ (2548933954068829/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (27097530029674217123/25000000000000000000 : ℝ)^32 ≤ (2548933954068829/2500000000000000 : ℝ)^133 := by
      have hnat : (27097530029674217123 : ℕ)^32*2500000000000000^133 ≤ 2548933954068829^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27097530029674217123 25000000000000000000 2548933954068829 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2548933954068829/2500000000000000 : ℝ)) (X := (27097530029674217123/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s6_corner1b : (14597530029674217123/12500000000000000000 : ℝ) ≤ (10380282436502123/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (14597530029674217123/12500000000000000000 : ℝ)^32 ≤ (10380282436502123/10000000000000000 : ℝ)^133 := by
      have hnat : (14597530029674217123 : ℕ)^32*10000000000000000^133 ≤ 10380282436502123^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14597530029674217123 12500000000000000000 10380282436502123 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10380282436502123/10000000000000000 : ℝ)) (X := (14597530029674217123/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(48933954068829/1377200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(184546620226807/5508800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (3443/6250 : ℝ)) (alpha := (48933954068829/1377200000000000 : ℝ)) (beta := (184546620226807/5508800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (3443/6250 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(48933954068829/1377200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(184546620226807/5508800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (24941/50000 : ℝ) ^ (133/32 : ℝ) ≤ (1388414589512793747/25000000000000000000 : ℝ) := by
    have hpowers : (24941/50000 : ℝ)^133 ≤ (1388414589512793747/25000000000000000000 : ℝ)^32 := by
      have hnat : (24941 : ℕ)^133*25000000000000000000^32 ≤ 1388414589512793747^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24941 50000 1388414589512793747 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24941/50000 : ℝ)) (X := (1388414589512793747/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s6_corner2a : (26388414589512793747/25000000000000000000 : ℝ) ≤ (31659039196687/31250000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (26388414589512793747/25000000000000000000 : ℝ)^32 ≤ (31659039196687/31250000000000 : ℝ)^133 := by
      have hnat : (26388414589512793747 : ℕ)^32*31250000000000^133 ≤ 31659039196687^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26388414589512793747 25000000000000000000 31659039196687 31250000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31659039196687/31250000000000 : ℝ)) (X := (26388414589512793747/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s6_corner2b : (13888414589512793747/12500000000000000000 : ℝ) ≤ (1282081890038759/1250000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (13888414589512793747/12500000000000000000 : ℝ)^32 ≤ (1282081890038759/1250000000000000 : ℝ)^133 := by
      have hnat : (13888414589512793747 : ℕ)^32*1250000000000000^133 ≤ 1282081890038759^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13888414589512793747 12500000000000000000 1282081890038759 1250000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1282081890038759/1250000000000000 : ℝ)) (X := (13888414589512793747/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(409039196687/15588125000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(15720322171279/623525000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (24941/50000 : ℝ)) (alpha := (409039196687/15588125000000 : ℝ)) (beta := (15720322171279/623525000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (24941/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(409039196687/15588125000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(15720322171279/623525000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-11981773/50000000 : ℝ)*X 0 0+(4564977311/10000000000 : ℝ)*X 0 1+(181559749/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_1 : ((2364310311/5000000000 : ℝ)*X 1 0+(-155774581/625000000 : ℝ)*X 1 1+(2791372833/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((2398628853/5000000000 : ℝ)*X 2 0+(3093215341/5000000000 : ℝ)*X 2 1+(-311446757/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((590536387/1000000000 : ℝ)*X 0 0+(3169579863/10000000000 : ℝ)*X 0 1+(3778003073/10000000000 : ℝ)*X 0 2+(590536387/1000000000 : ℝ)*X 1 0+(3169579863/10000000000 : ℝ)*X 1 1+(3778003073/10000000000 : ℝ)*X 1 2+(590536387/1000000000 : ℝ)*X 2 0+(3169579863/10000000000 : ℝ)*X 2 1+(3778003073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-597199969/2500000000 : ℝ)*X 0 0+(1993281493/5000000000 : ℝ)*X 0 1+(395853469/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((4405139157/10000000000 : ℝ)*X 1 0+(-1980759899/10000000000 : ℝ)*X 1 1+(6257807493/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((4474161243/10000000000 : ℝ)*X 2 0+(6853137521/10000000000 : ℝ)*X 2 1+(-922204671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((586215253/1000000000 : ℝ)*X 0 0+(4193912433/10000000000 : ℝ)*X 0 1+(2766904419/10000000000 : ℝ)*X 0 2+(586215253/1000000000 : ℝ)*X 1 0+(4193912433/10000000000 : ℝ)*X 1 1+(2766904419/10000000000 : ℝ)*X 1 2+(586215253/1000000000 : ℝ)*X 2 0+(4193912433/10000000000 : ℝ)*X 2 1+(2766904419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-791498287/5000000000 : ℝ)*X 0 0+(4620427913/10000000000 : ℝ)*X 0 1+(1266292371/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((4251450993/10000000000 : ℝ)*X 1 0+(-108865639/500000000 : ℝ)*X 1 1+(1563903601/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((2825474263/5000000000 : ℝ)*X 2 0+(5753593473/10000000000 : ℝ)*X 2 1+(-924398231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((6942222569/10000000000 : ℝ)*X 0 0+(2887846583/10000000000 : ℝ)*X 0 1+(138571011/500000000 : ℝ)*X 0 2+(6942222569/10000000000 : ℝ)*X 1 0+(2887846583/10000000000 : ℝ)*X 1 1+(138571011/500000000 : ℝ)*X 1 2+(6942222569/10000000000 : ℝ)*X 2 0+(2887846583/10000000000 : ℝ)*X 2 1+(138571011/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-1563018003/10000000000 : ℝ)*X 0 0+(5143870253/10000000000 : ℝ)*X 0 1+(1171255259/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((2800952649/5000000000 : ℝ)*X 1 0+(-415544681/2500000000 : ℝ)*X 1 1+(5336945359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((4233064479/10000000000 : ℝ)*X 2 0+(6792540639/10000000000 : ℝ)*X 2 1+(-696942551/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((7122158059/10000000000 : ℝ)*X 0 0+(518417481/2000000000 : ℝ)*X 0 1+(2824949821/10000000000 : ℝ)*X 0 2+(7122158059/10000000000 : ℝ)*X 1 0+(518417481/2000000000 : ℝ)*X 1 1+(2824949821/10000000000 : ℝ)*X 1 2+(7122158059/10000000000 : ℝ)*X 2 0+(518417481/2000000000 : ℝ)*X 2 1+(2824949821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305061_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((14467/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14467/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13346103666672654189640689007019/1111731487143200000000000000000000000 : ℝ) := by norm_num
    linear_combination (382889/500000000000 : ℝ)*(base50) + (949714070497/1000000000000 : ℝ)*(base59) + (5793862351111/1000000000000 : ℝ)*(major_s6_0) + (5793862351111/1000000000000 : ℝ)*(major_s6_1) + (5793862351111/1000000000000 : ℝ)*(major_s6_2) + (55032177/1000000000000 : ℝ)*(sp_s6_0) + (2896631/100000000000 : ℝ)*(sp_s6_1) + (22174801/500000000000 : ℝ)*(sp_s6_6) + (3899522324991/500000000000 : ℝ)*(sp_s6_7) + (7798766723599/1000000000000 : ℝ)*(sp_s6_8) + (1559795440323/200000000000 : ℝ)*(sp_s6_9) + (1894288334429/500000000000 : ℝ)*(sp_s6_13) + (1215969/4000000000 : ℝ)*(sp_s6_15) + (3827517/31250000000 : ℝ)*(sp_s6_23) + (189431050923/50000000000 : ℝ)*(f.failure) + (7799099682159/1000000000000 : ℝ)*(f.sum) + (11925646150140319441/34348745200000000000000000000000 : ℝ)*base62 + (774227534853067/1247050000000000000000000000 : ℝ)*base65 + (4309412629806017/5508800000000000000000000000 : ℝ)*base67 + (94747998513099/249410000000000000000000000 : ℝ)*base69 + (800232507055487941/2421721218000000000000000000000 : ℝ)*base71 + (556378895741483/1618300000000000000000000000 : ℝ)*base73 + (72480936058701/1377200000000000000000000000 : ℝ)*base74 + (768713153719367/2427450000000000000000000000 : ℝ)*base77 + (9192034193787249179/17829782080000000000000000000000 : ℝ)*base79 + (307/625000000000000 : ℝ)*base86 + (307/625000000000000 : ℝ)*base88 + (307/625000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16979/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16979/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (73118051770252279060841846831/5558657435716000000000000000000000 : ℝ) := by norm_num
    linear_combination (334897/250000000000 : ℝ)*(base39) + (204293/200000000000 : ℝ)*(base49) + (72016338309/125000000000 : ℝ)*(base59) + (111672946787/20000000000 : ℝ)*(major_s6_0) + (111672946787/20000000000 : ℝ)*(major_s6_1) + (111672946787/20000000000 : ℝ)*(major_s6_2) + (29781013/1000000000000 : ℝ)*(sp_s6_2) + (23022069/1000000000000 : ℝ)*(sp_s6_6) + (17994507/250000000000 : ℝ)*(sp_s6_7) + (7516057417211/1000000000000 : ℝ)*(sp_s6_14) + (7516129395239/1000000000000 : ℝ)*(sp_s6_15) + (3758049807113/500000000000 : ℝ)*(sp_s6_16) + (3650897257873/1000000000000 : ℝ)*(sp_s6_20) + (240618879/1000000000000 : ℝ)*(sp_s6_27) + (1825580449411/500000000000 : ℝ)*(f.failure) + (7516129395239/1000000000000 : ℝ)*(f.sum) + (2128450559959770943/3434874520000000000000000000000 : ℝ)*base63 + (38315201190523/62352500000000000000000000 : ℝ)*base64 + (39396372947479/550880000000000000000000000 : ℝ)*base66 + (5402894343309/49882000000000000000000000 : ℝ)*base69 + (984063351826021729/12108606090000000000000000000000 : ℝ)*base70 + (31286872510291/161830000000000000000000000 : ℝ)*base72 + (7828366479611/137720000000000000000000000 : ℝ)*base75 + (24386174054389/97098000000000000000000000 : ℝ)*base76 + (890177470224655539/1782978208000000000000000000000 : ℝ)*base79 + (397/781250000000000 : ℝ)*base87 + (397/781250000000000 : ℝ)*base89 + (397/781250000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(781/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(781/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (258121864467895987996354971/43682966096000000000000000000000 : ℝ) := by norm_num
    linear_combination (308435981739/1000000000000 : ℝ)*(base40) + (1397151/1000000000000 : ℝ)*(base50) + (291589612871/500000000000 : ℝ)*(base59) + (516665747163/100000000000 : ℝ)*(major_s6_0) + (516665747163/100000000000 : ℝ)*(major_s6_1) + (516665747163/100000000000 : ℝ)*(major_s6_2) + (1098879/1000000000000 : ℝ)*(sp_s6_1) + (15261151/100000000000 : ℝ)*(sp_s6_2) + (35841229/1000000000000 : ℝ)*(sp_s6_9) + (196186823/500000000000 : ℝ)*(sp_s6_20) + (3477411393803/500000000000 : ℝ)*(sp_s6_21) + (6954821688727/1000000000000 : ℝ)*(sp_s6_22) + (6954634334867/1000000000000 : ℝ)*(sp_s6_23) + (3378097812343/1000000000000 : ℝ)*(sp_s6_27) + (337849018599/100000000000 : ℝ)*(f.failure) + (3477411393803/500000000000 : ℝ)*(f.sum) + (646251110507699/6748280000000000000000000000 : ℝ)*base63 + (12330918911/490000000000000000000000 : ℝ)*base64 + (171461662184157/550880000000000000000000000 : ℝ)*base67 + (22258278977/98000000000000000000000 : ℝ)*base69 + (1833408803966673/7929670000000000000000000000 : ℝ)*base71 + (17951350596501/161830000000000000000000000 : ℝ)*base72 + (519592475793/27544000000000000000000000 : ℝ)*base74 + (30992710982239/161830000000000000000000000 : ℝ)*base77 + (540290357332534463/1782978208000000000000000000000 : ℝ)*base79 + (123/156250000000000 : ℝ)*base87 + (123/156250000000000 : ℝ)*base89 + (123/156250000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((48549/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48549/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3443/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3443/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(24941/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(24941/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14467/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14467/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16979/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16979/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(781/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(781/2500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305061_s6 p hpa hpb X hX hprev5

#print axioms solution

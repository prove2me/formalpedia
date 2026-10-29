-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c317055_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:14:59.109191+00:00
-- url     : https://prove2.me/submissions/1c065db1-7d0b-4f66-bad6-36cc265c0923

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
theorem collision_support_c317055_s2_s2_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2040306893/10000000000 : ℝ)*x 0 + (43238303/78125000 : ℝ)*x 1 + (2363212049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2040306893/10000000000 : ℝ)^39 ≤ (2707586841739/20000000000000 : ℝ)^31 := by
    have hnat : (2040306893 : ℕ)^39*20000000000000^31 ≤ 2707586841739^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040306893 10000000000 2707586841739 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43238303/78125000 : ℝ)^39 ≤ (11877261675229/25000000000000 : ℝ)^31 := by
    have hnat : (43238303 : ℕ)^39*25000000000000^31 ≤ 11877261675229^31*78125000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43238303 78125000 11877261675229 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2363212049/5000000000 : ℝ)^39 ≤ (38953019071931/100000000000000 : ℝ)^31 := by
    have hnat : (2363212049 : ℕ)^39*100000000000000^31 ≤ 38953019071931^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2363212049 5000000000 38953019071931 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2040306893/10000000000 : ℝ), (43238303/78125000 : ℝ), (2363212049/5000000000 : ℝ)] ![(2707586841739/20000000000000 : ℝ), (11877261675229/25000000000000 : ℝ), (38953019071931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2040306893/10000000000 : ℝ)|^39 ≤ (2707586841739/20000000000000 : ℝ)^31
        have hw : |(-2040306893/10000000000 : ℝ)|=(2040306893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43238303/78125000 : ℝ)|^39 ≤ (11877261675229/25000000000000 : ℝ)^31
        have hw : |(43238303/78125000 : ℝ)|=(43238303/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2363212049/5000000000 : ℝ)|^39 ≤ (38953019071931/100000000000000 : ℝ)^31
        have hw : |(2363212049/5000000000 : ℝ)|=(2363212049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317055_s2_s2_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4720517011/10000000000 : ℝ)*x 0 + (5541558013/10000000000 : ℝ)*x 1 + (-2038513611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4720517011/10000000000 : ℝ)^39 ≤ (19445890983377/50000000000000 : ℝ)^31 := by
    have hnat : (4720517011 : ℕ)^39*50000000000000^31 ≤ 19445890983377^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4720517011 10000000000 19445890983377 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5541558013/10000000000 : ℝ)^39 ≤ (9517050328731/20000000000000 : ℝ)^31 := by
    have hnat : (5541558013 : ℕ)^39*20000000000000^31 ≤ 9517050328731^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5541558013 10000000000 9517050328731 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2038513611/10000000000 : ℝ)^39 ≤ (1352296636849/10000000000000 : ℝ)^31 := by
    have hnat : (2038513611 : ℕ)^39*10000000000000^31 ≤ 1352296636849^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038513611 10000000000 1352296636849 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4720517011/10000000000 : ℝ), (5541558013/10000000000 : ℝ), (-2038513611/10000000000 : ℝ)] ![(19445890983377/50000000000000 : ℝ), (9517050328731/20000000000000 : ℝ), (1352296636849/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4720517011/10000000000 : ℝ)|^39 ≤ (19445890983377/50000000000000 : ℝ)^31
        have hw : |(4720517011/10000000000 : ℝ)|=(4720517011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5541558013/10000000000 : ℝ)|^39 ≤ (9517050328731/20000000000000 : ℝ)^31
        have hw : |(5541558013/10000000000 : ℝ)|=(5541558013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2038513611/10000000000 : ℝ)|^39 ≤ (1352296636849/10000000000000 : ℝ)^31
        have hw : |(-2038513611/10000000000 : ℝ)|=(2038513611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317055_s2_s2_6 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (301543359/500000000 : ℝ)*x 0 + (195316239/500000000 : ℝ)*x 1 + (237868041/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (301543359/500000000 : ℝ)^39 ≤ (52930204752989/100000000000000 : ℝ)^31 := by
    have hnat : (301543359 : ℕ)^39*100000000000000^31 ≤ 52930204752989^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301543359 500000000 52930204752989 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195316239/500000000 : ℝ)^39 ≤ (15324568309229/50000000000000 : ℝ)^31 := by
    have hnat : (195316239 : ℕ)^39*50000000000000^31 ≤ 15324568309229^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195316239 500000000 15324568309229 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237868041/1000000000 : ℝ)^39 ≤ (1026291163493/6250000000000 : ℝ)^31 := by
    have hnat : (237868041 : ℕ)^39*6250000000000^31 ≤ 1026291163493^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237868041 1000000000 1026291163493 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(301543359/500000000 : ℝ), (195316239/500000000 : ℝ), (237868041/1000000000 : ℝ)] ![(52930204752989/100000000000000 : ℝ), (15324568309229/50000000000000 : ℝ), (1026291163493/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(301543359/500000000 : ℝ)|^39 ≤ (52930204752989/100000000000000 : ℝ)^31
        have hw : |(301543359/500000000 : ℝ)|=(301543359/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195316239/500000000 : ℝ)|^39 ≤ (15324568309229/50000000000000 : ℝ)^31
        have hw : |(195316239/500000000 : ℝ)|=(195316239/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(237868041/1000000000 : ℝ)|^39 ≤ (1026291163493/6250000000000 : ℝ)^31
        have hw : |(237868041/1000000000 : ℝ)|=(237868041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317055_s2_s2_7 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-916062731/5000000000 : ℝ)*x 0 + (5049513171/10000000000 : ℝ)*x 1 + (5379798229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (916062731/5000000000 : ℝ)^39 ≤ (738975637293/6250000000000 : ℝ)^31 := by
    have hnat : (916062731 : ℕ)^39*6250000000000^31 ≤ 738975637293^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916062731 5000000000 738975637293 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5049513171/10000000000 : ℝ)^39 ≤ (42331995136129/100000000000000 : ℝ)^31 := by
    have hnat : (5049513171 : ℕ)^39*100000000000000^31 ≤ 42331995136129^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5049513171 10000000000 42331995136129 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5379798229/10000000000 : ℝ)^39 ≤ (45844394650971/100000000000000 : ℝ)^31 := by
    have hnat : (5379798229 : ℕ)^39*100000000000000^31 ≤ 45844394650971^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379798229 10000000000 45844394650971 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-916062731/5000000000 : ℝ), (5049513171/10000000000 : ℝ), (5379798229/10000000000 : ℝ)] ![(738975637293/6250000000000 : ℝ), (42331995136129/100000000000000 : ℝ), (45844394650971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-916062731/5000000000 : ℝ)|^39 ≤ (738975637293/6250000000000 : ℝ)^31
        have hw : |(-916062731/5000000000 : ℝ)|=(916062731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5049513171/10000000000 : ℝ)|^39 ≤ (42331995136129/100000000000000 : ℝ)^31
        have hw : |(5049513171/10000000000 : ℝ)|=(5049513171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5379798229/10000000000 : ℝ)|^39 ≤ (45844394650971/100000000000000 : ℝ)^31
        have hw : |(5379798229/10000000000 : ℝ)|=(5379798229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317055_s2_s2_8 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2329318807/5000000000 : ℝ)*x 0 + (-727885149/10000000000 : ℝ)*x 1 + (648984121/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2329318807/5000000000 : ℝ)^39 ≤ (4781435953803/12500000000000 : ℝ)^31 := by
    have hnat : (2329318807 : ℕ)^39*12500000000000^31 ≤ 4781435953803^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2329318807 5000000000 4781435953803 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (727885149/10000000000 : ℝ)^39 ≤ (115678242691/3125000000000 : ℝ)^31 := by
    have hnat : (727885149 : ℕ)^39*3125000000000^31 ≤ 115678242691^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      727885149 10000000000 115678242691 3125000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648984121/1000000000 : ℝ)^39 ≤ (14511702145581/25000000000000 : ℝ)^31 := by
    have hnat : (648984121 : ℕ)^39*25000000000000^31 ≤ 14511702145581^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648984121 1000000000 14511702145581 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2329318807/5000000000 : ℝ), (-727885149/10000000000 : ℝ), (648984121/1000000000 : ℝ)] ![(4781435953803/12500000000000 : ℝ), (115678242691/3125000000000 : ℝ), (14511702145581/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2329318807/5000000000 : ℝ)|^39 ≤ (4781435953803/12500000000000 : ℝ)^31
        have hw : |(2329318807/5000000000 : ℝ)|=(2329318807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-727885149/10000000000 : ℝ)|^39 ≤ (115678242691/3125000000000 : ℝ)^31
        have hw : |(-727885149/10000000000 : ℝ)|=(727885149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(648984121/1000000000 : ℝ)|^39 ≤ (14511702145581/25000000000000 : ℝ)^31
        have hw : |(648984121/1000000000 : ℝ)|=(648984121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317055_s2_s2_9 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (465411271/1000000000 : ℝ)*x 0 + (3031705671/5000000000 : ℝ)*x 1 + (-7050451/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (465411271/1000000000 : ℝ)^39 ≤ (38204752093331/100000000000000 : ℝ)^31 := by
    have hnat : (465411271 : ℕ)^39*100000000000000^31 ≤ 38204752093331^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465411271 1000000000 38204752093331 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3031705671/5000000000 : ℝ)^39 ≤ (13322447466761/25000000000000 : ℝ)^31 := by
    have hnat : (3031705671 : ℕ)^39*25000000000000^31 ≤ 13322447466761^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3031705671 5000000000 13322447466761 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7050451/50000000 : ℝ)^39 ≤ (1701091605301/20000000000000 : ℝ)^31 := by
    have hnat : (7050451 : ℕ)^39*20000000000000^31 ≤ 1701091605301^31*50000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7050451 50000000 1701091605301 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(465411271/1000000000 : ℝ), (3031705671/5000000000 : ℝ), (-7050451/50000000 : ℝ)] ![(38204752093331/100000000000000 : ℝ), (13322447466761/25000000000000 : ℝ), (1701091605301/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(465411271/1000000000 : ℝ)|^39 ≤ (38204752093331/100000000000000 : ℝ)^31
        have hw : |(465411271/1000000000 : ℝ)|=(465411271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3031705671/5000000000 : ℝ)|^39 ≤ (13322447466761/25000000000000 : ℝ)^31
        have hw : |(3031705671/5000000000 : ℝ)|=(3031705671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7050451/50000000 : ℝ)|^39 ≤ (1701091605301/20000000000000 : ℝ)^31
        have hw : |(-7050451/50000000 : ℝ)|=(7050451/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317055_s2_s2_13 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1094125013/2000000000 : ℝ)*x 0 + (5218975097/10000000000 : ℝ)*x 1 + (1481755167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094125013/2000000000 : ℝ)^39 ≤ (46820234386007/100000000000000 : ℝ)^31 := by
    have hnat : (1094125013 : ℕ)^39*100000000000000^31 ≤ 46820234386007^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094125013 2000000000 46820234386007 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218975097/10000000000 : ℝ)^39 ≤ (44126958292173/100000000000000 : ℝ)^31 := by
    have hnat : (5218975097 : ℕ)^39*100000000000000^31 ≤ 44126958292173^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218975097 10000000000 44126958292173 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1481755167/10000000000 : ℝ)^39 ≤ (1131600913133/12500000000000 : ℝ)^31 := by
    have hnat : (1481755167 : ℕ)^39*12500000000000^31 ≤ 1131600913133^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1481755167 10000000000 1131600913133 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094125013/2000000000 : ℝ), (5218975097/10000000000 : ℝ), (1481755167/10000000000 : ℝ)] ![(46820234386007/100000000000000 : ℝ), (44126958292173/100000000000000 : ℝ), (1131600913133/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094125013/2000000000 : ℝ)|^39 ≤ (46820234386007/100000000000000 : ℝ)^31
        have hw : |(1094125013/2000000000 : ℝ)|=(1094125013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218975097/10000000000 : ℝ)|^39 ≤ (44126958292173/100000000000000 : ℝ)^31
        have hw : |(5218975097/10000000000 : ℝ)|=(5218975097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1481755167/10000000000 : ℝ)|^39 ≤ (1131600913133/12500000000000 : ℝ)^31
        have hw : |(1481755167/10000000000 : ℝ)|=(1481755167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317055_s2_s2_14 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1333368343/10000000000 : ℝ)*x 0 + (1067393451/2000000000 : ℝ)*x 1 + (5458238883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1333368343/10000000000 : ℝ)^39 ≤ (7927400889851/100000000000000 : ℝ)^31 := by
    have hnat : (1333368343 : ℕ)^39*100000000000000^31 ≤ 7927400889851^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333368343 10000000000 7927400889851 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1067393451/2000000000 : ℝ)^39 ≤ (45385689239717/100000000000000 : ℝ)^31 := by
    have hnat : (1067393451 : ℕ)^39*100000000000000^31 ≤ 45385689239717^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067393451 2000000000 45385689239717 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458238883/10000000000 : ℝ)^39 ≤ (23343454931879/50000000000000 : ℝ)^31 := by
    have hnat : (5458238883 : ℕ)^39*50000000000000^31 ≤ 23343454931879^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458238883 10000000000 23343454931879 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1333368343/10000000000 : ℝ), (1067393451/2000000000 : ℝ), (5458238883/10000000000 : ℝ)] ![(7927400889851/100000000000000 : ℝ), (45385689239717/100000000000000 : ℝ), (23343454931879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1333368343/10000000000 : ℝ)|^39 ≤ (7927400889851/100000000000000 : ℝ)^31
        have hw : |(-1333368343/10000000000 : ℝ)|=(1333368343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1067393451/2000000000 : ℝ)|^39 ≤ (45385689239717/100000000000000 : ℝ)^31
        have hw : |(1067393451/2000000000 : ℝ)|=(1067393451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458238883/10000000000 : ℝ)|^39 ≤ (23343454931879/50000000000000 : ℝ)^31
        have hw : |(5458238883/10000000000 : ℝ)|=(5458238883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317055_s2_s2_15 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2200518031/5000000000 : ℝ)*x 0 + (-1123516127/10000000000 : ℝ)*x 1 + (6485614751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2200518031/5000000000 : ℝ)^39 ≤ (17804882266107/50000000000000 : ℝ)^31 := by
    have hnat : (2200518031 : ℕ)^39*50000000000000^31 ≤ 17804882266107^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200518031 5000000000 17804882266107 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123516127/10000000000 : ℝ)^39 ≤ (3195490451961/50000000000000 : ℝ)^31 := by
    have hnat : (1123516127 : ℕ)^39*50000000000000^31 ≤ 3195490451961^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123516127 10000000000 3195490451961 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6485614751/10000000000 : ℝ)^39 ≤ (11599850910011/20000000000000 : ℝ)^31 := by
    have hnat : (6485614751 : ℕ)^39*20000000000000^31 ≤ 11599850910011^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6485614751 10000000000 11599850910011 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2200518031/5000000000 : ℝ), (-1123516127/10000000000 : ℝ), (6485614751/10000000000 : ℝ)] ![(17804882266107/50000000000000 : ℝ), (3195490451961/50000000000000 : ℝ), (11599850910011/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2200518031/5000000000 : ℝ)|^39 ≤ (17804882266107/50000000000000 : ℝ)^31
        have hw : |(2200518031/5000000000 : ℝ)|=(2200518031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1123516127/10000000000 : ℝ)|^39 ≤ (3195490451961/50000000000000 : ℝ)^31
        have hw : |(-1123516127/10000000000 : ℝ)|=(1123516127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6485614751/10000000000 : ℝ)|^39 ≤ (11599850910011/20000000000000 : ℝ)^31
        have hw : |(6485614751/10000000000 : ℝ)|=(6485614751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317055_s2_s2_16 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1090478237/2000000000 : ℝ)*x 0 + (5344048499/10000000000 : ℝ)*x 1 + (-133164939/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090478237/2000000000 : ℝ)^39 ≤ (9324798503891/20000000000000 : ℝ)^31 := by
    have hnat : (1090478237 : ℕ)^39*20000000000000^31 ≤ 9324798503891^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090478237 2000000000 9324798503891 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5344048499/10000000000 : ℝ)^39 ≤ (45461461665583/100000000000000 : ℝ)^31 := by
    have hnat : (5344048499 : ℕ)^39*100000000000000^31 ≤ 45461461665583^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344048499 10000000000 45461461665583 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133164939/1000000000 : ℝ)^39 ≤ (3957272896921/50000000000000 : ℝ)^31 := by
    have hnat : (133164939 : ℕ)^39*50000000000000^31 ≤ 3957272896921^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133164939 1000000000 3957272896921 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090478237/2000000000 : ℝ), (5344048499/10000000000 : ℝ), (-133164939/1000000000 : ℝ)] ![(9324798503891/20000000000000 : ℝ), (45461461665583/100000000000000 : ℝ), (3957272896921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090478237/2000000000 : ℝ)|^39 ≤ (9324798503891/20000000000000 : ℝ)^31
        have hw : |(1090478237/2000000000 : ℝ)|=(1090478237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5344048499/10000000000 : ℝ)|^39 ≤ (45461461665583/100000000000000 : ℝ)^31
        have hw : |(5344048499/10000000000 : ℝ)|=(5344048499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133164939/1000000000 : ℝ)|^39 ≤ (3957272896921/50000000000000 : ℝ)^31
        have hw : |(-133164939/1000000000 : ℝ)|=(133164939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317055_s2_s2_20 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3458803577/5000000000 : ℝ)*x 0 + (3631579159/10000000000 : ℝ)*x 1 + (186591511/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3458803577/5000000000 : ℝ)^39 ≤ (31450256729039/50000000000000 : ℝ)^31 := by
    have hnat : (3458803577 : ℕ)^39*50000000000000^31 ≤ 31450256729039^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3458803577 5000000000 31450256729039 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3631579159/10000000000 : ℝ)^39 ≤ (27962228288897/100000000000000 : ℝ)^31 := by
    have hnat : (3631579159 : ℕ)^39*100000000000000^31 ≤ 27962228288897^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3631579159 10000000000 27962228288897 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (186591511/1250000000 : ℝ)^39 ≤ (9137258238561/100000000000000 : ℝ)^31 := by
    have hnat : (186591511 : ℕ)^39*100000000000000^31 ≤ 9137258238561^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186591511 1250000000 9137258238561 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3458803577/5000000000 : ℝ), (3631579159/10000000000 : ℝ), (186591511/1250000000 : ℝ)] ![(31450256729039/50000000000000 : ℝ), (27962228288897/100000000000000 : ℝ), (9137258238561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3458803577/5000000000 : ℝ)|^39 ≤ (31450256729039/50000000000000 : ℝ)^31
        have hw : |(3458803577/5000000000 : ℝ)|=(3458803577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3631579159/10000000000 : ℝ)|^39 ≤ (27962228288897/100000000000000 : ℝ)^31
        have hw : |(3631579159/10000000000 : ℝ)|=(3631579159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(186591511/1250000000 : ℝ)|^39 ≤ (9137258238561/100000000000000 : ℝ)^31
        have hw : |(186591511/1250000000 : ℝ)|=(186591511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317055_s2_s2_21 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-683541967/5000000000 : ℝ)*x 0 + (3008284949/5000000000 : ℝ)*x 1 + (4735506191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (683541967/5000000000 : ℝ)^39 ≤ (1022550095611/12500000000000 : ℝ)^31 := by
    have hnat : (683541967 : ℕ)^39*12500000000000^31 ≤ 1022550095611^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683541967 5000000000 1022550095611 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3008284949/5000000000 : ℝ)^39 ≤ (52772390123577/100000000000000 : ℝ)^31 := by
    have hnat : (3008284949 : ℕ)^39*100000000000000^31 ≤ 52772390123577^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008284949 5000000000 52772390123577 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4735506191/10000000000 : ℝ)^39 ≤ (39047209096299/100000000000000 : ℝ)^31 := by
    have hnat : (4735506191 : ℕ)^39*100000000000000^31 ≤ 39047209096299^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4735506191 10000000000 39047209096299 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-683541967/5000000000 : ℝ), (3008284949/5000000000 : ℝ), (4735506191/10000000000 : ℝ)] ![(1022550095611/12500000000000 : ℝ), (52772390123577/100000000000000 : ℝ), (39047209096299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-683541967/5000000000 : ℝ)|^39 ≤ (1022550095611/12500000000000 : ℝ)^31
        have hw : |(-683541967/5000000000 : ℝ)|=(683541967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3008284949/5000000000 : ℝ)|^39 ≤ (52772390123577/100000000000000 : ℝ)^31
        have hw : |(3008284949/5000000000 : ℝ)|=(3008284949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4735506191/10000000000 : ℝ)|^39 ≤ (39047209096299/100000000000000 : ℝ)^31
        have hw : |(4735506191/10000000000 : ℝ)|=(4735506191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317055_s2_s2_22 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5423200751/10000000000 : ℝ)*x 0 + (-350136297/5000000000 : ℝ)*x 1 + (5778957703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5423200751/10000000000 : ℝ)^39 ≤ (2894386469453/6250000000000 : ℝ)^31 := by
    have hnat : (5423200751 : ℕ)^39*6250000000000^31 ≤ 2894386469453^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423200751 10000000000 2894386469453 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350136297/5000000000 : ℝ)^39 ≤ (3525912663841/100000000000000 : ℝ)^31 := by
    have hnat : (350136297 : ℕ)^39*100000000000000^31 ≤ 3525912663841^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350136297 5000000000 3525912663841 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5778957703/10000000000 : ℝ)^39 ≤ (3135243987681/6250000000000 : ℝ)^31 := by
    have hnat : (5778957703 : ℕ)^39*6250000000000^31 ≤ 3135243987681^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5778957703 10000000000 3135243987681 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5423200751/10000000000 : ℝ), (-350136297/5000000000 : ℝ), (5778957703/10000000000 : ℝ)] ![(2894386469453/6250000000000 : ℝ), (3525912663841/100000000000000 : ℝ), (3135243987681/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5423200751/10000000000 : ℝ)|^39 ≤ (2894386469453/6250000000000 : ℝ)^31
        have hw : |(5423200751/10000000000 : ℝ)|=(5423200751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-350136297/5000000000 : ℝ)|^39 ≤ (3525912663841/100000000000000 : ℝ)^31
        have hw : |(-350136297/5000000000 : ℝ)|=(350136297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5778957703/10000000000 : ℝ)|^39 ≤ (3135243987681/6250000000000 : ℝ)^31
        have hw : |(5778957703/10000000000 : ℝ)|=(5778957703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317055_s2_s2_23 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (541179949/1250000000 : ℝ)*x 0 + (6091023099/10000000000 : ℝ)*x 1 + (-179490701/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541179949/1250000000 : ℝ)^39 ≤ (34882500001927/100000000000000 : ℝ)^31 := by
    have hnat : (541179949 : ℕ)^39*100000000000000^31 ≤ 34882500001927^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541179949 1250000000 34882500001927 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6091023099/10000000000 : ℝ)^39 ≤ (53595267036541/100000000000000 : ℝ)^31 := by
    have hnat : (6091023099 : ℕ)^39*100000000000000^31 ≤ 53595267036541^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6091023099 10000000000 53595267036541 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179490701/1000000000 : ℝ)^39 ≤ (5761116476711/50000000000000 : ℝ)^31 := by
    have hnat : (179490701 : ℕ)^39*50000000000000^31 ≤ 5761116476711^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179490701 1000000000 5761116476711 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541179949/1250000000 : ℝ), (6091023099/10000000000 : ℝ), (-179490701/1000000000 : ℝ)] ![(34882500001927/100000000000000 : ℝ), (53595267036541/100000000000000 : ℝ), (5761116476711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541179949/1250000000 : ℝ)|^39 ≤ (34882500001927/100000000000000 : ℝ)^31
        have hw : |(541179949/1250000000 : ℝ)|=(541179949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6091023099/10000000000 : ℝ)|^39 ≤ (53595267036541/100000000000000 : ℝ)^31
        have hw : |(6091023099/10000000000 : ℝ)|=(6091023099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-179490701/1000000000 : ℝ)|^39 ≤ (5761116476711/50000000000000 : ℝ)^31
        have hw : |(-179490701/1000000000 : ℝ)|=(179490701/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317055_s2_s2_27 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7091811093/10000000000 : ℝ)*x 0 + (2707286431/10000000000 : ℝ)*x 1 + (36003257/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7091811093/10000000000 : ℝ)^39 ≤ (64899728051989/100000000000000 : ℝ)^31 := by
    have hnat : (7091811093 : ℕ)^39*100000000000000^31 ≤ 64899728051989^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7091811093 10000000000 64899728051989 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707286431/10000000000 : ℝ)^39 ≤ (4830937622177/25000000000000 : ℝ)^31 := by
    have hnat : (2707286431 : ℕ)^39*25000000000000^31 ≤ 4830937622177^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707286431 10000000000 4830937622177 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36003257/156250000 : ℝ)^39 ≤ (788826072377/5000000000000 : ℝ)^31 := by
    have hnat : (36003257 : ℕ)^39*5000000000000^31 ≤ 788826072377^31*156250000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36003257 156250000 788826072377 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7091811093/10000000000 : ℝ), (2707286431/10000000000 : ℝ), (36003257/156250000 : ℝ)] ![(64899728051989/100000000000000 : ℝ), (4830937622177/25000000000000 : ℝ), (788826072377/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7091811093/10000000000 : ℝ)|^39 ≤ (64899728051989/100000000000000 : ℝ)^31
        have hw : |(7091811093/10000000000 : ℝ)|=(7091811093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707286431/10000000000 : ℝ)|^39 ≤ (4830937622177/25000000000000 : ℝ)^31
        have hw : |(2707286431/10000000000 : ℝ)|=(2707286431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36003257/156250000 : ℝ)|^39 ≤ (788826072377/5000000000000 : ℝ)^31
        have hw : |(36003257/156250000 : ℝ)|=(36003257/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317055_s2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((54667/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(54667/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(54023/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(54023/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10901/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10901/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((119/400 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(119/400 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30661/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30661/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3751/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3751/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (54667/100000 : ℝ) ^ (77/16 : ℝ) ≤ (5467675408212741087/100000000000000000000 : ℝ) := by
    have hpowers : (54667/100000 : ℝ)^77 ≤ (5467675408212741087/100000000000000000000 : ℝ)^16 := by
      have hnat : (54667 : ℕ)^77*100000000000000000000^16 ≤ 5467675408212741087^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54667 100000 5467675408212741087 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (54667/100000 : ℝ)) (X := (5467675408212741087/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (105467675408212741087/100000000000000000000 : ℝ) ≤ (2527807711622039/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (105467675408212741087/100000000000000000000 : ℝ)^16 ≤ (2527807711622039/2500000000000000 : ℝ)^77 := by
      have hnat : (105467675408212741087 : ℕ)^16*2500000000000000^77 ≤ 2527807711622039^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105467675408212741087 100000000000000000000 2527807711622039 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2527807711622039/2500000000000000 : ℝ)) (X := (105467675408212741087/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (55467675408212741087/50000000000000000000 : ℝ) ≤ (2043596651410869/2000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (55467675408212741087/50000000000000000000 : ℝ)^16 ≤ (2043596651410869/2000000000000000 : ℝ)^77 := by
      have hnat : (55467675408212741087 : ℕ)^16*2000000000000000^77 ≤ 2043596651410869^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55467675408212741087 50000000000000000000 2043596651410869 2000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2043596651410869/2000000000000000 : ℝ)) (X := (55467675408212741087/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27807711622039/1366675000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(106752410566189/5466700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (54667/100000 : ℝ)) (alpha := (27807711622039/1366675000000000 : ℝ)) (beta := (106752410566189/5466700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (54667/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27807711622039/1366675000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(106752410566189/5466700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (54023/100000 : ℝ) ^ (77/16 : ℝ) ≤ (258228984355744159/5000000000000000000 : ℝ) := by
    have hpowers : (54023/100000 : ℝ)^77 ≤ (258228984355744159/5000000000000000000 : ℝ)^16 := by
      have hnat : (54023 : ℕ)^77*5000000000000000000^16 ≤ 258228984355744159^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54023 100000 258228984355744159 5000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (54023/100000 : ℝ)) (X := (258228984355744159/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (5258228984355744159/5000000000000000000 : ℝ) ≤ (10105185952971809/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (5258228984355744159/5000000000000000000 : ℝ)^16 ≤ (10105185952971809/10000000000000000 : ℝ)^77 := by
      have hnat : (5258228984355744159 : ℕ)^16*10000000000000000^77 ≤ 10105185952971809^77*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5258228984355744159 5000000000000000000 10105185952971809 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10105185952971809/10000000000000000 : ℝ)) (X := (5258228984355744159/5000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (2758228984355744159/2500000000000000000 : ℝ) ≤ (10206356024637651/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2758228984355744159/2500000000000000000 : ℝ)^16 ≤ (10206356024637651/10000000000000000 : ℝ)^77 := by
      have hnat : (2758228984355744159 : ℕ)^16*10000000000000000^77 ≤ 10206356024637651^77*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2758228984355744159 2500000000000000000 10206356024637651 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10206356024637651/10000000000000000 : ℝ)) (X := (2758228984355744159/2500000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(105185952971809/5402300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(50585035832921/2701150000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (54023/100000 : ℝ)) (alpha := (105185952971809/5402300000000000 : ℝ)) (beta := (50585035832921/2701150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (54023/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(105185952971809/5402300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(50585035832921/2701150000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (10901/20000 : ℝ) ^ (77/16 : ℝ) ≤ (5390138262238763981/100000000000000000000 : ℝ) := by
    have hpowers : (10901/20000 : ℝ)^77 ≤ (5390138262238763981/100000000000000000000 : ℝ)^16 := by
      have hnat : (10901 : ℕ)^77*100000000000000000000^16 ≤ 5390138262238763981^16*20000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10901 20000 5390138262238763981 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10901/20000 : ℝ)) (X := (5390138262238763981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (105390138262238763981/100000000000000000000 : ℝ) ≤ (2527421442284021/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (105390138262238763981/100000000000000000000 : ℝ)^16 ≤ (2527421442284021/2500000000000000 : ℝ)^77 := by
      have hnat : (105390138262238763981 : ℕ)^16*2500000000000000^77 ≤ 2527421442284021^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105390138262238763981 100000000000000000000 2527421442284021 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2527421442284021/2500000000000000 : ℝ)) (X := (105390138262238763981/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (55390138262238763981/50000000000000000000 : ℝ) ≤ (10215013609592209/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (55390138262238763981/50000000000000000000 : ℝ)^16 ≤ (10215013609592209/10000000000000000 : ℝ)^77 := by
      have hnat : (55390138262238763981 : ℕ)^16*10000000000000000^77 ≤ 10215013609592209^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55390138262238763981 50000000000000000000 10215013609592209 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10215013609592209/10000000000000000 : ℝ)) (X := (55390138262238763981/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(27421442284021/1362625000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(842622723649/43604000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (10901/20000 : ℝ)) (alpha := (27421442284021/1362625000000000 : ℝ)) (beta := (842622723649/43604000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (10901/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(27421442284021/1362625000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(842622723649/43604000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-2040306893/10000000000 : ℝ)*X 0 0+(43238303/78125000 : ℝ)*X 0 1+(2363212049/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317055_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((4720517011/10000000000 : ℝ)*X 2 0+(5541558013/10000000000 : ℝ)*X 2 1+(-2038513611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317055_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((301543359/500000000 : ℝ)*X 0 0+(195316239/500000000 : ℝ)*X 0 1+(237868041/1000000000 : ℝ)*X 0 2+(301543359/500000000 : ℝ)*X 1 0+(195316239/500000000 : ℝ)*X 1 1+(237868041/1000000000 : ℝ)*X 1 2+(301543359/500000000 : ℝ)*X 2 0+(195316239/500000000 : ℝ)*X 2 1+(237868041/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317055_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-916062731/5000000000 : ℝ)*X 0 0+(5049513171/10000000000 : ℝ)*X 0 1+(5379798229/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317055_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2329318807/5000000000 : ℝ)*X 1 0+(-727885149/10000000000 : ℝ)*X 1 1+(648984121/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317055_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((465411271/1000000000 : ℝ)*X 2 0+(3031705671/5000000000 : ℝ)*X 2 1+(-7050451/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317055_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1094125013/2000000000 : ℝ)*X 0 0+(5218975097/10000000000 : ℝ)*X 0 1+(1481755167/10000000000 : ℝ)*X 0 2+(1094125013/2000000000 : ℝ)*X 1 0+(5218975097/10000000000 : ℝ)*X 1 1+(1481755167/10000000000 : ℝ)*X 1 2+(1094125013/2000000000 : ℝ)*X 2 0+(5218975097/10000000000 : ℝ)*X 2 1+(1481755167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317055_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1333368343/10000000000 : ℝ)*X 0 0+(1067393451/2000000000 : ℝ)*X 0 1+(5458238883/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317055_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2200518031/5000000000 : ℝ)*X 1 0+(-1123516127/10000000000 : ℝ)*X 1 1+(6485614751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317055_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1090478237/2000000000 : ℝ)*X 2 0+(5344048499/10000000000 : ℝ)*X 2 1+(-133164939/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317055_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3458803577/5000000000 : ℝ)*X 0 0+(3631579159/10000000000 : ℝ)*X 0 1+(186591511/1250000000 : ℝ)*X 0 2+(3458803577/5000000000 : ℝ)*X 1 0+(3631579159/10000000000 : ℝ)*X 1 1+(186591511/1250000000 : ℝ)*X 1 2+(3458803577/5000000000 : ℝ)*X 2 0+(3631579159/10000000000 : ℝ)*X 2 1+(186591511/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317055_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-683541967/5000000000 : ℝ)*X 0 0+(3008284949/5000000000 : ℝ)*X 0 1+(4735506191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317055_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5423200751/10000000000 : ℝ)*X 1 0+(-350136297/5000000000 : ℝ)*X 1 1+(5778957703/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317055_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((541179949/1250000000 : ℝ)*X 2 0+(6091023099/10000000000 : ℝ)*X 2 1+(-179490701/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317055_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((7091811093/10000000000 : ℝ)*X 0 0+(2707286431/10000000000 : ℝ)*X 0 1+(36003257/156250000 : ℝ)*X 0 2+(7091811093/10000000000 : ℝ)*X 1 0+(2707286431/10000000000 : ℝ)*X 1 1+(36003257/156250000 : ℝ)*X 1 2+(7091811093/10000000000 : ℝ)*X 2 0+(2707286431/10000000000 : ℝ)*X 2 1+(36003257/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317055_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((119/400 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(119/400 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3437019453867470700161828223063/321936544922410000000000000000000000 : ℝ) := by norm_num
    linear_combination (839407711963/1000000000000 : ℝ)*(base49) + (2116819/1000000000000 : ℝ)*(base60) + (1375653737319/200000000000 : ℝ)*(major_s2_0) + (1375653737319/200000000000 : ℝ)*(major_s2_1) + (1375653737319/200000000000 : ℝ)*(major_s2_2) + (5202269/100000000000 : ℝ)*(sp_s2_0) + (12824887/500000000000 : ℝ)*(sp_s2_6) + (9932264751067/1000000000000 : ℝ)*(sp_s2_7) + (9932237861469/1000000000000 : ℝ)*(sp_s2_8) + (9932195847283/1000000000000 : ℝ)*(sp_s2_9) + (1912083306201/500000000000 : ℝ)*(sp_s2_13) + (24778563/1000000000000 : ℝ)*(sp_s2_14) + (103690851/1000000000000 : ℝ)*(sp_s2_15) + (145705037/1000000000000 : ℝ)*(sp_s2_23) + (119506008193/31250000000 : ℝ)*(f.failure) + (31038567351/3125000000 : ℝ)*(f.sum) + (8854149092656422747/58890472300000000000000000000000 : ℝ)*base62 + (59630575793583/218020000000000000000000000 : ℝ)*base65 + (191956958953183/540230000000000000000000000 : ℝ)*base67 + (10666371943127/136262500000000000000000000 : ℝ)*base69 + (84379059395599437/2383699868000000000000000000000 : ℝ)*base71 + (242274623674581/1093340000000000000000000000 : ℝ)*base73 + (177691831165007/1080460000000000000000000000 : ℝ)*base75 + (105561751874161/546670000000000000000000000 : ℝ)*base77 + (3848661947611124099/59065506820000000000000000000000 : ℝ)*base79 + (9/3125000000000000 : ℝ)*base86 + (9/3125000000000000 : ℝ)*base88 + (9/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30661/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30661/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12152503538732949101130009/736130903750000000000000000000 : ℝ) := by norm_num
    linear_combination (601913/200000000000 : ℝ)*(base39) + (7221034099/10000000000 : ℝ)*(base49) + (522851/250000000000 : ℝ)*(base60) + (32793220511/5000000000 : ℝ)*(major_s2_0) + (32793220511/5000000000 : ℝ)*(major_s2_1) + (32793220511/5000000000 : ℝ)*(major_s2_2) + (589447/31250000000 : ℝ)*(sp_s2_2) + (60184299/1000000000000 : ℝ)*(sp_s2_7) + (14943991/125000000000 : ℝ)*(sp_s2_8) + (9470735709451/1000000000000 : ℝ)*(sp_s2_14) + (4735338170911/500000000000 : ℝ)*(sp_s2_15) + (4735388515723/500000000000 : ℝ)*(sp_s2_16) + (3646406050119/1000000000000 : ℝ)*(sp_s2_20) + (10094707/125000000000 : ℝ)*(sp_s2_27) + (145859472311/40000000000 : ℝ)*(f.failure) + (1515327343/160000000 : ℝ)*(f.sum) + (2316766872001634681/5889047230000000000000000000000 : ℝ)*base62 + (30082239132809/109010000000000000000000000 : ℝ)*base65 + (13277731894911/67528750000000000000000000 : ℝ)*base67 + (26009722869697/54505000000000000000000000 : ℝ)*base68 + (2104753433047388523/5959249670000000000000000000000 : ℝ)*base71 + (10299765363137/273335000000000000000000000 : ℝ)*base72 + (7623725780793/67528750000000000000000000 : ℝ)*base74 + (38740431215401/546670000000000000000000000 : ℝ)*base76 + (1119183738912555343/3691594176250000000000000000000 : ℝ)*base79 + (541/2000000000000000 : ℝ)*base87 + (541/2000000000000000 : ℝ)*base89 + (541/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3751/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3751/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (867257262700672901792175273/73831883525000000000000000000000 : ℝ) := by norm_num
    linear_combination (7732213177/125000000000 : ℝ)*(base40) + (97076178927/125000000000 : ℝ)*(base49) + (108687/20000000000 : ℝ)*(base59) + (397362430659/62500000000 : ℝ)*(major_s2_0) + (397362430659/62500000000 : ℝ)*(major_s2_1) + (397362430659/62500000000 : ℝ)*(major_s2_2) + (4365601/125000000000 : ℝ)*(sp_s2_0) + (34866307/1000000000000 : ℝ)*(sp_s2_2) + (11127409/200000000000 : ℝ)*(sp_s2_9) + (143588287/1000000000000 : ℝ)*(sp_s2_20) + (9180738416999/1000000000000 : ℝ)*(sp_s2_21) + (4590386670903/500000000000 : ℝ)*(sp_s2_22) + (1836136567691/200000000000 : ℝ)*(sp_s2_23) + (441834616941/125000000000 : ℝ)*(sp_s2_27) + (706964104763/200000000000 : ℝ)*(f.failure) + (4590386670903/500000000000 : ℝ)*(f.sum) + (8586671979330472961/36806545187500000000000000000000 : ℝ)*base63 + (8269283310527/21802000000000000000000000 : ℝ)*base64 + (3204584493055219/2701150000000000000000000000 : ℝ)*base66 + (68556512828169/340656250000000000000000000 : ℝ)*base68 + (25696392240388523737/29796248350000000000000000000000 : ℝ)*base71 + (890193596260311/1366675000000000000000000000 : ℝ)*base72 + (1852639485261687/2701150000000000000000000000 : ℝ)*base74 + (1274075820407613/2733350000000000000000000000 : ℝ)*base76 + (94212847011237542089/147663767050000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (1353/10000000000000000 : ℝ)*base87 + (1353/10000000000000000 : ℝ)*base89 + (1353/10000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((54667/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(54667/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(54023/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(54023/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10901/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10901/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((119/400 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(119/400 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30661/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30661/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3751/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3751/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c317055_s2 p hpa hpb X hX hprev1

#print axioms solution

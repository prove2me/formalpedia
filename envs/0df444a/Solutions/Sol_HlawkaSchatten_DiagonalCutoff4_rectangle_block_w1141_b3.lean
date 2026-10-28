-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1141_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:31:44.642197+00:00
-- url     : https://prove2.me/submissions/2f739a71-630f-4021-9b55-ed901ff80e86

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1141_s9_0 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167369593/10000000000 : ℝ)*x 0 + (337062517/625000000 : ℝ)*x 1 + (2632885741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167369593/10000000000 : ℝ)^4167 ≤ (658487756709/5000000000000 : ℝ)^3143 := by
    have hnat : (2167369593 : ℕ)^4167*5000000000000^3143 ≤ 658487756709^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167369593 10000000000 658487756709 5000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337062517/625000000 : ℝ)^4167 ≤ (44102163587043/100000000000000 : ℝ)^3143 := by
    have hnat : (337062517 : ℕ)^4167*100000000000000^3143 ≤ 44102163587043^3143*625000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337062517 625000000 44102163587043 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632885741/5000000000 : ℝ)^4167 ≤ (21364040636163/50000000000000 : ℝ)^3143 := by
    have hnat : (2632885741 : ℕ)^4167*50000000000000^3143 ≤ 21364040636163^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632885741 5000000000 21364040636163 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167369593/10000000000 : ℝ), (337062517/625000000 : ℝ), (2632885741/5000000000 : ℝ)] ![(658487756709/5000000000000 : ℝ), (44102163587043/100000000000000 : ℝ), (21364040636163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167369593/10000000000 : ℝ)|^4167 ≤ (658487756709/5000000000000 : ℝ)^3143
        have hw : |(-2167369593/10000000000 : ℝ)|=(2167369593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337062517/625000000 : ℝ)|^4167 ≤ (44102163587043/100000000000000 : ℝ)^3143
        have hw : |(337062517/625000000 : ℝ)|=(337062517/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632885741/5000000000 : ℝ)|^4167 ≤ (21364040636163/50000000000000 : ℝ)^3143
        have hw : |(2632885741/5000000000 : ℝ)|=(2632885741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s9_1 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672374251/5000000000 : ℝ)*x 0 + (-2231901761/10000000000 : ℝ)*x 1 + (164555357/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672374251/5000000000 : ℝ)^4167 ≤ (8715956583663/20000000000000 : ℝ)^3143 := by
    have hnat : (2672374251 : ℕ)^4167*20000000000000^3143 ≤ 8715956583663^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672374251 5000000000 8715956583663 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2231901761/10000000000 : ℝ)^4167 ≤ (13692136422291/100000000000000 : ℝ)^3143 := by
    have hnat : (2231901761 : ℕ)^4167*100000000000000^3143 ≤ 13692136422291^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231901761 10000000000 13692136422291 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164555357/312500000 : ℝ)^4167 ≤ (10682020162091/25000000000000 : ℝ)^3143 := by
    have hnat : (164555357 : ℕ)^4167*25000000000000^3143 ≤ 10682020162091^3143*312500000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164555357 312500000 10682020162091 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672374251/5000000000 : ℝ), (-2231901761/10000000000 : ℝ), (164555357/312500000 : ℝ)] ![(8715956583663/20000000000000 : ℝ), (13692136422291/100000000000000 : ℝ), (10682020162091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672374251/5000000000 : ℝ)|^4167 ≤ (8715956583663/20000000000000 : ℝ)^3143
        have hw : |(2672374251/5000000000 : ℝ)|=(2672374251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2231901761/10000000000 : ℝ)|^4167 ≤ (13692136422291/100000000000000 : ℝ)^3143
        have hw : |(-2231901761/10000000000 : ℝ)|=(2231901761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164555357/312500000 : ℝ)|^4167 ≤ (10682020162091/25000000000000 : ℝ)^3143
        have hw : |(164555357/312500000 : ℝ)|=(164555357/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s9_2 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344748429/10000000000 : ℝ)*x 0 + (5265771469/10000000000 : ℝ)*x 1 + (-1115950899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344748429/10000000000 : ℝ)^4167 ≤ (10894945532291/25000000000000 : ℝ)^3143 := by
    have hnat : (5344748429 : ℕ)^4167*25000000000000^3143 ≤ 10894945532291^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344748429 10000000000 10894945532291 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265771469/10000000000 : ℝ)^4167 ≤ (42728081132473/100000000000000 : ℝ)^3143 := by
    have hnat : (5265771469 : ℕ)^4167*100000000000000^3143 ≤ 42728081132473^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265771469 10000000000 42728081132473 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115950899/5000000000 : ℝ)^4167 ≤ (13692136723229/100000000000000 : ℝ)^3143 := by
    have hnat : (1115950899 : ℕ)^4167*100000000000000^3143 ≤ 13692136723229^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115950899 5000000000 13692136723229 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344748429/10000000000 : ℝ), (5265771469/10000000000 : ℝ), (-1115950899/5000000000 : ℝ)] ![(10894945532291/25000000000000 : ℝ), (42728081132473/100000000000000 : ℝ), (13692136723229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344748429/10000000000 : ℝ)|^4167 ≤ (10894945532291/25000000000000 : ℝ)^3143
        have hw : |(5344748429/10000000000 : ℝ)|=(5344748429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265771469/10000000000 : ℝ)|^4167 ≤ (42728081132473/100000000000000 : ℝ)^3143
        have hw : |(5265771469/10000000000 : ℝ)|=(5265771469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1115950899/5000000000 : ℝ)|^4167 ≤ (13692136723229/100000000000000 : ℝ)^3143
        have hw : |(-1115950899/5000000000 : ℝ)|=(1115950899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s9_3 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4364816533/10000000000 : ℝ)*x 0 + (4240107599/10000000000 : ℝ)*x 1 + (4493176557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364816533/10000000000 : ℝ)^4167 ≤ (4164623190687/12500000000000 : ℝ)^3143 := by
    have hnat : (4364816533 : ℕ)^4167*12500000000000^3143 ≤ 4164623190687^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364816533 10000000000 4164623190687 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4240107599/10000000000 : ℝ)^4167 ≤ (32060848183671/100000000000000 : ℝ)^3143 := by
    have hnat : (4240107599 : ℕ)^4167*100000000000000^3143 ≤ 32060848183671^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240107599 10000000000 32060848183671 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493176557/10000000000 : ℝ)^4167 ≤ (34622166269201/100000000000000 : ℝ)^3143 := by
    have hnat : (4493176557 : ℕ)^4167*100000000000000^3143 ≤ 34622166269201^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493176557 10000000000 34622166269201 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364816533/10000000000 : ℝ), (4240107599/10000000000 : ℝ), (4493176557/10000000000 : ℝ)] ![(4164623190687/12500000000000 : ℝ), (32060848183671/100000000000000 : ℝ), (34622166269201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364816533/10000000000 : ℝ)|^4167 ≤ (4164623190687/12500000000000 : ℝ)^3143
        have hw : |(4364816533/10000000000 : ℝ)|=(4364816533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4240107599/10000000000 : ℝ)|^4167 ≤ (32060848183671/100000000000000 : ℝ)^3143
        have hw : |(4240107599/10000000000 : ℝ)|=(4240107599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493176557/10000000000 : ℝ)|^4167 ≤ (34622166269201/100000000000000 : ℝ)^3143
        have hw : |(4493176557/10000000000 : ℝ)|=(4493176557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s9_4 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167374483/10000000000 : ℝ)*x 0 + (2633045533/5000000000 : ℝ)*x 1 + (1348169881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167374483/10000000000 : ℝ)^4167 ≤ (823112158027/6250000000000 : ℝ)^3143 := by
    have hnat : (2167374483 : ℕ)^4167*6250000000000^3143 ≤ 823112158027^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167374483 10000000000 823112158027 6250000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633045533/5000000000 : ℝ)^4167 ≤ (21365759691387/50000000000000 : ℝ)^3143 := by
    have hnat : (2633045533 : ℕ)^4167*50000000000000^3143 ≤ 21365759691387^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633045533 5000000000 21365759691387 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348169881/2500000000 : ℝ)^4167 ≤ (8819737215513/20000000000000 : ℝ)^3143 := by
    have hnat : (1348169881 : ℕ)^4167*20000000000000^3143 ≤ 8819737215513^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348169881 2500000000 8819737215513 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167374483/10000000000 : ℝ), (2633045533/5000000000 : ℝ), (1348169881/2500000000 : ℝ)] ![(823112158027/6250000000000 : ℝ), (21365759691387/50000000000000 : ℝ), (8819737215513/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167374483/10000000000 : ℝ)|^4167 ≤ (823112158027/6250000000000 : ℝ)^3143
        have hw : |(-2167374483/10000000000 : ℝ)|=(2167374483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633045533/5000000000 : ℝ)|^4167 ≤ (21365759691387/50000000000000 : ℝ)^3143
        have hw : |(2633045533/5000000000 : ℝ)|=(2633045533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348169881/2500000000 : ℝ)|^4167 ≤ (8819737215513/20000000000000 : ℝ)^3143
        have hw : |(1348169881/2500000000 : ℝ)|=(1348169881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s9_5 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4364826141/10000000000 : ℝ)*x 0 + (1123135313/2500000000 : ℝ)*x 1 + (530093161/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364826141/10000000000 : ℝ)^4167 ≤ (16658541379057/50000000000000 : ℝ)^3143 := by
    have hnat : (4364826141 : ℕ)^4167*50000000000000^3143 ≤ 16658541379057^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364826141 10000000000 16658541379057 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123135313/2500000000 : ℝ)^4167 ≤ (8653919039483/25000000000000 : ℝ)^3143 := by
    have hnat : (1123135313 : ℕ)^4167*25000000000000^3143 ≤ 8653919039483^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123135313 2500000000 8653919039483 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530093161/1250000000 : ℝ)^4167 ≤ (3206724106753/10000000000000 : ℝ)^3143 := by
    have hnat : (530093161 : ℕ)^4167*10000000000000^3143 ≤ 3206724106753^3143*1250000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530093161 1250000000 3206724106753 10000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364826141/10000000000 : ℝ), (1123135313/2500000000 : ℝ), (530093161/1250000000 : ℝ)] ![(16658541379057/50000000000000 : ℝ), (8653919039483/25000000000000 : ℝ), (3206724106753/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364826141/10000000000 : ℝ)|^4167 ≤ (16658541379057/50000000000000 : ℝ)^3143
        have hw : |(4364826141/10000000000 : ℝ)|=(4364826141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123135313/2500000000 : ℝ)|^4167 ≤ (8653919039483/25000000000000 : ℝ)^3143
        have hw : |(1123135313/2500000000 : ℝ)|=(1123135313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530093161/1250000000 : ℝ)|^4167 ≤ (3206724106753/10000000000000 : ℝ)^3143
        have hw : |(530093161/1250000000 : ℝ)|=(530093161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1141_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11353/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (439/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1419/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1419/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1419/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1419/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1419/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1419/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (1419/12500 : ℝ) ^ (8333/2048 : ℝ) ≤ (14296623426716087/100000000000000000000 : ℝ) := by
    have hpowers : (1419/12500 : ℝ)^8333 ≤ (14296623426716087/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1419 : ℕ)^8333*100000000000000000000^2048 ≤ 14296623426716087^2048*12500^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1419 12500 14296623426716087 100000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1419/12500 : ℝ)) (X := (14296623426716087/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (439/3125 : ℝ) ^ (8333/2048 : ℝ) ≤ (34023050537033721/100000000000000000000 : ℝ) := by
    have hpowers : (439/3125 : ℝ)^8333 ≤ (34023050537033721/100000000000000000000 : ℝ)^2048 := by
      have hnat : (439 : ℕ)^8333*100000000000000000000^2048 ≤ 34023050537033721^2048*3125^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        439 3125 34023050537033721 100000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (439/3125 : ℝ)) (X := (34023050537033721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014296623426716087/50000000000000000000 : ℝ) ≤ (250017566499529/250000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (50014296623426716087/50000000000000000000 : ℝ)^2048 ≤ (250017566499529/250000000000000 : ℝ)^8333 := by
      have hnat : (50014296623426716087 : ℕ)^2048*250000000000000^8333 ≤ 250017566499529^8333*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014296623426716087 50000000000000000000 250017566499529 250000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250017566499529/250000000000000 : ℝ)) (X := (50014296623426716087/50000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253019979622734363/6250000000000000000 : ℝ) ≤ (10001187335473911/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (6253019979622734363/6250000000000000000 : ℝ)^2048 ≤ (10001187335473911/10000000000000000 : ℝ)^8333 := by
      have hnat : (6253019979622734363 : ℕ)^2048*10000000000000000^8333 ≤ 10001187335473911^8333*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253019979622734363 6250000000000000000 10001187335473911 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001187335473911/10000000000000000 : ℝ)) (X := (6253019979622734363/6250000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034023050537033721/50000000000000000000 : ℝ) ≤ (5000836005483331/5000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (50034023050537033721/50000000000000000000 : ℝ)^2048 ≤ (5000836005483331/5000000000000000 : ℝ)^8333 := by
      have hnat : (50034023050537033721 : ℕ)^2048*5000000000000000^8333 ≤ 5000836005483331^8333*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034023050537033721 50000000000000000000 5000836005483331 5000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000836005483331/5000000000000000 : ℝ)) (X := (50034023050537033721/50000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14296623426716087/100000000000000000000 : ℝ) ≤ ((1684430643682611791/1685000000000000000 : ℝ)+2*(484675492751/269600000000000 : ℝ)*(1419/12500 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (1684430643682611791/1685000000000000000 : ℝ)+2*(484675492751/269600000000000 : ℝ)*(1419/12500 : ℝ)=(250017566499529/250000000000000 : ℝ) by norm_num, show 1+2*(14296623426716087/100000000000000000000 : ℝ)=(50014296623426716087/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34023050537033721/100000000000000000000 : ℝ)+(14296623426716087/100000000000000000000 : ℝ) ≤ ((1684430643682611791/1685000000000000000 : ℝ)+(484675492751/269600000000000 : ℝ)*((439/3125 : ℝ)+(1419/12500 : ℝ)))^(8333/2048 : ℝ) := by
    rw [show (1684430643682611791/1685000000000000000 : ℝ)+(484675492751/269600000000000 : ℝ)*((439/3125 : ℝ)+(1419/12500 : ℝ))=(10001187335473911/10000000000000000 : ℝ) by norm_num, show 1+(34023050537033721/100000000000000000000 : ℝ)+(14296623426716087/100000000000000000000 : ℝ)=(6253019979622734363/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34023050537033721/100000000000000000000 : ℝ) ≤ ((1684430643682611791/1685000000000000000 : ℝ)+2*(484675492751/269600000000000 : ℝ)*(439/3125 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (1684430643682611791/1685000000000000000 : ℝ)+2*(484675492751/269600000000000 : ℝ)*(439/3125 : ℝ)=(5000836005483331/5000000000000000 : ℝ) by norm_num, show 1+2*(34023050537033721/100000000000000000000 : ℝ)=(50034023050537033721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1684430643682611791/1685000000000000000 : ℝ)*(X 1 0+X 2 0)+(484675492751/269600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (1419/12500 : ℝ)) (hi := (439/3125 : ℝ)) (c := (1684430643682611791/1685000000000000000 : ℝ)) (alpha := (484675492751/269600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1684430643682611791/1685000000000000000 : ℝ)*(X 0 1+X 2 1)+(484675492751/269600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (1419/12500 : ℝ)) (hi := (439/3125 : ℝ)) (c := (1684430643682611791/1685000000000000000 : ℝ)) (alpha := (484675492751/269600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1684430643682611791/1685000000000000000 : ℝ)*(X 0 2+X 1 2)+(484675492751/269600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (1419/12500 : ℝ)) (hi := (439/3125 : ℝ)) (c := (1684430643682611791/1685000000000000000 : ℝ)) (alpha := (484675492751/269600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2167369593/10000000000 : ℝ)*X 0 0+(337062517/625000000 : ℝ)*X 0 1+(2632885741/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672374251/5000000000 : ℝ)*X 1 0+(-2231901761/10000000000 : ℝ)*X 1 1+(164555357/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344748429/10000000000 : ℝ)*X 2 0+(5265771469/10000000000 : ℝ)*X 2 1+(-1115950899/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364816533/10000000000 : ℝ)*X 0 0+(4240107599/10000000000 : ℝ)*X 0 1+(4493176557/10000000000 : ℝ)*X 0 2+(4364816533/10000000000 : ℝ)*X 1 0+(4240107599/10000000000 : ℝ)*X 1 1+(4493176557/10000000000 : ℝ)*X 1 2+(4364816533/10000000000 : ℝ)*X 2 0+(4240107599/10000000000 : ℝ)*X 2 1+(4493176557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2167374483/10000000000 : ℝ)*X 0 0+(2633045533/5000000000 : ℝ)*X 0 1+(1348169881/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4364826141/10000000000 : ℝ)*X 0 0+(1123135313/2500000000 : ℝ)*X 0 1+(530093161/1250000000 : ℝ)*X 0 2+(4364826141/10000000000 : ℝ)*X 1 0+(1123135313/2500000000 : ℝ)*X 1 1+(530093161/1250000000 : ℝ)*X 1 2+(4364826141/10000000000 : ℝ)*X 2 0+(1123135313/2500000000 : ℝ)*X 2 1+(530093161/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3731138698204499771025237/1053125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (812618131/100000000000000 : ℝ)*(base19) + (165273119/25000000000000 : ℝ)*(base23) + (11804709/50000000000000 : ℝ)*(lower2) + (5057561/4000000000000 : ℝ)*(upper3) + (14066201/100000000000000 : ℝ)*(upper5) + (36910659844139/625000000000 : ℝ)*(major0) + (36910659844139/625000000000 : ℝ)*(major1) + (36910659844139/625000000000 : ℝ)*(major2) + (7859878896641801/100000000000000 : ℝ)*(sp0) + (1964973710763601/25000000000000 : ℝ)*(sp1) + (392994749729003/5000000000000 : ℝ)*(sp2) + (246968922007057/6250000000000 : ℝ)*(sp3) + (3351806147/20000000000000 : ℝ)*(sp4) + (12624241651/100000000000000 : ℝ)*(sp5) + (1975757688177281/50000000000000 : ℝ)*(f.failure) + (1571979131134507/20000000000000 : ℝ)*(f.sum) + (1984124685963/337000000000000000000000000 : ℝ)*base65 + (10322447358217949/1053125000000000000000000000000 : ℝ)*base67 + (411598590830449/1053125000000000000000000000000 : ℝ)*base69 + (4012259722444331/263281250000000000000000000000 : ℝ)*base71 + (135053479849/84250000000000000000000000 : ℝ)*base74 + (3081836969149199/1053125000000000000000000000000 : ℝ)*base75 + (911377076814353/131640625000000000000000000000 : ℝ)*base77 + (9162286840050801/1053125000000000000000000000000 : ℝ)*base80 + (84573911013/84250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (74501643/5000000000000000000000 : ℝ)*base90 + (74501643/5000000000000000000000 : ℝ)*base92 + (74501643/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1141_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11353/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1141_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1141_box_0 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-8161757/40000000 : ℝ)*x 0 + (5376324703/10000000000 : ℝ)*x 1 + (672040609/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8161757/40000000 : ℝ)^4167 ≤ (3039270264721/25000000000000 : ℝ)^3143 := by
    have hnat : (8161757 : ℕ)^4167*25000000000000^3143 ≤ 3039270264721^3143*40000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8161757 40000000 3039270264721 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376324703/10000000000 : ℝ)^4167 ≤ (43921458544619/100000000000000 : ℝ)^3143 := by
    have hnat : (5376324703 : ℕ)^4167*100000000000000^3143 ≤ 43921458544619^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376324703 10000000000 43921458544619 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672040609/1250000000 : ℝ)^4167 ≤ (21960730187533/50000000000000 : ℝ)^3143 := by
    have hnat : (672040609 : ℕ)^4167*50000000000000^3143 ≤ 21960730187533^3143*1250000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672040609 1250000000 21960730187533 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8161757/40000000 : ℝ), (5376324703/10000000000 : ℝ), (672040609/1250000000 : ℝ)] ![(3039270264721/25000000000000 : ℝ), (43921458544619/100000000000000 : ℝ), (21960730187533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8161757/40000000 : ℝ)|^4167 ≤ (3039270264721/25000000000000 : ℝ)^3143
        have hw : |(-8161757/40000000 : ℝ)|=(8161757/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376324703/10000000000 : ℝ)|^4167 ≤ (43921458544619/100000000000000 : ℝ)^3143
        have hw : |(5376324703/10000000000 : ℝ)|=(5376324703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672040609/1250000000 : ℝ)|^4167 ≤ (21960730187533/50000000000000 : ℝ)^3143
        have hw : |(672040609/1250000000 : ℝ)|=(672040609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_box_1 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059195179/2000000000 : ℝ)*x 0 + (-268675471/1250000000 : ℝ)*x 1 + (2688162437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059195179/2000000000 : ℝ)^4167 ≤ (43053322803713/100000000000000 : ℝ)^3143 := by
    have hnat : (1059195179 : ℕ)^4167*100000000000000^3143 ≤ 43053322803713^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059195179 2000000000 43053322803713 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268675471/1250000000 : ℝ)^4167 ≤ (2605043358093/20000000000000 : ℝ)^3143 := by
    have hnat : (268675471 : ℕ)^4167*20000000000000^3143 ≤ 2605043358093^3143*1250000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268675471 1250000000 2605043358093 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688162437/5000000000 : ℝ)^4167 ≤ (5490182549591/12500000000000 : ℝ)^3143 := by
    have hnat : (2688162437 : ℕ)^4167*12500000000000^3143 ≤ 5490182549591^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688162437 5000000000 5490182549591 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059195179/2000000000 : ℝ), (-268675471/1250000000 : ℝ), (2688162437/5000000000 : ℝ)] ![(43053322803713/100000000000000 : ℝ), (2605043358093/20000000000000 : ℝ), (5490182549591/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059195179/2000000000 : ℝ)|^4167 ≤ (43053322803713/100000000000000 : ℝ)^3143
        have hw : |(1059195179/2000000000 : ℝ)|=(1059195179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-268675471/1250000000 : ℝ)|^4167 ≤ (2605043358093/20000000000000 : ℝ)^3143
        have hw : |(-268675471/1250000000 : ℝ)|=(268675471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688162437/5000000000 : ℝ)|^4167 ≤ (5490182549591/12500000000000 : ℝ)^3143
        have hw : |(2688162437/5000000000 : ℝ)|=(2688162437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_box_2 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647988179/5000000000 : ℝ)*x 0 + (672040581/1250000000 : ℝ)*x 1 + (-2149403451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647988179/5000000000 : ℝ)^4167 ≤ (8610665558789/20000000000000 : ℝ)^3143 := by
    have hnat : (2647988179 : ℕ)^4167*20000000000000^3143 ≤ 8610665558789^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647988179 5000000000 8610665558789 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672040581/1250000000 : ℝ)^4167 ≤ (43921457948911/100000000000000 : ℝ)^3143 := by
    have hnat : (672040581 : ℕ)^4167*100000000000000^3143 ≤ 43921457948911^3143*1250000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672040581 1250000000 43921457948911 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2149403451/10000000000 : ℝ)^4167 ≤ (3256303560901/25000000000000 : ℝ)^3143 := by
    have hnat : (2149403451 : ℕ)^4167*25000000000000^3143 ≤ 3256303560901^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149403451 10000000000 3256303560901 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647988179/5000000000 : ℝ), (672040581/1250000000 : ℝ), (-2149403451/10000000000 : ℝ)] ![(8610665558789/20000000000000 : ℝ), (43921457948911/100000000000000 : ℝ), (3256303560901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647988179/5000000000 : ℝ)|^4167 ≤ (8610665558789/20000000000000 : ℝ)^3143
        have hw : |(2647988179/5000000000 : ℝ)|=(2647988179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672040581/1250000000 : ℝ)|^4167 ≤ (43921457948911/100000000000000 : ℝ)^3143
        have hw : |(672040581/1250000000 : ℝ)|=(672040581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2149403451/10000000000 : ℝ)|^4167 ≤ (3256303560901/25000000000000 : ℝ)^3143
        have hw : |(-2149403451/10000000000 : ℝ)|=(2149403451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_box_3 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (279523251/625000000 : ℝ)*x 0 + (6739293/15625000 : ℝ)*x 1 + (862629417/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279523251/625000000 : ℝ)^4167 ≤ (215061175333/625000000000 : ℝ)^3143 := by
    have hnat : (279523251 : ℕ)^4167*625000000000^3143 ≤ 215061175333^3143*625000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279523251 625000000 215061175333 625000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6739293/15625000 : ℝ)^4167 ≤ (4099388520151/12500000000000 : ℝ)^3143 := by
    have hnat : (6739293 : ℕ)^4167*12500000000000^3143 ≤ 4099388520151^3143*15625000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6739293 15625000 4099388520151 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (862629417/2000000000 : ℝ)^4167 ≤ (4099387972009/12500000000000 : ℝ)^3143 := by
    have hnat : (862629417 : ℕ)^4167*12500000000000^3143 ≤ 4099387972009^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862629417 2000000000 4099387972009 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(279523251/625000000 : ℝ), (6739293/15625000 : ℝ), (862629417/2000000000 : ℝ)] ![(215061175333/625000000000 : ℝ), (4099388520151/12500000000000 : ℝ), (4099387972009/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(279523251/625000000 : ℝ)|^4167 ≤ (215061175333/625000000000 : ℝ)^3143
        have hw : |(279523251/625000000 : ℝ)|=(279523251/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6739293/15625000 : ℝ)|^4167 ≤ (4099388520151/12500000000000 : ℝ)^3143
        have hw : |(6739293/15625000 : ℝ)|=(6739293/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(862629417/2000000000 : ℝ)|^4167 ≤ (4099387972009/12500000000000 : ℝ)^3143
        have hw : |(862629417/2000000000 : ℝ)|=(862629417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_box_4 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2295677329/10000000000 : ℝ)*x 0 + (2640564349/5000000000 : ℝ)*x 1 + (5281129061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2295677329/10000000000 : ℝ)^4167 ≤ (1776656448001/12500000000000 : ℝ)^3143 := by
    have hnat : (2295677329 : ℕ)^4167*12500000000000^3143 ≤ 1776656448001^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295677329 10000000000 1776656448001 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640564349/5000000000 : ℝ)^4167 ≤ (42893372246793/100000000000000 : ℝ)^3143 := by
    have hnat : (2640564349 : ℕ)^4167*100000000000000^3143 ≤ 42893372246793^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640564349 5000000000 42893372246793 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281129061/10000000000 : ℝ)^4167 ≤ (8578675231129/20000000000000 : ℝ)^3143 := by
    have hnat : (5281129061 : ℕ)^4167*20000000000000^3143 ≤ 8578675231129^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281129061 10000000000 8578675231129 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2295677329/10000000000 : ℝ), (2640564349/5000000000 : ℝ), (5281129061/10000000000 : ℝ)] ![(1776656448001/12500000000000 : ℝ), (42893372246793/100000000000000 : ℝ), (8578675231129/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2295677329/10000000000 : ℝ)|^4167 ≤ (1776656448001/12500000000000 : ℝ)^3143
        have hw : |(-2295677329/10000000000 : ℝ)|=(2295677329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640564349/5000000000 : ℝ)|^4167 ≤ (42893372246793/100000000000000 : ℝ)^3143
        have hw : |(2640564349/5000000000 : ℝ)|=(2640564349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281129061/10000000000 : ℝ)|^4167 ≤ (8578675231129/20000000000000 : ℝ)^3143
        have hw : |(5281129061/10000000000 : ℝ)|=(5281129061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_box_5 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681616853/5000000000 : ℝ)*x 0 + (-2186847951/10000000000 : ℝ)*x 1 + (1056225711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681616853/5000000000 : ℝ)^4167 ≤ (43779725631713/100000000000000 : ℝ)^3143 := by
    have hnat : (2681616853 : ℕ)^4167*100000000000000^3143 ≤ 43779725631713^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681616853 5000000000 43779725631713 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2186847951/10000000000 : ℝ)^4167 ≤ (6663451820249/50000000000000 : ℝ)^3143 := by
    have hnat : (2186847951 : ℕ)^4167*50000000000000^3143 ≤ 6663451820249^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186847951 10000000000 6663451820249 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056225711/2000000000 : ℝ)^4167 ≤ (42893370706943/100000000000000 : ℝ)^3143 := by
    have hnat : (1056225711 : ℕ)^4167*100000000000000^3143 ≤ 42893370706943^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056225711 2000000000 42893370706943 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681616853/5000000000 : ℝ), (-2186847951/10000000000 : ℝ), (1056225711/2000000000 : ℝ)] ![(43779725631713/100000000000000 : ℝ), (6663451820249/50000000000000 : ℝ), (42893370706943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681616853/5000000000 : ℝ)|^4167 ≤ (43779725631713/100000000000000 : ℝ)^3143
        have hw : |(2681616853/5000000000 : ℝ)|=(2681616853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2186847951/10000000000 : ℝ)|^4167 ≤ (6663451820249/50000000000000 : ℝ)^3143
        have hw : |(-2186847951/10000000000 : ℝ)|=(2186847951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056225711/2000000000 : ℝ)|^4167 ≤ (42893370706943/100000000000000 : ℝ)^3143
        have hw : |(1056225711/2000000000 : ℝ)|=(1056225711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_box_6 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681616691/5000000000 : ℝ)*x 0 + (211245143/400000000 : ℝ)*x 1 + (-2186848359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681616691/5000000000 : ℝ)^4167 ≤ (1094493053131/2500000000000 : ℝ)^3143 := by
    have hnat : (2681616691 : ℕ)^4167*2500000000000^3143 ≤ 1094493053131^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681616691 5000000000 1094493053131 2500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211245143/400000000 : ℝ)^4167 ≤ (21446685461153/50000000000000 : ℝ)^3143 := by
    have hnat : (211245143 : ℕ)^4167*50000000000000^3143 ≤ 21446685461153^3143*400000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211245143 400000000 21446685461153 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2186848359/10000000000 : ℝ)^4167 ≤ (6663453468487/50000000000000 : ℝ)^3143 := by
    have hnat : (2186848359 : ℕ)^4167*50000000000000^3143 ≤ 6663453468487^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186848359 10000000000 6663453468487 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681616691/5000000000 : ℝ), (211245143/400000000 : ℝ), (-2186848359/10000000000 : ℝ)] ![(1094493053131/2500000000000 : ℝ), (21446685461153/50000000000000 : ℝ), (6663453468487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681616691/5000000000 : ℝ)|^4167 ≤ (1094493053131/2500000000000 : ℝ)^3143
        have hw : |(2681616691/5000000000 : ℝ)|=(2681616691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211245143/400000000 : ℝ)|^4167 ≤ (21446685461153/50000000000000 : ℝ)^3143
        have hw : |(211245143/400000000 : ℝ)|=(211245143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2186848359/10000000000 : ℝ)|^4167 ≤ (6663453468487/50000000000000 : ℝ)^3143
        have hw : |(-2186848359/10000000000 : ℝ)|=(2186848359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_box_7 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1064225019/2500000000 : ℝ)*x 0 + (1105215597/2500000000 : ℝ)*x 1 + (4420862463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064225019/2500000000 : ℝ)^4167 ≤ (8057324627759/25000000000000 : ℝ)^3143 := by
    have hnat : (1064225019 : ℕ)^4167*25000000000000^3143 ≤ 8057324627759^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064225019 2500000000 8057324627759 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105215597/2500000000 : ℝ)^4167 ≤ (16942675177299/50000000000000 : ℝ)^3143 := by
    have hnat : (1105215597 : ℕ)^4167*50000000000000^3143 ≤ 16942675177299^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105215597 2500000000 16942675177299 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4420862463/10000000000 : ℝ)^4167 ≤ (33885351116757/100000000000000 : ℝ)^3143 := by
    have hnat : (4420862463 : ℕ)^4167*100000000000000^3143 ≤ 33885351116757^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4420862463 10000000000 33885351116757 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1064225019/2500000000 : ℝ), (1105215597/2500000000 : ℝ), (4420862463/10000000000 : ℝ)] ![(8057324627759/25000000000000 : ℝ), (16942675177299/50000000000000 : ℝ), (33885351116757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1064225019/2500000000 : ℝ)|^4167 ≤ (8057324627759/25000000000000 : ℝ)^3143
        have hw : |(1064225019/2500000000 : ℝ)|=(1064225019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1105215597/2500000000 : ℝ)|^4167 ≤ (16942675177299/50000000000000 : ℝ)^3143
        have hw : |(1105215597/2500000000 : ℝ)|=(1105215597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4420862463/10000000000 : ℝ)|^4167 ≤ (33885351116757/100000000000000 : ℝ)^3143
        have hw : |(4420862463/10000000000 : ℝ)|=(4420862463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_box_8 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-448460879/2000000000 : ℝ)*x 0 + (5216387977/10000000000 : ℝ)*x 1 + (168310421/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448460879/2000000000 : ℝ)^4167 ≤ (1722101248683/12500000000000 : ℝ)^3143 := by
    have hnat : (448460879 : ℕ)^4167*12500000000000^3143 ≤ 1722101248683^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448460879 2000000000 1722101248683 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216387977/10000000000 : ℝ)^4167 ≤ (10549407035457/25000000000000 : ℝ)^3143 := by
    have hnat : (5216387977 : ℕ)^4167*25000000000000^3143 ≤ 10549407035457^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216387977 10000000000 10549407035457 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168310421/312500000 : ℝ)^4167 ≤ (44025561847619/100000000000000 : ℝ)^3143 := by
    have hnat : (168310421 : ℕ)^4167*100000000000000^3143 ≤ 44025561847619^3143*312500000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168310421 312500000 44025561847619 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-448460879/2000000000 : ℝ), (5216387977/10000000000 : ℝ), (168310421/312500000 : ℝ)] ![(1722101248683/12500000000000 : ℝ), (10549407035457/25000000000000 : ℝ), (44025561847619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-448460879/2000000000 : ℝ)|^4167 ≤ (1722101248683/12500000000000 : ℝ)^3143
        have hw : |(-448460879/2000000000 : ℝ)|=(448460879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216387977/10000000000 : ℝ)|^4167 ≤ (10549407035457/25000000000000 : ℝ)^3143
        have hw : |(5216387977/10000000000 : ℝ)|=(5216387977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168310421/312500000 : ℝ)|^4167 ≤ (44025561847619/100000000000000 : ℝ)^3143
        have hw : |(168310421/312500000 : ℝ)|=(168310421/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_box_9 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644592051/5000000000 : ℝ)*x 0 + (-1072777431/5000000000 : ℝ)*x 1 + (5385933431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644592051/5000000000 : ℝ)^4167 ≤ (42980135883651/100000000000000 : ℝ)^3143 := by
    have hnat : (2644592051 : ℕ)^4167*100000000000000^3143 ≤ 42980135883651^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644592051 5000000000 42980135883651 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072777431/5000000000 : ℝ)^4167 ≤ (6497151344681/50000000000000 : ℝ)^3143 := by
    have hnat : (1072777431 : ℕ)^4167*50000000000000^3143 ≤ 6497151344681^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072777431 5000000000 6497151344681 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385933431/10000000000 : ℝ)^4167 ≤ (5503195175411/12500000000000 : ℝ)^3143 := by
    have hnat : (5385933431 : ℕ)^4167*12500000000000^3143 ≤ 5503195175411^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385933431 10000000000 5503195175411 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644592051/5000000000 : ℝ), (-1072777431/5000000000 : ℝ), (5385933431/10000000000 : ℝ)] ![(42980135883651/100000000000000 : ℝ), (6497151344681/50000000000000 : ℝ), (5503195175411/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644592051/5000000000 : ℝ)|^4167 ≤ (42980135883651/100000000000000 : ℝ)^3143
        have hw : |(2644592051/5000000000 : ℝ)|=(2644592051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1072777431/5000000000 : ℝ)|^4167 ≤ (6497151344681/50000000000000 : ℝ)^3143
        have hw : |(-1072777431/5000000000 : ℝ)|=(1072777431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385933431/10000000000 : ℝ)|^4167 ≤ (5503195175411/12500000000000 : ℝ)^3143
        have hw : |(5385933431/10000000000 : ℝ)|=(5385933431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_box_10 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057836801/2000000000 : ℝ)*x 0 + (5385933381/10000000000 : ℝ)*x 1 + (-107277753/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057836801/2000000000 : ℝ)^4167 ≤ (21490067419309/50000000000000 : ℝ)^3143 := by
    have hnat : (1057836801 : ℕ)^4167*50000000000000^3143 ≤ 21490067419309^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057836801 2000000000 21490067419309 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385933381/10000000000 : ℝ)^4167 ≤ (2201278043071/5000000000000 : ℝ)^3143 := by
    have hnat : (5385933381 : ℕ)^4167*5000000000000^3143 ≤ 2201278043071^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385933381 10000000000 2201278043071 5000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107277753/500000000 : ℝ)^4167 ≤ (6497152139609/50000000000000 : ℝ)^3143 := by
    have hnat : (107277753 : ℕ)^4167*50000000000000^3143 ≤ 6497152139609^3143*500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107277753 500000000 6497152139609 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057836801/2000000000 : ℝ), (5385933381/10000000000 : ℝ), (-107277753/500000000 : ℝ)] ![(21490067419309/50000000000000 : ℝ), (2201278043071/5000000000000 : ℝ), (6497152139609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057836801/2000000000 : ℝ)|^4167 ≤ (21490067419309/50000000000000 : ℝ)^3143
        have hw : |(1057836801/2000000000 : ℝ)|=(1057836801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385933381/10000000000 : ℝ)|^4167 ≤ (2201278043071/5000000000000 : ℝ)^3143
        have hw : |(5385933381/10000000000 : ℝ)|=(5385933381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-107277753/500000000 : ℝ)|^4167 ≤ (6497152139609/50000000000000 : ℝ)^3143
        have hw : |(-107277753/500000000 : ℝ)|=(107277753/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_box_11 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (224692381/500000000 : ℝ)*x 0 + (4302268947/10000000000 : ℝ)*x 1 + (4302268983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224692381/500000000 : ℝ)^4167 ≤ (34629021999631/100000000000000 : ℝ)^3143 := by
    have hnat : (224692381 : ℕ)^4167*100000000000000^3143 ≤ 34629021999631^3143*500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224692381 500000000 34629021999631 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4302268947/10000000000 : ℝ)^4167 ≤ (817137220239/2500000000000 : ℝ)^3143 := by
    have hnat : (4302268947 : ℕ)^4167*2500000000000^3143 ≤ 817137220239^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302268947 10000000000 817137220239 2500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4302268983/10000000000 : ℝ)^4167 ≤ (32685489172169/100000000000000 : ℝ)^3143 := by
    have hnat : (4302268983 : ℕ)^4167*100000000000000^3143 ≤ 32685489172169^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302268983 10000000000 32685489172169 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(224692381/500000000 : ℝ), (4302268947/10000000000 : ℝ), (4302268983/10000000000 : ℝ)] ![(34629021999631/100000000000000 : ℝ), (817137220239/2500000000000 : ℝ), (32685489172169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(224692381/500000000 : ℝ)|^4167 ≤ (34629021999631/100000000000000 : ℝ)^3143
        have hw : |(224692381/500000000 : ℝ)|=(224692381/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4302268947/10000000000 : ℝ)|^4167 ≤ (817137220239/2500000000000 : ℝ)^3143
        have hw : |(4302268947/10000000000 : ℝ)|=(4302268947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4302268983/10000000000 : ℝ)|^4167 ≤ (32685489172169/100000000000000 : ℝ)^3143
        have hw : |(4302268983/10000000000 : ℝ)|=(4302268983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_box_12 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2094132227/10000000000 : ℝ)*x 0 + (543978697/1000000000 : ℝ)*x 1 + (2636545337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094132227/10000000000 : ℝ)^4167 ≤ (12583021718269/100000000000000 : ℝ)^3143 := by
    have hnat : (2094132227 : ℕ)^4167*100000000000000^3143 ≤ 12583021718269^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094132227 10000000000 12583021718269 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543978697/1000000000 : ℝ)^4167 ≤ (8922027897643/20000000000000 : ℝ)^3143 := by
    have hnat : (543978697 : ℕ)^4167*20000000000000^3143 ≤ 8922027897643^3143*1000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543978697 1000000000 8922027897643 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636545337/5000000000 : ℝ)^4167 ≤ (8561367754979/20000000000000 : ℝ)^3143 := by
    have hnat : (2636545337 : ℕ)^4167*20000000000000^3143 ≤ 8561367754979^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636545337 5000000000 8561367754979 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2094132227/10000000000 : ℝ), (543978697/1000000000 : ℝ), (2636545337/5000000000 : ℝ)] ![(12583021718269/100000000000000 : ℝ), (8922027897643/20000000000000 : ℝ), (8561367754979/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2094132227/10000000000 : ℝ)|^4167 ≤ (12583021718269/100000000000000 : ℝ)^3143
        have hw : |(-2094132227/10000000000 : ℝ)|=(2094132227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543978697/1000000000 : ℝ)|^4167 ≤ (8922027897643/20000000000000 : ℝ)^3143
        have hw : |(543978697/1000000000 : ℝ)|=(543978697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636545337/5000000000 : ℝ)|^4167 ≤ (8561367754979/20000000000000 : ℝ)^3143
        have hw : |(2636545337/5000000000 : ℝ)|=(2636545337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_box_13 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41944613/78125000 : ℝ)*x 0 + (-1094975997/5000000000 : ℝ)*x 1 + (5273090649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41944613/78125000 : ℝ)^4167 ≤ (43841172630019/100000000000000 : ℝ)^3143 := by
    have hnat : (41944613 : ℕ)^4167*100000000000000^3143 ≤ 43841172630019^3143*78125000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41944613 78125000 43841172630019 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094975997/5000000000 : ℝ)^4167 ≤ (6675994429663/50000000000000 : ℝ)^3143 := by
    have hnat : (1094975997 : ℕ)^4167*50000000000000^3143 ≤ 6675994429663^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094975997 5000000000 6675994429663 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273090649/10000000000 : ℝ)^4167 ≤ (1337713703307/3125000000000 : ℝ)^3143 := by
    have hnat : (5273090649 : ℕ)^4167*3125000000000^3143 ≤ 1337713703307^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273090649 10000000000 1337713703307 3125000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41944613/78125000 : ℝ), (-1094975997/5000000000 : ℝ), (5273090649/10000000000 : ℝ)] ![(43841172630019/100000000000000 : ℝ), (6675994429663/50000000000000 : ℝ), (1337713703307/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41944613/78125000 : ℝ)|^4167 ≤ (43841172630019/100000000000000 : ℝ)^3143
        have hw : |(41944613/78125000 : ℝ)|=(41944613/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1094975997/5000000000 : ℝ)|^4167 ≤ (6675994429663/50000000000000 : ℝ)^3143
        have hw : |(-1094975997/5000000000 : ℝ)|=(1094975997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273090649/10000000000 : ℝ)|^4167 ≤ (1337713703307/3125000000000 : ℝ)^3143
        have hw : |(5273090649/10000000000 : ℝ)|=(5273090649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_box_14 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368910441/10000000000 : ℝ)*x 0 + (5273090573/10000000000 : ℝ)*x 1 + (-547488031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368910441/10000000000 : ℝ)^4167 ≤ (43841172381017/100000000000000 : ℝ)^3143 := by
    have hnat : (5368910441 : ℕ)^4167*100000000000000^3143 ≤ 43841172381017^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368910441 10000000000 43841172381017 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273090573/10000000000 : ℝ)^4167 ≤ (5350854710981/12500000000000 : ℝ)^3143 := by
    have hnat : (5273090573 : ℕ)^4167*12500000000000^3143 ≤ 5350854710981^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273090573 10000000000 5350854710981 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547488031/2500000000 : ℝ)^4167 ≤ (166899873877/1250000000000 : ℝ)^3143 := by
    have hnat : (547488031 : ℕ)^4167*1250000000000^3143 ≤ 166899873877^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547488031 2500000000 166899873877 1250000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368910441/10000000000 : ℝ), (5273090573/10000000000 : ℝ), (-547488031/2500000000 : ℝ)] ![(43841172381017/100000000000000 : ℝ), (5350854710981/12500000000000 : ℝ), (166899873877/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368910441/10000000000 : ℝ)|^4167 ≤ (43841172381017/100000000000000 : ℝ)^3143
        have hw : |(5368910441/10000000000 : ℝ)|=(5368910441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273090573/10000000000 : ℝ)|^4167 ≤ (5350854710981/12500000000000 : ℝ)^3143
        have hw : |(5273090573/10000000000 : ℝ)|=(5273090573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-547488031/2500000000 : ℝ)|^4167 ≤ (166899873877/1250000000000 : ℝ)^3143
        have hw : |(-547488031/2500000000 : ℝ)|=(547488031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_box_15 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4238474897/10000000000 : ℝ)*x 0 + (1107488193/2500000000 : ℝ)*x 1 + (1107488211/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4238474897/10000000000 : ℝ)^4167 ≤ (16022240820843/50000000000000 : ℝ)^3143 := by
    have hnat : (4238474897 : ℕ)^4167*50000000000000^3143 ≤ 16022240820843^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238474897 10000000000 16022240820843 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107488193/2500000000 : ℝ)^4167 ≤ (33977758810829/100000000000000 : ℝ)^3143 := by
    have hnat : (1107488193 : ℕ)^4167*100000000000000^3143 ≤ 33977758810829^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107488193 2500000000 33977758810829 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1107488211/2500000000 : ℝ)^4167 ≤ (33977759542991/100000000000000 : ℝ)^3143 := by
    have hnat : (1107488211 : ℕ)^4167*100000000000000^3143 ≤ 33977759542991^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107488211 2500000000 33977759542991 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4238474897/10000000000 : ℝ), (1107488193/2500000000 : ℝ), (1107488211/2500000000 : ℝ)] ![(16022240820843/50000000000000 : ℝ), (33977758810829/100000000000000 : ℝ), (33977759542991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4238474897/10000000000 : ℝ)|^4167 ≤ (16022240820843/50000000000000 : ℝ)^3143
        have hw : |(4238474897/10000000000 : ℝ)|=(4238474897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1107488193/2500000000 : ℝ)|^4167 ≤ (33977758810829/100000000000000 : ℝ)^3143
        have hw : |(1107488193/2500000000 : ℝ)|=(1107488193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1107488211/2500000000 : ℝ)|^4167 ≤ (33977759542991/100000000000000 : ℝ)^3143
        have hw : |(1107488211/2500000000 : ℝ)|=(1107488211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1141_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11353/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62231/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29649/50000 : ℝ) ∧ (15961/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41561/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11353/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11353/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11353/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11353/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11353/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11353/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (11353/100000 : ℝ) ^ (8333/2048 : ℝ) ≤ (7150874197766569/50000000000000000000 : ℝ) := by
    have hpowers : (11353/100000 : ℝ)^8333 ≤ (7150874197766569/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11353 : ℕ)^8333*50000000000000000000^2048 ≤ 7150874197766569^2048*100000^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11353 100000 7150874197766569 50000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11353/100000 : ℝ)) (X := (7150874197766569/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (439/3125 : ℝ) ^ (8333/2048 : ℝ) ≤ (34023050537033721/100000000000000000000 : ℝ) := by
    have hpowers : (439/3125 : ℝ)^8333 ≤ (34023050537033721/100000000000000000000 : ℝ)^2048 := by
      have hnat : (439 : ℕ)^8333*100000000000000000000^2048 ≤ 34023050537033721^2048*3125^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        439 3125 34023050537033721 100000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (439/3125 : ℝ)) (X := (34023050537033721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007150874197766569/25000000000000000000 : ℝ) ≤ (10000702911839381/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (25007150874197766569/25000000000000000000 : ℝ)^2048 ≤ (10000702911839381/10000000000000000 : ℝ)^8333 := by
      have hnat : (25007150874197766569 : ℕ)^2048*10000000000000000^8333 ≤ 10000702911839381^8333*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007150874197766569 25000000000000000000 10000702911839381 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000702911839381/10000000000000000 : ℝ)) (X := (25007150874197766569/25000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048324798932566859/100000000000000000000 : ℝ) ≤ (10001187461384297/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (100048324798932566859/100000000000000000000 : ℝ)^2048 ≤ (10001187461384297/10000000000000000 : ℝ)^8333 := by
      have hnat : (100048324798932566859 : ℕ)^2048*10000000000000000^8333 ≤ 10001187461384297^8333*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048324798932566859 100000000000000000000 10001187461384297 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001187461384297/10000000000000000 : ℝ)) (X := (100048324798932566859/100000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034023050537033721/50000000000000000000 : ℝ) ≤ (10001672010929213/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (50034023050537033721/50000000000000000000 : ℝ)^2048 ≤ (10001672010929213/10000000000000000 : ℝ)^8333 := by
      have hnat : (50034023050537033721 : ℕ)^2048*10000000000000000^8333 ≤ 10001672010929213^8333*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034023050537033721 50000000000000000000 10001672010929213 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001672010929213/10000000000000000 : ℝ)) (X := (50034023050537033721/50000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7150874197766569/50000000000000000000 : ℝ) ≤ ((26940892165440269099/26950000000000000000 : ℝ)+2*(121137386229/67375000000000 : ℝ)*(11353/100000 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (26940892165440269099/26950000000000000000 : ℝ)+2*(121137386229/67375000000000 : ℝ)*(11353/100000 : ℝ)=(10000702911839381/10000000000000000 : ℝ) by norm_num, show 1+2*(7150874197766569/50000000000000000000 : ℝ)=(25007150874197766569/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34023050537033721/100000000000000000000 : ℝ)+(7150874197766569/50000000000000000000 : ℝ) ≤ ((26940892165440269099/26950000000000000000 : ℝ)+(121137386229/67375000000000 : ℝ)*((439/3125 : ℝ)+(11353/100000 : ℝ)))^(8333/2048 : ℝ) := by
    rw [show (26940892165440269099/26950000000000000000 : ℝ)+(121137386229/67375000000000 : ℝ)*((439/3125 : ℝ)+(11353/100000 : ℝ))=(10001187461384297/10000000000000000 : ℝ) by norm_num, show 1+(34023050537033721/100000000000000000000 : ℝ)+(7150874197766569/50000000000000000000 : ℝ)=(100048324798932566859/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34023050537033721/100000000000000000000 : ℝ) ≤ ((26940892165440269099/26950000000000000000 : ℝ)+2*(121137386229/67375000000000 : ℝ)*(439/3125 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (26940892165440269099/26950000000000000000 : ℝ)+2*(121137386229/67375000000000 : ℝ)*(439/3125 : ℝ)=(10001672010929213/10000000000000000 : ℝ) by norm_num, show 1+2*(34023050537033721/100000000000000000000 : ℝ)=(50034023050537033721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26940892165440269099/26950000000000000000 : ℝ)*(X 1 0+X 2 0)+(121137386229/67375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (11353/100000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (26940892165440269099/26950000000000000000 : ℝ)) (alpha := (121137386229/67375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26940892165440269099/26950000000000000000 : ℝ)*(X 0 1+X 2 1)+(121137386229/67375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (11353/100000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (26940892165440269099/26950000000000000000 : ℝ)) (alpha := (121137386229/67375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26940892165440269099/26950000000000000000 : ℝ)*(X 0 2+X 1 2)+(121137386229/67375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (11353/100000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (26940892165440269099/26950000000000000000 : ℝ)) (alpha := (121137386229/67375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-8161757/40000000 : ℝ)*X 0 0+(5376324703/10000000000 : ℝ)*X 0 1+(672040609/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1059195179/2000000000 : ℝ)*X 1 0+(-268675471/1250000000 : ℝ)*X 1 1+(2688162437/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647988179/5000000000 : ℝ)*X 2 0+(672040581/1250000000 : ℝ)*X 2 1+(-2149403451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((279523251/625000000 : ℝ)*X 0 0+(6739293/15625000 : ℝ)*X 0 1+(862629417/2000000000 : ℝ)*X 0 2+(279523251/625000000 : ℝ)*X 1 0+(6739293/15625000 : ℝ)*X 1 1+(862629417/2000000000 : ℝ)*X 1 2+(279523251/625000000 : ℝ)*X 2 0+(6739293/15625000 : ℝ)*X 2 1+(862629417/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2295677329/10000000000 : ℝ)*X 0 0+(2640564349/5000000000 : ℝ)*X 0 1+(5281129061/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681616853/5000000000 : ℝ)*X 1 0+(-2186847951/10000000000 : ℝ)*X 1 1+(1056225711/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681616691/5000000000 : ℝ)*X 2 0+(211245143/400000000 : ℝ)*X 2 1+(-2186848359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1064225019/2500000000 : ℝ)*X 0 0+(1105215597/2500000000 : ℝ)*X 0 1+(4420862463/10000000000 : ℝ)*X 0 2+(1064225019/2500000000 : ℝ)*X 1 0+(1105215597/2500000000 : ℝ)*X 1 1+(4420862463/10000000000 : ℝ)*X 1 2+(1064225019/2500000000 : ℝ)*X 2 0+(1105215597/2500000000 : ℝ)*X 2 1+(4420862463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-448460879/2000000000 : ℝ)*X 0 0+(5216387977/10000000000 : ℝ)*X 0 1+(168310421/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644592051/5000000000 : ℝ)*X 1 0+(-1072777431/5000000000 : ℝ)*X 1 1+(5385933431/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1057836801/2000000000 : ℝ)*X 2 0+(5385933381/10000000000 : ℝ)*X 2 1+(-107277753/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((224692381/500000000 : ℝ)*X 0 0+(4302268947/10000000000 : ℝ)*X 0 1+(4302268983/10000000000 : ℝ)*X 0 2+(224692381/500000000 : ℝ)*X 1 0+(4302268947/10000000000 : ℝ)*X 1 1+(4302268983/10000000000 : ℝ)*X 1 2+(224692381/500000000 : ℝ)*X 2 0+(4302268947/10000000000 : ℝ)*X 2 1+(4302268983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2094132227/10000000000 : ℝ)*X 0 0+(543978697/1000000000 : ℝ)*X 0 1+(2636545337/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((41944613/78125000 : ℝ)*X 1 0+(-1094975997/5000000000 : ℝ)*X 1 1+(5273090649/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368910441/10000000000 : ℝ)*X 2 0+(5273090573/10000000000 : ℝ)*X 2 1+(-547488031/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4238474897/10000000000 : ℝ)*X 0 0+(1107488193/2500000000 : ℝ)*X 0 1+(1107488211/2500000000 : ℝ)*X 0 2+(4238474897/10000000000 : ℝ)*X 1 0+(1107488193/2500000000 : ℝ)*X 1 1+(1107488211/2500000000 : ℝ)*X 1 2+(4238474897/10000000000 : ℝ)*X 2 0+(1107488193/2500000000 : ℝ)*X 2 1+(1107488211/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62231/100000 : ℝ) ≤ (-59894897441044217357637033974721/96250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (144755617/50000000000000 : ℝ)*(upper1) + (195190643/50000000000000 : ℝ)*(lower4) + (21818787/10000000000000 : ℝ)*(upper5) + (3919652823753499/100000000000000 : ℝ)*(major0) + (3919652823753499/100000000000000 : ℝ)*(major1) + (7839305647507/200000000000 : ℝ)*(major2) + (3776703953/12500000000000 : ℝ)*(sp2) + (1631651217/12500000000000 : ℝ)*(sp3) + (2618701643851321/50000000000000 : ℝ)*(sp4) + (5237372808835233/100000000000000 : ℝ)*(sp5) + (654671673761811/12500000000000 : ℝ)*(sp6) + (10490527248783/400000000000 : ℝ)*(sp7) + (31602347/10000000000000 : ℝ)*(sp12) + (30794890879/100000000000000 : ℝ)*(sp13) + (1311322432702743/50000000000000 : ℝ)*(f.failure) + (163668862616441/3125000000000 : ℝ)*(f.sum) + (12634315781121/6737500000000000000000000000 : ℝ)*base65 + (7984875814117172599/2695000000000000000000000000000000 : ℝ)*base68 + (35091300112577007/5390000000000000000000000000000 : ℝ)*base70 + (12451931005947172599/2695000000000000000000000000000000 : ℝ)*base72 + (67125825979683/13475000000000000000000000000 : ℝ)*base74 + (20548383961737007/5390000000000000000000000000000 : ℝ)*base76 + (363664652529974951/55000000000000000000000000000000 : ℝ)*base78 + (205385657369974951/55000000000000000000000000000000 : ℝ)*base80 + (4257113225219/962500000000000000000000000 : ℝ)*base82 + (44762371/5000000000000000000000 : ℝ)*base89 + (44762371/5000000000000000000000 : ℝ)*base91 + (5237629/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29649/50000 : ℝ) ≤ (14269099891633958571858345071949/24062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26592531/100000000000000 : ℝ)*(lower1) + (4544209/12500000000000 : ℝ)*(lower2) + (63143811/25000000000000 : ℝ)*(upper4) + (497974035756673/12500000000000 : ℝ)*(major0) + (497974035756673/12500000000000 : ℝ)*(major1) + (497974035756673/12500000000000 : ℝ)*(major2) + (1056450655933711/20000000000000 : ℝ)*(sp0) + (5282226703257007/100000000000000 : ℝ)*(sp1) + (2641126836246197/50000000000000 : ℝ)*(sp2) + (2665553183844031/100000000000000 : ℝ)*(sp3) + (703413317/20000000000000 : ℝ)*(sp6) + (149604783/2000000000000 : ℝ)*(sp7) + (488736303/12500000000000 : ℝ)*(sp8) + (30486301971/100000000000000 : ℝ)*(sp9) + (133278033204159/5000000000000 : ℝ)*(f.failure) + (5282257189558979/100000000000000 : ℝ)*(f.sum) + (3010902083671/962500000000000000000000000 : ℝ)*base65 + (41991795707196477/6875000000000000000000000000000 : ℝ)*base68 + (117959228732196477/6875000000000000000000000000000 : ℝ)*base70 + (2535025813446477/6875000000000000000000000000000 : ℝ)*base72 + (2270617694479/962500000000000000000000000 : ℝ)*base74 + (91025127382821477/6875000000000000000000000000000 : ℝ)*base76 + (58231121041571477/6875000000000000000000000000000 : ℝ)*base78 + (46364620715946477/6875000000000000000000000000000 : ℝ)*base80 + (15993321801/240625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (405323/500000000000000000000 : ℝ)*base89 + (405323/500000000000000000000 : ℝ)*base91 + (405323/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (15961/20000 : ℝ) ≤ (97764342352853543334433987562973/122500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27508547/50000000000000 : ℝ)*(upper0) + (205601/390625000000 : ℝ)*(upper1) + (157303/156250000000 : ℝ)*(upper2) + (83814163/100000000000000 : ℝ)*(lower5) + (4451669172469221/100000000000000 : ℝ)*(major0) + (4451669172469221/100000000000000 : ℝ)*(major1) + (2225834586234611/50000000000000 : ℝ)*(major2) + (63992197031/100000000000000 : ℝ)*(sp1) + (12803332609/50000000000000 : ℝ)*(sp3) + (1576064167/50000000000000 : ℝ)*(sp4) + (368632184114547/6250000000000 : ℝ)*(sp8) + (1179610821152811/20000000000000 : ℝ)*(sp9) + (2949059048980543/50000000000000 : ℝ)*(sp10) + (46540501533989/1562500000000 : ℝ)*(sp11) + (1489308852420257/50000000000000 : ℝ)*(f.failure) + (2949059048980543/50000000000000 : ℝ)*(f.sum) + (1561199945499/240625000000000000000000000 : ℝ)*base65 + (3930754726989898121/2695000000000000000000000000000000 : ℝ)*base68 + (4672626721949385489/1347500000000000000000000000000000 : ℝ)*base69 + (12138409176214898121/2695000000000000000000000000000000 : ℝ)*base72 + (362400838027/481250000000000000000000000 : ℝ)*base74 + (6428038578801885489/1347500000000000000000000000000000 : ℝ)*base75 + (2629536301024071697/385000000000000000000000000000000 : ℝ)*base77 + (13225125598975928303/385000000000000000000000000000000 : ℝ)*base80 + (32909560212943/6737500000000000000000000000 : ℝ)*base81 + (33531371/5000000000000000000000 : ℝ)*base90 + (33531371/5000000000000000000000 : ℝ)*base92 + (83531371/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-41561/50000 : ℝ) ≤ (-11200383446675474239688758677/13475000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9946897/100000000000000 : ℝ)*(upper1) + (6317113/50000000000000 : ℝ)*(upper3) + (37802789/50000000000000 : ℝ)*(lower4) + (560827018479697/12500000000000 : ℝ)*(major0) + (560827018479697/12500000000000 : ℝ)*(major1) + (560827018479697/12500000000000 : ℝ)*(major2) + (945152199/50000000000000 : ℝ)*(sp4) + (5973003013/25000000000000 : ℝ)*(sp5) + (132764054279/100000000000000 : ℝ)*(sp6) + (494633623/1250000000000 : ℝ)*(sp7) + (5998936209540449/100000000000000 : ℝ)*(sp12) + (2999457103916397/50000000000000 : ℝ)*(sp13) + (749850666973821/12500000000000 : ℝ)*(sp14) + (750490300346137/25000000000000 : ℝ)*(sp15) + (750500193018597/25000000000000 : ℝ)*(f.failure) + (5998938099844847/100000000000000 : ℝ)*(f.sum) + (24184540808391/13475000000000000000000000000 : ℝ)*base65 + (173497119665990429/48125000000000000000000000000000 : ℝ)*base67 + (844810797210259571/48125000000000000000000000000000 : ℝ)*base70 + (299053694367240429/48125000000000000000000000000000 : ℝ)*base71 + (1600813425537/421093750000000000000000000 : ℝ)*base74 + (890852237944009571/48125000000000000000000000000000 : ℝ)*base76 + (201623450774009571/48125000000000000000000000000000 : ℝ)*base78 + (129728656706615429/48125000000000000000000000000000 : ℝ)*base79 + (607675852116909/13475000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (20701609/2500000000000000000000 : ℝ)*base89 + (20701609/2500000000000000000000 : ℝ)*base91 + (20701609/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1141_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11353/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29649/50000 : ℝ) else (15961/20000 : ℝ) ≤ X j i ∧ X j i ≤ (41561/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1141_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1141_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29649/50000 : ℝ) else (15961/20000 : ℝ) ≤ X j i ∧ X j i ≤ (41561/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1141_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1141_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29649/50000 : ℝ) else (15961/20000 : ℝ) ≤ X j i ∧ X j i ≤ (41561/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1141_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

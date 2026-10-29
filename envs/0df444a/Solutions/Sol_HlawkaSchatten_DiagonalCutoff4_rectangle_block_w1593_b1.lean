-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1593_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:37:39.644069+00:00
-- url     : https://prove2.me/submissions/287a0104-f669-40cb-a8f3-ad4b8855e7cd

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
theorem support_rectangle_w1593_s3_0 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-54619991/312500000 : ℝ)*x 0 + (1366411043/2500000000 : ℝ)*x 1 + (2589102917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54619991/312500000 : ℝ)^4691 ≤ (10739206396521/100000000000000 : ℝ)^3667 := by
    have hnat : (54619991 : ℕ)^4691*100000000000000^3667 ≤ 10739206396521^3667*312500000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54619991 312500000 10739206396521 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366411043/2500000000 : ℝ)^4691 ≤ (9234393905859/20000000000000 : ℝ)^3667 := by
    have hnat : (1366411043 : ℕ)^4691*20000000000000^3667 ≤ 9234393905859^3667*2500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366411043 2500000000 9234393905859 20000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589102917/5000000000 : ℝ)^4691 ≤ (43088824056511/100000000000000 : ℝ)^3667 := by
    have hnat : (2589102917 : ℕ)^4691*100000000000000^3667 ≤ 43088824056511^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589102917 5000000000 43088824056511 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-54619991/312500000 : ℝ), (1366411043/2500000000 : ℝ), (2589102917/5000000000 : ℝ)] ![(10739206396521/100000000000000 : ℝ), (9234393905859/20000000000000 : ℝ), (43088824056511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-54619991/312500000 : ℝ)|^4691 ≤ (10739206396521/100000000000000 : ℝ)^3667
        have hw : |(-54619991/312500000 : ℝ)|=(54619991/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366411043/2500000000 : ℝ)|^4691 ≤ (9234393905859/20000000000000 : ℝ)^3667
        have hw : |(1366411043/2500000000 : ℝ)|=(1366411043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589102917/5000000000 : ℝ)|^4691 ≤ (43088824056511/100000000000000 : ℝ)^3667
        have hw : |(2589102917/5000000000 : ℝ)|=(2589102917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s3_1 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535617533/1000000000 : ℝ)*x 0 + (-11851251/62500000 : ℝ)*x 1 + (1294551463/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535617533/1000000000 : ℝ)^4691 ≤ (44992300998983/100000000000000 : ℝ)^3667 := by
    have hnat : (535617533 : ℕ)^4691*100000000000000^3667 ≤ 44992300998983^3667*1000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535617533 1000000000 44992300998983 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11851251/62500000 : ℝ)^4691 ≤ (2979718686399/25000000000000 : ℝ)^3667 := by
    have hnat : (11851251 : ℕ)^4691*25000000000000^3667 ≤ 2979718686399^3667*62500000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11851251 62500000 2979718686399 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294551463/2500000000 : ℝ)^4691 ≤ (43088824248119/100000000000000 : ℝ)^3667 := by
    have hnat : (1294551463 : ℕ)^4691*100000000000000^3667 ≤ 43088824248119^3667*2500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294551463 2500000000 43088824248119 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535617533/1000000000 : ℝ), (-11851251/62500000 : ℝ), (1294551463/2500000000 : ℝ)] ![(44992300998983/100000000000000 : ℝ), (2979718686399/25000000000000 : ℝ), (43088824248119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535617533/1000000000 : ℝ)|^4691 ≤ (44992300998983/100000000000000 : ℝ)^3667
        have hw : |(535617533/1000000000 : ℝ)|=(535617533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11851251/62500000 : ℝ)|^4691 ≤ (2979718686399/25000000000000 : ℝ)^3667
        have hw : |(-11851251/62500000 : ℝ)|=(11851251/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294551463/2500000000 : ℝ)|^4691 ≤ (43088824248119/100000000000000 : ℝ)^3667
        have hw : |(1294551463/2500000000 : ℝ)|=(1294551463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s3_2 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678087667/5000000000 : ℝ)*x 0 + (207128233/400000000 : ℝ)*x 1 + (-1896200189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678087667/5000000000 : ℝ)^4691 ≤ (22496150520983/50000000000000 : ℝ)^3667 := by
    have hnat : (2678087667 : ℕ)^4691*50000000000000^3667 ≤ 22496150520983^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678087667 5000000000 22496150520983 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207128233/400000000 : ℝ)^4691 ≤ (43088823960707/100000000000000 : ℝ)^3667 := by
    have hnat : (207128233 : ℕ)^4691*100000000000000^3667 ≤ 43088823960707^3667*400000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207128233 400000000 43088823960707 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1896200189/10000000000 : ℝ)^4691 ≤ (5959437489391/50000000000000 : ℝ)^3667 := by
    have hnat : (1896200189 : ℕ)^4691*50000000000000^3667 ≤ 5959437489391^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896200189 10000000000 5959437489391 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678087667/5000000000 : ℝ), (207128233/400000000 : ℝ), (-1896200189/10000000000 : ℝ)] ![(22496150520983/50000000000000 : ℝ), (43088823960707/100000000000000 : ℝ), (5959437489391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678087667/5000000000 : ℝ)|^4691 ≤ (22496150520983/50000000000000 : ℝ)^3667
        have hw : |(2678087667/5000000000 : ℝ)|=(2678087667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207128233/400000000 : ℝ)|^4691 ≤ (43088823960707/100000000000000 : ℝ)^3667
        have hw : |(207128233/400000000 : ℝ)|=(207128233/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1896200189/10000000000 : ℝ)|^4691 ≤ (5959437489391/50000000000000 : ℝ)^3667
        have hw : |(-1896200189/10000000000 : ℝ)|=(1896200189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s3_3 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4226664237/10000000000 : ℝ)*x 0 + (778507993/2000000000 : ℝ)*x 1 + (1145772313/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4226664237/10000000000 : ℝ)^4691 ≤ (33232163435119/100000000000000 : ℝ)^3667 := by
    have hnat : (4226664237 : ℕ)^4691*100000000000000^3667 ≤ 33232163435119^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226664237 10000000000 33232163435119 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (778507993/2000000000 : ℝ)^4691 ≤ (29909335017569/100000000000000 : ℝ)^3667 := by
    have hnat : (778507993 : ℕ)^4691*100000000000000^3667 ≤ 29909335017569^3667*2000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778507993 2000000000 29909335017569 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1145772313/2500000000 : ℝ)^4691 ≤ (7371700307263/20000000000000 : ℝ)^3667 := by
    have hnat : (1145772313 : ℕ)^4691*20000000000000^3667 ≤ 7371700307263^3667*2500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145772313 2500000000 7371700307263 20000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4226664237/10000000000 : ℝ), (778507993/2000000000 : ℝ), (1145772313/2500000000 : ℝ)] ![(33232163435119/100000000000000 : ℝ), (29909335017569/100000000000000 : ℝ), (7371700307263/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4226664237/10000000000 : ℝ)|^4691 ≤ (33232163435119/100000000000000 : ℝ)^3667
        have hw : |(4226664237/10000000000 : ℝ)|=(4226664237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(778507993/2000000000 : ℝ)|^4691 ≤ (29909335017569/100000000000000 : ℝ)^3667
        have hw : |(778507993/2000000000 : ℝ)|=(778507993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1145772313/2500000000 : ℝ)|^4691 ≤ (7371700307263/20000000000000 : ℝ)^3667
        have hw : |(1145772313/2500000000 : ℝ)|=(1145772313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s3_4 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-873957111/5000000000 : ℝ)*x 0 + (5180338731/10000000000 : ℝ)*x 1 + (5463488777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873957111/5000000000 : ℝ)^4691 ≤ (10739792052063/100000000000000 : ℝ)^3667 := by
    have hnat : (873957111 : ℕ)^4691*100000000000000^3667 ≤ 10739792052063^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873957111 5000000000 10739792052063 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180338731/10000000000 : ℝ)^4691 ≤ (43111529746921/100000000000000 : ℝ)^3667 := by
    have hnat : (5180338731 : ℕ)^4691*100000000000000^3667 ≤ 43111529746921^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180338731 10000000000 43111529746921 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463488777/10000000000 : ℝ)^4691 ≤ (46148678186661/100000000000000 : ℝ)^3667 := by
    have hnat : (5463488777 : ℕ)^4691*100000000000000^3667 ≤ 46148678186661^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463488777 10000000000 46148678186661 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-873957111/5000000000 : ℝ), (5180338731/10000000000 : ℝ), (5463488777/10000000000 : ℝ)] ![(10739792052063/100000000000000 : ℝ), (43111529746921/100000000000000 : ℝ), (46148678186661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-873957111/5000000000 : ℝ)|^4691 ≤ (10739792052063/100000000000000 : ℝ)^3667
        have hw : |(-873957111/5000000000 : ℝ)|=(873957111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180338731/10000000000 : ℝ)|^4691 ≤ (43111529746921/100000000000000 : ℝ)^3667
        have hw : |(5180338731/10000000000 : ℝ)|=(5180338731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463488777/10000000000 : ℝ)|^4691 ≤ (46148678186661/100000000000000 : ℝ)^3667
        have hw : |(5463488777/10000000000 : ℝ)|=(5463488777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s3_5 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280089963/10000000000 : ℝ)*x 0 + (-805458617/5000000000 : ℝ)*x 1 + (5463488779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280089963/10000000000 : ℝ)^4691 ≤ (1767053262381/4000000000000 : ℝ)^3667 := by
    have hnat : (5280089963 : ℕ)^4691*4000000000000^3667 ≤ 1767053262381^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280089963 10000000000 1767053262381 4000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805458617/5000000000 : ℝ)^4691 ≤ (1209373777959/12500000000000 : ℝ)^3667 := by
    have hnat : (805458617 : ℕ)^4691*12500000000000^3667 ≤ 1209373777959^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805458617 5000000000 1209373777959 12500000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463488779/10000000000 : ℝ)^4691 ≤ (2884292388017/6250000000000 : ℝ)^3667 := by
    have hnat : (5463488779 : ℕ)^4691*6250000000000^3667 ≤ 2884292388017^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463488779 10000000000 2884292388017 6250000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280089963/10000000000 : ℝ), (-805458617/5000000000 : ℝ), (5463488779/10000000000 : ℝ)] ![(1767053262381/4000000000000 : ℝ), (1209373777959/12500000000000 : ℝ), (2884292388017/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280089963/10000000000 : ℝ)|^4691 ≤ (1767053262381/4000000000000 : ℝ)^3667
        have hw : |(5280089963/10000000000 : ℝ)|=(5280089963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-805458617/5000000000 : ℝ)|^4691 ≤ (1209373777959/12500000000000 : ℝ)^3667
        have hw : |(-805458617/5000000000 : ℝ)|=(805458617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463488779/10000000000 : ℝ)|^4691 ≤ (2884292388017/6250000000000 : ℝ)^3667
        have hw : |(5463488779/10000000000 : ℝ)|=(5463488779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s3_6 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280089963/10000000000 : ℝ)*x 0 + (5463488777/10000000000 : ℝ)*x 1 + (-322183447/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280089963/10000000000 : ℝ)^4691 ≤ (1767053262381/4000000000000 : ℝ)^3667 := by
    have hnat : (5280089963 : ℕ)^4691*4000000000000^3667 ≤ 1767053262381^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280089963 10000000000 1767053262381 4000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463488777/10000000000 : ℝ)^4691 ≤ (46148678186661/100000000000000 : ℝ)^3667 := by
    have hnat : (5463488777 : ℕ)^4691*100000000000000^3667 ≤ 46148678186661^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463488777 10000000000 46148678186661 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (322183447/2000000000 : ℝ)^4691 ≤ (1934998046271/20000000000000 : ℝ)^3667 := by
    have hnat : (322183447 : ℕ)^4691*20000000000000^3667 ≤ 1934998046271^3667*2000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322183447 2000000000 1934998046271 20000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280089963/10000000000 : ℝ), (5463488777/10000000000 : ℝ), (-322183447/2000000000 : ℝ)] ![(1767053262381/4000000000000 : ℝ), (46148678186661/100000000000000 : ℝ), (1934998046271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280089963/10000000000 : ℝ)|^4691 ≤ (1767053262381/4000000000000 : ℝ)^3667
        have hw : |(5280089963/10000000000 : ℝ)|=(5280089963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463488777/10000000000 : ℝ)|^4691 ≤ (46148678186661/100000000000000 : ℝ)^3667
        have hw : |(5463488777/10000000000 : ℝ)|=(5463488777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-322183447/2000000000 : ℝ)|^4691 ≤ (1934998046271/20000000000000 : ℝ)^3667
        have hw : |(-322183447/2000000000 : ℝ)|=(322183447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s3_7 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2113421633/5000000000 : ℝ)*x 0 + (228898257/500000000 : ℝ)*x 1 + (155908727/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113421633/5000000000 : ℝ)^4691 ≤ (3323396413503/10000000000000 : ℝ)^3667 := by
    have hnat : (2113421633 : ℕ)^4691*10000000000000^3667 ≤ 3323396413503^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113421633 5000000000 3323396413503 10000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228898257/500000000 : ℝ)^4691 ≤ (36805792548353/100000000000000 : ℝ)^3667 := by
    have hnat : (228898257 : ℕ)^4691*100000000000000^3667 ≤ 36805792548353^3667*500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228898257 500000000 36805792548353 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (155908727/400000000 : ℝ)^4691 ≤ (29960243305511/100000000000000 : ℝ)^3667 := by
    have hnat : (155908727 : ℕ)^4691*100000000000000^3667 ≤ 29960243305511^3667*400000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155908727 400000000 29960243305511 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2113421633/5000000000 : ℝ), (228898257/500000000 : ℝ), (155908727/400000000 : ℝ)] ![(3323396413503/10000000000000 : ℝ), (36805792548353/100000000000000 : ℝ), (29960243305511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2113421633/5000000000 : ℝ)|^4691 ≤ (3323396413503/10000000000000 : ℝ)^3667
        have hw : |(2113421633/5000000000 : ℝ)|=(2113421633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(228898257/500000000 : ℝ)|^4691 ≤ (36805792548353/100000000000000 : ℝ)^3667
        have hw : |(228898257/500000000 : ℝ)|=(228898257/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(155908727/400000000 : ℝ)|^4691 ≤ (29960243305511/100000000000000 : ℝ)^3667
        have hw : |(155908727/400000000 : ℝ)|=(155908727/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1593_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16571/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1267/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (103/1000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4097/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16571/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1267/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16571/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1267/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16571/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1267/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16571/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1267/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16571/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1267/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16571/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1267/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1267/12500 : ℝ) ^ (4687/1024 : ℝ) ≤ (2816461831665437/100000000000000000000 : ℝ) := by
    have hpowers : (1267/12500 : ℝ)^4687 ≤ (2816461831665437/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1267 : ℕ)^4687*100000000000000000000^1024 ≤ 2816461831665437^1024*12500^4687 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1267 12500 2816461831665437 100000000000000000000 4687 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1267/12500 : ℝ)) (X := (2816461831665437/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16571/100000 : ℝ) ^ (4687/1024 : ℝ) ≤ (1068816605539579/4000000000000000000 : ℝ) := by
    have hpowers : (16571/100000 : ℝ)^4687 ≤ (1068816605539579/4000000000000000000 : ℝ)^1024 := by
      have hnat : (16571 : ℕ)^4687*4000000000000000000^1024 ≤ 1068816605539579^1024*100000^4687 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16571 100000 1068816605539579 4000000000000000000 4687 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16571/100000 : ℝ)) (X := (1068816605539579/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002816461831665437/50000000000000000000 : ℝ) ≤ (10000123063513373/10000000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (50002816461831665437/50000000000000000000 : ℝ)^1024 ≤ (10000123063513373/10000000000000000 : ℝ)^4687 := by
      have hnat : (50002816461831665437 : ℕ)^1024*10000000000000000^4687 ≤ 10000123063513373^4687*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002816461831665437 50000000000000000000 10000123063513373 10000000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000123063513373/10000000000000000 : ℝ)) (X := (50002816461831665437/50000000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125923027405317341/3125000000000000000 : ℝ) ≤ (1250080654661031/1250000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (3125923027405317341/3125000000000000000 : ℝ)^1024 ≤ (1250080654661031/1250000000000000 : ℝ)^4687 := by
      have hnat : (3125923027405317341 : ℕ)^1024*1250000000000000^4687 ≤ 1250080654661031^4687*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125923027405317341 3125000000000000000 1250080654661031 1250000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250080654661031/1250000000000000 : ℝ)) (X := (3125923027405317341/3125000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001068816605539579/2000000000000000000 : ℝ) ≤ (10001167411063123/10000000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (2001068816605539579/2000000000000000000 : ℝ)^1024 ≤ (10001167411063123/10000000000000000 : ℝ)^4687 := by
      have hnat : (2001068816605539579 : ℕ)^1024*10000000000000000^4687 ≤ 10001167411063123^4687*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001068816605539579 2000000000000000000 10001167411063123 10000000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001167411063123/10000000000000000 : ℝ)) (X := (2001068816605539579/2000000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2816461831665437/100000000000000000000 : ℝ) ≤ ((12868041281388857851/12870000000000000000 : ℝ)+2*(4177390199/5148000000000 : ℝ)*(1267/12500 : ℝ))^(4687/1024 : ℝ) := by
    rw [show (12868041281388857851/12870000000000000000 : ℝ)+2*(4177390199/5148000000000 : ℝ)*(1267/12500 : ℝ)=(10000123063513373/10000000000000000 : ℝ) by norm_num, show 1+2*(2816461831665437/100000000000000000000 : ℝ)=(50002816461831665437/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1068816605539579/4000000000000000000 : ℝ)+(2816461831665437/100000000000000000000 : ℝ) ≤ ((12868041281388857851/12870000000000000000 : ℝ)+(4177390199/5148000000000 : ℝ)*((16571/100000 : ℝ)+(1267/12500 : ℝ)))^(4687/1024 : ℝ) := by
    rw [show (12868041281388857851/12870000000000000000 : ℝ)+(4177390199/5148000000000 : ℝ)*((16571/100000 : ℝ)+(1267/12500 : ℝ))=(1250080654661031/1250000000000000 : ℝ) by norm_num, show 1+(1068816605539579/4000000000000000000 : ℝ)+(2816461831665437/100000000000000000000 : ℝ)=(3125923027405317341/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1068816605539579/4000000000000000000 : ℝ) ≤ ((12868041281388857851/12870000000000000000 : ℝ)+2*(4177390199/5148000000000 : ℝ)*(16571/100000 : ℝ))^(4687/1024 : ℝ) := by
    rw [show (12868041281388857851/12870000000000000000 : ℝ)+2*(4177390199/5148000000000 : ℝ)*(16571/100000 : ℝ)=(10001167411063123/10000000000000000 : ℝ) by norm_num, show 1+2*(1068816605539579/4000000000000000000 : ℝ)=(2001068816605539579/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12868041281388857851/12870000000000000000 : ℝ)*(X 1 0+X 2 0)+(4177390199/5148000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (1267/12500 : ℝ)) (hi := (16571/100000 : ℝ)) (c := (12868041281388857851/12870000000000000000 : ℝ)) (alpha := (4177390199/5148000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12868041281388857851/12870000000000000000 : ℝ)*(X 0 1+X 2 1)+(4177390199/5148000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (1267/12500 : ℝ)) (hi := (16571/100000 : ℝ)) (c := (12868041281388857851/12870000000000000000 : ℝ)) (alpha := (4177390199/5148000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12868041281388857851/12870000000000000000 : ℝ)*(X 0 2+X 1 2)+(4177390199/5148000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (1267/12500 : ℝ)) (hi := (16571/100000 : ℝ)) (c := (12868041281388857851/12870000000000000000 : ℝ)) (alpha := (4177390199/5148000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-54619991/312500000 : ℝ)*X 0 0+(1366411043/2500000000 : ℝ)*X 0 1+(2589102917/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535617533/1000000000 : ℝ)*X 1 0+(-11851251/62500000 : ℝ)*X 1 1+(1294551463/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2678087667/5000000000 : ℝ)*X 2 0+(207128233/400000000 : ℝ)*X 2 1+(-1896200189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4226664237/10000000000 : ℝ)*X 0 0+(778507993/2000000000 : ℝ)*X 0 1+(1145772313/2500000000 : ℝ)*X 0 2+(4226664237/10000000000 : ℝ)*X 1 0+(778507993/2000000000 : ℝ)*X 1 1+(1145772313/2500000000 : ℝ)*X 1 2+(4226664237/10000000000 : ℝ)*X 2 0+(778507993/2000000000 : ℝ)*X 2 1+(1145772313/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-873957111/5000000000 : ℝ)*X 0 0+(5180338731/10000000000 : ℝ)*X 0 1+(5463488777/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280089963/10000000000 : ℝ)*X 1 0+(-805458617/5000000000 : ℝ)*X 1 1+(5463488779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280089963/10000000000 : ℝ)*X 2 0+(5463488777/10000000000 : ℝ)*X 2 1+(-322183447/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2113421633/5000000000 : ℝ)*X 0 0+(228898257/500000000 : ℝ)*X 0 1+(155908727/400000000 : ℝ)*X 0 2+(2113421633/5000000000 : ℝ)*X 1 0+(228898257/500000000 : ℝ)*X 1 1+(155908727/400000000 : ℝ)*X 1 2+(2113421633/5000000000 : ℝ)*X 2 0+(228898257/500000000 : ℝ)*X 2 1+(155908727/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (147570126946287303649/14300000000000000000000000 : ℝ) := by norm_num
    linear_combination (876965703/50000000000000 : ℝ)*(base19) + (1649943957/100000000000000 : ℝ)*(base23) + (356807/625000000000 : ℝ)*(lower2) + (1352777/500000000000 : ℝ)*(upper3) + (42601147/25000000000000 : ℝ)*(upper5) + (1231797369722151/50000000000000 : ℝ)*(major0) + (1231797369722151/50000000000000 : ℝ)*(major1) + (1231797369722151/50000000000000 : ℝ)*(major2) + (869757131061323/25000000000000 : ℝ)*(sp0) + (869761787664959/25000000000000 : ℝ)*(sp1) + (1739523627323643/50000000000000 : ℝ)*(sp2) + (1448130814650607/100000000000000 : ℝ)*(sp3) + (20380345951/100000000000000 : ℝ)*(sp4) + (2353915109/25000000000000 : ℝ)*(sp7) + (1448140230311043/100000000000000 : ℝ)*(f.failure) + (1739524452295621/50000000000000 : ℝ)*(f.sum) + (2023691773769/429000000000000000000000000 : ℝ)*base65 + (19111494449217601/6500000000000000000000000000000 : ℝ)*base68 + (41057766322717601/6500000000000000000000000000000 : ℝ)*base70 + (47105724703282399/6500000000000000000000000000000 : ℝ)*base71 + (33342653563/85800000000000000000000000 : ℝ)*base73 + (9062207366782399/6500000000000000000000000000000 : ℝ)*base75 + (25407440017282399/6500000000000000000000000000000 : ℝ)*base77 + (36161478991717601/6500000000000000000000000000000 : ℝ)*base80 + (14093039513/21450000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (75771831/10000000000000000000000 : ℝ)*base90 + (75771831/10000000000000000000000 : ℝ)*base92 + (75771831/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (380610963231456100205891/125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (478810399/100000000000000 : ℝ)*(base19) + (25994871/5000000000000 : ℝ)*(base23) + (6624069/10000000000000 : ℝ)*(upper3) + (18210571/100000000000000 : ℝ)*(lower4) + (61719381/100000000000000 : ℝ)*(upper5) + (625218809792863/25000000000000 : ℝ)*(major0) + (625218809792863/25000000000000 : ℝ)*(major1) + (625218809792863/25000000000000 : ℝ)*(major2) + (332298461/6250000000000 : ℝ)*(sp1) + (2887324211/50000000000000 : ℝ)*(sp2) + (176584803747847/5000000000000 : ℝ)*(sp4) + (1765845139685583/50000000000000 : ℝ)*(sp5) + (1765844890205549/50000000000000 : ℝ)*(sp6) + (1470054301889701/100000000000000 : ℝ)*(sp7) + (1470054301889701/100000000000000 : ℝ)*(f.failure) + (176584803747847/5000000000000 : ℝ)*(f.sum) + (18979379053/4500000000000000000000000 : ℝ)*base65 + (3812230111389703/750000000000000000000000000000 : ℝ)*base68 + (3848613942639703/750000000000000000000000000000 : ℝ)*base70 + (5337893704389703/750000000000000000000000000000 : ℝ)*base72 + (4151147489/2250000000000000000000000 : ℝ)*base73 + (6804802157139703/750000000000000000000000000000 : ℝ)*base76 + (4866257242389703/750000000000000000000000000000 : ℝ)*base78 + (3105326728389703/750000000000000000000000000000 : ℝ)*base80 + (21834474197/9000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (58606383/10000000000000000000000 : ℝ)*base89 + (58606383/10000000000000000000000 : ℝ)*base91 + (58606383/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1593_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16571/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1267/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (103/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4097/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1593_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1593_s4_0 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-34960261/200000000 : ℝ)*x 0 + (5464784587/10000000000 : ℝ)*x 1 + (5178950459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34960261/200000000 : ℝ)^4691 ≤ (2685142215027/25000000000000 : ℝ)^3667 := by
    have hnat : (34960261 : ℕ)^4691*25000000000000^3667 ≤ 2685142215027^3667*200000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34960261 200000000 2685142215027 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5464784587/10000000000 : ℝ)^4691 ≤ (9232536097743/20000000000000 : ℝ)^3667 := by
    have hnat : (5464784587 : ℕ)^4691*20000000000000^3667 ≤ 9232536097743^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464784587 10000000000 9232536097743 20000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178950459/10000000000 : ℝ)^4691 ≤ (1723870025709/4000000000000 : ℝ)^3667 := by
    have hnat : (5178950459 : ℕ)^4691*4000000000000^3667 ≤ 1723870025709^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178950459 10000000000 1723870025709 4000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-34960261/200000000 : ℝ), (5464784587/10000000000 : ℝ), (5178950459/10000000000 : ℝ)] ![(2685142215027/25000000000000 : ℝ), (9232536097743/20000000000000 : ℝ), (1723870025709/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-34960261/200000000 : ℝ)|^4691 ≤ (2685142215027/25000000000000 : ℝ)^3667
        have hw : |(-34960261/200000000 : ℝ)|=(34960261/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5464784587/10000000000 : ℝ)|^4691 ≤ (9232536097743/20000000000000 : ℝ)^3667
        have hw : |(5464784587/10000000000 : ℝ)|=(5464784587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178950459/10000000000 : ℝ)|^4691 ≤ (1723870025709/4000000000000 : ℝ)^3667
        have hw : |(5178950459/10000000000 : ℝ)|=(5178950459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s4_1 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355946333/10000000000 : ℝ)*x 0 + (-947759881/5000000000 : ℝ)*x 1 + (647368867/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355946333/10000000000 : ℝ)^4691 ≤ (44989840262303/100000000000000 : ℝ)^3667 := by
    have hnat : (5355946333 : ℕ)^4691*100000000000000^3667 ≤ 44989840262303^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355946333 10000000000 44989840262303 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (947759881/5000000000 : ℝ)^4691 ≤ (2978350998903/25000000000000 : ℝ)^3667 := by
    have hnat : (947759881 : ℕ)^4691*25000000000000^3667 ≤ 2978350998903^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947759881 5000000000 2978350998903 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647368867/1250000000 : ℝ)^4691 ≤ (21548377860263/50000000000000 : ℝ)^3667 := by
    have hnat : (647368867 : ℕ)^4691*50000000000000^3667 ≤ 21548377860263^3667*1250000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647368867 1250000000 21548377860263 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355946333/10000000000 : ℝ), (-947759881/5000000000 : ℝ), (647368867/1250000000 : ℝ)] ![(44989840262303/100000000000000 : ℝ), (2978350998903/25000000000000 : ℝ), (21548377860263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355946333/10000000000 : ℝ)|^4691 ≤ (44989840262303/100000000000000 : ℝ)^3667
        have hw : |(5355946333/10000000000 : ℝ)|=(5355946333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-947759881/5000000000 : ℝ)|^4691 ≤ (2978350998903/25000000000000 : ℝ)^3667
        have hw : |(-947759881/5000000000 : ℝ)|=(947759881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647368867/1250000000 : ℝ)|^4691 ≤ (21548377860263/50000000000000 : ℝ)^3667
        have hw : |(647368867/1250000000 : ℝ)|=(647368867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s4_2 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355946409/10000000000 : ℝ)*x 0 + (517895091/1000000000 : ℝ)*x 1 + (-379103939/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355946409/10000000000 : ℝ)^4691 ≤ (11247460269743/25000000000000 : ℝ)^3667 := by
    have hnat : (5355946409 : ℕ)^4691*25000000000000^3667 ≤ 11247460269743^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355946409 10000000000 11247460269743 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517895091/1000000000 : ℝ)^4691 ≤ (10774188860937/25000000000000 : ℝ)^3667 := by
    have hnat : (517895091 : ℕ)^4691*25000000000000^3667 ≤ 10774188860937^3667*1000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517895091 1000000000 10774188860937 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (379103939/2000000000 : ℝ)^4691 ≤ (476536138277/4000000000000 : ℝ)^3667 := by
    have hnat : (379103939 : ℕ)^4691*4000000000000^3667 ≤ 476536138277^3667*2000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379103939 2000000000 476536138277 4000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355946409/10000000000 : ℝ), (517895091/1000000000 : ℝ), (-379103939/2000000000 : ℝ)] ![(11247460269743/25000000000000 : ℝ), (10774188860937/25000000000000 : ℝ), (476536138277/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355946409/10000000000 : ℝ)|^4691 ≤ (11247460269743/25000000000000 : ℝ)^3667
        have hw : |(5355946409/10000000000 : ℝ)|=(5355946409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517895091/1000000000 : ℝ)|^4691 ≤ (10774188860937/25000000000000 : ℝ)^3667
        have hw : |(517895091/1000000000 : ℝ)|=(517895091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-379103939/2000000000 : ℝ)|^4691 ≤ (476536138277/4000000000000 : ℝ)^3667
        have hw : |(-379103939/2000000000 : ℝ)|=(379103939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s4_3 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (422677601/1000000000 : ℝ)*x 0 + (3894455263/10000000000 : ℝ)*x 1 + (4581149823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422677601/1000000000 : ℝ)^4691 ≤ (33233287661831/100000000000000 : ℝ)^3667 := by
    have hnat : (422677601 : ℕ)^4691*100000000000000^3667 ≤ 33233287661831^3667*1000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422677601 1000000000 33233287661831 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3894455263/10000000000 : ℝ)^4691 ≤ (29928162592607/100000000000000 : ℝ)^3667 := by
    have hnat : (3894455263 : ℕ)^4691*100000000000000^3667 ≤ 29928162592607^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3894455263 10000000000 29928162592607 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4581149823/10000000000 : ℝ)^4691 ≤ (36838549735287/100000000000000 : ℝ)^3667 := by
    have hnat : (4581149823 : ℕ)^4691*100000000000000^3667 ≤ 36838549735287^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4581149823 10000000000 36838549735287 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(422677601/1000000000 : ℝ), (3894455263/10000000000 : ℝ), (4581149823/10000000000 : ℝ)] ![(33233287661831/100000000000000 : ℝ), (29928162592607/100000000000000 : ℝ), (36838549735287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(422677601/1000000000 : ℝ)|^4691 ≤ (33233287661831/100000000000000 : ℝ)^3667
        have hw : |(422677601/1000000000 : ℝ)|=(422677601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3894455263/10000000000 : ℝ)|^4691 ≤ (29928162592607/100000000000000 : ℝ)^3667
        have hw : |(3894455263/10000000000 : ℝ)|=(3894455263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4581149823/10000000000 : ℝ)|^4691 ≤ (36838549735287/100000000000000 : ℝ)^3667
        have hw : |(4581149823/10000000000 : ℝ)|=(4581149823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s4_4 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-874043273/5000000000 : ℝ)*x 0 + (1036211967/2000000000 : ℝ)*x 1 + (1365663231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874043273/5000000000 : ℝ)^4691 ≤ (10741146561467/100000000000000 : ℝ)^3667 := by
    have hnat : (874043273 : ℕ)^4691*100000000000000^3667 ≤ 10741146561467^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874043273 5000000000 10741146561467 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036211967/2000000000 : ℝ)^4691 ≤ (21559603414141/50000000000000 : ℝ)^3667 := by
    have hnat : (1036211967 : ℕ)^4691*50000000000000^3667 ≤ 21559603414141^3667*2000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036211967 2000000000 21559603414141 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365663231/2500000000 : ℝ)^4691 ≤ (46139646593581/100000000000000 : ℝ)^3667 := by
    have hnat : (1365663231 : ℕ)^4691*100000000000000^3667 ≤ 46139646593581^3667*2500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365663231 2500000000 46139646593581 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-874043273/5000000000 : ℝ), (1036211967/2000000000 : ℝ), (1365663231/2500000000 : ℝ)] ![(10741146561467/100000000000000 : ℝ), (21559603414141/50000000000000 : ℝ), (46139646593581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-874043273/5000000000 : ℝ)|^4691 ≤ (10741146561467/100000000000000 : ℝ)^3667
        have hw : |(-874043273/5000000000 : ℝ)|=(874043273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036211967/2000000000 : ℝ)|^4691 ≤ (21559603414141/50000000000000 : ℝ)^3667
        have hw : |(1036211967/2000000000 : ℝ)|=(1036211967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365663231/2500000000 : ℝ)|^4691 ≤ (46139646593581/100000000000000 : ℝ)^3667
        have hw : |(1365663231/2500000000 : ℝ)|=(1365663231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s4_5 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280287541/10000000000 : ℝ)*x 0 + (-1611817451/10000000000 : ℝ)*x 1 + (218506117/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280287541/10000000000 : ℝ)^4691 ≤ (22089223117439/50000000000000 : ℝ)^3667 := by
    have hnat : (5280287541 : ℕ)^4691*50000000000000^3667 ≤ 22089223117439^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280287541 10000000000 22089223117439 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1611817451/10000000000 : ℝ)^4691 ≤ (9681907146337/100000000000000 : ℝ)^3667 := by
    have hnat : (1611817451 : ℕ)^4691*100000000000000^3667 ≤ 9681907146337^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1611817451 10000000000 9681907146337 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218506117/400000000 : ℝ)^4691 ≤ (23069823302193/50000000000000 : ℝ)^3667 := by
    have hnat : (218506117 : ℕ)^4691*50000000000000^3667 ≤ 23069823302193^3667*400000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218506117 400000000 23069823302193 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280287541/10000000000 : ℝ), (-1611817451/10000000000 : ℝ), (218506117/400000000 : ℝ)] ![(22089223117439/50000000000000 : ℝ), (9681907146337/100000000000000 : ℝ), (23069823302193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280287541/10000000000 : ℝ)|^4691 ≤ (22089223117439/50000000000000 : ℝ)^3667
        have hw : |(5280287541/10000000000 : ℝ)|=(5280287541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1611817451/10000000000 : ℝ)|^4691 ≤ (9681907146337/100000000000000 : ℝ)^3667
        have hw : |(-1611817451/10000000000 : ℝ)|=(1611817451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218506117/400000000 : ℝ)|^4691 ≤ (23069823302193/50000000000000 : ℝ)^3667
        have hw : |(218506117/400000000 : ℝ)|=(218506117/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s4_6 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280287543/10000000000 : ℝ)*x 0 + (1365663231/2500000000 : ℝ)*x 1 + (-32236349/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280287543/10000000000 : ℝ)^4691 ≤ (11044611564071/25000000000000 : ℝ)^3667 := by
    have hnat : (5280287543 : ℕ)^4691*25000000000000^3667 ≤ 11044611564071^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280287543 10000000000 11044611564071 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365663231/2500000000 : ℝ)^4691 ≤ (46139646593581/100000000000000 : ℝ)^3667 := by
    have hnat : (1365663231 : ℕ)^4691*100000000000000^3667 ≤ 46139646593581^3667*2500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365663231 2500000000 46139646593581 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32236349/200000000 : ℝ)^4691 ≤ (9681907138653/100000000000000 : ℝ)^3667 := by
    have hnat : (32236349 : ℕ)^4691*100000000000000^3667 ≤ 9681907138653^3667*200000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32236349 200000000 9681907138653 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280287543/10000000000 : ℝ), (1365663231/2500000000 : ℝ), (-32236349/200000000 : ℝ)] ![(11044611564071/25000000000000 : ℝ), (46139646593581/100000000000000 : ℝ), (9681907138653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280287543/10000000000 : ℝ)|^4691 ≤ (11044611564071/25000000000000 : ℝ)^3667
        have hw : |(5280287543/10000000000 : ℝ)|=(5280287543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365663231/2500000000 : ℝ)|^4691 ≤ (46139646593581/100000000000000 : ℝ)^3667
        have hw : |(1365663231/2500000000 : ℝ)|=(1365663231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32236349/200000000 : ℝ)|^4691 ≤ (9681907138653/100000000000000 : ℝ)^3667
        have hw : |(-32236349/200000000 : ℝ)|=(32236349/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s4_7 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1056738053/2500000000 : ℝ)*x 0 + (35750643/78125000 : ℝ)*x 1 + (24372349/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056738053/2500000000 : ℝ)^4691 ≤ (33235059940283/100000000000000 : ℝ)^3667 := by
    have hnat : (1056738053 : ℕ)^4691*100000000000000^3667 ≤ 33235059940283^3667*2500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056738053 2500000000 33235059940283 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35750643/78125000 : ℝ)^4691 ≤ (4598303620417/12500000000000 : ℝ)^3667 := by
    have hnat : (35750643 : ℕ)^4691*12500000000000^3667 ≤ 4598303620417^3667*78125000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35750643 78125000 4598303620417 12500000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24372349/62500000 : ℝ)^4691 ≤ (117103558919/390625000000 : ℝ)^3667 := by
    have hnat : (24372349 : ℕ)^4691*390625000000^3667 ≤ 117103558919^3667*62500000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24372349 62500000 117103558919 390625000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056738053/2500000000 : ℝ), (35750643/78125000 : ℝ), (24372349/62500000 : ℝ)] ![(33235059940283/100000000000000 : ℝ), (4598303620417/12500000000000 : ℝ), (117103558919/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056738053/2500000000 : ℝ)|^4691 ≤ (33235059940283/100000000000000 : ℝ)^3667
        have hw : |(1056738053/2500000000 : ℝ)|=(1056738053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35750643/78125000 : ℝ)|^4691 ≤ (4598303620417/12500000000000 : ℝ)^3667
        have hw : |(35750643/78125000 : ℝ)|=(35750643/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(24372349/62500000 : ℝ)|^4691 ≤ (117103558919/390625000000 : ℝ)^3667
        have hw : |(24372349/62500000 : ℝ)|=(24372349/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1593_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4097/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (103/1000 : ℝ)*pair X i i ≤ pair X i h) :
    (2579/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16371/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4097/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (103/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4097/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (103/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4097/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (103/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4097/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (103/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4097/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (103/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4097/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (103/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (103/1000 : ℝ) ^ (4687/1024 : ℝ) ≤ (606232815573411/20000000000000000000 : ℝ) := by
    have hpowers : (103/1000 : ℝ)^4687 ≤ (606232815573411/20000000000000000000 : ℝ)^1024 := by
      have hnat : (103 : ℕ)^4687*20000000000000000000^1024 ≤ 606232815573411^1024*1000^4687 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103 1000 606232815573411 20000000000000000000 4687 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (103/1000 : ℝ)) (X := (606232815573411/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4097/25000 : ℝ) ^ (4687/1024 : ℝ) ≤ (25396197950329089/100000000000000000000 : ℝ) := by
    have hpowers : (4097/25000 : ℝ)^4687 ≤ (25396197950329089/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4097 : ℕ)^4687*100000000000000000000^1024 ≤ 25396197950329089^1024*25000^4687 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4097 25000 25396197950329089 100000000000000000000 4687 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4097/25000 : ℝ)) (X := (25396197950329089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000606232815573411/10000000000000000000 : ℝ) ≤ (10000132444569619/10000000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (10000606232815573411/10000000000000000000 : ℝ)^1024 ≤ (10000132444569619/10000000000000000 : ℝ)^4687 := by
      have hnat : (10000606232815573411 : ℕ)^1024*10000000000000000^4687 ≤ 10000132444569619^4687*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000606232815573411 10000000000000000000 10000132444569619 10000000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000132444569619/10000000000000000 : ℝ)) (X := (10000606232815573411/10000000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251776710126762259/6250000000000000000 : ℝ) ≤ (2500155250616983/2500000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (6251776710126762259/6250000000000000000 : ℝ)^1024 ≤ (2500155250616983/2500000000000000 : ℝ)^4687 := by
      have hnat : (6251776710126762259 : ℕ)^1024*2500000000000000^4687 ≤ 2500155250616983^4687*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251776710126762259 6250000000000000000 2500155250616983 2500000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500155250616983/2500000000000000 : ℝ)) (X := (6251776710126762259/6250000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025396197950329089/50000000000000000000 : ℝ) ≤ (2000221912073249/2000000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (50025396197950329089/50000000000000000000 : ℝ)^1024 ≤ (2000221912073249/2000000000000000 : ℝ)^4687 := by
      have hnat : (50025396197950329089 : ℕ)^1024*2000000000000000^4687 ≤ 2000221912073249^4687*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025396197950329089 50000000000000000000 2000221912073249 2000000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000221912073249/2000000000000000 : ℝ)) (X := (50025396197950329089/50000000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(606232815573411/20000000000000000000 : ℝ) ≤ ((1902210688432331021/1902500000000000000 : ℝ)+2*(488557898313/608800000000000 : ℝ)*(103/1000 : ℝ))^(4687/1024 : ℝ) := by
    rw [show (1902210688432331021/1902500000000000000 : ℝ)+2*(488557898313/608800000000000 : ℝ)*(103/1000 : ℝ)=(10000132444569619/10000000000000000 : ℝ) by norm_num, show 1+2*(606232815573411/20000000000000000000 : ℝ)=(10000606232815573411/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25396197950329089/100000000000000000000 : ℝ)+(606232815573411/20000000000000000000 : ℝ) ≤ ((1902210688432331021/1902500000000000000 : ℝ)+(488557898313/608800000000000 : ℝ)*((4097/25000 : ℝ)+(103/1000 : ℝ)))^(4687/1024 : ℝ) := by
    rw [show (1902210688432331021/1902500000000000000 : ℝ)+(488557898313/608800000000000 : ℝ)*((4097/25000 : ℝ)+(103/1000 : ℝ))=(2500155250616983/2500000000000000 : ℝ) by norm_num, show 1+(25396197950329089/100000000000000000000 : ℝ)+(606232815573411/20000000000000000000 : ℝ)=(6251776710126762259/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25396197950329089/100000000000000000000 : ℝ) ≤ ((1902210688432331021/1902500000000000000 : ℝ)+2*(488557898313/608800000000000 : ℝ)*(4097/25000 : ℝ))^(4687/1024 : ℝ) := by
    rw [show (1902210688432331021/1902500000000000000 : ℝ)+2*(488557898313/608800000000000 : ℝ)*(4097/25000 : ℝ)=(2000221912073249/2000000000000000 : ℝ) by norm_num, show 1+2*(25396197950329089/100000000000000000000 : ℝ)=(50025396197950329089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1902210688432331021/1902500000000000000 : ℝ)*(X 1 0+X 2 0)+(488557898313/608800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (103/1000 : ℝ)) (hi := (4097/25000 : ℝ)) (c := (1902210688432331021/1902500000000000000 : ℝ)) (alpha := (488557898313/608800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1902210688432331021/1902500000000000000 : ℝ)*(X 0 1+X 2 1)+(488557898313/608800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (103/1000 : ℝ)) (hi := (4097/25000 : ℝ)) (c := (1902210688432331021/1902500000000000000 : ℝ)) (alpha := (488557898313/608800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1902210688432331021/1902500000000000000 : ℝ)*(X 0 2+X 1 2)+(488557898313/608800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (103/1000 : ℝ)) (hi := (4097/25000 : ℝ)) (c := (1902210688432331021/1902500000000000000 : ℝ)) (alpha := (488557898313/608800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-34960261/200000000 : ℝ)*X 0 0+(5464784587/10000000000 : ℝ)*X 0 1+(5178950459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355946333/10000000000 : ℝ)*X 1 0+(-947759881/5000000000 : ℝ)*X 1 1+(647368867/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355946409/10000000000 : ℝ)*X 2 0+(517895091/1000000000 : ℝ)*X 2 1+(-379103939/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((422677601/1000000000 : ℝ)*X 0 0+(3894455263/10000000000 : ℝ)*X 0 1+(4581149823/10000000000 : ℝ)*X 0 2+(422677601/1000000000 : ℝ)*X 1 0+(3894455263/10000000000 : ℝ)*X 1 1+(4581149823/10000000000 : ℝ)*X 1 2+(422677601/1000000000 : ℝ)*X 2 0+(3894455263/10000000000 : ℝ)*X 2 1+(4581149823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-874043273/5000000000 : ℝ)*X 0 0+(1036211967/2000000000 : ℝ)*X 0 1+(1365663231/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280287541/10000000000 : ℝ)*X 1 0+(-1611817451/10000000000 : ℝ)*X 1 1+(218506117/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280287543/10000000000 : ℝ)*X 2 0+(1365663231/2500000000 : ℝ)*X 2 1+(-32236349/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1056738053/2500000000 : ℝ)*X 0 0+(35750643/78125000 : ℝ)*X 0 1+(24372349/62500000 : ℝ)*X 0 2+(1056738053/2500000000 : ℝ)*X 1 0+(35750643/78125000 : ℝ)*X 1 1+(24372349/62500000 : ℝ)*X 1 2+(1056738053/2500000000 : ℝ)*X 2 0+(35750643/78125000 : ℝ)*X 2 1+(24372349/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (562971092463609185354564163/47562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (149442311/10000000000000 : ℝ)*(base19) + (164405109/12500000000000 : ℝ)*(base23) + (61279111/50000000000000 : ℝ)*(lower2) + (257444531/100000000000000 : ℝ)*(upper3) + (36440103/25000000000000 : ℝ)*(upper5) + (1238711601885933/50000000000000 : ℝ)*(major0) + (1238711601885933/50000000000000 : ℝ)*(major1) + (1238711601885933/50000000000000 : ℝ)*(major2) + (1749277494009383/50000000000000 : ℝ)*(sp0) + (874643924164171/25000000000000 : ℝ)*(sp1) + (1749287937919461/50000000000000 : ℝ)*(sp2) + (182032420823769/12500000000000 : ℝ)*(sp3) + (5550765257/25000000000000 : ℝ)*(sp4) + (2363831371/25000000000000 : ℝ)*(sp7) + (364067205478909/25000000000000 : ℝ)*(f.failure) + (1749288595539897/50000000000000 : ℝ)*(f.sum) + (69082601352229/15220000000000000000000000000 : ℝ)*base65 + (371058491301071609/47562500000000000000000000000000 : ℝ)*base67 + (597549499746821609/47562500000000000000000000000000 : ℝ)*base69 + (490868963118196609/47562500000000000000000000000000 : ℝ)*base71 + (49460154927851/15220000000000000000000000000 : ℝ)*base74 + (519475810194446609/47562500000000000000000000000000 : ℝ)*base75 + (627915963175321609/47562500000000000000000000000000 : ℝ)*base77 + (191407842083696609/47562500000000000000000000000000 : ℝ)*base79 + (33780080350509/15220000000000000000000000000 : ℝ)*base81 + (21479753/2500000000000000000000 : ℝ)*base90 + (21479753/2500000000000000000000 : ℝ)*base92 + (21479753/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (194067221511776510900421/15220000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1990988839/100000000000000 : ℝ)*(base19) + (2158257787/100000000000000 : ℝ)*(base23) + (39726069/6250000000000 : ℝ)*(lower1) + (268118757/100000000000000 : ℝ)*(upper3) + (74490521/100000000000000 : ℝ)*(lower4) + (132130811/50000000000000 : ℝ)*(upper5) + (1257343277983513/50000000000000 : ℝ)*(major0) + (1257343277983513/50000000000000 : ℝ)*(major1) + (1257343277983513/50000000000000 : ℝ)*(major2) + (216796331/12500000000000 : ℝ)*(sp2) + (355119987300543/10000000000000 : ℝ)*(sp4) + (221949867626037/6250000000000 : ℝ)*(sp5) + (710239196075399/20000000000000 : ℝ)*(sp6) + (184771601737731/12500000000000 : ℝ)*(sp7) + (184771601737731/12500000000000 : ℝ)*(f.failure) + (355119987300543/10000000000000 : ℝ)*(f.sum) + (55959239885551/15220000000000000000000000000 : ℝ)*base66 + (95166652809445051/47562500000000000000000000000000 : ℝ)*base68 + (48380406298179949/47562500000000000000000000000000 : ℝ)*base69 + (1027551757982320051/47562500000000000000000000000000 : ℝ)*base72 + (52641398662431/15220000000000000000000000000 : ℝ)*base74 + (983936955855679949/47562500000000000000000000000000 : ℝ)*base75 + (186243430127367449/47562500000000000000000000000000 : ℝ)*base77 + (94504060097570051/47562500000000000000000000000000 : ℝ)*base80 + (98151122622631/15220000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2228873/1250000000000000000000 : ℝ)*base89 + (2228873/1250000000000000000000 : ℝ)*base91 + (2228873/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1593_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4097/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (103/1000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2579/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16371/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1593_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1593_s5_0 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1748028091/10000000000 : ℝ)*x 0 + (2732352891/5000000000 : ℝ)*x 1 + (5179019349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1748028091/10000000000 : ℝ)^4691 ≤ (5370343543241/50000000000000 : ℝ)^3667 := by
    have hnat : (1748028091 : ℕ)^4691*50000000000000^3667 ≤ 5370343543241^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748028091 10000000000 5370343543241 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732352891/5000000000 : ℝ)^4691 ≤ (46161828908833/100000000000000 : ℝ)^3667 := by
    have hnat : (2732352891 : ℕ)^4691*100000000000000^3667 ≤ 46161828908833^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732352891 5000000000 46161828908833 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179019349/10000000000 : ℝ)^4691 ≤ (43097483997771/100000000000000 : ℝ)^3667 := by
    have hnat : (5179019349 : ℕ)^4691*100000000000000^3667 ≤ 43097483997771^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179019349 10000000000 43097483997771 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1748028091/10000000000 : ℝ), (2732352891/5000000000 : ℝ), (5179019349/10000000000 : ℝ)] ![(5370343543241/50000000000000 : ℝ), (46161828908833/100000000000000 : ℝ), (43097483997771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1748028091/10000000000 : ℝ)|^4691 ≤ (5370343543241/50000000000000 : ℝ)^3667
        have hw : |(-1748028091/10000000000 : ℝ)|=(1748028091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732352891/5000000000 : ℝ)|^4691 ≤ (46161828908833/100000000000000 : ℝ)^3667
        have hw : |(2732352891/5000000000 : ℝ)|=(2732352891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179019349/10000000000 : ℝ)|^4691 ≤ (43097483997771/100000000000000 : ℝ)^3667
        have hw : |(5179019349/10000000000 : ℝ)|=(5179019349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s5_1 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677963021/5000000000 : ℝ)*x 0 + (-1895456241/10000000000 : ℝ)*x 1 + (1035803879/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677963021/5000000000 : ℝ)^4691 ≤ (44989622222401/100000000000000 : ℝ)^3667 := by
    have hnat : (2677963021 : ℕ)^4691*100000000000000^3667 ≤ 44989622222401^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677963021 5000000000 44989622222401 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1895456241/10000000000 : ℝ)^4691 ≤ (5956446641037/50000000000000 : ℝ)^3667 := by
    have hnat : (1895456241 : ℕ)^4691*50000000000000^3667 ≤ 5956446641037^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895456241 10000000000 5956446641037 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035803879/2000000000 : ℝ)^4691 ≤ (1346796390233/3125000000000 : ℝ)^3667 := by
    have hnat : (1035803879 : ℕ)^4691*3125000000000^3667 ≤ 1346796390233^3667*2000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035803879 2000000000 1346796390233 3125000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677963021/5000000000 : ℝ), (-1895456241/10000000000 : ℝ), (1035803879/2000000000 : ℝ)] ![(44989622222401/100000000000000 : ℝ), (5956446641037/50000000000000 : ℝ), (1346796390233/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677963021/5000000000 : ℝ)|^4691 ≤ (44989622222401/100000000000000 : ℝ)^3667
        have hw : |(2677963021/5000000000 : ℝ)|=(2677963021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1895456241/10000000000 : ℝ)|^4691 ≤ (5956446641037/50000000000000 : ℝ)^3667
        have hw : |(-1895456241/10000000000 : ℝ)|=(1895456241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035803879/2000000000 : ℝ)|^4691 ≤ (1346796390233/3125000000000 : ℝ)^3667
        have hw : |(1035803879/2000000000 : ℝ)|=(1035803879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s5_2 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677963019/5000000000 : ℝ)*x 0 + (2589509709/5000000000 : ℝ)*x 1 + (-379091243/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677963019/5000000000 : ℝ)^4691 ≤ (22494811089709/50000000000000 : ℝ)^3667 := by
    have hnat : (2677963019 : ℕ)^4691*50000000000000^3667 ≤ 22494811089709^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677963019 5000000000 22494811089709 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589509709/5000000000 : ℝ)^4691 ≤ (21548742366149/50000000000000 : ℝ)^3667 := by
    have hnat : (2589509709 : ℕ)^4691*50000000000000^3667 ≤ 21548742366149^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589509709 5000000000 21548742366149 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (379091243/2000000000 : ℝ)^4691 ≤ (11912893073033/100000000000000 : ℝ)^3667 := by
    have hnat : (379091243 : ℕ)^4691*100000000000000^3667 ≤ 11912893073033^3667*2000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379091243 2000000000 11912893073033 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677963019/5000000000 : ℝ), (2589509709/5000000000 : ℝ), (-379091243/2000000000 : ℝ)] ![(22494811089709/50000000000000 : ℝ), (21548742366149/50000000000000 : ℝ), (11912893073033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677963019/5000000000 : ℝ)|^4691 ≤ (22494811089709/50000000000000 : ℝ)^3667
        have hw : |(2677963019/5000000000 : ℝ)|=(2677963019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589509709/5000000000 : ℝ)|^4691 ≤ (21548742366149/50000000000000 : ℝ)^3667
        have hw : |(2589509709/5000000000 : ℝ)|=(2589509709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-379091243/2000000000 : ℝ)|^4691 ≤ (11912893073033/100000000000000 : ℝ)^3667
        have hw : |(-379091243/2000000000 : ℝ)|=(379091243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s5_3 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2113393187/5000000000 : ℝ)*x 0 + (3894631209/10000000000 : ℝ)*x 1 + (2290485771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113393187/5000000000 : ℝ)^4691 ≤ (664667838093/2000000000000 : ℝ)^3667 := by
    have hnat : (2113393187 : ℕ)^4691*2000000000000^3667 ≤ 664667838093^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113393187 5000000000 664667838093 2000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3894631209/10000000000 : ℝ)^4691 ≤ (14964946144731/50000000000000 : ℝ)^3667 := by
    have hnat : (3894631209 : ℕ)^4691*50000000000000^3667 ≤ 14964946144731^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3894631209 10000000000 14964946144731 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2290485771/5000000000 : ℝ)^4691 ≤ (7367343158947/20000000000000 : ℝ)^3667 := by
    have hnat : (2290485771 : ℕ)^4691*20000000000000^3667 ≤ 7367343158947^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2290485771 5000000000 7367343158947 20000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2113393187/5000000000 : ℝ), (3894631209/10000000000 : ℝ), (2290485771/5000000000 : ℝ)] ![(664667838093/2000000000000 : ℝ), (14964946144731/50000000000000 : ℝ), (7367343158947/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2113393187/5000000000 : ℝ)|^4691 ≤ (664667838093/2000000000000 : ℝ)^3667
        have hw : |(2113393187/5000000000 : ℝ)|=(2113393187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3894631209/10000000000 : ℝ)|^4691 ≤ (14964946144731/50000000000000 : ℝ)^3667
        have hw : |(3894631209/10000000000 : ℝ)|=(3894631209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2290485771/5000000000 : ℝ)|^4691 ≤ (7367343158947/20000000000000 : ℝ)^3667
        have hw : |(2290485771/5000000000 : ℝ)|=(2290485771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s5_4 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1748101293/10000000000 : ℝ)*x 0 + (5181126443/10000000000 : ℝ)*x 1 + (1092515313/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1748101293/10000000000 : ℝ)^4691 ≤ (5370631239139/50000000000000 : ℝ)^3667 := by
    have hnat : (1748101293 : ℕ)^4691*50000000000000^3667 ≤ 5370631239139^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748101293 10000000000 5370631239139 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181126443/10000000000 : ℝ)^4691 ≤ (43119915971333/100000000000000 : ℝ)^3667 := by
    have hnat : (5181126443 : ℕ)^4691*100000000000000^3667 ≤ 43119915971333^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181126443 10000000000 43119915971333 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092515313/2000000000 : ℝ)^4691 ≤ (23069410767711/50000000000000 : ℝ)^3667 := by
    have hnat : (1092515313 : ℕ)^4691*50000000000000^3667 ≤ 23069410767711^3667*2000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092515313 2000000000 23069410767711 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1748101293/10000000000 : ℝ), (5181126443/10000000000 : ℝ), (1092515313/2000000000 : ℝ)] ![(5370631239139/50000000000000 : ℝ), (43119915971333/100000000000000 : ℝ), (23069410767711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1748101293/10000000000 : ℝ)|^4691 ≤ (5370631239139/50000000000000 : ℝ)^3667
        have hw : |(-1748101293/10000000000 : ℝ)|=(1748101293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181126443/10000000000 : ℝ)|^4691 ≤ (43119915971333/100000000000000 : ℝ)^3667
        have hw : |(5181126443/10000000000 : ℝ)|=(5181126443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092515313/2000000000 : ℝ)|^4691 ≤ (23069410767711/50000000000000 : ℝ)^3667
        have hw : |(1092515313/2000000000 : ℝ)|=(1092515313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s5_5 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280306043/10000000000 : ℝ)*x 0 + (-1611899051/10000000000 : ℝ)*x 1 + (1092515313/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280306043/10000000000 : ℝ)^4691 ≤ (4417864426273/10000000000000 : ℝ)^3667 := by
    have hnat : (5280306043 : ℕ)^4691*10000000000000^3667 ≤ 4417864426273^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280306043 10000000000 4417864426273 10000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1611899051/10000000000 : ℝ)^4691 ≤ (4841267091411/50000000000000 : ℝ)^3667 := by
    have hnat : (1611899051 : ℕ)^4691*50000000000000^3667 ≤ 4841267091411^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1611899051 10000000000 4841267091411 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092515313/2000000000 : ℝ)^4691 ≤ (23069410767711/50000000000000 : ℝ)^3667 := by
    have hnat : (1092515313 : ℕ)^4691*50000000000000^3667 ≤ 23069410767711^3667*2000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092515313 2000000000 23069410767711 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280306043/10000000000 : ℝ), (-1611899051/10000000000 : ℝ), (1092515313/2000000000 : ℝ)] ![(4417864426273/10000000000000 : ℝ), (4841267091411/50000000000000 : ℝ), (23069410767711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280306043/10000000000 : ℝ)|^4691 ≤ (4417864426273/10000000000000 : ℝ)^3667
        have hw : |(5280306043/10000000000 : ℝ)|=(5280306043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1611899051/10000000000 : ℝ)|^4691 ≤ (4841267091411/50000000000000 : ℝ)^3667
        have hw : |(-1611899051/10000000000 : ℝ)|=(1611899051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092515313/2000000000 : ℝ)|^4691 ≤ (23069410767711/50000000000000 : ℝ)^3667
        have hw : |(1092515313/2000000000 : ℝ)|=(1092515313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s5_6 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280306043/10000000000 : ℝ)*x 0 + (2731288283/5000000000 : ℝ)*x 1 + (-32237981/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280306043/10000000000 : ℝ)^4691 ≤ (4417864426273/10000000000000 : ℝ)^3667 := by
    have hnat : (5280306043 : ℕ)^4691*10000000000000^3667 ≤ 4417864426273^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280306043 10000000000 4417864426273 10000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731288283/5000000000 : ℝ)^4691 ≤ (46138821546227/100000000000000 : ℝ)^3667 := by
    have hnat : (2731288283 : ℕ)^4691*100000000000000^3667 ≤ 46138821546227^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731288283 5000000000 46138821546227 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32237981/200000000 : ℝ)^4691 ≤ (9682534175137/100000000000000 : ℝ)^3667 := by
    have hnat : (32237981 : ℕ)^4691*100000000000000^3667 ≤ 9682534175137^3667*200000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32237981 200000000 9682534175137 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280306043/10000000000 : ℝ), (2731288283/5000000000 : ℝ), (-32237981/200000000 : ℝ)] ![(4417864426273/10000000000000 : ℝ), (46138821546227/100000000000000 : ℝ), (9682534175137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280306043/10000000000 : ℝ)|^4691 ≤ (4417864426273/10000000000000 : ℝ)^3667
        have hw : |(5280306043/10000000000 : ℝ)|=(5280306043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731288283/5000000000 : ℝ)|^4691 ≤ (46138821546227/100000000000000 : ℝ)^3667
        have hw : |(2731288283/5000000000 : ℝ)|=(2731288283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32237981/200000000 : ℝ)|^4691 ≤ (9682534175137/100000000000000 : ℝ)^3667
        have hw : |(-32237981/200000000 : ℝ)|=(32237981/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s5_7 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528370273/1250000000 : ℝ)*x 0 + (4575909419/10000000000 : ℝ)*x 1 + (1949873211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528370273/1250000000 : ℝ)^4691 ≤ (33235160241469/100000000000000 : ℝ)^3667 := by
    have hnat : (528370273 : ℕ)^4691*100000000000000^3667 ≤ 33235160241469^3667*1250000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528370273 1250000000 33235160241469 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4575909419/10000000000 : ℝ)^4691 ≤ (9196162769907/25000000000000 : ℝ)^3667 := by
    have hnat : (4575909419 : ℕ)^4691*25000000000000^3667 ≤ 9196162769907^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4575909419 10000000000 9196162769907 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1949873211/5000000000 : ℝ)^4691 ≤ (29980188662591/100000000000000 : ℝ)^3667 := by
    have hnat : (1949873211 : ℕ)^4691*100000000000000^3667 ≤ 29980188662591^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949873211 5000000000 29980188662591 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528370273/1250000000 : ℝ), (4575909419/10000000000 : ℝ), (1949873211/5000000000 : ℝ)] ![(33235160241469/100000000000000 : ℝ), (9196162769907/25000000000000 : ℝ), (29980188662591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528370273/1250000000 : ℝ)|^4691 ≤ (33235160241469/100000000000000 : ℝ)^3667
        have hw : |(528370273/1250000000 : ℝ)|=(528370273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4575909419/10000000000 : ℝ)|^4691 ≤ (9196162769907/25000000000000 : ℝ)^3667
        have hw : |(4575909419/10000000000 : ℝ)|=(4575909419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1949873211/5000000000 : ℝ)|^4691 ≤ (29980188662591/100000000000000 : ℝ)^3667
        have hw : |(1949873211/5000000000 : ℝ)|=(1949873211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1593_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16371/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2579/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5159/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16369/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16371/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2579/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16371/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2579/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16371/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2579/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16371/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2579/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16371/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2579/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16371/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2579/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2579/25000 : ℝ) ^ (4687/1024 : ℝ) ≤ (381597002298749/12500000000000000000 : ℝ) := by
    have hpowers : (2579/25000 : ℝ)^4687 ≤ (381597002298749/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2579 : ℕ)^4687*12500000000000000000^1024 ≤ 381597002298749^1024*25000^4687 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2579 25000 381597002298749 12500000000000000000 4687 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2579/25000 : ℝ)) (X := (381597002298749/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16371/100000 : ℝ) ^ (4687/1024 : ℝ) ≤ (6318959578882601/25000000000000000000 : ℝ) := by
    have hpowers : (16371/100000 : ℝ)^4687 ≤ (6318959578882601/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16371 : ℕ)^4687*25000000000000000000^1024 ≤ 6318959578882601^1024*100000^4687 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16371 100000 6318959578882601 25000000000000000000 4687 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16371/100000 : ℝ)) (X := (6318959578882601/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250381597002298749/6250000000000000000 : ℝ) ≤ (500006669443277/500000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (6250381597002298749/6250000000000000000 : ℝ)^1024 ≤ (500006669443277/500000000000000 : ℝ)^4687 := by
      have hnat : (6250381597002298749 : ℕ)^1024*500000000000000^4687 ≤ 500006669443277^4687*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250381597002298749 6250000000000000000 500006669443277 500000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500006669443277/500000000000000 : ℝ)) (X := (6250381597002298749/6250000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25007082153583480099/25000000000000000000 : ℝ) ≤ (10000618845539861/10000000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (25007082153583480099/25000000000000000000 : ℝ)^1024 ≤ (10000618845539861/10000000000000000 : ℝ)^4687 := by
      have hnat : (25007082153583480099 : ℕ)^1024*10000000000000000^4687 ≤ 10000618845539861^4687*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007082153583480099 25000000000000000000 10000618845539861 10000000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000618845539861/10000000000000000 : ℝ)) (X := (25007082153583480099/25000000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506318959578882601/12500000000000000000 : ℝ) ≤ (5000552151107091/5000000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (12506318959578882601/12500000000000000000 : ℝ)^1024 ≤ (5000552151107091/5000000000000000 : ℝ)^4687 := by
      have hnat : (12506318959578882601 : ℕ)^1024*5000000000000000^4687 ≤ 5000552151107091^4687*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506318959578882601 12500000000000000000 5000552151107091 5000000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000552151107091/5000000000000000 : ℝ)) (X := (12506318959578882601/12500000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(381597002298749/12500000000000000000 : ℝ) ≤ ((15135197931869063457/15137500000000000000 : ℝ)+2*(485456674321/605500000000000 : ℝ)*(2579/25000 : ℝ))^(4687/1024 : ℝ) := by
    rw [show (15135197931869063457/15137500000000000000 : ℝ)+2*(485456674321/605500000000000 : ℝ)*(2579/25000 : ℝ)=(500006669443277/500000000000000 : ℝ) by norm_num, show 1+2*(381597002298749/12500000000000000000 : ℝ)=(6250381597002298749/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6318959578882601/25000000000000000000 : ℝ)+(381597002298749/12500000000000000000 : ℝ) ≤ ((15135197931869063457/15137500000000000000 : ℝ)+(485456674321/605500000000000 : ℝ)*((16371/100000 : ℝ)+(2579/25000 : ℝ)))^(4687/1024 : ℝ) := by
    rw [show (15135197931869063457/15137500000000000000 : ℝ)+(485456674321/605500000000000 : ℝ)*((16371/100000 : ℝ)+(2579/25000 : ℝ))=(10000618845539861/10000000000000000 : ℝ) by norm_num, show 1+(6318959578882601/25000000000000000000 : ℝ)+(381597002298749/12500000000000000000 : ℝ)=(25007082153583480099/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6318959578882601/25000000000000000000 : ℝ) ≤ ((15135197931869063457/15137500000000000000 : ℝ)+2*(485456674321/605500000000000 : ℝ)*(16371/100000 : ℝ))^(4687/1024 : ℝ) := by
    rw [show (15135197931869063457/15137500000000000000 : ℝ)+2*(485456674321/605500000000000 : ℝ)*(16371/100000 : ℝ)=(5000552151107091/5000000000000000 : ℝ) by norm_num, show 1+2*(6318959578882601/25000000000000000000 : ℝ)=(12506318959578882601/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15135197931869063457/15137500000000000000 : ℝ)*(X 1 0+X 2 0)+(485456674321/605500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (2579/25000 : ℝ)) (hi := (16371/100000 : ℝ)) (c := (15135197931869063457/15137500000000000000 : ℝ)) (alpha := (485456674321/605500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15135197931869063457/15137500000000000000 : ℝ)*(X 0 1+X 2 1)+(485456674321/605500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (2579/25000 : ℝ)) (hi := (16371/100000 : ℝ)) (c := (15135197931869063457/15137500000000000000 : ℝ)) (alpha := (485456674321/605500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15135197931869063457/15137500000000000000 : ℝ)*(X 0 2+X 1 2)+(485456674321/605500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (2579/25000 : ℝ)) (hi := (16371/100000 : ℝ)) (c := (15135197931869063457/15137500000000000000 : ℝ)) (alpha := (485456674321/605500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1748028091/10000000000 : ℝ)*X 0 0+(2732352891/5000000000 : ℝ)*X 0 1+(5179019349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677963021/5000000000 : ℝ)*X 1 0+(-1895456241/10000000000 : ℝ)*X 1 1+(1035803879/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677963019/5000000000 : ℝ)*X 2 0+(2589509709/5000000000 : ℝ)*X 2 1+(-379091243/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2113393187/5000000000 : ℝ)*X 0 0+(3894631209/10000000000 : ℝ)*X 0 1+(2290485771/5000000000 : ℝ)*X 0 2+(2113393187/5000000000 : ℝ)*X 1 0+(3894631209/10000000000 : ℝ)*X 1 1+(2290485771/5000000000 : ℝ)*X 1 2+(2113393187/5000000000 : ℝ)*X 2 0+(3894631209/10000000000 : ℝ)*X 2 1+(2290485771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1748101293/10000000000 : ℝ)*X 0 0+(5181126443/10000000000 : ℝ)*X 0 1+(1092515313/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280306043/10000000000 : ℝ)*X 1 0+(-1611899051/10000000000 : ℝ)*X 1 1+(1092515313/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280306043/10000000000 : ℝ)*X 2 0+(2731288283/5000000000 : ℝ)*X 2 1+(-32237981/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((528370273/1250000000 : ℝ)*X 0 0+(4575909419/10000000000 : ℝ)*X 0 1+(1949873211/5000000000 : ℝ)*X 0 2+(528370273/1250000000 : ℝ)*X 1 0+(4575909419/10000000000 : ℝ)*X 1 1+(1949873211/5000000000 : ℝ)*X 1 2+(528370273/1250000000 : ℝ)*X 2 0+(4575909419/10000000000 : ℝ)*X 2 1+(1949873211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (579634196892559155065771187/108125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17310789/2000000000000 : ℝ)*(base19) + (395245469/50000000000000 : ℝ)*(base23) + (38795283/100000000000000 : ℝ)*(lower2) + (62036871/50000000000000 : ℝ)*(upper3) + (89095491/100000000000000 : ℝ)*(upper5) + (2478687710279079/100000000000000 : ℝ)*(major0) + (2478687710279079/100000000000000 : ℝ)*(major1) + (2478687710279079/100000000000000 : ℝ)*(major2) + (70007044298637/2000000000000 : ℝ)*(sp0) + (700072451468649/20000000000000 : ℝ)*(sp1) + (1750181166195879/50000000000000 : ℝ)*(sp2) + (364251840488343/25000000000000 : ℝ)*(sp3) + (2181590169/20000000000000 : ℝ)*(sp4) + (4757029459/100000000000000 : ℝ)*(sp7) + (1457012118982831/100000000000000 : ℝ)*(f.failure) + (437545390360337/12500000000000 : ℝ)*(f.sum) + (37158576017029/7568750000000000000000000000 : ℝ)*base66 + (432276598159491103/1513750000000000000000000000000000 : ℝ)*base67 + (15033627097130741103/1513750000000000000000000000000000 : ℝ)*base69 + (2256757636178008897/1513750000000000000000000000000000 : ℝ)*base72 + (66701930621241/30275000000000000000000000000 : ℝ)*base74 + (1756772403744258897/1513750000000000000000000000000000 : ℝ)*base76 + (11128102399245508897/1513750000000000000000000000000000 : ℝ)*base78 + (8136314070214258897/1513750000000000000000000000000000 : ℝ)*base80 + (195092342198559/30275000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (35307827/10000000000000000000000 : ℝ)*base90 + (35307827/10000000000000000000000 : ℝ)*base92 + (35307827/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3330903469053461893330932897/378437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1375975037/100000000000000 : ℝ)*(base19) + (1490125269/100000000000000 : ℝ)*(base23) + (438997009/100000000000000 : ℝ)*(lower1) + (46335283/25000000000000 : ℝ)*(upper3) + (2560637/5000000000000 : ℝ)*(lower4) + (22818011/12500000000000 : ℝ)*(upper5) + (1257984508055231/50000000000000 : ℝ)*(major0) + (1257984508055231/50000000000000 : ℝ)*(major1) + (1257984508055231/50000000000000 : ℝ)*(major2) + (1198370221/100000000000000 : ℝ)*(sp2) + (1776505537213809/50000000000000 : ℝ)*(sp4) + (3553009698452581/100000000000000 : ℝ)*(sp5) + (111031512060379/3125000000000 : ℝ)*(sp6) + (369731666100599/25000000000000 : ℝ)*(sp7) + (369731666100599/25000000000000 : ℝ)*(f.failure) + (1776505537213809/50000000000000 : ℝ)*(f.sum) + (13695620844763/7568750000000000000000000000 : ℝ)*base65 + (12269312285429818567/756875000000000000000000000000000 : ℝ)*base67 + (4557264213414818567/756875000000000000000000000000000 : ℝ)*base69 + (3819583135780443567/756875000000000000000000000000000 : ℝ)*base71 + (182243730050727/30275000000000000000000000000 : ℝ)*base73 + (28127265946511693567/756875000000000000000000000000000 : ℝ)*base75 + (11175865517712318567/756875000000000000000000000000000 : ℝ)*base77 + (6000903014197318567/756875000000000000000000000000000 : ℝ)*base79 + (133706409242873/30275000000000000000000000000 : ℝ)*base82 + (41051483/2500000000000000000000 : ℝ)*base90 + (41051483/2500000000000000000000 : ℝ)*base92 + (41051483/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1593_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16371/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2579/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5159/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1593_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1593_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16571/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1267/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5159/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1593_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1593_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1593_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16571/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1267/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5159/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1593_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

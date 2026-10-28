-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1086_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:54:59.638282+00:00
-- url     : https://prove2.me/submissions/fde83cc5-97a4-43c1-866c-b487ada345e3

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
theorem support_rectangle_w1086_s6_0 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2193915559/10000000000 : ℝ)*x 0 + (1078901713/2000000000 : ℝ)*x 1 + (263217009/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2193915559/10000000000 : ℝ)^8279 ≤ (832861183919/6250000000000 : ℝ)^6231 := by
    have hnat : (2193915559 : ℕ)^8279*6250000000000^6231 ≤ 832861183919^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193915559 10000000000 832861183919 6250000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078901713/2000000000 : ℝ)^8279 ≤ (44040277996831/100000000000000 : ℝ)^6231 := by
    have hnat : (1078901713 : ℕ)^8279*100000000000000^6231 ≤ 44040277996831^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078901713 2000000000 44040277996831 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263217009/500000000 : ℝ)^8279 ≤ (266462144021/625000000000 : ℝ)^6231 := by
    have hnat : (263217009 : ℕ)^8279*625000000000^6231 ≤ 266462144021^6231*500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263217009 500000000 266462144021 625000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2193915559/10000000000 : ℝ), (1078901713/2000000000 : ℝ), (263217009/500000000 : ℝ)] ![(832861183919/6250000000000 : ℝ), (44040277996831/100000000000000 : ℝ), (266462144021/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2193915559/10000000000 : ℝ)|^8279 ≤ (832861183919/6250000000000 : ℝ)^6231
        have hw : |(-2193915559/10000000000 : ℝ)|=(2193915559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078901713/2000000000 : ℝ)|^8279 ≤ (44040277996831/100000000000000 : ℝ)^6231
        have hw : |(1078901713/2000000000 : ℝ)|=(1078901713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263217009/500000000 : ℝ)|^8279 ≤ (266462144021/625000000000 : ℝ)^6231
        have hw : |(263217009/500000000 : ℝ)|=(263217009/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s6_1 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66813183/125000000 : ℝ)*x 0 + (-282495091/1250000000 : ℝ)*x 1 + (5264340181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66813183/125000000 : ℝ)^8279 ≤ (43504650428853/100000000000000 : ℝ)^6231 := by
    have hnat : (66813183 : ℕ)^8279*100000000000000^6231 ≤ 43504650428853^6231*125000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66813183 125000000 43504650428853 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282495091/1250000000 : ℝ)^8279 ≤ (3465351628137/25000000000000 : ℝ)^6231 := by
    have hnat : (282495091 : ℕ)^8279*25000000000000^6231 ≤ 3465351628137^6231*1250000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282495091 1250000000 3465351628137 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264340181/10000000000 : ℝ)^8279 ≤ (1065848576353/2500000000000 : ℝ)^6231 := by
    have hnat : (5264340181 : ℕ)^8279*2500000000000^6231 ≤ 1065848576353^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264340181 10000000000 1065848576353 2500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66813183/125000000 : ℝ), (-282495091/1250000000 : ℝ), (5264340181/10000000000 : ℝ)] ![(43504650428853/100000000000000 : ℝ), (3465351628137/25000000000000 : ℝ), (1065848576353/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66813183/125000000 : ℝ)|^8279 ≤ (43504650428853/100000000000000 : ℝ)^6231
        have hw : |(66813183/125000000 : ℝ)|=(66813183/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-282495091/1250000000 : ℝ)|^8279 ≤ (3465351628137/25000000000000 : ℝ)^6231
        have hw : |(-282495091/1250000000 : ℝ)|=(282495091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264340181/10000000000 : ℝ)|^8279 ≤ (1065848576353/2500000000000 : ℝ)^6231
        have hw : |(5264340181/10000000000 : ℝ)|=(5264340181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s6_2 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66813183/125000000 : ℝ)*x 0 + (263217009/500000000 : ℝ)*x 1 + (-282495091/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66813183/125000000 : ℝ)^8279 ≤ (43504650428853/100000000000000 : ℝ)^6231 := by
    have hnat : (66813183 : ℕ)^8279*100000000000000^6231 ≤ 43504650428853^6231*125000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66813183 125000000 43504650428853 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263217009/500000000 : ℝ)^8279 ≤ (266462144021/625000000000 : ℝ)^6231 := by
    have hnat : (263217009 : ℕ)^8279*625000000000^6231 ≤ 266462144021^6231*500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263217009 500000000 266462144021 625000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282495091/1250000000 : ℝ)^8279 ≤ (3465351628137/25000000000000 : ℝ)^6231 := by
    have hnat : (282495091 : ℕ)^8279*25000000000000^6231 ≤ 3465351628137^6231*1250000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282495091 1250000000 3465351628137 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66813183/125000000 : ℝ), (263217009/500000000 : ℝ), (-282495091/1250000000 : ℝ)] ![(43504650428853/100000000000000 : ℝ), (266462144021/625000000000 : ℝ), (3465351628137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66813183/125000000 : ℝ)|^8279 ≤ (43504650428853/100000000000000 : ℝ)^6231
        have hw : |(66813183/125000000 : ℝ)|=(66813183/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263217009/500000000 : ℝ)|^8279 ≤ (266462144021/625000000000 : ℝ)^6231
        have hw : |(263217009/500000000 : ℝ)|=(263217009/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-282495091/1250000000 : ℝ)|^8279 ≤ (3465351628137/25000000000000 : ℝ)^6231
        have hw : |(-282495091/1250000000 : ℝ)|=(282495091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s6_3 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372598747/10000000000 : ℝ)*x 0 + (2123213503/5000000000 : ℝ)*x 1 + (450255221/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372598747/10000000000 : ℝ)^8279 ≤ (8329102906223/25000000000000 : ℝ)^6231 := by
    have hnat : (4372598747 : ℕ)^8279*25000000000000^6231 ≤ 8329102906223^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372598747 10000000000 8329102906223 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123213503/5000000000 : ℝ)^8279 ≤ (8011296266609/25000000000000 : ℝ)^6231 := by
    have hnat : (2123213503 : ℕ)^8279*25000000000000^6231 ≤ 8011296266609^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123213503 5000000000 8011296266609 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450255221/1000000000 : ℝ)^8279 ≤ (34638403292393/100000000000000 : ℝ)^6231 := by
    have hnat : (450255221 : ℕ)^8279*100000000000000^6231 ≤ 34638403292393^6231*1000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450255221 1000000000 34638403292393 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372598747/10000000000 : ℝ), (2123213503/5000000000 : ℝ), (450255221/1000000000 : ℝ)] ![(8329102906223/25000000000000 : ℝ), (8011296266609/25000000000000 : ℝ), (34638403292393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372598747/10000000000 : ℝ)|^8279 ≤ (8329102906223/25000000000000 : ℝ)^6231
        have hw : |(4372598747/10000000000 : ℝ)|=(4372598747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123213503/5000000000 : ℝ)|^8279 ≤ (8011296266609/25000000000000 : ℝ)^6231
        have hw : |(2123213503/5000000000 : ℝ)|=(2123213503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450255221/1000000000 : ℝ)|^8279 ≤ (34638403292393/100000000000000 : ℝ)^6231
        have hw : |(450255221/1000000000 : ℝ)|=(450255221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s6_4 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2193920741/10000000000 : ℝ)*x 0 + (5264668871/10000000000 : ℝ)*x 1 + (67427233/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2193920741/10000000000 : ℝ)^8279 ≤ (6662910381659/50000000000000 : ℝ)^6231 := by
    have hnat : (2193920741 : ℕ)^8279*50000000000000^6231 ≤ 6662910381659^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193920741 10000000000 6662910381659 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264668871/10000000000 : ℝ)^8279 ≤ (42637479952923/100000000000000 : ℝ)^6231 := by
    have hnat : (5264668871 : ℕ)^8279*100000000000000^6231 ≤ 42637479952923^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264668871 10000000000 42637479952923 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67427233/125000000 : ℝ)^8279 ≤ (22018349632499/50000000000000 : ℝ)^6231 := by
    have hnat : (67427233 : ℕ)^8279*50000000000000^6231 ≤ 22018349632499^6231*125000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67427233 125000000 22018349632499 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2193920741/10000000000 : ℝ), (5264668871/10000000000 : ℝ), (67427233/125000000 : ℝ)] ![(6662910381659/50000000000000 : ℝ), (42637479952923/100000000000000 : ℝ), (22018349632499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2193920741/10000000000 : ℝ)|^8279 ≤ (6662910381659/50000000000000 : ℝ)^6231
        have hw : |(-2193920741/10000000000 : ℝ)|=(2193920741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264668871/10000000000 : ℝ)|^8279 ≤ (42637479952923/100000000000000 : ℝ)^6231
        have hw : |(5264668871/10000000000 : ℝ)|=(5264668871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67427233/125000000 : ℝ)|^8279 ≤ (22018349632499/50000000000000 : ℝ)^6231
        have hw : |(67427233/125000000 : ℝ)|=(67427233/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s6_5 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312216211/10000000000 : ℝ)*x 0 + (-106506111/500000000 : ℝ)*x 1 + (1078835727/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312216211/10000000000 : ℝ)^8279 ≤ (10787470140667/25000000000000 : ℝ)^6231 := by
    have hnat : (5312216211 : ℕ)^8279*25000000000000^6231 ≤ 10787470140667^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312216211 10000000000 10787470140667 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106506111/500000000 : ℝ)^8279 ≤ (12813420205563/100000000000000 : ℝ)^6231 := by
    have hnat : (106506111 : ℕ)^8279*100000000000000^6231 ≤ 12813420205563^6231*500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106506111 500000000 12813420205563 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078835727/2000000000 : ℝ)^8279 ≤ (44036699210763/100000000000000 : ℝ)^6231 := by
    have hnat : (1078835727 : ℕ)^8279*100000000000000^6231 ≤ 44036699210763^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078835727 2000000000 44036699210763 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312216211/10000000000 : ℝ), (-106506111/500000000 : ℝ), (1078835727/2000000000 : ℝ)] ![(10787470140667/25000000000000 : ℝ), (12813420205563/100000000000000 : ℝ), (44036699210763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312216211/10000000000 : ℝ)|^8279 ≤ (10787470140667/25000000000000 : ℝ)^6231
        have hw : |(5312216211/10000000000 : ℝ)|=(5312216211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106506111/500000000 : ℝ)|^8279 ≤ (12813420205563/100000000000000 : ℝ)^6231
        have hw : |(-106506111/500000000 : ℝ)|=(106506111/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078835727/2000000000 : ℝ)|^8279 ≤ (44036699210763/100000000000000 : ℝ)^6231
        have hw : |(1078835727/2000000000 : ℝ)|=(1078835727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s6_6 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062443239/2000000000 : ℝ)*x 0 + (1078835727/2000000000 : ℝ)*x 1 + (-2130122243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062443239/2000000000 : ℝ)^8279 ≤ (10787470097497/25000000000000 : ℝ)^6231 := by
    have hnat : (1062443239 : ℕ)^8279*25000000000000^6231 ≤ 10787470097497^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062443239 2000000000 10787470097497 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078835727/2000000000 : ℝ)^8279 ≤ (44036699210763/100000000000000 : ℝ)^6231 := by
    have hnat : (1078835727 : ℕ)^8279*100000000000000^6231 ≤ 44036699210763^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078835727 2000000000 44036699210763 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2130122243/10000000000 : ℝ)^8279 ≤ (1281342038939/10000000000000 : ℝ)^6231 := by
    have hnat : (2130122243 : ℕ)^8279*10000000000000^6231 ≤ 1281342038939^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130122243 10000000000 1281342038939 10000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062443239/2000000000 : ℝ), (1078835727/2000000000 : ℝ), (-2130122243/10000000000 : ℝ)] ![(10787470097497/25000000000000 : ℝ), (44036699210763/100000000000000 : ℝ), (1281342038939/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062443239/2000000000 : ℝ)|^8279 ≤ (10787470097497/25000000000000 : ℝ)^6231
        have hw : |(1062443239/2000000000 : ℝ)|=(1062443239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078835727/2000000000 : ℝ)|^8279 ≤ (44036699210763/100000000000000 : ℝ)^6231
        have hw : |(1078835727/2000000000 : ℝ)|=(1078835727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2130122243/10000000000 : ℝ)|^8279 ≤ (1281342038939/10000000000000 : ℝ)^6231
        have hw : |(-2130122243/10000000000 : ℝ)|=(2130122243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s6_7 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372608871/10000000000 : ℝ)*x 0 + (4501905379/10000000000 : ℝ)*x 1 + (849415231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372608871/10000000000 : ℝ)^8279 ≤ (16658257058571/50000000000000 : ℝ)^6231 := by
    have hnat : (4372608871 : ℕ)^8279*50000000000000^6231 ≤ 16658257058571^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372608871 10000000000 16658257058571 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501905379/10000000000 : ℝ)^8279 ≤ (17315895897657/50000000000000 : ℝ)^6231 := by
    have hnat : (4501905379 : ℕ)^8279*50000000000000^6231 ≤ 17315895897657^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501905379 10000000000 17315895897657 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849415231/2000000000 : ℝ)^8279 ≤ (32051694070679/100000000000000 : ℝ)^6231 := by
    have hnat : (849415231 : ℕ)^8279*100000000000000^6231 ≤ 32051694070679^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849415231 2000000000 32051694070679 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372608871/10000000000 : ℝ), (4501905379/10000000000 : ℝ), (849415231/2000000000 : ℝ)] ![(16658257058571/50000000000000 : ℝ), (17315895897657/50000000000000 : ℝ), (32051694070679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372608871/10000000000 : ℝ)|^8279 ≤ (16658257058571/50000000000000 : ℝ)^6231
        have hw : |(4372608871/10000000000 : ℝ)|=(4372608871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501905379/10000000000 : ℝ)|^8279 ≤ (17315895897657/50000000000000 : ℝ)^6231
        have hw : |(4501905379/10000000000 : ℝ)|=(4501905379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849415231/2000000000 : ℝ)|^8279 ≤ (32051694070679/100000000000000 : ℝ)^6231
        have hw : |(849415231/2000000000 : ℝ)|=(849415231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1086_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11269/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7013/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1123/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1123/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1123/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1123/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1123/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1123/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1123/10000 : ℝ) ^ (4139/1024 : ℝ) ≤ (14509164135863423/100000000000000000000 : ℝ) := by
    have hpowers : (1123/10000 : ℝ)^4139 ≤ (14509164135863423/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1123 : ℕ)^4139*100000000000000000000^1024 ≤ 14509164135863423^1024*10000^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1123 10000 14509164135863423 100000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1123/10000 : ℝ)) (X := (14509164135863423/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7033/50000 : ℝ) ^ (4139/1024 : ℝ) ≤ (36050581387464679/100000000000000000000 : ℝ) := by
    have hpowers : (7033/50000 : ℝ)^4139 ≤ (36050581387464679/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7033 : ℕ)^4139*100000000000000000000^1024 ≤ 36050581387464679^1024*50000^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7033 50000 36050581387464679 100000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7033/50000 : ℝ)) (X := (36050581387464679/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014509164135863423/50000000000000000000 : ℝ) ≤ (80005742744427/80000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (50014509164135863423/50000000000000000000 : ℝ)^1024 ≤ (80005742744427/80000000000000 : ℝ)^4139 := by
      have hnat : (50014509164135863423 : ℕ)^1024*80000000000000^4139 ≤ 80005742744427^4139*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014509164135863423 50000000000000000000 80005742744427 80000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80005742744427/80000000000000 : ℝ)) (X := (50014509164135863423/50000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025279872761664051/50000000000000000000 : ℝ) ≤ (1000125062411659/1000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (50025279872761664051/50000000000000000000 : ℝ)^1024 ≤ (1000125062411659/1000000000000000 : ℝ)^4139 := by
      have hnat : (50025279872761664051 : ℕ)^1024*1000000000000000^4139 ≤ 1000125062411659^4139*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025279872761664051 50000000000000000000 1000125062411659 1000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000125062411659/1000000000000000 : ℝ)) (X := (50025279872761664051/50000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036050581387464679/50000000000000000000 : ℝ) ≤ (2000356681035961/2000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (50036050581387464679/50000000000000000000 : ℝ)^1024 ≤ (2000356681035961/2000000000000000 : ℝ)^4139 := by
      have hnat : (50036050581387464679 : ℕ)^1024*2000000000000000^4139 ≤ 2000356681035961^4139*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036050581387464679 50000000000000000000 2000356681035961 2000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000356681035961/2000000000000000 : ℝ)) (X := (50036050581387464679/50000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14509164135863423/100000000000000000000 : ℝ) ≤ ((141750347701097813/141800000000000000 : ℝ)+2*(106556212643/56720000000000 : ℝ)*(1123/10000 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (141750347701097813/141800000000000000 : ℝ)+2*(106556212643/56720000000000 : ℝ)*(1123/10000 : ℝ)=(80005742744427/80000000000000 : ℝ) by norm_num, show 1+2*(14509164135863423/100000000000000000000 : ℝ)=(50014509164135863423/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36050581387464679/100000000000000000000 : ℝ)+(14509164135863423/100000000000000000000 : ℝ) ≤ ((141750347701097813/141800000000000000 : ℝ)+(106556212643/56720000000000 : ℝ)*((7033/50000 : ℝ)+(1123/10000 : ℝ)))^(4139/1024 : ℝ) := by
    rw [show (141750347701097813/141800000000000000 : ℝ)+(106556212643/56720000000000 : ℝ)*((7033/50000 : ℝ)+(1123/10000 : ℝ))=(1000125062411659/1000000000000000 : ℝ) by norm_num, show 1+(36050581387464679/100000000000000000000 : ℝ)+(14509164135863423/100000000000000000000 : ℝ)=(50025279872761664051/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36050581387464679/100000000000000000000 : ℝ) ≤ ((141750347701097813/141800000000000000 : ℝ)+2*(106556212643/56720000000000 : ℝ)*(7033/50000 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (141750347701097813/141800000000000000 : ℝ)+2*(106556212643/56720000000000 : ℝ)*(7033/50000 : ℝ)=(2000356681035961/2000000000000000 : ℝ) by norm_num, show 1+2*(36050581387464679/100000000000000000000 : ℝ)=(50036050581387464679/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (141750347701097813/141800000000000000 : ℝ)*(X 1 0+X 2 0)+(106556212643/56720000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (1123/10000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (141750347701097813/141800000000000000 : ℝ)) (alpha := (106556212643/56720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (141750347701097813/141800000000000000 : ℝ)*(X 0 1+X 2 1)+(106556212643/56720000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (1123/10000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (141750347701097813/141800000000000000 : ℝ)) (alpha := (106556212643/56720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (141750347701097813/141800000000000000 : ℝ)*(X 0 2+X 1 2)+(106556212643/56720000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (1123/10000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (141750347701097813/141800000000000000 : ℝ)) (alpha := (106556212643/56720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2193915559/10000000000 : ℝ)*X 0 0+(1078901713/2000000000 : ℝ)*X 0 1+(263217009/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66813183/125000000 : ℝ)*X 1 0+(-282495091/1250000000 : ℝ)*X 1 1+(5264340181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66813183/125000000 : ℝ)*X 2 0+(263217009/500000000 : ℝ)*X 2 1+(-282495091/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4372598747/10000000000 : ℝ)*X 0 0+(2123213503/5000000000 : ℝ)*X 0 1+(450255221/1000000000 : ℝ)*X 0 2+(4372598747/10000000000 : ℝ)*X 1 0+(2123213503/5000000000 : ℝ)*X 1 1+(450255221/1000000000 : ℝ)*X 1 2+(4372598747/10000000000 : ℝ)*X 2 0+(2123213503/5000000000 : ℝ)*X 2 1+(450255221/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2193920741/10000000000 : ℝ)*X 0 0+(5264668871/10000000000 : ℝ)*X 0 1+(67427233/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312216211/10000000000 : ℝ)*X 1 0+(-106506111/500000000 : ℝ)*X 1 1+(1078835727/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062443239/2000000000 : ℝ)*X 2 0+(1078835727/2000000000 : ℝ)*X 2 1+(-2130122243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372608871/10000000000 : ℝ)*X 0 0+(4501905379/10000000000 : ℝ)*X 0 1+(849415231/2000000000 : ℝ)*X 0 2+(4372608871/10000000000 : ℝ)*X 1 0+(4501905379/10000000000 : ℝ)*X 1 1+(849415231/2000000000 : ℝ)*X 1 2+(4372608871/10000000000 : ℝ)*X 2 0+(4501905379/10000000000 : ℝ)*X 2 1+(849415231/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3081647535828412286862939/709000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34806119/4000000000000 : ℝ)*(base19) + (810922069/100000000000000 : ℝ)*(base23) + (7914811/25000000000000 : ℝ)*(lower2) + (55428579/50000000000000 : ℝ)*(upper3) + (8235301/12500000000000 : ℝ)*(upper5) + (1158676952851251/20000000000000 : ℝ)*(major0) + (1158676952851251/20000000000000 : ℝ)*(major1) + (1158676952851251/20000000000000 : ℝ)*(major2) + (7682381353829309/100000000000000 : ℝ)*(sp0) + (384120187113233/5000000000000 : ℝ)*(sp1) + (3841201900747783/50000000000000 : ℝ)*(sp2) + (1952175986400343/50000000000000 : ℝ)*(sp3) + (930343533/4000000000000 : ℝ)*(sp4) + (12798411829/100000000000000 : ℝ)*(sp7) + (780872954242503/20000000000000 : ℝ)*(f.failure) + (1536480922483527/20000000000000 : ℝ)*(f.sum) + (1643659899989/567200000000000000000000000 : ℝ)*base65 + (21678136312015437/2836000000000000000000000000000 : ℝ)*base68 + (27898193901903437/2836000000000000000000000000000 : ℝ)*base70 + (25236695040839437/2836000000000000000000000000000 : ℝ)*base72 + (566845570593/2836000000000000000000000000 : ℝ)*base73 + (84832566688143437/2836000000000000000000000000000 : ℝ)*base76 + (6110452868920563/2836000000000000000000000000000 : ℝ)*base77 + (81817158979935437/2836000000000000000000000000000 : ℝ)*base80 + (4800964161887/2836000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4159107/1000000000000000000000 : ℝ)*base90 + (4159107/1000000000000000000000 : ℝ)*base92 + (4159107/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11631024908704495755259947/1772500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30527689/2000000000000 : ℝ)*(base19) + (306418191/20000000000000 : ℝ)*(base23) + (30132879/20000000000000 : ℝ)*(upper3) + (2434111/12500000000000 : ℝ)*(lower4) + (84768937/50000000000000 : ℝ)*(upper5) + (2911405354091423/50000000000000 : ℝ)*(major0) + (2911405354091423/50000000000000 : ℝ)*(major1) + (2911405354091423/50000000000000 : ℝ)*(major2) + (1689793077/4000000000000 : ℝ)*(sp1) + (20500085363/50000000000000 : ℝ)*(sp2) + (7721425252850551/100000000000000 : ℝ)*(sp4) + (965172685204897/12500000000000 : ℝ)*(sp5) + (7721382720588869/100000000000000 : ℝ)*(sp6) + (981048986196013/25000000000000 : ℝ)*(sp7) + (981048986196013/25000000000000 : ℝ)*(f.failure) + (7721425252850551/100000000000000 : ℝ)*(f.sum) + (6362602413571/1418000000000000000000000000 : ℝ)*base65 + (125548411209779601/7090000000000000000000000000000 : ℝ)*base68 + (141822776443169601/7090000000000000000000000000000 : ℝ)*base70 + (12901735375310399/7090000000000000000000000000000 : ℝ)*base71 + (1413958957359/283600000000000000000000000 : ℝ)*base74 + (264550304537219601/7090000000000000000000000000000 : ℝ)*base76 + (47852034753999601/7090000000000000000000000000000 : ℝ)*base78 + (137284393019439601/7090000000000000000000000000000 : ℝ)*base80 + (6627371380581/1418000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (17160703/1250000000000000000000 : ℝ)*base89 + (17160703/1250000000000000000000 : ℝ)*base91 + (17160703/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1086_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7013/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1086_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1086_s7_0 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2193949471/10000000000 : ℝ)*x 0 + (5394087999/10000000000 : ℝ)*x 1 + (5264738691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2193949471/10000000000 : ℝ)^8279 ≤ (13326052625397/100000000000000 : ℝ)^6231 := by
    have hnat : (2193949471 : ℕ)^8279*100000000000000^6231 ≤ 13326052625397^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193949471 10000000000 13326052625397 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394087999/10000000000 : ℝ)^8279 ≤ (8807143216991/20000000000000 : ℝ)^6231 := by
    have hnat : (5394087999 : ℕ)^8279*20000000000000^6231 ≤ 8807143216991^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394087999 10000000000 8807143216991 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264738691/10000000000 : ℝ)^8279 ≤ (8527646253353/20000000000000 : ℝ)^6231 := by
    have hnat : (5264738691 : ℕ)^8279*20000000000000^6231 ≤ 8527646253353^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264738691 10000000000 8527646253353 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2193949471/10000000000 : ℝ), (5394087999/10000000000 : ℝ), (5264738691/10000000000 : ℝ)] ![(13326052625397/100000000000000 : ℝ), (8807143216991/20000000000000 : ℝ), (8527646253353/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2193949471/10000000000 : ℝ)|^8279 ≤ (13326052625397/100000000000000 : ℝ)^6231
        have hw : |(-2193949471/10000000000 : ℝ)|=(2193949471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394087999/10000000000 : ℝ)|^8279 ≤ (8807143216991/20000000000000 : ℝ)^6231
        have hw : |(5394087999/10000000000 : ℝ)|=(5394087999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264738691/10000000000 : ℝ)|^8279 ≤ (8527646253353/20000000000000 : ℝ)^6231
        have hw : |(5264738691/10000000000 : ℝ)|=(5264738691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s7_1 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672475053/5000000000 : ℝ)*x 0 + (-1129786529/5000000000 : ℝ)*x 1 + (2632369413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672475053/5000000000 : ℝ)^8279 ≤ (43503519956779/100000000000000 : ℝ)^6231 := by
    have hnat : (2672475053 : ℕ)^8279*100000000000000^6231 ≤ 43503519956779^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672475053 5000000000 43503519956779 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129786529/5000000000 : ℝ)^8279 ≤ (13858247317137/100000000000000 : ℝ)^6231 := by
    have hnat : (1129786529 : ℕ)^8279*100000000000000^6231 ≤ 13858247317137^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129786529 5000000000 13858247317137 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632369413/5000000000 : ℝ)^8279 ≤ (21319116359733/50000000000000 : ℝ)^6231 := by
    have hnat : (2632369413 : ℕ)^8279*50000000000000^6231 ≤ 21319116359733^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632369413 5000000000 21319116359733 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672475053/5000000000 : ℝ), (-1129786529/5000000000 : ℝ), (2632369413/5000000000 : ℝ)] ![(43503519956779/100000000000000 : ℝ), (13858247317137/100000000000000 : ℝ), (21319116359733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672475053/5000000000 : ℝ)|^8279 ≤ (43503519956779/100000000000000 : ℝ)^6231
        have hw : |(2672475053/5000000000 : ℝ)|=(2672475053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1129786529/5000000000 : ℝ)|^8279 ≤ (13858247317137/100000000000000 : ℝ)^6231
        have hw : |(-1129786529/5000000000 : ℝ)|=(1129786529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632369413/5000000000 : ℝ)|^8279 ≤ (21319116359733/50000000000000 : ℝ)^6231
        have hw : |(2632369413/5000000000 : ℝ)|=(2632369413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s7_2 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336237607/2500000000 : ℝ)*x 0 + (1316184651/2500000000 : ℝ)*x 1 + (-2259572923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336237607/2500000000 : ℝ)^8279 ≤ (43503523439003/100000000000000 : ℝ)^6231 := by
    have hnat : (1336237607 : ℕ)^8279*100000000000000^6231 ≤ 43503523439003^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336237607 2500000000 43503523439003 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316184651/2500000000 : ℝ)^8279 ≤ (42638230330579/100000000000000 : ℝ)^6231 := by
    have hnat : (1316184651 : ℕ)^8279*100000000000000^6231 ≤ 42638230330579^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316184651 2500000000 42638230330579 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259572923/10000000000 : ℝ)^8279 ≤ (3464561554257/25000000000000 : ℝ)^6231 := by
    have hnat : (2259572923 : ℕ)^8279*25000000000000^6231 ≤ 3464561554257^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259572923 10000000000 3464561554257 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336237607/2500000000 : ℝ), (1316184651/2500000000 : ℝ), (-2259572923/10000000000 : ℝ)] ![(43503523439003/100000000000000 : ℝ), (42638230330579/100000000000000 : ℝ), (3464561554257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336237607/2500000000 : ℝ)|^8279 ≤ (43503523439003/100000000000000 : ℝ)^6231
        have hw : |(1336237607/2500000000 : ℝ)|=(1336237607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316184651/2500000000 : ℝ)|^8279 ≤ (42638230330579/100000000000000 : ℝ)^6231
        have hw : |(1316184651/2500000000 : ℝ)|=(1316184651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2259572923/10000000000 : ℝ)|^8279 ≤ (3464561554257/25000000000000 : ℝ)^6231
        have hw : |(-2259572923/10000000000 : ℝ)|=(2259572923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s7_3 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372619809/10000000000 : ℝ)*x 0 + (4247230283/10000000000 : ℝ)*x 1 + (4501743339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372619809/10000000000 : ℝ)^8279 ≤ (8329156212541/25000000000000 : ℝ)^6231 := by
    have hnat : (4372619809 : ℕ)^8279*25000000000000^6231 ≤ 8329156212541^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372619809 10000000000 8329156212541 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4247230283/10000000000 : ℝ)^8279 ≤ (1602661977857/5000000000000 : ℝ)^6231 := by
    have hnat : (4247230283 : ℕ)^8279*5000000000000^6231 ≤ 1602661977857^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247230283 10000000000 1602661977857 5000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501743339/10000000000 : ℝ)^8279 ≤ (34630135573899/100000000000000 : ℝ)^6231 := by
    have hnat : (4501743339 : ℕ)^8279*100000000000000^6231 ≤ 34630135573899^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501743339 10000000000 34630135573899 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372619809/10000000000 : ℝ), (4247230283/10000000000 : ℝ), (4501743339/10000000000 : ℝ)] ![(8329156212541/25000000000000 : ℝ), (1602661977857/5000000000000 : ℝ), (34630135573899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372619809/10000000000 : ℝ)|^8279 ≤ (8329156212541/25000000000000 : ℝ)^6231
        have hw : |(4372619809/10000000000 : ℝ)|=(4372619809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4247230283/10000000000 : ℝ)|^8279 ≤ (1602661977857/5000000000000 : ℝ)^6231
        have hw : |(4247230283/10000000000 : ℝ)|=(4247230283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501743339/10000000000 : ℝ)|^8279 ≤ (34630135573899/100000000000000 : ℝ)^6231
        have hw : |(4501743339/10000000000 : ℝ)|=(4501743339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s7_4 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2193954637/10000000000 : ℝ)*x 0 + (2632531679/5000000000 : ℝ)*x 1 + (2696881031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2193954637/10000000000 : ℝ)^8279 ≤ (13326094317097/100000000000000 : ℝ)^6231 := by
    have hnat : (2193954637 : ℕ)^8279*100000000000000^6231 ≤ 13326094317097^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193954637 10000000000 13326094317097 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632531679/5000000000 : ℝ)^8279 ≤ (42641724962189/100000000000000 : ℝ)^6231 := by
    have hnat : (2632531679 : ℕ)^8279*100000000000000^6231 ≤ 42641724962189^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632531679 5000000000 42641724962189 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696881031/5000000000 : ℝ)^8279 ≤ (11008045175389/25000000000000 : ℝ)^6231 := by
    have hnat : (2696881031 : ℕ)^8279*25000000000000^6231 ≤ 11008045175389^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696881031 5000000000 11008045175389 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2193954637/10000000000 : ℝ), (2632531679/5000000000 : ℝ), (2696881031/5000000000 : ℝ)] ![(13326094317097/100000000000000 : ℝ), (42641724962189/100000000000000 : ℝ), (11008045175389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2193954637/10000000000 : ℝ)|^8279 ≤ (13326094317097/100000000000000 : ℝ)^6231
        have hw : |(-2193954637/10000000000 : ℝ)|=(2193954637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632531679/5000000000 : ℝ)|^8279 ≤ (42641724962189/100000000000000 : ℝ)^6231
        have hw : |(2632531679/5000000000 : ℝ)|=(2632531679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696881031/5000000000 : ℝ)|^8279 ≤ (11008045175389/25000000000000 : ℝ)^6231
        have hw : |(2696881031/5000000000 : ℝ)|=(2696881031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s7_5 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656159123/5000000000 : ℝ)*x 0 + (-213054977/1000000000 : ℝ)*x 1 + (2696881031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656159123/5000000000 : ℝ)^8279 ≤ (43150981783773/100000000000000 : ℝ)^6231 := by
    have hnat : (2656159123 : ℕ)^8279*100000000000000^6231 ≤ 43150981783773^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656159123 5000000000 43150981783773 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (213054977/1000000000 : ℝ)^8279 ≤ (12816837496169/100000000000000 : ℝ)^6231 := by
    have hnat : (213054977 : ℕ)^8279*100000000000000^6231 ≤ 12816837496169^6231*1000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213054977 1000000000 12816837496169 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696881031/5000000000 : ℝ)^8279 ≤ (11008045175389/25000000000000 : ℝ)^6231 := by
    have hnat : (2696881031 : ℕ)^8279*25000000000000^6231 ≤ 11008045175389^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696881031 5000000000 11008045175389 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656159123/5000000000 : ℝ), (-213054977/1000000000 : ℝ), (2696881031/5000000000 : ℝ)] ![(43150981783773/100000000000000 : ℝ), (12816837496169/100000000000000 : ℝ), (11008045175389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656159123/5000000000 : ℝ)|^8279 ≤ (43150981783773/100000000000000 : ℝ)^6231
        have hw : |(2656159123/5000000000 : ℝ)|=(2656159123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-213054977/1000000000 : ℝ)|^8279 ≤ (12816837496169/100000000000000 : ℝ)^6231
        have hw : |(-213054977/1000000000 : ℝ)|=(213054977/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696881031/5000000000 : ℝ)|^8279 ≤ (11008045175389/25000000000000 : ℝ)^6231
        have hw : |(2696881031/5000000000 : ℝ)|=(2696881031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s7_6 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312318249/10000000000 : ℝ)*x 0 + (5393762061/10000000000 : ℝ)*x 1 + (-2130549769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312318249/10000000000 : ℝ)^8279 ≤ (43150981816151/100000000000000 : ℝ)^6231 := by
    have hnat : (5312318249 : ℕ)^8279*100000000000000^6231 ≤ 43150981816151^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312318249 10000000000 43150981816151 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393762061/10000000000 : ℝ)^8279 ≤ (44032180690709/100000000000000 : ℝ)^6231 := by
    have hnat : (5393762061 : ℕ)^8279*100000000000000^6231 ≤ 44032180690709^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393762061 10000000000 44032180690709 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2130549769/10000000000 : ℝ)^8279 ≤ (801052343011/6250000000000 : ℝ)^6231 := by
    have hnat : (2130549769 : ℕ)^8279*6250000000000^6231 ≤ 801052343011^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130549769 10000000000 801052343011 6250000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312318249/10000000000 : ℝ), (5393762061/10000000000 : ℝ), (-2130549769/10000000000 : ℝ)] ![(43150981816151/100000000000000 : ℝ), (44032180690709/100000000000000 : ℝ), (801052343011/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312318249/10000000000 : ℝ)|^8279 ≤ (43150981816151/100000000000000 : ℝ)^6231
        have hw : |(5312318249/10000000000 : ℝ)|=(5312318249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393762061/10000000000 : ℝ)|^8279 ≤ (44032180690709/100000000000000 : ℝ)^6231
        have hw : |(5393762061/10000000000 : ℝ)|=(5393762061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2130549769/10000000000 : ℝ)|^8279 ≤ (801052343011/6250000000000 : ℝ)^6231
        have hw : |(-2130549769/10000000000 : ℝ)|=(2130549769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s7_7 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372629609/10000000000 : ℝ)*x 0 + (562638089/1250000000 : ℝ)*x 1 + (2123935659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372629609/10000000000 : ℝ)^8279 ≤ (33316724062493/100000000000000 : ℝ)^6231 := by
    have hnat : (4372629609 : ℕ)^8279*100000000000000^6231 ≤ 33316724062493^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372629609 10000000000 33316724062493 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562638089/1250000000 : ℝ)^8279 ≤ (6924721663289/20000000000000 : ℝ)^6231 := by
    have hnat : (562638089 : ℕ)^8279*20000000000000^6231 ≤ 6924721663289^6231*1250000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562638089 1250000000 6924721663289 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123935659/5000000000 : ℝ)^8279 ≤ (8014916900007/25000000000000 : ℝ)^6231 := by
    have hnat : (2123935659 : ℕ)^8279*25000000000000^6231 ≤ 8014916900007^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123935659 5000000000 8014916900007 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372629609/10000000000 : ℝ), (562638089/1250000000 : ℝ), (2123935659/5000000000 : ℝ)] ![(33316724062493/100000000000000 : ℝ), (6924721663289/20000000000000 : ℝ), (8014916900007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372629609/10000000000 : ℝ)|^8279 ≤ (33316724062493/100000000000000 : ℝ)^6231
        have hw : |(4372629609/10000000000 : ℝ)|=(4372629609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562638089/1250000000 : ℝ)|^8279 ≤ (6924721663289/20000000000000 : ℝ)^6231
        have hw : |(562638089/1250000000 : ℝ)|=(562638089/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123935659/5000000000 : ℝ)|^8279 ≤ (8014916900007/25000000000000 : ℝ)^6231
        have hw : |(2123935659/5000000000 : ℝ)|=(2123935659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1086_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7013/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11277/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14017/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7013/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7013/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7013/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7013/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7013/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7013/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11269/100000 : ℝ) ^ (4139/1024 : ℝ) ≤ (147139104518197/1000000000000000000 : ℝ) := by
    have hpowers : (11269/100000 : ℝ)^4139 ≤ (147139104518197/1000000000000000000 : ℝ)^1024 := by
      have hnat : (11269 : ℕ)^4139*1000000000000000000^1024 ≤ 147139104518197^1024*100000^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11269 100000 147139104518197 1000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11269/100000 : ℝ)) (X := (147139104518197/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7013/50000 : ℝ) ^ (4139/1024 : ℝ) ≤ (1781899591278607/5000000000000000000 : ℝ) := by
    have hpowers : (7013/50000 : ℝ)^4139 ≤ (1781899591278607/5000000000000000000 : ℝ)^1024 := by
      have hnat : (7013 : ℕ)^4139*5000000000000000000^1024 ≤ 1781899591278607^1024*50000^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7013 50000 1781899591278607 5000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7013/50000 : ℝ)) (X := (1781899591278607/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (500147139104518197/500000000000000000 : ℝ) ≤ (5000363985893161/5000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (500147139104518197/500000000000000000 : ℝ)^1024 ≤ (5000363985893161/5000000000000000 : ℝ)^4139 := by
      have hnat : (500147139104518197 : ℕ)^1024*5000000000000000^4139 ≤ 5000363985893161^4139*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500147139104518197 500000000000000000 5000363985893161 5000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000363985893161/5000000000000000 : ℝ)) (X := (500147139104518197/500000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (625314699389233699/625000000000000000 : ℝ) ≤ (5000622741984591/5000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (625314699389233699/625000000000000000 : ℝ)^1024 ≤ (5000622741984591/5000000000000000 : ℝ)^4139 := by
      have hnat : (625314699389233699 : ℕ)^1024*5000000000000000^4139 ≤ 5000622741984591^4139*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625314699389233699 625000000000000000 5000622741984591 5000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000622741984591/5000000000000000 : ℝ)) (X := (625314699389233699/625000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501781899591278607/2500000000000000000 : ℝ) ≤ (5000881498076021/5000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (2501781899591278607/2500000000000000000 : ℝ)^1024 ≤ (5000881498076021/5000000000000000 : ℝ)^4139 := by
      have hnat : (2501781899591278607 : ℕ)^1024*5000000000000000^4139 ≤ 5000881498076021^4139*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501781899591278607 2500000000000000000 5000881498076021 5000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000881498076021/5000000000000000 : ℝ)) (X := (2501781899591278607/2500000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(147139104518197/1000000000000000000 : ℝ) ≤ ((13780171664318795537/13785000000000000000 : ℝ)+2*(25875609143/13785000000000 : ℝ)*(11269/100000 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (13780171664318795537/13785000000000000000 : ℝ)+2*(25875609143/13785000000000 : ℝ)*(11269/100000 : ℝ)=(5000363985893161/5000000000000000 : ℝ) by norm_num, show 1+2*(147139104518197/1000000000000000000 : ℝ)=(500147139104518197/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1781899591278607/5000000000000000000 : ℝ)+(147139104518197/1000000000000000000 : ℝ) ≤ ((13780171664318795537/13785000000000000000 : ℝ)+(25875609143/13785000000000 : ℝ)*((7013/50000 : ℝ)+(11269/100000 : ℝ)))^(4139/1024 : ℝ) := by
    rw [show (13780171664318795537/13785000000000000000 : ℝ)+(25875609143/13785000000000 : ℝ)*((7013/50000 : ℝ)+(11269/100000 : ℝ))=(5000622741984591/5000000000000000 : ℝ) by norm_num, show 1+(1781899591278607/5000000000000000000 : ℝ)+(147139104518197/1000000000000000000 : ℝ)=(625314699389233699/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1781899591278607/5000000000000000000 : ℝ) ≤ ((13780171664318795537/13785000000000000000 : ℝ)+2*(25875609143/13785000000000 : ℝ)*(7013/50000 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (13780171664318795537/13785000000000000000 : ℝ)+2*(25875609143/13785000000000 : ℝ)*(7013/50000 : ℝ)=(5000881498076021/5000000000000000 : ℝ) by norm_num, show 1+2*(1781899591278607/5000000000000000000 : ℝ)=(2501781899591278607/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13780171664318795537/13785000000000000000 : ℝ)*(X 1 0+X 2 0)+(25875609143/13785000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (7013/50000 : ℝ)) (c := (13780171664318795537/13785000000000000000 : ℝ)) (alpha := (25875609143/13785000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13780171664318795537/13785000000000000000 : ℝ)*(X 0 1+X 2 1)+(25875609143/13785000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (7013/50000 : ℝ)) (c := (13780171664318795537/13785000000000000000 : ℝ)) (alpha := (25875609143/13785000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13780171664318795537/13785000000000000000 : ℝ)*(X 0 2+X 1 2)+(25875609143/13785000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (7013/50000 : ℝ)) (c := (13780171664318795537/13785000000000000000 : ℝ)) (alpha := (25875609143/13785000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2193949471/10000000000 : ℝ)*X 0 0+(5394087999/10000000000 : ℝ)*X 0 1+(5264738691/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672475053/5000000000 : ℝ)*X 1 0+(-1129786529/5000000000 : ℝ)*X 1 1+(2632369413/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336237607/2500000000 : ℝ)*X 2 0+(1316184651/2500000000 : ℝ)*X 2 1+(-2259572923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4372619809/10000000000 : ℝ)*X 0 0+(4247230283/10000000000 : ℝ)*X 0 1+(4501743339/10000000000 : ℝ)*X 0 2+(4372619809/10000000000 : ℝ)*X 1 0+(4247230283/10000000000 : ℝ)*X 1 1+(4501743339/10000000000 : ℝ)*X 1 2+(4372619809/10000000000 : ℝ)*X 2 0+(4247230283/10000000000 : ℝ)*X 2 1+(4501743339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2193954637/10000000000 : ℝ)*X 0 0+(2632531679/5000000000 : ℝ)*X 0 1+(2696881031/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656159123/5000000000 : ℝ)*X 1 0+(-213054977/1000000000 : ℝ)*X 1 1+(2696881031/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312318249/10000000000 : ℝ)*X 2 0+(5393762061/10000000000 : ℝ)*X 2 1+(-2130549769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372629609/10000000000 : ℝ)*X 0 0+(562638089/1250000000 : ℝ)*X 0 1+(2123935659/5000000000 : ℝ)*X 0 2+(4372629609/10000000000 : ℝ)*X 1 0+(562638089/1250000000 : ℝ)*X 1 1+(2123935659/5000000000 : ℝ)*X 1 2+(4372629609/10000000000 : ℝ)*X 2 0+(562638089/1250000000 : ℝ)*X 2 1+(2123935659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1880310889382816545689957/224365234375000000000000000000 : ℝ) := by norm_num
    linear_combination (71597457/4000000000000 : ℝ)*(base19) + (374064839/20000000000000 : ℝ)*(base23) + (205975121/100000000000000 : ℝ)*(lower2) + (131367073/100000000000000 : ℝ)*(upper3) + (72767381/50000000000000 : ℝ)*(upper5) + (364382572316973/6250000000000 : ℝ)*(major0) + (364382572316973/6250000000000 : ℝ)*(major1) + (364382572316973/6250000000000 : ℝ)*(major2) + (7731055722928477/100000000000000 : ℝ)*(sp0) + (773111753268539/10000000000000 : ℝ)*(sp1) + (386555872614881/5000000000000 : ℝ)*(sp2) + (1964547458853667/50000000000000 : ℝ)*(sp3) + (63599693339/100000000000000 : ℝ)*(sp4) + (277944613/1000000000000 : ℝ)*(sp7) + (1964561356084317/50000000000000 : ℝ)*(f.failure) + (1546223864524363/20000000000000 : ℝ)*(f.sum) + (431901638951/114875000000000000000000000 : ℝ)*base65 + (296882288373801917/28718750000000000000000000000000 : ℝ)*base67 + (80449481647676917/28718750000000000000000000000000 : ℝ)*base69 + (94364765958729333/28718750000000000000000000000000 : ℝ)*base72 + (506321629147/459500000000000000000000000 : ℝ)*base73 + (41505606951270667/28718750000000000000000000000000 : ℝ)*base75 + (196922909404395667/28718750000000000000000000000000 : ℝ)*base77 + (515584110723645667/28718750000000000000000000000000 : ℝ)*base79 + (1409615981639/459500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (9592527/2500000000000000000000 : ℝ)*base89 + (9592527/2500000000000000000000 : ℝ)*base91 + (9592527/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (633175186607227461233512993/114875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (504385291/50000000000000 : ℝ)*(base19) + (1105693657/100000000000000 : ℝ)*(base23) + (5499207/5000000000000 : ℝ)*(upper3) + (41652029/100000000000000 : ℝ)*(lower4) + (111444941/100000000000000 : ℝ)*(upper5) + (5859505543649689/100000000000000 : ℝ)*(major0) + (5859505543649689/100000000000000 : ℝ)*(major1) + (5859505543649689/100000000000000 : ℝ)*(major2) + (27489590453/100000000000000 : ℝ)*(sp1) + (29789372749/100000000000000 : ℝ)*(sp2) + (1942521256195543/25000000000000 : ℝ)*(sp4) + (3885028263210569/50000000000000 : ℝ)*(sp5) + (3885027064857883/50000000000000 : ℝ)*(sp6) + (493615734848557/12500000000000 : ℝ)*(sp7) + (493615734848557/12500000000000 : ℝ)*(f.failure) + (1942521256195543/25000000000000 : ℝ)*(f.sum) + (749328843367/172312500000000000000000000 : ℝ)*base66 + (5370859612796362007/1378500000000000000000000000000000 : ℝ)*base68 + (19310761860219637993/1378500000000000000000000000000000 : ℝ)*base69 + (11948727219023362007/1378500000000000000000000000000000 : ℝ)*base72 + (7417641130679/1378500000000000000000000000 : ℝ)*base74 + (511704312275362007/1378500000000000000000000000000000 : ℝ)*base76 + (2833366110713362007/1378500000000000000000000000000000 : ℝ)*base78 + (189633022457362007/1378500000000000000000000000000000 : ℝ)*base80 + (4191940249531/2757000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1297967/625000000000000000000 : ℝ)*base89 + (1297967/625000000000000000000 : ℝ)*base91 + (1297967/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1086_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7013/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14017/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1086_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1086_s8_0 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-548489869/2500000000 : ℝ)*x 0 + (5393997263/10000000000 : ℝ)*x 1 + (5264822651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548489869/2500000000 : ℝ)^8279 ≤ (2665226673961/20000000000000 : ℝ)^6231 := by
    have hnat : (548489869 : ℕ)^8279*20000000000000^6231 ≤ 2665226673961^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548489869 2500000000 2665226673961 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393997263/10000000000 : ℝ)^8279 ≤ (2752170742493/6250000000000 : ℝ)^6231 := by
    have hnat : (5393997263 : ℕ)^8279*6250000000000^6231 ≤ 2752170742493^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393997263 10000000000 2752170742493 6250000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264822651/10000000000 : ℝ)^8279 ≤ (42639134741599/100000000000000 : ℝ)^6231 := by
    have hnat : (5264822651 : ℕ)^8279*100000000000000^6231 ≤ 42639134741599^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264822651 10000000000 42639134741599 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548489869/2500000000 : ℝ), (5393997263/10000000000 : ℝ), (5264822651/10000000000 : ℝ)] ![(2665226673961/20000000000000 : ℝ), (2752170742493/6250000000000 : ℝ), (42639134741599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548489869/2500000000 : ℝ)|^8279 ≤ (2665226673961/20000000000000 : ℝ)^6231
        have hw : |(-548489869/2500000000 : ℝ)|=(548489869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393997263/10000000000 : ℝ)|^8279 ≤ (2752170742493/6250000000000 : ℝ)^6231
        have hw : |(5393997263/10000000000 : ℝ)|=(5393997263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264822651/10000000000 : ℝ)|^8279 ≤ (42639134741599/100000000000000 : ℝ)^6231
        have hw : |(5264822651/10000000000 : ℝ)|=(5264822651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s8_1 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672463453/5000000000 : ℝ)*x 0 + (-1129746577/5000000000 : ℝ)*x 1 + (5264822651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672463453/5000000000 : ℝ)^8279 ≤ (1359477158243/3125000000000 : ℝ)^6231 := by
    have hnat : (2672463453 : ℕ)^8279*3125000000000^6231 ≤ 1359477158243^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672463453 5000000000 1359477158243 3125000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129746577/5000000000 : ℝ)^8279 ≤ (1691601097/12207031250 : ℝ)^6231 := by
    have hnat : (1129746577 : ℕ)^8279*12207031250^6231 ≤ 1691601097^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129746577 5000000000 1691601097 12207031250 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264822651/10000000000 : ℝ)^8279 ≤ (42639134741599/100000000000000 : ℝ)^6231 := by
    have hnat : (5264822651 : ℕ)^8279*100000000000000^6231 ≤ 42639134741599^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264822651 10000000000 42639134741599 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672463453/5000000000 : ℝ), (-1129746577/5000000000 : ℝ), (5264822651/10000000000 : ℝ)] ![(1359477158243/3125000000000 : ℝ), (1691601097/12207031250 : ℝ), (42639134741599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672463453/5000000000 : ℝ)|^8279 ≤ (1359477158243/3125000000000 : ℝ)^6231
        have hw : |(2672463453/5000000000 : ℝ)|=(2672463453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1129746577/5000000000 : ℝ)|^8279 ≤ (1691601097/12207031250 : ℝ)^6231
        have hw : |(-1129746577/5000000000 : ℝ)|=(1129746577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264822651/10000000000 : ℝ)|^8279 ≤ (42639134741599/100000000000000 : ℝ)^6231
        have hw : |(5264822651/10000000000 : ℝ)|=(5264822651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s8_2 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672463453/5000000000 : ℝ)*x 0 + (105296453/200000000 : ℝ)*x 1 + (-1129746577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672463453/5000000000 : ℝ)^8279 ≤ (1359477158243/3125000000000 : ℝ)^6231 := by
    have hnat : (2672463453 : ℕ)^8279*3125000000000^6231 ≤ 1359477158243^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672463453 5000000000 1359477158243 3125000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105296453/200000000 : ℝ)^8279 ≤ (21319567365419/50000000000000 : ℝ)^6231 := by
    have hnat : (105296453 : ℕ)^8279*50000000000000^6231 ≤ 21319567365419^6231*200000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105296453 200000000 21319567365419 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129746577/5000000000 : ℝ)^8279 ≤ (1691601097/12207031250 : ℝ)^6231 := by
    have hnat : (1129746577 : ℕ)^8279*12207031250^6231 ≤ 1691601097^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129746577 5000000000 1691601097 12207031250 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672463453/5000000000 : ℝ), (105296453/200000000 : ℝ), (-1129746577/5000000000 : ℝ)] ![(1359477158243/3125000000000 : ℝ), (21319567365419/50000000000000 : ℝ), (1691601097/12207031250 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672463453/5000000000 : ℝ)|^8279 ≤ (1359477158243/3125000000000 : ℝ)^6231
        have hw : |(2672463453/5000000000 : ℝ)|=(2672463453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105296453/200000000 : ℝ)|^8279 ≤ (21319567365419/50000000000000 : ℝ)^6231
        have hw : |(105296453/200000000 : ℝ)|=(105296453/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1129746577/5000000000 : ℝ)|^8279 ≤ (1691601097/12207031250 : ℝ)^6231
        have hw : |(-1129746577/5000000000 : ℝ)|=(1129746577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s8_3 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874524831/2000000000 : ℝ)*x 0 + (4247401373/10000000000 : ℝ)*x 1 + (281348199/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874524831/2000000000 : ℝ)^8279 ≤ (16658334423893/50000000000000 : ℝ)^6231 := by
    have hnat : (874524831 : ℕ)^8279*50000000000000^6231 ≤ 16658334423893^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874524831 2000000000 16658334423893 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4247401373/10000000000 : ℝ)^8279 ≤ (6410991029623/20000000000000 : ℝ)^6231 := by
    have hnat : (4247401373 : ℕ)^8279*20000000000000^6231 ≤ 6410991029623^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247401373 10000000000 6410991029623 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281348199/625000000 : ℝ)^8279 ≤ (277027007903/800000000000 : ℝ)^6231 := by
    have hnat : (281348199 : ℕ)^8279*800000000000^6231 ≤ 277027007903^6231*625000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281348199 625000000 277027007903 800000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874524831/2000000000 : ℝ), (4247401373/10000000000 : ℝ), (281348199/625000000 : ℝ)] ![(16658334423893/50000000000000 : ℝ), (6410991029623/20000000000000 : ℝ), (277027007903/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874524831/2000000000 : ℝ)|^8279 ≤ (16658334423893/50000000000000 : ℝ)^6231
        have hw : |(874524831/2000000000 : ℝ)|=(874524831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4247401373/10000000000 : ℝ)|^8279 ≤ (6410991029623/20000000000000 : ℝ)^6231
        have hw : |(4247401373/10000000000 : ℝ)|=(4247401373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281348199/625000000 : ℝ)|^8279 ≤ (277027007903/800000000000 : ℝ)^6231
        have hw : |(281348199/625000000 : ℝ)|=(281348199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s8_4 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2193964541/10000000000 : ℝ)*x 0 + (5265146233/10000000000 : ℝ)*x 1 + (5393672473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2193964541/10000000000 : ℝ)^8279 ≤ (2665234849291/20000000000000 : ℝ)^6231 := by
    have hnat : (2193964541 : ℕ)^8279*20000000000000^6231 ≤ 2665234849291^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193964541 10000000000 2665234849291 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265146233/10000000000 : ℝ)^8279 ≤ (21321308389813/50000000000000 : ℝ)^6231 := by
    have hnat : (5265146233 : ℕ)^8279*50000000000000^6231 ≤ 21321308389813^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265146233 10000000000 21321308389813 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393672473/10000000000 : ℝ)^8279 ≤ (44031208957159/100000000000000 : ℝ)^6231 := by
    have hnat : (5393672473 : ℕ)^8279*100000000000000^6231 ≤ 44031208957159^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393672473 10000000000 44031208957159 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2193964541/10000000000 : ℝ), (5265146233/10000000000 : ℝ), (5393672473/10000000000 : ℝ)] ![(2665234849291/20000000000000 : ℝ), (21321308389813/50000000000000 : ℝ), (44031208957159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2193964541/10000000000 : ℝ)|^8279 ≤ (2665234849291/20000000000000 : ℝ)^6231
        have hw : |(-2193964541/10000000000 : ℝ)|=(2193964541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265146233/10000000000 : ℝ)|^8279 ≤ (21321308389813/50000000000000 : ℝ)^6231
        have hw : |(5265146233/10000000000 : ℝ)|=(5265146233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393672473/10000000000 : ℝ)|^8279 ≤ (44031208957159/100000000000000 : ℝ)^6231
        have hw : |(5393672473/10000000000 : ℝ)|=(5393672473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s8_5 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062467873/2000000000 : ℝ)*x 0 + (-3329129/15625000 : ℝ)*x 1 + (5393672671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062467873/2000000000 : ℝ)^8279 ≤ (43151209713181/100000000000000 : ℝ)^6231 := by
    have hnat : (1062467873 : ℕ)^8279*100000000000000^6231 ≤ 43151209713181^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062467873 2000000000 43151209713181 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3329129/15625000 : ℝ)^8279 ≤ (2563515834223/20000000000000 : ℝ)^6231 := by
    have hnat : (3329129 : ℕ)^8279*20000000000000^6231 ≤ 2563515834223^6231*15625000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3329129 15625000 2563515834223 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393672671/10000000000 : ℝ)^8279 ≤ (44031211104799/100000000000000 : ℝ)^6231 := by
    have hnat : (5393672671 : ℕ)^8279*100000000000000^6231 ≤ 44031211104799^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393672671 10000000000 44031211104799 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062467873/2000000000 : ℝ), (-3329129/15625000 : ℝ), (5393672671/10000000000 : ℝ)] ![(43151209713181/100000000000000 : ℝ), (2563515834223/20000000000000 : ℝ), (44031211104799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062467873/2000000000 : ℝ)|^8279 ≤ (43151209713181/100000000000000 : ℝ)^6231
        have hw : |(1062467873/2000000000 : ℝ)|=(1062467873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3329129/15625000 : ℝ)|^8279 ≤ (2563515834223/20000000000000 : ℝ)^6231
        have hw : |(-3329129/15625000 : ℝ)|=(3329129/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393672671/10000000000 : ℝ)|^8279 ≤ (44031211104799/100000000000000 : ℝ)^6231
        have hw : |(5393672671/10000000000 : ℝ)|=(5393672671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s8_6 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312338221/10000000000 : ℝ)*x 0 + (26968363/50000000 : ℝ)*x 1 + (-2130644201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312338221/10000000000 : ℝ)^8279 ≤ (43151197366413/100000000000000 : ℝ)^6231 := by
    have hnat : (5312338221 : ℕ)^8279*100000000000000^6231 ≤ 43151197366413^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312338221 10000000000 43151197366413 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26968363/50000000 : ℝ)^8279 ≤ (22015605167343/50000000000000 : ℝ)^6231 := by
    have hnat : (26968363 : ℕ)^8279*50000000000000^6231 ≤ 22015605167343^6231*50000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26968363 50000000 22015605167343 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2130644201/10000000000 : ℝ)^8279 ≤ (12817592287803/100000000000000 : ℝ)^6231 := by
    have hnat : (2130644201 : ℕ)^8279*100000000000000^6231 ≤ 12817592287803^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130644201 10000000000 12817592287803 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312338221/10000000000 : ℝ), (26968363/50000000 : ℝ), (-2130644201/10000000000 : ℝ)] ![(43151197366413/100000000000000 : ℝ), (22015605167343/50000000000000 : ℝ), (12817592287803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312338221/10000000000 : ℝ)|^8279 ≤ (43151197366413/100000000000000 : ℝ)^6231
        have hw : |(5312338221/10000000000 : ℝ)|=(5312338221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26968363/50000000 : ℝ)|^8279 ≤ (22015605167343/50000000000000 : ℝ)^6231
        have hw : |(26968363/50000000 : ℝ)|=(26968363/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2130644201/10000000000 : ℝ)|^8279 ≤ (12817592287803/100000000000000 : ℝ)^6231
        have hw : |(-2130644201/10000000000 : ℝ)|=(2130644201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s8_7 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (6996213/16000000 : ℝ)*x 0 + (2250467149/5000000000 : ℝ)*x 1 + (849608291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6996213/16000000 : ℝ)^8279 ≤ (6663351931493/20000000000000 : ℝ)^6231 := by
    have hnat : (6996213 : ℕ)^8279*20000000000000^6231 ≤ 6663351931493^6231*16000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6996213 16000000 6663351931493 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250467149/5000000000 : ℝ)^8279 ≤ (8655466651547/25000000000000 : ℝ)^6231 := by
    have hnat : (2250467149 : ℕ)^8279*25000000000000^6231 ≤ 8655466651547^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250467149 5000000000 8655466651547 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849608291/2000000000 : ℝ)^8279 ≤ (16030686859719/50000000000000 : ℝ)^6231 := by
    have hnat : (849608291 : ℕ)^8279*50000000000000^6231 ≤ 16030686859719^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849608291 2000000000 16030686859719 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6996213/16000000 : ℝ), (2250467149/5000000000 : ℝ), (849608291/2000000000 : ℝ)] ![(6663351931493/20000000000000 : ℝ), (8655466651547/25000000000000 : ℝ), (16030686859719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6996213/16000000 : ℝ)|^8279 ≤ (6663351931493/20000000000000 : ℝ)^6231
        have hw : |(6996213/16000000 : ℝ)|=(6996213/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250467149/5000000000 : ℝ)|^8279 ≤ (8655466651547/25000000000000 : ℝ)^6231
        have hw : |(2250467149/5000000000 : ℝ)|=(2250467149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849608291/2000000000 : ℝ)|^8279 ≤ (16030686859719/50000000000000 : ℝ)^6231
        have hw : |(849608291/2000000000 : ℝ)|=(849608291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1086_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14017/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11279/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2803/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14017/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14017/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14017/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14017/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14017/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14017/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11277/100000 : ℝ) ^ (4139/1024 : ℝ) ≤ (14756177030971619/100000000000000000000 : ℝ) := by
    have hpowers : (11277/100000 : ℝ)^4139 ≤ (14756177030971619/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11277 : ℕ)^4139*100000000000000000000^1024 ≤ 14756177030971619^1024*100000^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11277 100000 14756177030971619 100000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11277/100000 : ℝ)) (X := (14756177030971619/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14017/100000 : ℝ) ^ (4139/1024 : ℝ) ≤ (4443206382040441/12500000000000000000 : ℝ) := by
    have hpowers : (14017/100000 : ℝ)^4139 ≤ (4443206382040441/12500000000000000000 : ℝ)^1024 := by
      have hnat : (14017 : ℕ)^4139*12500000000000000000^1024 ≤ 4443206382040441^1024*100000^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14017 100000 4443206382040441 12500000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14017/100000 : ℝ)) (X := (4443206382040441/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014756177030971619/50000000000000000000 : ℝ) ≤ (10000730062696213/10000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (50014756177030971619/50000000000000000000 : ℝ)^1024 ≤ (10000730062696213/10000000000000000 : ℝ)^4139 := by
      have hnat : (50014756177030971619 : ℕ)^1024*10000000000000000^4139 ≤ 10000730062696213^4139*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014756177030971619 50000000000000000000 10000730062696213 10000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000730062696213/10000000000000000 : ℝ)) (X := (50014756177030971619/50000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050301828087295147/100000000000000000000 : ℝ) ≤ (2000248849117789/2000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (100050301828087295147/100000000000000000000 : ℝ)^1024 ≤ (2000248849117789/2000000000000000 : ℝ)^4139 := by
      have hnat : (100050301828087295147 : ℕ)^1024*2000000000000000^4139 ≤ 2000248849117789^4139*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050301828087295147 100000000000000000000 2000248849117789 2000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000248849117789/2000000000000000 : ℝ)) (X := (100050301828087295147/100000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254443206382040441/6250000000000000000 : ℝ) ≤ (10001758428481677/10000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (6254443206382040441/6250000000000000000 : ℝ)^1024 ≤ (10001758428481677/10000000000000000 : ℝ)^4139 := by
      have hnat : (6254443206382040441 : ℕ)^1024*10000000000000000^4139 ≤ 10001758428481677^4139*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254443206382040441 6250000000000000000 10001758428481677 10000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001758428481677/10000000000000000 : ℝ)) (X := (6254443206382040441/6250000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14756177030971619/100000000000000000000 : ℝ) ≤ ((6847600872706236523/6850000000000000000 : ℝ)+2*(128545723183/68500000000000 : ℝ)*(11277/100000 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (6847600872706236523/6850000000000000000 : ℝ)+2*(128545723183/68500000000000 : ℝ)*(11277/100000 : ℝ)=(10000730062696213/10000000000000000 : ℝ) by norm_num, show 1+2*(14756177030971619/100000000000000000000 : ℝ)=(50014756177030971619/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4443206382040441/12500000000000000000 : ℝ)+(14756177030971619/100000000000000000000 : ℝ) ≤ ((6847600872706236523/6850000000000000000 : ℝ)+(128545723183/68500000000000 : ℝ)*((14017/100000 : ℝ)+(11277/100000 : ℝ)))^(4139/1024 : ℝ) := by
    rw [show (6847600872706236523/6850000000000000000 : ℝ)+(128545723183/68500000000000 : ℝ)*((14017/100000 : ℝ)+(11277/100000 : ℝ))=(2000248849117789/2000000000000000 : ℝ) by norm_num, show 1+(4443206382040441/12500000000000000000 : ℝ)+(14756177030971619/100000000000000000000 : ℝ)=(100050301828087295147/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4443206382040441/12500000000000000000 : ℝ) ≤ ((6847600872706236523/6850000000000000000 : ℝ)+2*(128545723183/68500000000000 : ℝ)*(14017/100000 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (6847600872706236523/6850000000000000000 : ℝ)+2*(128545723183/68500000000000 : ℝ)*(14017/100000 : ℝ)=(10001758428481677/10000000000000000 : ℝ) by norm_num, show 1+2*(4443206382040441/12500000000000000000 : ℝ)=(6254443206382040441/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6847600872706236523/6850000000000000000 : ℝ)*(X 1 0+X 2 0)+(128545723183/68500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (11277/100000 : ℝ)) (hi := (14017/100000 : ℝ)) (c := (6847600872706236523/6850000000000000000 : ℝ)) (alpha := (128545723183/68500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6847600872706236523/6850000000000000000 : ℝ)*(X 0 1+X 2 1)+(128545723183/68500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (11277/100000 : ℝ)) (hi := (14017/100000 : ℝ)) (c := (6847600872706236523/6850000000000000000 : ℝ)) (alpha := (128545723183/68500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6847600872706236523/6850000000000000000 : ℝ)*(X 0 2+X 1 2)+(128545723183/68500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (11277/100000 : ℝ)) (hi := (14017/100000 : ℝ)) (c := (6847600872706236523/6850000000000000000 : ℝ)) (alpha := (128545723183/68500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-548489869/2500000000 : ℝ)*X 0 0+(5393997263/10000000000 : ℝ)*X 0 1+(5264822651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672463453/5000000000 : ℝ)*X 1 0+(-1129746577/5000000000 : ℝ)*X 1 1+(5264822651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672463453/5000000000 : ℝ)*X 2 0+(105296453/200000000 : ℝ)*X 2 1+(-1129746577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874524831/2000000000 : ℝ)*X 0 0+(4247401373/10000000000 : ℝ)*X 0 1+(281348199/625000000 : ℝ)*X 0 2+(874524831/2000000000 : ℝ)*X 1 0+(4247401373/10000000000 : ℝ)*X 1 1+(281348199/625000000 : ℝ)*X 1 2+(874524831/2000000000 : ℝ)*X 2 0+(4247401373/10000000000 : ℝ)*X 2 1+(281348199/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2193964541/10000000000 : ℝ)*X 0 0+(5265146233/10000000000 : ℝ)*X 0 1+(5393672473/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062467873/2000000000 : ℝ)*X 1 0+(-3329129/15625000 : ℝ)*X 1 1+(5393672671/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312338221/10000000000 : ℝ)*X 2 0+(26968363/50000000 : ℝ)*X 2 1+(-2130644201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((6996213/16000000 : ℝ)*X 0 0+(2250467149/5000000000 : ℝ)*X 0 1+(849608291/2000000000 : ℝ)*X 0 2+(6996213/16000000 : ℝ)*X 1 0+(2250467149/5000000000 : ℝ)*X 1 1+(849608291/2000000000 : ℝ)*X 1 2+(6996213/16000000 : ℝ)*X 2 0+(2250467149/5000000000 : ℝ)*X 2 1+(849608291/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (148403223167469015421046907/21406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (138668957/10000000000000 : ℝ)*(base19) + (1290947239/100000000000000 : ℝ)*(base23) + (25586789/50000000000000 : ℝ)*(lower2) + (176139261/100000000000000 : ℝ)*(upper3) + (20812929/20000000000000 : ℝ)*(upper5) + (364873513632399/6250000000000 : ℝ)*(major0) + (364873513632399/6250000000000 : ℝ)*(major1) + (364873513632399/6250000000000 : ℝ)*(major2) + (7741498402253457/100000000000000 : ℝ)*(sp0) + (7741534305708079/100000000000000 : ℝ)*(sp1) + (774153440145041/10000000000000 : ℝ)*(sp2) + (1967197995455417/50000000000000 : ℝ)*(sp3) + (37290144193/100000000000000 : ℝ)*(sp4) + (10260919049/50000000000000 : ℝ)*(sp7) + (983604128187233/25000000000000 : ℝ)*(f.failure) + (7741535692397649/100000000000000 : ℝ)*(f.sum) + (7450064976897/3425000000000000000000000000 : ℝ)*base65 + (361635945889733677/42812500000000000000000000000000 : ℝ)*base67 + (297683044560983677/42812500000000000000000000000000 : ℝ)*base69 + (172034725334733677/42812500000000000000000000000000 : ℝ)*base71 + (235073785017/214062500000000000000000000 : ℝ)*base73 + (936816145273171177/42812500000000000000000000000000 : ℝ)*base75 + (985255684590358677/42812500000000000000000000000000 : ℝ)*base77 + (124937477895983677/42812500000000000000000000000000 : ℝ)*base79 + (2853098428389/1712500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (3969477/1250000000000000000000 : ℝ)*base90 + (3969477/1250000000000000000000 : ℝ)*base92 + (3969477/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6067892287257847366923/856250000000000000000000000 : ℝ) := by norm_num
    linear_combination (130759919/50000000000000 : ℝ)*(base19) + (226198477/100000000000000 : ℝ)*(upper1) + (324347157/50000000000000 : ℝ)*(upper2) + (307118097/100000000000000 : ℝ)*(lower4) + (4346187/25000000000000 : ℝ)*(lower5) + (5867380236883411/100000000000000 : ℝ)*(major0) + (5867380236883411/100000000000000 : ℝ)*(major1) + (5867380236883411/100000000000000 : ℝ)*(major2) + (23939097377/100000000000000 : ℝ)*(sp0) + (31399776343/50000000000000 : ℝ)*(sp1) + (7780503388263111/100000000000000 : ℝ)*(sp4) + (1945116066571991/25000000000000 : ℝ)*(sp5) + (972565915920061/12500000000000 : ℝ)*(sp6) + (247139556886667/6250000000000 : ℝ)*(sp7) + (247139556886667/6250000000000 : ℝ)*(f.failure) + (972565915920061/12500000000000 : ℝ)*(f.sum) + (15648163446253/856250000000000000000000000 : ℝ)*base66 + (6420624464687680047/685000000000000000000000000000000 : ℝ)*base68 + (716492312612319953/685000000000000000000000000000000 : ℝ)*base69 + (16888942497297680047/685000000000000000000000000000000 : ℝ)*base72 + (8961771626887/3425000000000000000000000000 : ℝ)*base74 + (18555678450112319953/685000000000000000000000000000000 : ℝ)*base75 + (2982579035617680047/685000000000000000000000000000000 : ℝ)*base78 + (1165586966902319953/685000000000000000000000000000000 : ℝ)*base79 + (22856794209387/3425000000000000000000000000 : ℝ)*base82 + (4175377/312500000000000000000 : ℝ)*base89 + (4175377/312500000000000000000 : ℝ)*base91 + (4175377/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1086_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14017/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1086_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1086_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1086_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1086_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1086_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1086_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

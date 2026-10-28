-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1281_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:23:34.285584+00:00
-- url     : https://prove2.me/submissions/ecfdb666-c639-4886-8630-12043a53ef62

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
theorem support_rectangle_w1281_s3_0 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1047677909/5000000000 : ℝ)*x 0 + (2717874457/5000000000 : ℝ)*x 1 + (5224282611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047677909/5000000000 : ℝ)^4241 ≤ (12741132639271/100000000000000 : ℝ)^3217 := by
    have hnat : (1047677909 : ℕ)^4241*100000000000000^3217 ≤ 12741132639271^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047677909 5000000000 12741132639271 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717874457/5000000000 : ℝ)^4241 ≤ (11192576753471/25000000000000 : ℝ)^3217 := by
    have hnat : (2717874457 : ℕ)^4241*25000000000000^3217 ≤ 11192576753471^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717874457 5000000000 11192576753471 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5224282611/10000000000 : ℝ)^4241 ≤ (42488560332687/100000000000000 : ℝ)^3217 := by
    have hnat : (5224282611 : ℕ)^4241*100000000000000^3217 ≤ 42488560332687^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224282611 10000000000 42488560332687 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1047677909/5000000000 : ℝ), (2717874457/5000000000 : ℝ), (5224282611/10000000000 : ℝ)] ![(12741132639271/100000000000000 : ℝ), (11192576753471/25000000000000 : ℝ), (42488560332687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1047677909/5000000000 : ℝ)|^4241 ≤ (12741132639271/100000000000000 : ℝ)^3217
        have hw : |(-1047677909/5000000000 : ℝ)|=(1047677909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717874457/5000000000 : ℝ)|^4241 ≤ (11192576753471/25000000000000 : ℝ)^3217
        have hw : |(2717874457/5000000000 : ℝ)|=(2717874457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5224282611/10000000000 : ℝ)|^4241 ≤ (42488560332687/100000000000000 : ℝ)^3217
        have hw : |(5224282611/10000000000 : ℝ)|=(5224282611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s3_1 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535497941/1000000000 : ℝ)*x 0 + (-2203618687/10000000000 : ℝ)*x 1 + (5224282719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535497941/1000000000 : ℝ)^4241 ≤ (10973849168613/25000000000000 : ℝ)^3217 := by
    have hnat : (535497941 : ℕ)^4241*25000000000000^3217 ≤ 10973849168613^3217*1000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535497941 1000000000 10973849168613 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2203618687/10000000000 : ℝ)^4241 ≤ (6808020909569/50000000000000 : ℝ)^3217 := by
    have hnat : (2203618687 : ℕ)^4241*50000000000000^3217 ≤ 6808020909569^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203618687 10000000000 6808020909569 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5224282719/10000000000 : ℝ)^4241 ≤ (42488561490627/100000000000000 : ℝ)^3217 := by
    have hnat : (5224282719 : ℕ)^4241*100000000000000^3217 ≤ 42488561490627^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224282719 10000000000 42488561490627 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535497941/1000000000 : ℝ), (-2203618687/10000000000 : ℝ), (5224282719/10000000000 : ℝ)] ![(10973849168613/25000000000000 : ℝ), (6808020909569/50000000000000 : ℝ), (42488561490627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535497941/1000000000 : ℝ)|^4241 ≤ (10973849168613/25000000000000 : ℝ)^3217
        have hw : |(535497941/1000000000 : ℝ)|=(535497941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2203618687/10000000000 : ℝ)|^4241 ≤ (6808020909569/50000000000000 : ℝ)^3217
        have hw : |(-2203618687/10000000000 : ℝ)|=(2203618687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5224282719/10000000000 : ℝ)|^4241 ≤ (42488561490627/100000000000000 : ℝ)^3217
        have hw : |(5224282719/10000000000 : ℝ)|=(5224282719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s3_2 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677489733/5000000000 : ℝ)*x 0 + (522428239/1000000000 : ℝ)*x 1 + (-440723809/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677489733/5000000000 : ℝ)^4241 ≤ (43895397279607/100000000000000 : ℝ)^3217 := by
    have hnat : (2677489733 : ℕ)^4241*100000000000000^3217 ≤ 43895397279607^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677489733 5000000000 43895397279607 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522428239/1000000000 : ℝ)^4241 ≤ (42488557963197/100000000000000 : ℝ)^3217 := by
    have hnat : (522428239 : ℕ)^4241*100000000000000^3217 ≤ 42488557963197^3217*1000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522428239 1000000000 42488557963197 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440723809/2000000000 : ℝ)^4241 ≤ (340401118383/2500000000000 : ℝ)^3217 := by
    have hnat : (440723809 : ℕ)^4241*2500000000000^3217 ≤ 340401118383^3217*2000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440723809 2000000000 340401118383 2500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677489733/5000000000 : ℝ), (522428239/1000000000 : ℝ), (-440723809/2000000000 : ℝ)] ![(43895397279607/100000000000000 : ℝ), (42488557963197/100000000000000 : ℝ), (340401118383/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677489733/5000000000 : ℝ)|^4241 ≤ (43895397279607/100000000000000 : ℝ)^3217
        have hw : |(2677489733/5000000000 : ℝ)|=(2677489733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522428239/1000000000 : ℝ)|^4241 ≤ (42488557963197/100000000000000 : ℝ)^3217
        have hw : |(522428239/1000000000 : ℝ)|=(522428239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-440723809/2000000000 : ℝ)|^4241 ≤ (340401118383/2500000000000 : ℝ)^3217
        have hw : |(-440723809/2000000000 : ℝ)|=(440723809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s3_3 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135666139/312500000 : ℝ)*x 0 + (2065049657/5000000000 : ℝ)*x 1 + (4562887153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135666139/312500000 : ℝ)^4241 ≤ (3328688025837/10000000000000 : ℝ)^3217 := by
    have hnat : (135666139 : ℕ)^4241*10000000000000^3217 ≤ 3328688025837^3217*312500000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135666139 312500000 3328688025837 10000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065049657/5000000000 : ℝ)^4241 ≤ (15584299103559/50000000000000 : ℝ)^3217 := by
    have hnat : (2065049657 : ℕ)^4241*50000000000000^3217 ≤ 15584299103559^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065049657 5000000000 15584299103559 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4562887153/10000000000 : ℝ)^4241 ≤ (4443065190197/12500000000000 : ℝ)^3217 := by
    have hnat : (4562887153 : ℕ)^4241*12500000000000^3217 ≤ 4443065190197^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4562887153 10000000000 4443065190197 12500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135666139/312500000 : ℝ), (2065049657/5000000000 : ℝ), (4562887153/10000000000 : ℝ)] ![(3328688025837/10000000000000 : ℝ), (15584299103559/50000000000000 : ℝ), (4443065190197/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135666139/312500000 : ℝ)|^4241 ≤ (3328688025837/10000000000000 : ℝ)^3217
        have hw : |(135666139/312500000 : ℝ)|=(135666139/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2065049657/5000000000 : ℝ)|^4241 ≤ (15584299103559/50000000000000 : ℝ)^3217
        have hw : |(2065049657/5000000000 : ℝ)|=(2065049657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4562887153/10000000000 : ℝ)|^4241 ≤ (4443065190197/12500000000000 : ℝ)^3217
        have hw : |(4562887153/10000000000 : ℝ)|=(4562887153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s3_4 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-419075843/2000000000 : ℝ)*x 0 + (1306300159/2500000000 : ℝ)*x 1 + (42459571/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419075843/2000000000 : ℝ)^4241 ≤ (12741320194171/100000000000000 : ℝ)^3217 := by
    have hnat : (419075843 : ℕ)^4241*100000000000000^3217 ≤ 12741320194171^3217*2000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419075843 2000000000 12741320194171 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306300159/2500000000 : ℝ)^4241 ≤ (1699936134879/4000000000000 : ℝ)^3217 := by
    have hnat : (1306300159 : ℕ)^4241*4000000000000^3217 ≤ 1699936134879^3217*2500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306300159 2500000000 1699936134879 4000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42459571/78125000 : ℝ)^4241 ≤ (2238013821367/5000000000000 : ℝ)^3217 := by
    have hnat : (42459571 : ℕ)^4241*5000000000000^3217 ≤ 2238013821367^3217*78125000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42459571 78125000 2238013821367 5000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419075843/2000000000 : ℝ), (1306300159/2500000000 : ℝ), (42459571/78125000 : ℝ)] ![(12741320194171/100000000000000 : ℝ), (1699936134879/4000000000000 : ℝ), (2238013821367/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419075843/2000000000 : ℝ)|^4241 ≤ (12741320194171/100000000000000 : ℝ)^3217
        have hw : |(-419075843/2000000000 : ℝ)|=(419075843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1306300159/2500000000 : ℝ)|^4241 ≤ (1699936134879/4000000000000 : ℝ)^3217
        have hw : |(1306300159/2500000000 : ℝ)|=(1306300159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42459571/78125000 : ℝ)|^4241 ≤ (2238013821367/5000000000000 : ℝ)^3217
        have hw : |(42459571/78125000 : ℝ)|=(42459571/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s3_5 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331306857/625000000 : ℝ)*x 0 + (-1993076103/10000000000 : ℝ)*x 1 + (2717412511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331306857/625000000 : ℝ)^4241 ≤ (8662408517137/20000000000000 : ℝ)^3217 := by
    have hnat : (331306857 : ℕ)^4241*20000000000000^3217 ≤ 8662408517137^3217*625000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331306857 625000000 8662408517137 20000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1993076103/10000000000 : ℝ)^4241 ≤ (5963840846971/50000000000000 : ℝ)^3217 := by
    have hnat : (1993076103 : ℕ)^4241*50000000000000^3217 ≤ 5963840846971^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993076103 10000000000 5963840846971 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717412511/5000000000 : ℝ)^4241 ≤ (22380137855377/50000000000000 : ℝ)^3217 := by
    have hnat : (2717412511 : ℕ)^4241*50000000000000^3217 ≤ 22380137855377^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717412511 5000000000 22380137855377 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331306857/625000000 : ℝ), (-1993076103/10000000000 : ℝ), (2717412511/5000000000 : ℝ)] ![(8662408517137/20000000000000 : ℝ), (5963840846971/50000000000000 : ℝ), (22380137855377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331306857/625000000 : ℝ)|^4241 ≤ (8662408517137/20000000000000 : ℝ)^3217
        have hw : |(331306857/625000000 : ℝ)|=(331306857/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1993076103/10000000000 : ℝ)|^4241 ≤ (5963840846971/50000000000000 : ℝ)^3217
        have hw : |(-1993076103/10000000000 : ℝ)|=(1993076103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717412511/5000000000 : ℝ)|^4241 ≤ (22380137855377/50000000000000 : ℝ)^3217
        have hw : |(2717412511/5000000000 : ℝ)|=(2717412511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s3_6 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132522743/250000000 : ℝ)*x 0 + (2717412499/5000000000 : ℝ)*x 1 + (-1993076123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132522743/250000000 : ℝ)^4241 ≤ (43312042671857/100000000000000 : ℝ)^3217 := by
    have hnat : (132522743 : ℕ)^4241*100000000000000^3217 ≤ 43312042671857^3217*250000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132522743 250000000 43312042671857 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717412499/5000000000 : ℝ)^4241 ≤ (22380137725089/50000000000000 : ℝ)^3217 := by
    have hnat : (2717412499 : ℕ)^4241*50000000000000^3217 ≤ 22380137725089^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717412499 5000000000 22380137725089 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1993076123/10000000000 : ℝ)^4241 ≤ (11927681851731/100000000000000 : ℝ)^3217 := by
    have hnat : (1993076123 : ℕ)^4241*100000000000000^3217 ≤ 11927681851731^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993076123 10000000000 11927681851731 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132522743/250000000 : ℝ), (2717412499/5000000000 : ℝ), (-1993076123/10000000000 : ℝ)] ![(43312042671857/100000000000000 : ℝ), (22380137725089/50000000000000 : ℝ), (11927681851731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132522743/250000000 : ℝ)|^4241 ≤ (43312042671857/100000000000000 : ℝ)^3217
        have hw : |(132522743/250000000 : ℝ)|=(132522743/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717412499/5000000000 : ℝ)|^4241 ≤ (22380137725089/50000000000000 : ℝ)^3217
        have hw : |(2717412499/5000000000 : ℝ)|=(2717412499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1993076123/10000000000 : ℝ)|^4241 ≤ (11927681851731/100000000000000 : ℝ)^3217
        have hw : |(-1993076123/10000000000 : ℝ)|=(1993076123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s3_7 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4341363959/10000000000 : ℝ)*x 0 + (4561008087/10000000000 : ℝ)*x 1 + (1032997601/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341363959/10000000000 : ℝ)^4241 ≤ (33287360504407/100000000000000 : ℝ)^3217 := by
    have hnat : (4341363959 : ℕ)^4241*100000000000000^3217 ≤ 33287360504407^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341363959 10000000000 33287360504407 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4561008087/10000000000 : ℝ)^4241 ≤ (35525225680123/100000000000000 : ℝ)^3217 := by
    have hnat : (4561008087 : ℕ)^4241*100000000000000^3217 ≤ 35525225680123^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4561008087 10000000000 35525225680123 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032997601/2500000000 : ℝ)^4241 ≤ (31187413796613/100000000000000 : ℝ)^3217 := by
    have hnat : (1032997601 : ℕ)^4241*100000000000000^3217 ≤ 31187413796613^3217*2500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032997601 2500000000 31187413796613 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341363959/10000000000 : ℝ), (4561008087/10000000000 : ℝ), (1032997601/2500000000 : ℝ)] ![(33287360504407/100000000000000 : ℝ), (35525225680123/100000000000000 : ℝ), (31187413796613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341363959/10000000000 : ℝ)|^4241 ≤ (33287360504407/100000000000000 : ℝ)^3217
        have hw : |(4341363959/10000000000 : ℝ)|=(4341363959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4561008087/10000000000 : ℝ)|^4241 ≤ (35525225680123/100000000000000 : ℝ)^3217
        have hw : |(4561008087/10000000000 : ℝ)|=(4561008087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032997601/2500000000 : ℝ)|^4241 ≤ (31187413796613/100000000000000 : ℝ)^3217
        have hw : |(1032997601/2500000000 : ℝ)|=(1032997601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1281_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (663/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15081/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16369/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9423/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16369/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9423/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16369/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9423/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16369/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9423/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16369/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9423/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16369/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9423/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9423/100000 : ℝ) ^ (265/64 : ℝ) ≤ (5655905173159799/100000000000000000000 : ℝ) := by
    have hpowers : (9423/100000 : ℝ)^265 ≤ (5655905173159799/100000000000000000000 : ℝ)^64 := by
      have hnat : (9423 : ℕ)^265*100000000000000000000^64 ≤ 5655905173159799^64*100000^265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9423 100000 5655905173159799 100000000000000000000 265 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9423/100000 : ℝ)) (X := (5655905173159799/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hpowhi : (16369/100000 : ℝ) ^ (265/64 : ℝ) ≤ (6957776474146693/12500000000000000000 : ℝ) := by
    have hpowers : (16369/100000 : ℝ)^265 ≤ (6957776474146693/12500000000000000000 : ℝ)^64 := by
      have hnat : (16369 : ℕ)^265*12500000000000000000^64 ≤ 6957776474146693^64*100000^265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16369 100000 6957776474146693 12500000000000000000 265 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16369/100000 : ℝ)) (X := (6957776474146693/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005655905173159799/50000000000000000000 : ℝ) ≤ (5000136589586203/5000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (50005655905173159799/50000000000000000000 : ℝ)^64 ≤ (5000136589586203/5000000000000000 : ℝ)^265 := by
      have hnat : (50005655905173159799 : ℕ)^64*5000000000000000^265 ≤ 5000136589586203^265*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005655905173159799 50000000000000000000 5000136589586203 5000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000136589586203/5000000000000000 : ℝ)) (X := (50005655905173159799/50000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100061318116966333343/100000000000000000000 : ℝ) ≤ (156273133533133/156250000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (100061318116966333343/100000000000000000000 : ℝ)^64 ≤ (156273133533133/156250000000000 : ℝ)^265 := by
      have hnat : (100061318116966333343 : ℕ)^64*156250000000000^265 ≤ 156273133533133^265*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100061318116966333343 100000000000000000000 156273133533133 156250000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156273133533133/156250000000000 : ℝ)) (X := (100061318116966333343/100000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (6256957776474146693/6250000000000000000 : ℝ) ≤ (5001343956534309/5000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (6256957776474146693/6250000000000000000 : ℝ)^64 ≤ (5001343956534309/5000000000000000 : ℝ)^265 := by
      have hnat : (6256957776474146693 : ℕ)^64*5000000000000000^265 ≤ 5001343956534309^265*6250000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6256957776474146693 6250000000000000000 5001343956534309 5000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001343956534309/5000000000000000 : ℝ)) (X := (6256957776474146693/6250000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5655905173159799/100000000000000000000 : ℝ) ≤ ((10849866166410551/10853125000000000 : ℝ)+2*(603683474053/347300000000000 : ℝ)*(9423/100000 : ℝ))^(265/64 : ℝ) := by
    rw [show (10849866166410551/10853125000000000 : ℝ)+2*(603683474053/347300000000000 : ℝ)*(9423/100000 : ℝ)=(5000136589586203/5000000000000000 : ℝ) by norm_num, show 1+2*(5655905173159799/100000000000000000000 : ℝ)=(50005655905173159799/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6957776474146693/12500000000000000000 : ℝ)+(5655905173159799/100000000000000000000 : ℝ) ≤ ((10849866166410551/10853125000000000 : ℝ)+(603683474053/347300000000000 : ℝ)*((16369/100000 : ℝ)+(9423/100000 : ℝ)))^(265/64 : ℝ) := by
    rw [show (10849866166410551/10853125000000000 : ℝ)+(603683474053/347300000000000 : ℝ)*((16369/100000 : ℝ)+(9423/100000 : ℝ))=(156273133533133/156250000000000 : ℝ) by norm_num, show 1+(6957776474146693/12500000000000000000 : ℝ)+(5655905173159799/100000000000000000000 : ℝ)=(100061318116966333343/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6957776474146693/12500000000000000000 : ℝ) ≤ ((10849866166410551/10853125000000000 : ℝ)+2*(603683474053/347300000000000 : ℝ)*(16369/100000 : ℝ))^(265/64 : ℝ) := by
    rw [show (10849866166410551/10853125000000000 : ℝ)+2*(603683474053/347300000000000 : ℝ)*(16369/100000 : ℝ)=(5001343956534309/5000000000000000 : ℝ) by norm_num, show 1+2*(6957776474146693/12500000000000000000 : ℝ)=(6256957776474146693/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10849866166410551/10853125000000000 : ℝ)*(X 1 0+X 2 0)+(603683474053/347300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (9423/100000 : ℝ)) (hi := (16369/100000 : ℝ)) (c := (10849866166410551/10853125000000000 : ℝ)) (alpha := (603683474053/347300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10849866166410551/10853125000000000 : ℝ)*(X 0 1+X 2 1)+(603683474053/347300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (9423/100000 : ℝ)) (hi := (16369/100000 : ℝ)) (c := (10849866166410551/10853125000000000 : ℝ)) (alpha := (603683474053/347300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10849866166410551/10853125000000000 : ℝ)*(X 0 2+X 1 2)+(603683474053/347300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (9423/100000 : ℝ)) (hi := (16369/100000 : ℝ)) (c := (10849866166410551/10853125000000000 : ℝ)) (alpha := (603683474053/347300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1047677909/5000000000 : ℝ)*X 0 0+(2717874457/5000000000 : ℝ)*X 0 1+(5224282611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535497941/1000000000 : ℝ)*X 1 0+(-2203618687/10000000000 : ℝ)*X 1 1+(5224282719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677489733/5000000000 : ℝ)*X 2 0+(522428239/1000000000 : ℝ)*X 2 1+(-440723809/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((135666139/312500000 : ℝ)*X 0 0+(2065049657/5000000000 : ℝ)*X 0 1+(4562887153/10000000000 : ℝ)*X 0 2+(135666139/312500000 : ℝ)*X 1 0+(2065049657/5000000000 : ℝ)*X 1 1+(4562887153/10000000000 : ℝ)*X 1 2+(135666139/312500000 : ℝ)*X 2 0+(2065049657/5000000000 : ℝ)*X 2 1+(4562887153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-419075843/2000000000 : ℝ)*X 0 0+(1306300159/2500000000 : ℝ)*X 0 1+(42459571/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331306857/625000000 : ℝ)*X 1 0+(-1993076103/10000000000 : ℝ)*X 1 1+(2717412511/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132522743/250000000 : ℝ)*X 2 0+(2717412499/5000000000 : ℝ)*X 2 1+(-1993076123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4341363959/10000000000 : ℝ)*X 0 0+(4561008087/10000000000 : ℝ)*X 0 1+(1032997601/2500000000 : ℝ)*X 0 2+(4341363959/10000000000 : ℝ)*X 1 0+(4561008087/10000000000 : ℝ)*X 1 1+(1032997601/2500000000 : ℝ)*X 1 2+(4341363959/10000000000 : ℝ)*X 2 0+(4561008087/10000000000 : ℝ)*X 2 1+(1032997601/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (426697761718945366132251/54265625000000000000000000000 : ℝ) := by norm_num
    linear_combination (696914247/50000000000000 : ℝ)*(base19) + (169804599/12500000000000 : ℝ)*(base23) + (42266899/50000000000000 : ℝ)*(lower2) + (206440741/50000000000000 : ℝ)*(upper3) + (39099639/100000000000000 : ℝ)*(lower4) + (703954936919759/20000000000000 : ℝ)*(major0) + (703954936919759/20000000000000 : ℝ)*(major1) + (703954936919759/20000000000000 : ℝ)*(major2) + (1182227871512731/25000000000000 : ℝ)*(sp0) + (1182231130926147/25000000000000 : ℝ)*(sp1) + (472892455909629/10000000000000 : ℝ)*(sp2) + (1155304647259577/50000000000000 : ℝ)*(sp3) + (7215741079/50000000000000 : ℝ)*(sp4) + (13895040953/100000000000000 : ℝ)*(sp7) + (1155311594780053/50000000000000 : ℝ)*(f.failure) + (2364462958766541/50000000000000 : ℝ)*(f.sum) + (1824954739443/1736500000000000000000000000 : ℝ)*base65 + (3307803988598539/868250000000000000000000000000 : ℝ)*base68 + (10399852104904289/868250000000000000000000000000 : ℝ)*base70 + (2789920356180461/868250000000000000000000000000 : ℝ)*base71 + (4652809942469/868250000000000000000000000 : ℝ)*base74 + (14144572942852289/868250000000000000000000000000 : ℝ)*base76 + (15273368021914539/868250000000000000000000000000 : ℝ)*base78 + (620693787414461/868250000000000000000000000000 : ℝ)*base79 + (46344431253/27784000000000000000000000 : ℝ)*base82 + (14164541/5000000000000000000000 : ℝ)*base90 + (14164541/5000000000000000000000 : ℝ)*base92 + (14164541/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1481732288777517749029893/434125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40898471/4000000000000 : ℝ)*(base19) + (41260713/4000000000000 : ℝ)*(base23) + (41664309/50000000000000 : ℝ)*(upper3) + (47651/781250000000 : ℝ)*(lower4) + (56138557/50000000000000 : ℝ)*(upper5) + (44383391260821/1250000000000 : ℝ)*(major0) + (44383391260821/1250000000000 : ℝ)*(major1) + (44383391260821/1250000000000 : ℝ)*(major2) + (16716744639/100000000000000 : ℝ)*(sp1) + (15770702531/100000000000000 : ℝ)*(sp2) + (2385218312832837/50000000000000 : ℝ)*(sp4) + (238520944322963/5000000000000 : ℝ)*(sp5) + (2385209911722659/50000000000000 : ℝ)*(sp6) + (1165452931147063/50000000000000 : ℝ)*(sp7) + (1165452931147063/50000000000000 : ℝ)*(f.failure) + (2385218312832837/50000000000000 : ℝ)*(f.sum) + (5305260285711/868250000000000000000000000 : ℝ)*base66 + (1313595004720811/217062500000000000000000000000 : ℝ)*base67 + (253237583097367/27132812500000000000000000000 : ℝ)*base69 + (306125136814359/54265625000000000000000000000 : ℝ)*base71 + (9158705288189/3473000000000000000000000000 : ℝ)*base74 + (4512161437110747/434125000000000000000000000000 : ℝ)*base75 + (88641184232641/54265625000000000000000000000 : ℝ)*base78 + (22036315059129/13566406250000000000000000000 : ℝ)*base80 + (14202396301127/3473000000000000000000000000 : ℝ)*base82 + (14937489/5000000000000000000000 : ℝ)*base89 + (14937489/5000000000000000000000 : ℝ)*base91 + (14937489/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1281_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (663/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15081/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1281_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1281_s4_0 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2097398741/10000000000 : ℝ)*x 0 + (270989541/500000000 : ℝ)*x 1 + (5238901827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097398741/10000000000 : ℝ)^4241 ≤ (6378755809289/50000000000000 : ℝ)^3217 := by
    have hnat : (2097398741 : ℕ)^4241*50000000000000^3217 ≤ 6378755809289^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097398741 10000000000 6378755809289 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270989541/500000000 : ℝ)^4241 ≤ (22298557908749/50000000000000 : ℝ)^3217 := by
    have hnat : (270989541 : ℕ)^4241*50000000000000^3217 ≤ 22298557908749^3217*500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270989541 500000000 22298557908749 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238901827/10000000000 : ℝ)^4241 ≤ (10661343138043/25000000000000 : ℝ)^3217 := by
    have hnat : (5238901827 : ℕ)^4241*25000000000000^3217 ≤ 10661343138043^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238901827 10000000000 10661343138043 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2097398741/10000000000 : ℝ), (270989541/500000000 : ℝ), (5238901827/10000000000 : ℝ)] ![(6378755809289/50000000000000 : ℝ), (22298557908749/50000000000000 : ℝ), (10661343138043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2097398741/10000000000 : ℝ)|^4241 ≤ (6378755809289/50000000000000 : ℝ)^3217
        have hw : |(-2097398741/10000000000 : ℝ)|=(2097398741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270989541/500000000 : ℝ)|^4241 ≤ (22298557908749/50000000000000 : ℝ)^3217
        have hw : |(270989541/500000000 : ℝ)|=(270989541/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238901827/10000000000 : ℝ)|^4241 ≤ (10661343138043/25000000000000 : ℝ)^3217
        have hw : |(5238901827/10000000000 : ℝ)|=(5238901827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s4_1 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350952879/10000000000 : ℝ)*x 0 + (-1094847521/5000000000 : ℝ)*x 1 + (654862731/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350952879/10000000000 : ℝ)^4241 ≤ (21925944921943/50000000000000 : ℝ)^3217 := by
    have hnat : (5350952879 : ℕ)^4241*50000000000000^3217 ≤ 21925944921943^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350952879 10000000000 21925944921943 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094847521/5000000000 : ℝ)^4241 ≤ (6751368680571/50000000000000 : ℝ)^3217 := by
    have hnat : (1094847521 : ℕ)^4241*50000000000000^3217 ≤ 6751368680571^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094847521 5000000000 6751368680571 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654862731/1250000000 : ℝ)^4241 ≤ (5330671597191/12500000000000 : ℝ)^3217 := by
    have hnat : (654862731 : ℕ)^4241*12500000000000^3217 ≤ 5330671597191^3217*1250000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654862731 1250000000 5330671597191 12500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350952879/10000000000 : ℝ), (-1094847521/5000000000 : ℝ), (654862731/1250000000 : ℝ)] ![(21925944921943/50000000000000 : ℝ), (6751368680571/50000000000000 : ℝ), (5330671597191/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350952879/10000000000 : ℝ)|^4241 ≤ (21925944921943/50000000000000 : ℝ)^3217
        have hw : |(5350952879/10000000000 : ℝ)|=(5350952879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1094847521/5000000000 : ℝ)|^4241 ≤ (6751368680571/50000000000000 : ℝ)^3217
        have hw : |(-1094847521/5000000000 : ℝ)|=(1094847521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654862731/1250000000 : ℝ)|^4241 ≤ (5330671597191/12500000000000 : ℝ)^3217
        have hw : |(654862731/1250000000 : ℝ)|=(654862731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s4_2 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675476337/5000000000 : ℝ)*x 0 + (523890203/1000000000 : ℝ)*x 1 + (-87587803/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675476337/5000000000 : ℝ)^4241 ≤ (21925943814559/50000000000000 : ℝ)^3217 := by
    have hnat : (2675476337 : ℕ)^4241*50000000000000^3217 ≤ 21925943814559^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675476337 5000000000 21925943814559 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523890203/1000000000 : ℝ)^4241 ≤ (42645374730609/100000000000000 : ℝ)^3217 := by
    have hnat : (523890203 : ℕ)^4241*100000000000000^3217 ≤ 42645374730609^3217*1000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523890203 1000000000 42645374730609 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87587803/400000000 : ℝ)^4241 ≤ (13502737629411/100000000000000 : ℝ)^3217 := by
    have hnat : (87587803 : ℕ)^4241*100000000000000^3217 ≤ 13502737629411^3217*400000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87587803 400000000 13502737629411 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675476337/5000000000 : ℝ), (523890203/1000000000 : ℝ), (-87587803/400000000 : ℝ)] ![(21925943814559/50000000000000 : ℝ), (42645374730609/100000000000000 : ℝ), (13502737629411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675476337/5000000000 : ℝ)|^4241 ≤ (21925943814559/50000000000000 : ℝ)^3217
        have hw : |(2675476337/5000000000 : ℝ)|=(2675476337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523890203/1000000000 : ℝ)|^4241 ≤ (42645374730609/100000000000000 : ℝ)^3217
        have hw : |(523890203/1000000000 : ℝ)|=(523890203/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-87587803/400000000 : ℝ)|^4241 ≤ (13502737629411/100000000000000 : ℝ)^3217
        have hw : |(-87587803/400000000 : ℝ)|=(87587803/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s4_3 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6948077/16000000 : ℝ)*x 0 + (2080617021/5000000000 : ℝ)*x 1 + (2265720751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6948077/16000000 : ℝ)^4241 ≤ (4162416339453/12500000000000 : ℝ)^3217 := by
    have hnat : (6948077 : ℕ)^4241*12500000000000^3217 ≤ 4162416339453^3217*16000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6948077 16000000 4162416339453 12500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080617021/5000000000 : ℝ)^4241 ≤ (7869681184683/25000000000000 : ℝ)^3217 := by
    have hnat : (2080617021 : ℕ)^4241*25000000000000^3217 ≤ 7869681184683^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080617021 5000000000 7869681184683 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265720751/5000000000 : ℝ)^4241 ≤ (4402743066199/12500000000000 : ℝ)^3217 := by
    have hnat : (2265720751 : ℕ)^4241*12500000000000^3217 ≤ 4402743066199^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265720751 5000000000 4402743066199 12500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6948077/16000000 : ℝ), (2080617021/5000000000 : ℝ), (2265720751/5000000000 : ℝ)] ![(4162416339453/12500000000000 : ℝ), (7869681184683/25000000000000 : ℝ), (4402743066199/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6948077/16000000 : ℝ)|^4241 ≤ (4162416339453/12500000000000 : ℝ)^3217
        have hw : |(6948077/16000000 : ℝ)|=(6948077/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2080617021/5000000000 : ℝ)|^4241 ≤ (7869681184683/25000000000000 : ℝ)^3217
        have hw : |(2080617021/5000000000 : ℝ)|=(2080617021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2265720751/5000000000 : ℝ)|^4241 ≤ (4402743066199/12500000000000 : ℝ)^3217
        have hw : |(2265720751/5000000000 : ℝ)|=(2265720751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s4_4 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2097413597/10000000000 : ℝ)*x 0 + (2619787173/5000000000 : ℝ)*x 1 + (5419114519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097413597/10000000000 : ℝ)^4241 ≤ (1275763074403/10000000000000 : ℝ)^3217 := by
    have hnat : (2097413597 : ℕ)^4241*10000000000000^3217 ≤ 1275763074403^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097413597 10000000000 1275763074403 10000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619787173/5000000000 : ℝ)^4241 ≤ (21326294822533/50000000000000 : ℝ)^3217 := by
    have hnat : (2619787173 : ℕ)^4241*50000000000000^3217 ≤ 21326294822533^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619787173 5000000000 21326294822533 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419114519/10000000000 : ℝ)^4241 ≤ (22294889794381/50000000000000 : ℝ)^3217 := by
    have hnat : (5419114519 : ℕ)^4241*50000000000000^3217 ≤ 22294889794381^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419114519 10000000000 22294889794381 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2097413597/10000000000 : ℝ), (2619787173/5000000000 : ℝ), (5419114519/10000000000 : ℝ)] ![(1275763074403/10000000000000 : ℝ), (21326294822533/50000000000000 : ℝ), (22294889794381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2097413597/10000000000 : ℝ)|^4241 ≤ (1275763074403/10000000000000 : ℝ)^3217
        have hw : |(-2097413597/10000000000 : ℝ)|=(2097413597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619787173/5000000000 : ℝ)|^4241 ≤ (21326294822533/50000000000000 : ℝ)^3217
        have hw : |(2619787173/5000000000 : ℝ)|=(2619787173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419114519/10000000000 : ℝ)|^4241 ≤ (22294889794381/50000000000000 : ℝ)^3217
        have hw : |(5419114519/10000000000 : ℝ)|=(5419114519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s4_5 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304705313/10000000000 : ℝ)*x 0 + (-2009482321/10000000000 : ℝ)*x 1 + (5419114623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304705313/10000000000 : ℝ)^4241 ≤ (43352931492833/100000000000000 : ℝ)^3217 := by
    have hnat : (5304705313 : ℕ)^4241*100000000000000^3217 ≤ 43352931492833^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304705313 10000000000 43352931492833 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2009482321/10000000000 : ℝ)^4241 ≤ (12057287776771/100000000000000 : ℝ)^3217 := by
    have hnat : (2009482321 : ℕ)^4241*100000000000000^3217 ≤ 12057287776771^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009482321 10000000000 12057287776771 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419114623/10000000000 : ℝ)^4241 ≤ (5573722589611/12500000000000 : ℝ)^3217 := by
    have hnat : (5419114623 : ℕ)^4241*12500000000000^3217 ≤ 5573722589611^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419114623 10000000000 5573722589611 12500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304705313/10000000000 : ℝ), (-2009482321/10000000000 : ℝ), (5419114623/10000000000 : ℝ)] ![(43352931492833/100000000000000 : ℝ), (12057287776771/100000000000000 : ℝ), (5573722589611/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304705313/10000000000 : ℝ)|^4241 ≤ (43352931492833/100000000000000 : ℝ)^3217
        have hw : |(5304705313/10000000000 : ℝ)|=(5304705313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2009482321/10000000000 : ℝ)|^4241 ≤ (12057287776771/100000000000000 : ℝ)^3217
        have hw : |(-2009482321/10000000000 : ℝ)|=(2009482321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419114623/10000000000 : ℝ)|^4241 ≤ (5573722589611/12500000000000 : ℝ)^3217
        have hw : |(5419114623/10000000000 : ℝ)|=(5419114623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s4_6 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165772041/312500000 : ℝ)*x 0 + (135477863/250000000 : ℝ)*x 1 + (-62796327/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165772041/312500000 : ℝ)^4241 ≤ (43352931482059/100000000000000 : ℝ)^3217 := by
    have hnat : (165772041 : ℕ)^4241*100000000000000^3217 ≤ 43352931482059^3217*312500000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165772041 312500000 43352931482059 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135477863/250000000 : ℝ)^4241 ≤ (44589779599609/100000000000000 : ℝ)^3217 := by
    have hnat : (135477863 : ℕ)^4241*100000000000000^3217 ≤ 44589779599609^3217*250000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135477863 250000000 44589779599609 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62796327/312500000 : ℝ)^4241 ≤ (12057288907917/100000000000000 : ℝ)^3217 := by
    have hnat : (62796327 : ℕ)^4241*100000000000000^3217 ≤ 12057288907917^3217*312500000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62796327 312500000 12057288907917 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165772041/312500000 : ℝ), (135477863/250000000 : ℝ), (-62796327/312500000 : ℝ)] ![(43352931482059/100000000000000 : ℝ), (44589779599609/100000000000000 : ℝ), (12057288907917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165772041/312500000 : ℝ)|^4241 ≤ (43352931482059/100000000000000 : ℝ)^3217
        have hw : |(165772041/312500000 : ℝ)|=(165772041/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135477863/250000000 : ℝ)|^4241 ≤ (44589779599609/100000000000000 : ℝ)^3217
        have hw : |(135477863/250000000 : ℝ)|=(135477863/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62796327/312500000 : ℝ)|^4241 ≤ (12057288907917/100000000000000 : ℝ)^3217
        have hw : |(-62796327/312500000 : ℝ)|=(62796327/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s4_7 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2171289109/5000000000 : ℝ)*x 0 + (4530064877/10000000000 : ℝ)*x 1 + (2081308939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171289109/5000000000 : ℝ)^4241 ≤ (8324908731503/25000000000000 : ℝ)^3217 := by
    have hnat : (2171289109 : ℕ)^4241*25000000000000^3217 ≤ 8324908731503^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171289109 5000000000 8324908731503 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4530064877/10000000000 : ℝ)^4241 ≤ (35207839018899/100000000000000 : ℝ)^3217 := by
    have hnat : (4530064877 : ℕ)^4241*100000000000000^3217 ≤ 35207839018899^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530064877 10000000000 35207839018899 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081308939/5000000000 : ℝ)^4241 ≤ (31492526032719/100000000000000 : ℝ)^3217 := by
    have hnat : (2081308939 : ℕ)^4241*100000000000000^3217 ≤ 31492526032719^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081308939 5000000000 31492526032719 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171289109/5000000000 : ℝ), (4530064877/10000000000 : ℝ), (2081308939/5000000000 : ℝ)] ![(8324908731503/25000000000000 : ℝ), (35207839018899/100000000000000 : ℝ), (31492526032719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171289109/5000000000 : ℝ)|^4241 ≤ (8324908731503/25000000000000 : ℝ)^3217
        have hw : |(2171289109/5000000000 : ℝ)|=(2171289109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4530064877/10000000000 : ℝ)|^4241 ≤ (35207839018899/100000000000000 : ℝ)^3217
        have hw : |(4530064877/10000000000 : ℝ)|=(4530064877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2081308939/5000000000 : ℝ)|^4241 ≤ (31492526032719/100000000000000 : ℝ)^3217
        have hw : |(2081308939/5000000000 : ℝ)|=(2081308939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1281_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (663/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (273/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3687/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (663/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (663/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (663/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (663/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (663/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (663/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (663/6250 : ℝ) ^ (265/64 : ℝ) ≤ (369465378387981/4000000000000000000 : ℝ) := by
    have hpowers : (663/6250 : ℝ)^265 ≤ (369465378387981/4000000000000000000 : ℝ)^64 := by
      have hnat : (663 : ℕ)^265*4000000000000000000^64 ≤ 369465378387981^64*6250^265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        663 6250 369465378387981 4000000000000000000 265 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (663/6250 : ℝ)) (X := (369465378387981/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hpowhi : (15081/100000 : ℝ) ^ (265/64 : ℝ) ≤ (39644897397761727/100000000000000000000 : ℝ) := by
    have hpowers : (15081/100000 : ℝ)^265 ≤ (39644897397761727/100000000000000000000 : ℝ)^64 := by
      have hnat : (15081 : ℕ)^265*100000000000000000000^64 ≤ 39644897397761727^64*100000^265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15081 100000 39644897397761727 100000000000000000000 265 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15081/100000 : ℝ)) (X := (39644897397761727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000369465378387981/2000000000000000000 : ℝ) ≤ (2500111528904699/2500000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (2000369465378387981/2000000000000000000 : ℝ)^64 ≤ (2500111528904699/2500000000000000 : ℝ)^265 := by
      have hnat : (2000369465378387981 : ℕ)^64*2500000000000000^265 ≤ 2500111528904699^265*2000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000369465378387981 2000000000000000000 2500111528904699 2500000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500111528904699/2500000000000000 : ℝ)) (X := (2000369465378387981/2000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012220382964365313/25000000000000000000 : ℝ) ≤ (1000118031632303/1000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (25012220382964365313/25000000000000000000 : ℝ)^64 ≤ (1000118031632303/1000000000000000 : ℝ)^265 := by
      have hnat : (25012220382964365313 : ℕ)^64*1000000000000000^265 ≤ 1000118031632303^265*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012220382964365313 25000000000000000000 1000118031632303 1000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000118031632303/1000000000000000 : ℝ)) (X := (25012220382964365313/25000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039644897397761727/50000000000000000000 : ℝ) ≤ (156279914328551/156250000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (50039644897397761727/50000000000000000000 : ℝ)^64 ≤ (156279914328551/156250000000000 : ℝ)^265 := by
      have hnat : (50039644897397761727 : ℕ)^64*156250000000000^265 ≤ 156279914328551^265*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039644897397761727 50000000000000000000 156279914328551 156250000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156279914328551/156250000000000 : ℝ)) (X := (50039644897397761727/50000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(369465378387981/4000000000000000000 : ℝ) ≤ ((1242122740917273499/1242500000000000000 : ℝ)+2*(40788928013/24850000000000 : ℝ)*(663/6250 : ℝ))^(265/64 : ℝ) := by
    rw [show (1242122740917273499/1242500000000000000 : ℝ)+2*(40788928013/24850000000000 : ℝ)*(663/6250 : ℝ)=(2500111528904699/2500000000000000 : ℝ) by norm_num, show 1+2*(369465378387981/4000000000000000000 : ℝ)=(2000369465378387981/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39644897397761727/100000000000000000000 : ℝ)+(369465378387981/4000000000000000000 : ℝ) ≤ ((1242122740917273499/1242500000000000000 : ℝ)+(40788928013/24850000000000 : ℝ)*((15081/100000 : ℝ)+(663/6250 : ℝ)))^(265/64 : ℝ) := by
    rw [show (1242122740917273499/1242500000000000000 : ℝ)+(40788928013/24850000000000 : ℝ)*((15081/100000 : ℝ)+(663/6250 : ℝ))=(1000118031632303/1000000000000000 : ℝ) by norm_num, show 1+(39644897397761727/100000000000000000000 : ℝ)+(369465378387981/4000000000000000000 : ℝ)=(25012220382964365313/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39644897397761727/100000000000000000000 : ℝ) ≤ ((1242122740917273499/1242500000000000000 : ℝ)+2*(40788928013/24850000000000 : ℝ)*(15081/100000 : ℝ))^(265/64 : ℝ) := by
    rw [show (1242122740917273499/1242500000000000000 : ℝ)+2*(40788928013/24850000000000 : ℝ)*(15081/100000 : ℝ)=(156279914328551/156250000000000 : ℝ) by norm_num, show 1+2*(39644897397761727/100000000000000000000 : ℝ)=(50039644897397761727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1242122740917273499/1242500000000000000 : ℝ)*(X 1 0+X 2 0)+(40788928013/24850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (663/6250 : ℝ)) (hi := (15081/100000 : ℝ)) (c := (1242122740917273499/1242500000000000000 : ℝ)) (alpha := (40788928013/24850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1242122740917273499/1242500000000000000 : ℝ)*(X 0 1+X 2 1)+(40788928013/24850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (663/6250 : ℝ)) (hi := (15081/100000 : ℝ)) (c := (1242122740917273499/1242500000000000000 : ℝ)) (alpha := (40788928013/24850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1242122740917273499/1242500000000000000 : ℝ)*(X 0 2+X 1 2)+(40788928013/24850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (663/6250 : ℝ)) (hi := (15081/100000 : ℝ)) (c := (1242122740917273499/1242500000000000000 : ℝ)) (alpha := (40788928013/24850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2097398741/10000000000 : ℝ)*X 0 0+(270989541/500000000 : ℝ)*X 0 1+(5238901827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350952879/10000000000 : ℝ)*X 1 0+(-1094847521/5000000000 : ℝ)*X 1 1+(654862731/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675476337/5000000000 : ℝ)*X 2 0+(523890203/1000000000 : ℝ)*X 2 1+(-87587803/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((6948077/16000000 : ℝ)*X 0 0+(2080617021/5000000000 : ℝ)*X 0 1+(2265720751/5000000000 : ℝ)*X 0 2+(6948077/16000000 : ℝ)*X 1 0+(2080617021/5000000000 : ℝ)*X 1 1+(2265720751/5000000000 : ℝ)*X 1 2+(6948077/16000000 : ℝ)*X 2 0+(2080617021/5000000000 : ℝ)*X 2 1+(2265720751/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2097413597/10000000000 : ℝ)*X 0 0+(2619787173/5000000000 : ℝ)*X 0 1+(5419114519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304705313/10000000000 : ℝ)*X 1 0+(-2009482321/10000000000 : ℝ)*X 1 1+(5419114623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165772041/312500000 : ℝ)*X 2 0+(135477863/250000000 : ℝ)*X 2 1+(-62796327/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2171289109/5000000000 : ℝ)*X 0 0+(4530064877/10000000000 : ℝ)*X 0 1+(2081308939/5000000000 : ℝ)*X 0 2+(2171289109/5000000000 : ℝ)*X 1 0+(4530064877/10000000000 : ℝ)*X 1 1+(2081308939/5000000000 : ℝ)*X 1 2+(2171289109/5000000000 : ℝ)*X 2 0+(4530064877/10000000000 : ℝ)*X 2 1+(2081308939/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (97819954916970372541385961/7765625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (904045213/50000000000000 : ℝ)*(base19) + (31555337/2500000000000 : ℝ)*(base23) + (96803123/50000000000000 : ℝ)*(lower2) + (327479531/100000000000000 : ℝ)*(upper3) + (7420319/50000000000000 : ℝ)*(lower4) + (514346392150079/12500000000000 : ℝ)*(major0) + (514346392150079/12500000000000 : ℝ)*(major1) + (514346392150079/12500000000000 : ℝ)*(major2) + (2764145830127411/50000000000000 : ℝ)*(sp0) + (221132803722897/4000000000000 : ℝ)*(sp1) + (5528320638949371/100000000000000 : ℝ)*(sp2) + (1350600707506973/50000000000000 : ℝ)*(sp3) + (30240908029/100000000000000 : ℝ)*(sp4) + (2317292501/12500000000000 : ℝ)*(sp7) + (540243990670791/20000000000000 : ℝ)*(f.failure) + (5528321901162851/100000000000000 : ℝ)*(f.sum) + (2307894025383/2485000000000000000000000000 : ℝ)*base66 + (312277468169618921/15531250000000000000000000000000 : ℝ)*base67 + (56082107492025171/15531250000000000000000000000000 : ℝ)*base69 + (182301845724025171/15531250000000000000000000000000 : ℝ)*base71 + (2650110470951/1242500000000000000000000000 : ℝ)*base73 + (190094918372181421/15531250000000000000000000000000 : ℝ)*base75 + (107848038847056421/15531250000000000000000000000000 : ℝ)*base77 + (231996979643618921/15531250000000000000000000000000 : ℝ)*base79 + (2523478987703/2485000000000000000000000000 : ℝ)*base82 + (7878527/2000000000000000000000 : ℝ)*base90 + (7878527/2000000000000000000000 : ℝ)*base92 + (7878527/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8007081631283853397922991/1553125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (145817921/25000000000000 : ℝ)*(base19) + (137099361/20000000000000 : ℝ)*(base23) + (32276651/50000000000000 : ℝ)*(upper3) + (72590949/100000000000000 : ℝ)*(lower4) + (27377439/20000000000000 : ℝ)*(upper5) + (103640803223253/2500000000000 : ℝ)*(major0) + (103640803223253/2500000000000 : ℝ)*(major1) + (103640803223253/2500000000000 : ℝ)*(major2) + (14458605037/100000000000000 : ℝ)*(sp1) + (2121676569/20000000000000 : ℝ)*(sp2) + (2784892423165057/50000000000000 : ℝ)*(sp4) + (2784884902226697/50000000000000 : ℝ)*(sp5) + (1113954710490093/20000000000000 : ℝ)*(sp6) + (1360739619840643/50000000000000 : ℝ)*(sp7) + (1360739619840643/50000000000000 : ℝ)*(f.failure) + (2784892423165057/50000000000000 : ℝ)*(f.sum) + (1187252079753/248500000000000000000000000 : ℝ)*base66 + (3374662501909747/3106250000000000000000000000000 : ℝ)*base67 + (1258026729190253/3106250000000000000000000000000 : ℝ)*base70 + (33649709490084003/3106250000000000000000000000000 : ℝ)*base72 + (24297368503/248500000000000000000000000 : ℝ)*base73 + (4813017010340253/3106250000000000000000000000000 : ℝ)*base76 + (15941331622615253/3106250000000000000000000000000 : ℝ)*base78 + (1547343515147247/3106250000000000000000000000000 : ℝ)*base79 + (1319288014957/497000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8223771/5000000000000000000000 : ℝ)*base90 + (8223771/5000000000000000000000 : ℝ)*base92 + (8223771/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1281_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (663/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (273/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1281_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1281_s5_0 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1048893863/5000000000 : ℝ)*x 0 + (2708258981/5000000000 : ℝ)*x 1 + (10238123/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048893863/5000000000 : ℝ)^4241 ≤ (3190157712961/25000000000000 : ℝ)^3217 := by
    have hnat : (1048893863 : ℕ)^4241*25000000000000^3217 ≤ 3190157712961^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048893863 5000000000 3190157712961 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708258981/5000000000 : ℝ)^4241 ≤ (44561615938307/100000000000000 : ℝ)^3217 := by
    have hnat : (2708258981 : ℕ)^4241*100000000000000^3217 ≤ 44561615938307^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708258981 5000000000 44561615938307 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10238123/19531250 : ℝ)^4241 ≤ (1066943829793/2500000000000 : ℝ)^3217 := by
    have hnat : (10238123 : ℕ)^4241*2500000000000^3217 ≤ 1066943829793^3217*19531250^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10238123 19531250 1066943829793 2500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1048893863/5000000000 : ℝ), (2708258981/5000000000 : ℝ), (10238123/19531250 : ℝ)] ![(3190157712961/25000000000000 : ℝ), (44561615938307/100000000000000 : ℝ), (1066943829793/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1048893863/5000000000 : ℝ)|^4241 ≤ (3190157712961/25000000000000 : ℝ)^3217
        have hw : |(-1048893863/5000000000 : ℝ)|=(1048893863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708258981/5000000000 : ℝ)|^4241 ≤ (44561615938307/100000000000000 : ℝ)^3217
        have hw : |(2708258981/5000000000 : ℝ)|=(2708258981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10238123/19531250 : ℝ)|^4241 ≤ (1066943829793/2500000000000 : ℝ)^3217
        have hw : |(10238123/19531250 : ℝ)|=(10238123/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s5_1 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337531059/2500000000 : ℝ)*x 0 + (-2186812449/10000000000 : ℝ)*x 1 + (2620959511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337531059/2500000000 : ℝ)^4241 ≤ (43842937615337/100000000000000 : ℝ)^3217 := by
    have hnat : (1337531059 : ℕ)^4241*100000000000000^3217 ≤ 43842937615337^3217*2500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337531059 2500000000 43842937615337 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2186812449/10000000000 : ℝ)^4241 ≤ (26326774781/195312500000 : ℝ)^3217 := by
    have hnat : (2186812449 : ℕ)^4241*195312500000^3217 ≤ 26326774781^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186812449 10000000000 26326774781 195312500000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620959511/5000000000 : ℝ)^4241 ≤ (21338876842723/50000000000000 : ℝ)^3217 := by
    have hnat : (2620959511 : ℕ)^4241*50000000000000^3217 ≤ 21338876842723^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620959511 5000000000 21338876842723 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337531059/2500000000 : ℝ), (-2186812449/10000000000 : ℝ), (2620959511/5000000000 : ℝ)] ![(43842937615337/100000000000000 : ℝ), (26326774781/195312500000 : ℝ), (21338876842723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337531059/2500000000 : ℝ)|^4241 ≤ (43842937615337/100000000000000 : ℝ)^3217
        have hw : |(1337531059/2500000000 : ℝ)|=(1337531059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2186812449/10000000000 : ℝ)|^4241 ≤ (26326774781/195312500000 : ℝ)^3217
        have hw : |(-2186812449/10000000000 : ℝ)|=(2186812449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620959511/5000000000 : ℝ)|^4241 ≤ (21338876842723/50000000000000 : ℝ)^3217
        have hw : |(2620959511/5000000000 : ℝ)|=(2620959511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s5_2 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070024869/2000000000 : ℝ)*x 0 + (2620959531/5000000000 : ℝ)*x 1 + (-2186812251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070024869/2000000000 : ℝ)^4241 ≤ (43842938792887/100000000000000 : ℝ)^3217 := by
    have hnat : (1070024869 : ℕ)^4241*100000000000000^3217 ≤ 43842938792887^3217*2000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070024869 2000000000 43842938792887 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620959531/5000000000 : ℝ)^4241 ≤ (42677754114773/100000000000000 : ℝ)^3217 := by
    have hnat : (2620959531 : ℕ)^4241*100000000000000^3217 ≤ 42677754114773^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620959531 5000000000 42677754114773 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2186812251/10000000000 : ℝ)^4241 ≤ (13479307078937/100000000000000 : ℝ)^3217 := by
    have hnat : (2186812251 : ℕ)^4241*100000000000000^3217 ≤ 13479307078937^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186812251 10000000000 13479307078937 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070024869/2000000000 : ℝ), (2620959531/5000000000 : ℝ), (-2186812251/10000000000 : ℝ)] ![(43842938792887/100000000000000 : ℝ), (42677754114773/100000000000000 : ℝ), (13479307078937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070024869/2000000000 : ℝ)|^4241 ≤ (43842938792887/100000000000000 : ℝ)^3217
        have hw : |(1070024869/2000000000 : ℝ)|=(1070024869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620959531/5000000000 : ℝ)|^4241 ≤ (42677754114773/100000000000000 : ℝ)^3217
        have hw : |(2620959531/5000000000 : ℝ)|=(2620959531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2186812251/10000000000 : ℝ)|^4241 ≤ (13479307078937/100000000000000 : ℝ)^3217
        have hw : |(-2186812251/10000000000 : ℝ)|=(2186812251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s5_3 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2171389389/5000000000 : ℝ)*x 0 + (4167640331/10000000000 : ℝ)*x 1 + (4418922/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171389389/5000000000 : ℝ)^4241 ≤ (6660332481173/20000000000000 : ℝ)^3217 := by
    have hnat : (2171389389 : ℕ)^4241*20000000000000^3217 ≤ 6660332481173^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171389389 5000000000 6660332481173 20000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4167640331/10000000000 : ℝ)^4241 ≤ (1261705132147/4000000000000 : ℝ)^3217 := by
    have hnat : (4167640331 : ℕ)^4241*4000000000000^3217 ≤ 1261705132147^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167640331 10000000000 1261705132147 4000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4418922/9765625 : ℝ)^4241 ≤ (35155709283739/100000000000000 : ℝ)^3217 := by
    have hnat : (4418922 : ℕ)^4241*100000000000000^3217 ≤ 35155709283739^3217*9765625^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418922 9765625 35155709283739 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171389389/5000000000 : ℝ), (4167640331/10000000000 : ℝ), (4418922/9765625 : ℝ)] ![(6660332481173/20000000000000 : ℝ), (1261705132147/4000000000000 : ℝ), (35155709283739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171389389/5000000000 : ℝ)|^4241 ≤ (6660332481173/20000000000000 : ℝ)^3217
        have hw : |(2171389389/5000000000 : ℝ)|=(2171389389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4167640331/10000000000 : ℝ)|^4241 ≤ (1261705132147/4000000000000 : ℝ)^3217
        have hw : |(4167640331/10000000000 : ℝ)|=(4167640331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4418922/9765625 : ℝ)|^4241 ≤ (35155709283739/100000000000000 : ℝ)^3217
        have hw : |(4418922/9765625 : ℝ)|=(4418922/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s5_4 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2097800469/10000000000 : ℝ)*x 0 + (5242545649/10000000000 : ℝ)*x 1 + (2707944173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097800469/10000000000 : ℝ)^4241 ≤ (12760733039849/100000000000000 : ℝ)^3217 := by
    have hnat : (2097800469 : ℕ)^4241*100000000000000^3217 ≤ 12760733039849^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097800469 10000000000 12760733039849 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242545649/10000000000 : ℝ)^4241 ≤ (8536895902893/20000000000000 : ℝ)^3217 := by
    have hnat : (5242545649 : ℕ)^4241*20000000000000^3217 ≤ 8536895902893^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242545649 10000000000 8536895902893 20000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707944173/5000000000 : ℝ)^4241 ≤ (22277393716303/50000000000000 : ℝ)^3217 := by
    have hnat : (2707944173 : ℕ)^4241*50000000000000^3217 ≤ 22277393716303^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707944173 5000000000 22277393716303 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2097800469/10000000000 : ℝ), (5242545649/10000000000 : ℝ), (2707944173/5000000000 : ℝ)] ![(12760733039849/100000000000000 : ℝ), (8536895902893/20000000000000 : ℝ), (22277393716303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2097800469/10000000000 : ℝ)|^4241 ≤ (12760733039849/100000000000000 : ℝ)^3217
        have hw : |(-2097800469/10000000000 : ℝ)|=(2097800469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242545649/10000000000 : ℝ)|^4241 ≤ (8536895902893/20000000000000 : ℝ)^3217
        have hw : |(5242545649/10000000000 : ℝ)|=(5242545649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707944173/5000000000 : ℝ)|^4241 ≤ (22277393716303/50000000000000 : ℝ)^3217
        have hw : |(2707944173/5000000000 : ℝ)|=(2707944173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s5_5 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061097071/2000000000 : ℝ)*x 0 + (-2012842777/10000000000 : ℝ)*x 1 + (2707944187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061097071/2000000000 : ℝ)^4241 ≤ (43361335812611/100000000000000 : ℝ)^3217 := by
    have hnat : (1061097071 : ℕ)^4241*100000000000000^3217 ≤ 43361335812611^3217*2000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061097071 2000000000 43361335812611 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012842777/10000000000 : ℝ)^4241 ≤ (6041938216583/50000000000000 : ℝ)^3217 := by
    have hnat : (2012842777 : ℕ)^4241*50000000000000^3217 ≤ 6041938216583^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012842777 10000000000 6041938216583 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707944187/5000000000 : ℝ)^4241 ≤ (1782191509451/4000000000000 : ℝ)^3217 := by
    have hnat : (2707944187 : ℕ)^4241*4000000000000^3217 ≤ 1782191509451^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707944187 5000000000 1782191509451 4000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061097071/2000000000 : ℝ), (-2012842777/10000000000 : ℝ), (2707944187/5000000000 : ℝ)] ![(43361335812611/100000000000000 : ℝ), (6041938216583/50000000000000 : ℝ), (1782191509451/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061097071/2000000000 : ℝ)|^4241 ≤ (43361335812611/100000000000000 : ℝ)^3217
        have hw : |(1061097071/2000000000 : ℝ)|=(1061097071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2012842777/10000000000 : ℝ)|^4241 ≤ (6041938216583/50000000000000 : ℝ)^3217
        have hw : |(-2012842777/10000000000 : ℝ)|=(2012842777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707944187/5000000000 : ℝ)|^4241 ≤ (1782191509451/4000000000000 : ℝ)^3217
        have hw : |(2707944187/5000000000 : ℝ)|=(2707944187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s5_6 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652742689/5000000000 : ℝ)*x 0 + (5415888349/10000000000 : ℝ)*x 1 + (-2012842779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652742689/5000000000 : ℝ)^4241 ≤ (5420167007553/12500000000000 : ℝ)^3217 := by
    have hnat : (2652742689 : ℕ)^4241*12500000000000^3217 ≤ 5420167007553^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652742689 5000000000 5420167007553 12500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415888349/10000000000 : ℝ)^4241 ≤ (22277393732571/50000000000000 : ℝ)^3217 := by
    have hnat : (5415888349 : ℕ)^4241*50000000000000^3217 ≤ 22277393732571^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415888349 10000000000 22277393732571 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012842779/10000000000 : ℝ)^4241 ≤ (6041938224497/50000000000000 : ℝ)^3217 := by
    have hnat : (2012842779 : ℕ)^4241*50000000000000^3217 ≤ 6041938224497^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012842779 10000000000 6041938224497 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652742689/5000000000 : ℝ), (5415888349/10000000000 : ℝ), (-2012842779/10000000000 : ℝ)] ![(5420167007553/12500000000000 : ℝ), (22277393732571/50000000000000 : ℝ), (6041938224497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652742689/5000000000 : ℝ)|^4241 ≤ (5420167007553/12500000000000 : ℝ)^3217
        have hw : |(2652742689/5000000000 : ℝ)|=(2652742689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415888349/10000000000 : ℝ)|^4241 ≤ (22277393732571/50000000000000 : ℝ)^3217
        have hw : |(5415888349/10000000000 : ℝ)|=(5415888349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2012842779/10000000000 : ℝ)|^4241 ≤ (6041938224497/50000000000000 : ℝ)^3217
        have hw : |(-2012842779/10000000000 : ℝ)|=(2012842779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s5_7 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (217140241/500000000 : ℝ)*x 0 + (4523693737/10000000000 : ℝ)*x 1 + (833786047/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217140241/500000000 : ℝ)^4241 ≤ (2081370354317/6250000000000 : ℝ)^3217 := by
    have hnat : (217140241 : ℕ)^4241*6250000000000^3217 ≤ 2081370354317^3217*500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217140241 500000000 2081370354317 6250000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523693737/10000000000 : ℝ)^4241 ≤ (7028515052861/20000000000000 : ℝ)^3217 := by
    have hnat : (4523693737 : ℕ)^4241*20000000000000^3217 ≤ 7028515052861^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523693737 10000000000 7028515052861 20000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (833786047/2000000000 : ℝ)^4241 ≤ (31555499047257/100000000000000 : ℝ)^3217 := by
    have hnat : (833786047 : ℕ)^4241*100000000000000^3217 ≤ 31555499047257^3217*2000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833786047 2000000000 31555499047257 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217140241/500000000 : ℝ), (4523693737/10000000000 : ℝ), (833786047/2000000000 : ℝ)] ![(2081370354317/6250000000000 : ℝ), (7028515052861/20000000000000 : ℝ), (31555499047257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217140241/500000000 : ℝ)|^4241 ≤ (2081370354317/6250000000000 : ℝ)^3217
        have hw : |(217140241/500000000 : ℝ)|=(217140241/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4523693737/10000000000 : ℝ)|^4241 ≤ (7028515052861/20000000000000 : ℝ)^3217
        have hw : |(4523693737/10000000000 : ℝ)|=(4523693737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(833786047/2000000000 : ℝ)|^4241 ≤ (31555499047257/100000000000000 : ℝ)^3217
        have hw : |(833786047/2000000000 : ℝ)|=(833786047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1281_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (273/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (2197/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (367/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (273/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (273/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (273/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (273/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (273/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (273/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (273/2500 : ℝ) ^ (265/64 : ℝ) ≤ (10414552461372269/100000000000000000000 : ℝ) := by
    have hpowers : (273/2500 : ℝ)^265 ≤ (10414552461372269/100000000000000000000 : ℝ)^64 := by
      have hnat : (273 : ℕ)^265*100000000000000000000^64 ≤ 10414552461372269^64*2500^265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        273 2500 10414552461372269 100000000000000000000 265 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (273/2500 : ℝ)) (X := (10414552461372269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hpowhi : (3687/25000 : ℝ) ^ (265/64 : ℝ) ≤ (564749217710271/1562500000000000000 : ℝ) := by
    have hpowers : (3687/25000 : ℝ)^265 ≤ (564749217710271/1562500000000000000 : ℝ)^64 := by
      have hnat : (3687 : ℕ)^265*1562500000000000000^64 ≤ 564749217710271^64*25000^265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3687 25000 564749217710271 1562500000000000000 265 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3687/25000 : ℝ)) (X := (564749217710271/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010414552461372269/50000000000000000000 : ℝ) ≤ (2500125750700449/2500000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (50010414552461372269/50000000000000000000 : ℝ)^64 ≤ (2500125750700449/2500000000000000 : ℝ)^265 := by
      have hnat : (50010414552461372269 : ℕ)^64*2500000000000000^265 ≤ 2500125750700449^265*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010414552461372269 50000000000000000000 2500125750700449 2500000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500125750700449/2500000000000000 : ℝ)) (X := (50010414552461372269/50000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046558502394829613/100000000000000000000 : ℝ) ≤ (10001124233268163/10000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (100046558502394829613/100000000000000000000 : ℝ)^64 ≤ (10001124233268163/10000000000000000 : ℝ)^265 := by
      have hnat : (100046558502394829613 : ℕ)^64*10000000000000000^265 ≤ 10001124233268163^265*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046558502394829613 100000000000000000000 10001124233268163 10000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001124233268163/10000000000000000 : ℝ)) (X := (100046558502394829613/100000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (781814749217710271/781250000000000000 : ℝ) ≤ (1000174546373453/1000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (781814749217710271/781250000000000000 : ℝ)^64 ≤ (1000174546373453/1000000000000000 : ℝ)^265 := by
      have hnat : (781814749217710271 : ℕ)^64*1000000000000000^265 ≤ 1000174546373453^265*781250000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781814749217710271 781250000000000000 1000174546373453 1000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000174546373453/1000000000000000 : ℝ)) (X := (781814749217710271/781250000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10414552461372269/100000000000000000000 : ℝ) ≤ ((398628727305623123/398750000000000000 : ℝ)+2*(621230466367/382800000000000 : ℝ)*(273/2500 : ℝ))^(265/64 : ℝ) := by
    rw [show (398628727305623123/398750000000000000 : ℝ)+2*(621230466367/382800000000000 : ℝ)*(273/2500 : ℝ)=(2500125750700449/2500000000000000 : ℝ) by norm_num, show 1+2*(10414552461372269/100000000000000000000 : ℝ)=(50010414552461372269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(564749217710271/1562500000000000000 : ℝ)+(10414552461372269/100000000000000000000 : ℝ) ≤ ((398628727305623123/398750000000000000 : ℝ)+(621230466367/382800000000000 : ℝ)*((3687/25000 : ℝ)+(273/2500 : ℝ)))^(265/64 : ℝ) := by
    rw [show (398628727305623123/398750000000000000 : ℝ)+(621230466367/382800000000000 : ℝ)*((3687/25000 : ℝ)+(273/2500 : ℝ))=(10001124233268163/10000000000000000 : ℝ) by norm_num, show 1+(564749217710271/1562500000000000000 : ℝ)+(10414552461372269/100000000000000000000 : ℝ)=(100046558502394829613/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(564749217710271/1562500000000000000 : ℝ) ≤ ((398628727305623123/398750000000000000 : ℝ)+2*(621230466367/382800000000000 : ℝ)*(3687/25000 : ℝ))^(265/64 : ℝ) := by
    rw [show (398628727305623123/398750000000000000 : ℝ)+2*(621230466367/382800000000000 : ℝ)*(3687/25000 : ℝ)=(1000174546373453/1000000000000000 : ℝ) by norm_num, show 1+2*(564749217710271/1562500000000000000 : ℝ)=(781814749217710271/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (398628727305623123/398750000000000000 : ℝ)*(X 1 0+X 2 0)+(621230466367/382800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (273/2500 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (398628727305623123/398750000000000000 : ℝ)) (alpha := (621230466367/382800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (398628727305623123/398750000000000000 : ℝ)*(X 0 1+X 2 1)+(621230466367/382800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (273/2500 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (398628727305623123/398750000000000000 : ℝ)) (alpha := (621230466367/382800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (398628727305623123/398750000000000000 : ℝ)*(X 0 2+X 1 2)+(621230466367/382800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (273/2500 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (398628727305623123/398750000000000000 : ℝ)) (alpha := (621230466367/382800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1048893863/5000000000 : ℝ)*X 0 0+(2708258981/5000000000 : ℝ)*X 0 1+(10238123/19531250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337531059/2500000000 : ℝ)*X 1 0+(-2186812449/10000000000 : ℝ)*X 1 1+(2620959511/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070024869/2000000000 : ℝ)*X 2 0+(2620959531/5000000000 : ℝ)*X 2 1+(-2186812251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2171389389/5000000000 : ℝ)*X 0 0+(4167640331/10000000000 : ℝ)*X 0 1+(4418922/9765625 : ℝ)*X 0 2+(2171389389/5000000000 : ℝ)*X 1 0+(4167640331/10000000000 : ℝ)*X 1 1+(4418922/9765625 : ℝ)*X 1 2+(2171389389/5000000000 : ℝ)*X 2 0+(4167640331/10000000000 : ℝ)*X 2 1+(4418922/9765625 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2097800469/10000000000 : ℝ)*X 0 0+(5242545649/10000000000 : ℝ)*X 0 1+(2707944173/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061097071/2000000000 : ℝ)*X 1 0+(-2012842777/10000000000 : ℝ)*X 1 1+(2707944187/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652742689/5000000000 : ℝ)*X 2 0+(5415888349/10000000000 : ℝ)*X 2 1+(-2012842779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((217140241/500000000 : ℝ)*X 0 0+(4523693737/10000000000 : ℝ)*X 0 1+(833786047/2000000000 : ℝ)*X 0 2+(217140241/500000000 : ℝ)*X 1 0+(4523693737/10000000000 : ℝ)*X 1 1+(833786047/2000000000 : ℝ)*X 1 2+(217140241/500000000 : ℝ)*X 2 0+(4523693737/10000000000 : ℝ)*X 2 1+(833786047/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3647945771227722020747757/906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1230398689/100000000000000 : ℝ)*(base19) + (637420389/50000000000000 : ℝ)*(base23) + (38652067/100000000000000 : ℝ)*(lower2) + (228713051/100000000000000 : ℝ)*(upper3) + (429762319/100000000000000 : ℝ)*(upper5) + (2131489863359461/50000000000000 : ℝ)*(major0) + (2131489863359461/50000000000000 : ℝ)*(major1) + (2131489863359461/50000000000000 : ℝ)*(major2) + (5727422992787789/100000000000000 : ℝ)*(sp0) + (5727443781601809/100000000000000 : ℝ)*(sp1) + (5727443737159719/100000000000000 : ℝ)*(sp2) + (699625571220009/25000000000000 : ℝ)*(sp3) + (5504803177/25000000000000 : ℝ)*(sp4) + (12022379983/100000000000000 : ℝ)*(sp7) + (1399257153630009/50000000000000 : ℝ)*(f.failure) + (5727445012000497/100000000000000 : ℝ)*(f.sum) + (4896302827723/870000000000000000000000000 : ℝ)*base66 + (3128714914485733/169921875000000000000000000000 : ℝ)*base68 + (2623847555830841/339843750000000000000000000000 : ℝ)*base70 + (29894195304401489/1359375000000000000000000000000 : ℝ)*base72 + (2163564919003/870000000000000000000000000 : ℝ)*base74 + (5637989186989807/679687500000000000000000000000 : ℝ)*base76 + (11237985959989807/679687500000000000000000000000 : ℝ)*base78 + (8453156922393341/339843750000000000000000000000 : ℝ)*base80 + (1466582687263/870000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5139073/5000000000000000000000 : ℝ)*base90 + (5139073/5000000000000000000000 : ℝ)*base92 + (5139073/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6397855212143835433737/797500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1397795109/100000000000000 : ℝ)*(base19) + (19318279/1250000000000 : ℝ)*(base23) + (163957093/100000000000000 : ℝ)*(upper3) + (28003059/50000000000000 : ℝ)*(lower4) + (42464293/25000000000000 : ℝ)*(upper5) + (33545693739853/781250000000 : ℝ)*(major0) + (33545693739853/781250000000 : ℝ)*(major1) + (33545693739853/781250000000 : ℝ)*(major2) + (14168034639/50000000000000 : ℝ)*(sp1) + (15183935497/50000000000000 : ℝ)*(sp2) + (5768918431966077/100000000000000 : ℝ)*(sp4) + (5768888698101689/100000000000000 : ℝ)*(sp5) + (5768886518632763/100000000000000 : ℝ)*(sp6) + (2818778898023317/100000000000000 : ℝ)*(sp7) + (2818778898023317/100000000000000 : ℝ)*(f.failure) + (5768918431966077/100000000000000 : ℝ)*(f.sum) + (18276278667437/4785000000000000000000000000 : ℝ)*base65 + (49945242465611431/7476562500000000000000000000000 : ℝ)*base67 + (84480253396824013/14953125000000000000000000000000 : ℝ)*base70 + (182062997732207237/14953125000000000000000000000000 : ℝ)*base71 + (6737084646121/2392500000000000000000000000 : ℝ)*base73 + (213218055663800987/14953125000000000000000000000000 : ℝ)*base75 + (10460908179983347/3738281250000000000000000000000 : ℝ)*base78 + (4064774370890111/1869140625000000000000000000000 : ℝ)*base80 + (4117862247349/598125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (24988349/10000000000000000000000 : ℝ)*base90 + (24988349/10000000000000000000000 : ℝ)*base92 + (24988349/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1281_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (273/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2197/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (367/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1281_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1281_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2197/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (367/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1281_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1281_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1281_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2197/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (367/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1281_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1671_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:26:42.391734+00:00
-- url     : https://prove2.me/submissions/f80adb72-35d0-4236-9f29-0e22e99a7968

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
theorem support_rectangle_w1671_s0_0 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1456509127/10000000000 : ℝ)*x 0 + (1439970031/2500000000 : ℝ)*x 1 + (2467727959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1456509127/10000000000 : ℝ)^5003 ≤ (354855010469/4000000000000 : ℝ)^3979 := by
    have hnat : (1456509127 : ℕ)^5003*4000000000000^3979 ≤ 354855010469^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1456509127 10000000000 354855010469 4000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1439970031/2500000000 : ℝ)^5003 ≤ (49975319923367/100000000000000 : ℝ)^3979 := by
    have hnat : (1439970031 : ℕ)^5003*100000000000000^3979 ≤ 49975319923367^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1439970031 2500000000 49975319923367 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2467727959/5000000000 : ℝ)^5003 ≤ (10288326200413/25000000000000 : ℝ)^3979 := by
    have hnat : (2467727959 : ℕ)^5003*25000000000000^3979 ≤ 10288326200413^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2467727959 5000000000 10288326200413 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1456509127/10000000000 : ℝ), (1439970031/2500000000 : ℝ), (2467727959/5000000000 : ℝ)] ![(354855010469/4000000000000 : ℝ), (49975319923367/100000000000000 : ℝ), (10288326200413/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1456509127/10000000000 : ℝ)|^5003 ≤ (354855010469/4000000000000 : ℝ)^3979
        have hw : |(-1456509127/10000000000 : ℝ)|=(1456509127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1439970031/2500000000 : ℝ)|^5003 ≤ (49975319923367/100000000000000 : ℝ)^3979
        have hw : |(1439970031/2500000000 : ℝ)|=(1439970031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2467727959/5000000000 : ℝ)|^5003 ≤ (10288326200413/25000000000000 : ℝ)^3979
        have hw : |(2467727959/5000000000 : ℝ)|=(2467727959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s0_1 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2120821/3906250 : ℝ)*x 0 + (-381432741/2000000000 : ℝ)*x 1 + (4935456959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120821/3906250 : ℝ)^5003 ≤ (4639594807643/10000000000000 : ℝ)^3979 := by
    have hnat : (2120821 : ℕ)^5003*10000000000000^3979 ≤ 4639594807643^3979*3906250^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120821 3906250 4639594807643 10000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (381432741/2000000000 : ℝ)^5003 ≤ (12450736191601/100000000000000 : ℝ)^3979 := by
    have hnat : (381432741 : ℕ)^5003*100000000000000^3979 ≤ 12450736191601^3979*2000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381432741 2000000000 12450736191601 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4935456959/10000000000 : ℝ)^5003 ≤ (5144164464459/12500000000000 : ℝ)^3979 := by
    have hnat : (4935456959 : ℕ)^5003*12500000000000^3979 ≤ 5144164464459^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4935456959 10000000000 5144164464459 12500000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120821/3906250 : ℝ), (-381432741/2000000000 : ℝ), (4935456959/10000000000 : ℝ)] ![(4639594807643/10000000000000 : ℝ), (12450736191601/100000000000000 : ℝ), (5144164464459/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120821/3906250 : ℝ)|^5003 ≤ (4639594807643/10000000000000 : ℝ)^3979
        have hw : |(2120821/3906250 : ℝ)|=(2120821/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-381432741/2000000000 : ℝ)|^5003 ≤ (12450736191601/100000000000000 : ℝ)^3979
        have hw : |(-381432741/2000000000 : ℝ)|=(381432741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4935456959/10000000000 : ℝ)|^5003 ≤ (5144164464459/12500000000000 : ℝ)^3979
        have hw : |(4935456959/10000000000 : ℝ)|=(4935456959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s0_2 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5429304167/10000000000 : ℝ)*x 0 + (4935455519/10000000000 : ℝ)*x 1 + (-953581197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5429304167/10000000000 : ℝ)^5003 ≤ (1855838957553/4000000000000 : ℝ)^3979 := by
    have hnat : (5429304167 : ℕ)^5003*4000000000000^3979 ≤ 1855838957553^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429304167 10000000000 1855838957553 4000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4935455519/10000000000 : ℝ)^5003 ≤ (10288325154617/25000000000000 : ℝ)^3979 := by
    have hnat : (4935455519 : ℕ)^5003*25000000000000^3979 ≤ 10288325154617^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4935455519 10000000000 10288325154617 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (953581197/5000000000 : ℝ)^5003 ≤ (12450725430263/100000000000000 : ℝ)^3979 := by
    have hnat : (953581197 : ℕ)^5003*100000000000000^3979 ≤ 12450725430263^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953581197 5000000000 12450725430263 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5429304167/10000000000 : ℝ), (4935455519/10000000000 : ℝ), (-953581197/5000000000 : ℝ)] ![(1855838957553/4000000000000 : ℝ), (10288325154617/25000000000000 : ℝ), (12450725430263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5429304167/10000000000 : ℝ)|^5003 ≤ (1855838957553/4000000000000 : ℝ)^3979
        have hw : |(5429304167/10000000000 : ℝ)|=(5429304167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4935455519/10000000000 : ℝ)|^5003 ≤ (10288325154617/25000000000000 : ℝ)^3979
        have hw : |(4935455519/10000000000 : ℝ)|=(4935455519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-953581197/5000000000 : ℝ)|^5003 ≤ (12450725430263/100000000000000 : ℝ)^3979
        have hw : |(-953581197/5000000000 : ℝ)|=(953581197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s0_3 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (81617883/200000000 : ℝ)*x 0 + (193014339/625000000 : ℝ)*x 1 + (5277752929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81617883/200000000 : ℝ)^5003 ≤ (1012588079861/3125000000000 : ℝ)^3979 := by
    have hnat : (81617883 : ℕ)^5003*3125000000000^3979 ≤ 1012588079861^3979*200000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81617883 200000000 1012588079861 3125000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193014339/625000000 : ℝ)^5003 ≤ (22823684381177/100000000000000 : ℝ)^3979 := by
    have hnat : (193014339 : ℕ)^5003*100000000000000^3979 ≤ 22823684381177^3979*625000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193014339 625000000 22823684381177 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5277752929/10000000000 : ℝ)^5003 ≤ (22386748524681/50000000000000 : ℝ)^3979 := by
    have hnat : (5277752929 : ℕ)^5003*50000000000000^3979 ≤ 22386748524681^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277752929 10000000000 22386748524681 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(81617883/200000000 : ℝ), (193014339/625000000 : ℝ), (5277752929/10000000000 : ℝ)] ![(1012588079861/3125000000000 : ℝ), (22823684381177/100000000000000 : ℝ), (22386748524681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(81617883/200000000 : ℝ)|^5003 ≤ (1012588079861/3125000000000 : ℝ)^3979
        have hw : |(81617883/200000000 : ℝ)|=(81617883/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(193014339/625000000 : ℝ)|^5003 ≤ (22823684381177/100000000000000 : ℝ)^3979
        have hw : |(193014339/625000000 : ℝ)|=(193014339/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5277752929/10000000000 : ℝ)|^5003 ≤ (22386748524681/50000000000000 : ℝ)^3979
        have hw : |(5277752929/10000000000 : ℝ)|=(5277752929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s0_4 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-729289999/5000000000 : ℝ)*x 0 + (4955669447/10000000000 : ℝ)*x 1 + (5738980383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (729289999/5000000000 : ℝ)^5003 ≤ (8887237584019/100000000000000 : ℝ)^3979 := by
    have hnat : (729289999 : ℕ)^5003*100000000000000^3979 ≤ 8887237584019^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729289999 5000000000 8887237584019 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4955669447/10000000000 : ℝ)^5003 ≤ (4136533842101/10000000000000 : ℝ)^3979 := by
    have hnat : (4955669447 : ℕ)^5003*10000000000000^3979 ≤ 4136533842101^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4955669447 10000000000 4136533842101 10000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5738980383/10000000000 : ℝ)^5003 ≤ (49747423974971/100000000000000 : ℝ)^3979 := by
    have hnat : (5738980383 : ℕ)^5003*100000000000000^3979 ≤ 49747423974971^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5738980383 10000000000 49747423974971 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-729289999/5000000000 : ℝ), (4955669447/10000000000 : ℝ), (5738980383/10000000000 : ℝ)] ![(8887237584019/100000000000000 : ℝ), (4136533842101/10000000000000 : ℝ), (49747423974971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-729289999/5000000000 : ℝ)|^5003 ≤ (8887237584019/100000000000000 : ℝ)^3979
        have hw : |(-729289999/5000000000 : ℝ)|=(729289999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4955669447/10000000000 : ℝ)|^5003 ≤ (4136533842101/10000000000000 : ℝ)^3979
        have hw : |(4955669447/10000000000 : ℝ)|=(4955669447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5738980383/10000000000 : ℝ)|^5003 ≤ (49747423974971/100000000000000 : ℝ)^3979
        have hw : |(5738980383/10000000000 : ℝ)|=(5738980383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s0_5 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (650564471/1250000000 : ℝ)*x 0 + (-1103640987/10000000000 : ℝ)*x 1 + (1434744363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (650564471/1250000000 : ℝ)^5003 ≤ (21996850364599/50000000000000 : ℝ)^3979 := by
    have hnat : (650564471 : ℕ)^5003*50000000000000^3979 ≤ 21996850364599^3979*1250000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650564471 1250000000 21996850364599 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103640987/10000000000 : ℝ)^5003 ≤ (1564726806671/25000000000000 : ℝ)^3979 := by
    have hnat : (1103640987 : ℕ)^5003*25000000000000^3979 ≤ 1564726806671^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103640987 10000000000 1564726806671 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1434744363/2500000000 : ℝ)^5003 ≤ (2487369601479/5000000000000 : ℝ)^3979 := by
    have hnat : (1434744363 : ℕ)^5003*5000000000000^3979 ≤ 2487369601479^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1434744363 2500000000 2487369601479 5000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(650564471/1250000000 : ℝ), (-1103640987/10000000000 : ℝ), (1434744363/2500000000 : ℝ)] ![(21996850364599/50000000000000 : ℝ), (1564726806671/25000000000000 : ℝ), (2487369601479/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(650564471/1250000000 : ℝ)|^5003 ≤ (21996850364599/50000000000000 : ℝ)^3979
        have hw : |(650564471/1250000000 : ℝ)|=(650564471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1103640987/10000000000 : ℝ)|^5003 ≤ (1564726806671/25000000000000 : ℝ)^3979
        have hw : |(-1103640987/10000000000 : ℝ)|=(1103640987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1434744363/2500000000 : ℝ)|^5003 ≤ (2487369601479/5000000000000 : ℝ)^3979
        have hw : |(1434744363/2500000000 : ℝ)|=(1434744363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s0_6 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2602257923/5000000000 : ℝ)*x 0 + (5738976663/10000000000 : ℝ)*x 1 + (-1103642077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2602257923/5000000000 : ℝ)^5003 ≤ (43993701558211/100000000000000 : ℝ)^3979 := by
    have hnat : (2602257923 : ℕ)^5003*100000000000000^3979 ≤ 43993701558211^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602257923 5000000000 43993701558211 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5738976663/10000000000 : ℝ)^5003 ≤ (12436845857539/25000000000000 : ℝ)^3979 := by
    have hnat : (5738976663 : ℕ)^5003*25000000000000^3979 ≤ 12436845857539^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5738976663 10000000000 12436845857539 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103642077/10000000000 : ℝ)^5003 ≤ (312945749953/5000000000000 : ℝ)^3979 := by
    have hnat : (1103642077 : ℕ)^5003*5000000000000^3979 ≤ 312945749953^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103642077 10000000000 312945749953 5000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2602257923/5000000000 : ℝ), (5738976663/10000000000 : ℝ), (-1103642077/10000000000 : ℝ)] ![(43993701558211/100000000000000 : ℝ), (12436845857539/25000000000000 : ℝ), (312945749953/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2602257923/5000000000 : ℝ)|^5003 ≤ (43993701558211/100000000000000 : ℝ)^3979
        have hw : |(2602257923/5000000000 : ℝ)|=(2602257923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5738976663/10000000000 : ℝ)|^5003 ≤ (12436845857539/25000000000000 : ℝ)^3979
        have hw : |(5738976663/10000000000 : ℝ)|=(5738976663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1103642077/10000000000 : ℝ)|^5003 ≤ (312945749953/5000000000000 : ℝ)^3979
        have hw : |(-1103642077/10000000000 : ℝ)|=(1103642077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s0_7 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (51079877/125000000 : ℝ)*x 0 + (1044813529/2000000000 : ℝ)*x 1 + (628747833/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51079877/125000000 : ℝ)^5003 ≤ (16228848814259/50000000000000 : ℝ)^3979 := by
    have hnat : (51079877 : ℕ)^5003*50000000000000^3979 ≤ 16228848814259^3979*125000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51079877 125000000 16228848814259 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044813529/2000000000 : ℝ)^5003 ≤ (44201605702817/100000000000000 : ℝ)^3979 := by
    have hnat : (1044813529 : ℕ)^5003*100000000000000^3979 ≤ 44201605702817^3979*2000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044813529 2000000000 44201605702817 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628747833/2000000000 : ℝ)^5003 ≤ (11670348327711/50000000000000 : ℝ)^3979 := by
    have hnat : (628747833 : ℕ)^5003*50000000000000^3979 ≤ 11670348327711^3979*2000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628747833 2000000000 11670348327711 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(51079877/125000000 : ℝ), (1044813529/2000000000 : ℝ), (628747833/2000000000 : ℝ)] ![(16228848814259/50000000000000 : ℝ), (44201605702817/100000000000000 : ℝ), (11670348327711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(51079877/125000000 : ℝ)|^5003 ≤ (16228848814259/50000000000000 : ℝ)^3979
        have hw : |(51079877/125000000 : ℝ)|=(51079877/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044813529/2000000000 : ℝ)|^5003 ≤ (44201605702817/100000000000000 : ℝ)^3979
        have hw : |(1044813529/2000000000 : ℝ)|=(1044813529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(628747833/2000000000 : ℝ)|^5003 ≤ (11670348327711/50000000000000 : ℝ)^3979
        have hw : |(628747833/2000000000 : ℝ)|=(628747833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1671_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2619/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (573/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4999/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4999 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4999*1^1024 ≤ 0^1024*1^4999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4999/1024 : ℝ) ≤ (142636993989825787/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4999 ≤ (142636993989825787/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4999*12500000000000000000^1024 ≤ 142636993989825787^1024*5^4999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 142636993989825787 12500000000000000000 4999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (142636993989825787/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4999 := by
      have hnat : (1 : ℕ)^1024*1^4999 ≤ 1^4999*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12642636993989825787/12500000000000000000 : ℝ) ≤ (5011634497275707/5000000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (12642636993989825787/12500000000000000000 : ℝ)^1024 ≤ (5011634497275707/5000000000000000 : ℝ)^4999 := by
      have hnat : (12642636993989825787 : ℕ)^1024*5000000000000000^4999 ≤ 5011634497275707^4999*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12642636993989825787 12500000000000000000 5011634497275707 5000000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011634497275707/5000000000000000 : ℝ)) (X := (12642636993989825787/12500000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6392636993989825787/6250000000000000000 : ℝ) ≤ (2511634497275707/2500000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (6392636993989825787/6250000000000000000 : ℝ)^1024 ≤ (2511634497275707/2500000000000000 : ℝ)^4999 := by
      have hnat : (6392636993989825787 : ℕ)^1024*2500000000000000^4999 ≤ 2511634497275707^4999*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6392636993989825787 6250000000000000000 2511634497275707 2500000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511634497275707/2500000000000000 : ℝ)) (X := (6392636993989825787/6250000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11634497275707/2000000000000000 : ℝ)*(0 : ℝ))^(4999/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11634497275707/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(142636993989825787/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11634497275707/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4999/1024 : ℝ) := by
    rw [show (1 : ℝ)+(11634497275707/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5011634497275707/5000000000000000 : ℝ) by norm_num, show 1+(142636993989825787/12500000000000000000 : ℝ)+(0 : ℝ)=(12642636993989825787/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(142636993989825787/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11634497275707/2000000000000000 : ℝ)*(2/5 : ℝ))^(4999/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11634497275707/2000000000000000 : ℝ)*(2/5 : ℝ)=(2511634497275707/2500000000000000 : ℝ) by norm_num, show 1+2*(142636993989825787/12500000000000000000 : ℝ)=(6392636993989825787/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11634497275707/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11634497275707/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11634497275707/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11634497275707/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11634497275707/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11634497275707/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1456509127/10000000000 : ℝ)*X 0 0+(1439970031/2500000000 : ℝ)*X 0 1+(2467727959/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2120821/3906250 : ℝ)*X 1 0+(-381432741/2000000000 : ℝ)*X 1 1+(4935456959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5429304167/10000000000 : ℝ)*X 2 0+(4935455519/10000000000 : ℝ)*X 2 1+(-953581197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((81617883/200000000 : ℝ)*X 0 0+(193014339/625000000 : ℝ)*X 0 1+(5277752929/10000000000 : ℝ)*X 0 2+(81617883/200000000 : ℝ)*X 1 0+(193014339/625000000 : ℝ)*X 1 1+(5277752929/10000000000 : ℝ)*X 1 2+(81617883/200000000 : ℝ)*X 2 0+(193014339/625000000 : ℝ)*X 2 1+(5277752929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-729289999/5000000000 : ℝ)*X 0 0+(4955669447/10000000000 : ℝ)*X 0 1+(5738980383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((650564471/1250000000 : ℝ)*X 1 0+(-1103640987/10000000000 : ℝ)*X 1 1+(1434744363/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2602257923/5000000000 : ℝ)*X 2 0+(5738976663/10000000000 : ℝ)*X 2 1+(-1103642077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((51079877/125000000 : ℝ)*X 0 0+(1044813529/2000000000 : ℝ)*X 0 1+(628747833/2000000000 : ℝ)*X 0 2+(51079877/125000000 : ℝ)*X 1 0+(1044813529/2000000000 : ℝ)*X 1 1+(628747833/2000000000 : ℝ)*X 1 2+(51079877/125000000 : ℝ)*X 2 0+(1044813529/2000000000 : ℝ)*X 2 1+(628747833/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (432815293172477897527329/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (157433567/100000000000000 : ℝ)*(base1) + (735797277/50000000000000 : ℝ)*(base19) + (484967197/25000000000000 : ℝ)*(base23) + (69482709/100000000000000 : ℝ)*(base24) + (367159169/100000000000000 : ℝ)*(upper5) + (834854786600449/100000000000000 : ℝ)*(major0) + (834854786600449/100000000000000 : ℝ)*(major1) + (834854786600449/100000000000000 : ℝ)*(major2) + (606486528452949/50000000000000 : ℝ)*(sp0) + (606490653839881/50000000000000 : ℝ)*(sp1) + (1212980769922819/100000000000000 : ℝ)*(sp2) + (456723695965811/100000000000000 : ℝ)*(sp3) + (77185953/781250000000 : ℝ)*(sp4) + (265198367/10000000000000 : ℝ)*(sp7) + (456726505383047/100000000000000 : ℝ)*(f.failure) + (303245694818579/25000000000000 : ℝ)*(f.sum) + (267096174207557/100000000000000000000000000000 : ℝ)*base66 + (225448439807557/200000000000000000000000000000 : ℝ)*base68 + (680292361992443/200000000000000000000000000000 : ℝ)*base69 + (851576391007557/200000000000000000000000000000 : ℝ)*base72 + (456675777407557/100000000000000000000000000000 : ℝ)*base74 + (209756457592443/200000000000000000000000000000 : ℝ)*base75 + (75997521607557/200000000000000000000000000000 : ℝ)*base78 + (3495212007557/200000000000000000000000000000 : ℝ)*base80 + (259810674692443/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (8845929/2000000000000000000000 : ℝ)*base90 + (8845929/2000000000000000000000 : ℝ)*base92 + (8845929/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (496304656530366753989721/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1835558609/100000000000000 : ℝ)*(base19) + (2179367853/100000000000000 : ℝ)*(base23) + (428308307/100000000000000 : ℝ)*(base39) + (23663549/100000000000000 : ℝ)*(upper2) + (79931769/20000000000000 : ℝ)*(upper5) + (439330737952951/50000000000000 : ℝ)*(major0) + (439330737952951/50000000000000 : ℝ)*(major1) + (175732209519519/20000000000000 : ℝ)*(major2) + (5077099401/100000000000000 : ℝ)*(sp1) + (1735799113/100000000000000 : ℝ)*(sp2) + (63831511534731/5000000000000 : ℝ)*(sp4) + (127662331803661/10000000000000 : ℝ)*(sp5) + (31915668595899/2500000000000 : ℝ)*(sp6) + (480691961939093/100000000000000 : ℝ)*(sp7) + (480691961939093/100000000000000 : ℝ)*(f.failure) + (1276630659002927/100000000000000 : ℝ)*(f.sum) + (831060763647379/200000000000000000000000000000 : ℝ)*base65 + (370608096024933/40000000000000000000000000000 : ℝ)*base67 + (489087760761357/100000000000000000000000000000 : ℝ)*base69 + (285735456224933/40000000000000000000000000000 : ℝ)*base71 + (1231329345647379/200000000000000000000000000000 : ℝ)*base73 + (363381778861357/100000000000000000000000000000 : ℝ)*base75 + (1145824350161357/100000000000000000000000000000 : ℝ)*base77 + (1266989230061357/100000000000000000000000000000 : ℝ)*base79 + (38577846111357/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (23861051/2000000000000000000000 : ℝ)*base90 + (23861051/2000000000000000000000 : ℝ)*base92 + (23861051/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1671_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2619/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (573/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1671_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1671_s1_0 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-388499129/2500000000 : ℝ)*x 0 + (1096276113/2000000000 : ℝ)*x 1 + (5150418053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (388499129/2500000000 : ℝ)^5003 ≤ (384971710027/4000000000000 : ℝ)^3979 := by
    have hnat : (388499129 : ℕ)^5003*4000000000000^3979 ≤ 384971710027^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388499129 2500000000 384971710027 4000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096276113/2000000000 : ℝ)^5003 ≤ (23478103054029/50000000000000 : ℝ)^3979 := by
    have hnat : (1096276113 : ℕ)^5003*50000000000000^3979 ≤ 23478103054029^3979*2000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096276113 2000000000 23478103054029 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5150418053/10000000000 : ℝ)^5003 ≤ (5427437640327/12500000000000 : ℝ)^3979 := by
    have hnat : (5150418053 : ℕ)^5003*12500000000000^3979 ≤ 5427437640327^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150418053 10000000000 5427437640327 12500000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-388499129/2500000000 : ℝ), (1096276113/2000000000 : ℝ), (5150418053/10000000000 : ℝ)] ![(384971710027/4000000000000 : ℝ), (23478103054029/50000000000000 : ℝ), (5427437640327/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-388499129/2500000000 : ℝ)|^5003 ≤ (384971710027/4000000000000 : ℝ)^3979
        have hw : |(-388499129/2500000000 : ℝ)|=(388499129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1096276113/2000000000 : ℝ)|^5003 ≤ (23478103054029/50000000000000 : ℝ)^3979
        have hw : |(1096276113/2000000000 : ℝ)|=(1096276113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5150418053/10000000000 : ℝ)|^5003 ≤ (5427437640327/12500000000000 : ℝ)^3979
        have hw : |(5150418053/10000000000 : ℝ)|=(5150418053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s1_1 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355212443/10000000000 : ℝ)*x 0 + (-107851081/625000000 : ℝ)*x 1 + (1287604443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355212443/10000000000 : ℝ)^5003 ≤ (5700160776833/12500000000000 : ℝ)^3979 := by
    have hnat : (5355212443 : ℕ)^5003*12500000000000^3979 ≤ 5700160776833^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355212443 10000000000 5700160776833 12500000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107851081/625000000 : ℝ)^5003 ≤ (10979215616879/100000000000000 : ℝ)^3979 := by
    have hnat : (107851081 : ℕ)^5003*100000000000000^3979 ≤ 10979215616879^3979*625000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107851081 625000000 10979215616879 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1287604443/2500000000 : ℝ)^5003 ≤ (678429658501/1562500000000 : ℝ)^3979 := by
    have hnat : (1287604443 : ℕ)^5003*1562500000000^3979 ≤ 678429658501^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287604443 2500000000 678429658501 1562500000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355212443/10000000000 : ℝ), (-107851081/625000000 : ℝ), (1287604443/2500000000 : ℝ)] ![(5700160776833/12500000000000 : ℝ), (10979215616879/100000000000000 : ℝ), (678429658501/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355212443/10000000000 : ℝ)|^5003 ≤ (5700160776833/12500000000000 : ℝ)^3979
        have hw : |(5355212443/10000000000 : ℝ)|=(5355212443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107851081/625000000 : ℝ)|^5003 ≤ (10979215616879/100000000000000 : ℝ)^3979
        have hw : |(-107851081/625000000 : ℝ)|=(107851081/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1287604443/2500000000 : ℝ)|^5003 ≤ (678429658501/1562500000000 : ℝ)^3979
        have hw : |(1287604443/2500000000 : ℝ)|=(1287604443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s1_2 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071042369/2000000000 : ℝ)*x 0 + (5150418469/10000000000 : ℝ)*x 1 + (-862808587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071042369/2000000000 : ℝ)^5003 ≤ (22800639906019/50000000000000 : ℝ)^3979 := by
    have hnat : (1071042369 : ℕ)^5003*50000000000000^3979 ≤ 22800639906019^3979*2000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071042369 2000000000 22800639906019 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150418469/10000000000 : ℝ)^5003 ≤ (21709752766073/50000000000000 : ℝ)^3979 := by
    have hnat : (5150418469 : ℕ)^5003*50000000000000^3979 ≤ 21709752766073^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150418469 10000000000 21709752766073 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (862808587/5000000000 : ℝ)^5003 ≤ (5489607320447/50000000000000 : ℝ)^3979 := by
    have hnat : (862808587 : ℕ)^5003*50000000000000^3979 ≤ 5489607320447^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862808587 5000000000 5489607320447 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071042369/2000000000 : ℝ), (5150418469/10000000000 : ℝ), (-862808587/5000000000 : ℝ)] ![(22800639906019/50000000000000 : ℝ), (21709752766073/50000000000000 : ℝ), (5489607320447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071042369/2000000000 : ℝ)|^5003 ≤ (22800639906019/50000000000000 : ℝ)^3979
        have hw : |(1071042369/2000000000 : ℝ)|=(1071042369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150418469/10000000000 : ℝ)|^5003 ≤ (21709752766073/50000000000000 : ℝ)^3979
        have hw : |(5150418469/10000000000 : ℝ)|=(5150418469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-862808587/5000000000 : ℝ)|^5003 ≤ (5489607320447/50000000000000 : ℝ)^3979
        have hw : |(-862808587/5000000000 : ℝ)|=(862808587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s1_3 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4158981501/10000000000 : ℝ)*x 0 + (373579941/1000000000 : ℝ)*x 1 + (2307388353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4158981501/10000000000 : ℝ)^5003 ≤ (33184316252397/100000000000000 : ℝ)^3979 := by
    have hnat : (4158981501 : ℕ)^5003*100000000000000^3979 ≤ 33184316252397^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158981501 10000000000 33184316252397 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (373579941/1000000000 : ℝ)^5003 ≤ (3624482448921/12500000000000 : ℝ)^3979 := by
    have hnat : (373579941 : ℕ)^5003*12500000000000^3979 ≤ 3624482448921^3979*1000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373579941 1000000000 3624482448921 12500000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2307388353/5000000000 : ℝ)^5003 ≤ (37819824146239/100000000000000 : ℝ)^3979 := by
    have hnat : (2307388353 : ℕ)^5003*100000000000000^3979 ≤ 37819824146239^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2307388353 5000000000 37819824146239 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4158981501/10000000000 : ℝ), (373579941/1000000000 : ℝ), (2307388353/5000000000 : ℝ)] ![(33184316252397/100000000000000 : ℝ), (3624482448921/12500000000000 : ℝ), (37819824146239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4158981501/10000000000 : ℝ)|^5003 ≤ (33184316252397/100000000000000 : ℝ)^3979
        have hw : |(4158981501/10000000000 : ℝ)|=(4158981501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(373579941/1000000000 : ℝ)|^5003 ≤ (3624482448921/12500000000000 : ℝ)^3979
        have hw : |(373579941/1000000000 : ℝ)|=(373579941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2307388353/5000000000 : ℝ)|^5003 ≤ (37819824146239/100000000000000 : ℝ)^3979
        have hw : |(2307388353/5000000000 : ℝ)|=(2307388353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s1_4 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1554128211/10000000000 : ℝ)*x 0 + (5153673019/10000000000 : ℝ)*x 1 + (43824653/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1554128211/10000000000 : ℝ)^5003 ≤ (4812659141519/50000000000000 : ℝ)^3979 := by
    have hnat : (1554128211 : ℕ)^5003*50000000000000^3979 ≤ 4812659141519^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554128211 10000000000 4812659141519 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5153673019/10000000000 : ℝ)^5003 ≤ (43454006015053/100000000000000 : ℝ)^3979 := by
    have hnat : (5153673019 : ℕ)^5003*100000000000000^3979 ≤ 43454006015053^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153673019 10000000000 43454006015053 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43824653/80000000 : ℝ)^5003 ≤ (11730168921101/25000000000000 : ℝ)^3979 := by
    have hnat : (43824653 : ℕ)^5003*25000000000000^3979 ≤ 11730168921101^3979*80000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43824653 80000000 11730168921101 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1554128211/10000000000 : ℝ), (5153673019/10000000000 : ℝ), (43824653/80000000 : ℝ)] ![(4812659141519/50000000000000 : ℝ), (43454006015053/100000000000000 : ℝ), (11730168921101/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1554128211/10000000000 : ℝ)|^5003 ≤ (4812659141519/50000000000000 : ℝ)^3979
        have hw : |(-1554128211/10000000000 : ℝ)|=(1554128211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5153673019/10000000000 : ℝ)|^5003 ≤ (43454006015053/100000000000000 : ℝ)^3979
        have hw : |(5153673019/10000000000 : ℝ)|=(5153673019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43824653/80000000 : ℝ)|^5003 ≤ (11730168921101/25000000000000 : ℝ)^3979
        have hw : |(43824653/80000000 : ℝ)|=(43824653/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s1_5 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1316637693/2500000000 : ℝ)*x 0 + (-1397954009/10000000000 : ℝ)*x 1 + (1095616331/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316637693/2500000000 : ℝ)^5003 ≤ (8930808016243/20000000000000 : ℝ)^3979 := by
    have hnat : (1316637693 : ℕ)^5003*20000000000000^3979 ≤ 8930808016243^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316637693 2500000000 8930808016243 20000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1397954009/10000000000 : ℝ)^5003 ≤ (2106320972599/25000000000000 : ℝ)^3979 := by
    have hnat : (1397954009 : ℕ)^5003*25000000000000^3979 ≤ 2106320972599^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397954009 10000000000 2106320972599 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095616331/2000000000 : ℝ)^5003 ≤ (46920676007487/100000000000000 : ℝ)^3979 := by
    have hnat : (1095616331 : ℕ)^5003*100000000000000^3979 ≤ 46920676007487^3979*2000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095616331 2000000000 46920676007487 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1316637693/2500000000 : ℝ), (-1397954009/10000000000 : ℝ), (1095616331/2000000000 : ℝ)] ![(8930808016243/20000000000000 : ℝ), (2106320972599/25000000000000 : ℝ), (46920676007487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1316637693/2500000000 : ℝ)|^5003 ≤ (8930808016243/20000000000000 : ℝ)^3979
        have hw : |(1316637693/2500000000 : ℝ)|=(1316637693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1397954009/10000000000 : ℝ)|^5003 ≤ (2106320972599/25000000000000 : ℝ)^3979
        have hw : |(-1397954009/10000000000 : ℝ)|=(1397954009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095616331/2000000000 : ℝ)|^5003 ≤ (46920676007487/100000000000000 : ℝ)^3979
        have hw : |(1095616331/2000000000 : ℝ)|=(1095616331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s1_6 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266550701/10000000000 : ℝ)*x 0 + (5478081637/10000000000 : ℝ)*x 1 + (-174744267/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266550701/10000000000 : ℝ)^5003 ≤ (5581754915537/12500000000000 : ℝ)^3979 := by
    have hnat : (5266550701 : ℕ)^5003*12500000000000^3979 ≤ 5581754915537^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266550701 10000000000 5581754915537 12500000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5478081637/10000000000 : ℝ)^5003 ≤ (46920675813637/100000000000000 : ℝ)^3979 := by
    have hnat : (5478081637 : ℕ)^5003*100000000000000^3979 ≤ 46920675813637^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478081637 10000000000 46920675813637 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (174744267/1250000000 : ℝ)^5003 ≤ (2106321213197/25000000000000 : ℝ)^3979 := by
    have hnat : (174744267 : ℕ)^5003*25000000000000^3979 ≤ 2106321213197^3979*1250000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174744267 1250000000 2106321213197 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266550701/10000000000 : ℝ), (5478081637/10000000000 : ℝ), (-174744267/1250000000 : ℝ)] ![(5581754915537/12500000000000 : ℝ), (46920675813637/100000000000000 : ℝ), (2106321213197/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266550701/10000000000 : ℝ)|^5003 ≤ (5581754915537/12500000000000 : ℝ)^3979
        have hw : |(5266550701/10000000000 : ℝ)|=(5266550701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5478081637/10000000000 : ℝ)|^5003 ≤ (46920675813637/100000000000000 : ℝ)^3979
        have hw : |(5478081637/10000000000 : ℝ)|=(5478081637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-174744267/1250000000 : ℝ)|^5003 ≤ (2106321213197/25000000000000 : ℝ)^3979
        have hw : |(-174744267/1250000000 : ℝ)|=(174744267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s1_7 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2079665981/5000000000 : ℝ)*x 0 + (4606132183/10000000000 : ℝ)*x 1 + (234035119/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079665981/5000000000 : ℝ)^5003 ≤ (33187832236101/100000000000000 : ℝ)^3979 := by
    have hnat : (2079665981 : ℕ)^5003*100000000000000^3979 ≤ 33187832236101^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079665981 5000000000 33187832236101 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4606132183/10000000000 : ℝ)^5003 ≤ (37730768457169/100000000000000 : ℝ)^3979 := by
    have hnat : (4606132183 : ℕ)^5003*100000000000000^3979 ≤ 37730768457169^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4606132183 10000000000 37730768457169 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234035119/625000000 : ℝ)^5003 ≤ (29081399290197/100000000000000 : ℝ)^3979 := by
    have hnat : (234035119 : ℕ)^5003*100000000000000^3979 ≤ 29081399290197^3979*625000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234035119 625000000 29081399290197 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2079665981/5000000000 : ℝ), (4606132183/10000000000 : ℝ), (234035119/625000000 : ℝ)] ![(33187832236101/100000000000000 : ℝ), (37730768457169/100000000000000 : ℝ), (29081399290197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2079665981/5000000000 : ℝ)|^5003 ≤ (33187832236101/100000000000000 : ℝ)^3979
        have hw : |(2079665981/5000000000 : ℝ)|=(2079665981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4606132183/10000000000 : ℝ)|^5003 ≤ (37730768457169/100000000000000 : ℝ)^3979
        have hw : |(4606132183/10000000000 : ℝ)|=(4606132183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(234035119/625000000 : ℝ)|^5003 ≤ (29081399290197/100000000000000 : ℝ)^3979
        have hw : |(234035119/625000000 : ℝ)|=(234035119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1671_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (573/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5011/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3413/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (573/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2619/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (573/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2619/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (573/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2619/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (573/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2619/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (573/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2619/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (573/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2619/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2619/50000 : ℝ) ^ (4999/1024 : ℝ) ≤ (27934833256371/50000000000000000000 : ℝ) := by
    have hpowers : (2619/50000 : ℝ)^4999 ≤ (27934833256371/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2619 : ℕ)^4999*50000000000000000000^1024 ≤ 27934833256371^1024*50000^4999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2619 50000 27934833256371 50000000000000000000 4999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2619/50000 : ℝ)) (X := (27934833256371/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (573/2500 : ℝ) ^ (4999/1024 : ℝ) ≤ (3763940168137819/5000000000000000000 : ℝ) := by
    have hpowers : (573/2500 : ℝ)^4999 ≤ (3763940168137819/5000000000000000000 : ℝ)^1024 := by
      have hnat : (573 : ℕ)^4999*5000000000000000000^1024 ≤ 3763940168137819^1024*2500^4999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        573 2500 3763940168137819 5000000000000000000 4999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (573/2500 : ℝ)) (X := (3763940168137819/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000027934833256371/25000000000000000000 : ℝ) ≤ (100000022888783/100000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (25000027934833256371/25000000000000000000 : ℝ)^1024 ≤ (100000022888783/100000000000000 : ℝ)^4999 := by
      have hnat : (25000027934833256371 : ℕ)^1024*100000000000000^4999 ≤ 100000022888783^4999*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000027934833256371 25000000000000000000 100000022888783 100000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100000022888783/100000000000000 : ℝ)) (X := (25000027934833256371/25000000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50037667336514634561/50000000000000000000 : ℝ) ≤ (2000308540148739/2000000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (50037667336514634561/50000000000000000000 : ℝ)^1024 ≤ (2000308540148739/2000000000000000 : ℝ)^4999 := by
      have hnat : (50037667336514634561 : ℕ)^1024*2000000000000000^4999 ≤ 2000308540148739^4999*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037667336514634561 50000000000000000000 2000308540148739 2000000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000308540148739/2000000000000000 : ℝ)) (X := (50037667336514634561/50000000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2503763940168137819/2500000000000000000 : ℝ) ≤ (1000308311260909/1000000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (2503763940168137819/2500000000000000000 : ℝ)^1024 ≤ (1000308311260909/1000000000000000 : ℝ)^4999 := by
      have hnat : (2503763940168137819 : ℕ)^1024*1000000000000000^4999 ≤ 1000308311260909^4999*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2503763940168137819 2500000000000000000 1000308311260909 1000000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000308311260909/1000000000000000 : ℝ)) (X := (2503763940168137819/2500000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(27934833256371/50000000000000000000 : ℝ) ≤ ((2946731718620737043/2947000000000000000 : ℝ)+2*(308082373079/353640000000000 : ℝ)*(2619/50000 : ℝ))^(4999/1024 : ℝ) := by
    rw [show (2946731718620737043/2947000000000000000 : ℝ)+2*(308082373079/353640000000000 : ℝ)*(2619/50000 : ℝ)=(100000022888783/100000000000000 : ℝ) by norm_num, show 1+2*(27934833256371/50000000000000000000 : ℝ)=(25000027934833256371/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3763940168137819/5000000000000000000 : ℝ)+(27934833256371/50000000000000000000 : ℝ) ≤ ((2946731718620737043/2947000000000000000 : ℝ)+(308082373079/353640000000000 : ℝ)*((573/2500 : ℝ)+(2619/50000 : ℝ)))^(4999/1024 : ℝ) := by
    rw [show (2946731718620737043/2947000000000000000 : ℝ)+(308082373079/353640000000000 : ℝ)*((573/2500 : ℝ)+(2619/50000 : ℝ))=(2000308540148739/2000000000000000 : ℝ) by norm_num, show 1+(3763940168137819/5000000000000000000 : ℝ)+(27934833256371/50000000000000000000 : ℝ)=(50037667336514634561/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3763940168137819/5000000000000000000 : ℝ) ≤ ((2946731718620737043/2947000000000000000 : ℝ)+2*(308082373079/353640000000000 : ℝ)*(573/2500 : ℝ))^(4999/1024 : ℝ) := by
    rw [show (2946731718620737043/2947000000000000000 : ℝ)+2*(308082373079/353640000000000 : ℝ)*(573/2500 : ℝ)=(1000308311260909/1000000000000000 : ℝ) by norm_num, show 1+2*(3763940168137819/5000000000000000000 : ℝ)=(2503763940168137819/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2946731718620737043/2947000000000000000 : ℝ)*(X 1 0+X 2 0)+(308082373079/353640000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (2619/50000 : ℝ)) (hi := (573/2500 : ℝ)) (c := (2946731718620737043/2947000000000000000 : ℝ)) (alpha := (308082373079/353640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2946731718620737043/2947000000000000000 : ℝ)*(X 0 1+X 2 1)+(308082373079/353640000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (2619/50000 : ℝ)) (hi := (573/2500 : ℝ)) (c := (2946731718620737043/2947000000000000000 : ℝ)) (alpha := (308082373079/353640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2946731718620737043/2947000000000000000 : ℝ)*(X 0 2+X 1 2)+(308082373079/353640000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (2619/50000 : ℝ)) (hi := (573/2500 : ℝ)) (c := (2946731718620737043/2947000000000000000 : ℝ)) (alpha := (308082373079/353640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-388499129/2500000000 : ℝ)*X 0 0+(1096276113/2000000000 : ℝ)*X 0 1+(5150418053/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355212443/10000000000 : ℝ)*X 1 0+(-107851081/625000000 : ℝ)*X 1 1+(1287604443/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071042369/2000000000 : ℝ)*X 2 0+(5150418469/10000000000 : ℝ)*X 2 1+(-862808587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4158981501/10000000000 : ℝ)*X 0 0+(373579941/1000000000 : ℝ)*X 0 1+(2307388353/5000000000 : ℝ)*X 0 2+(4158981501/10000000000 : ℝ)*X 1 0+(373579941/1000000000 : ℝ)*X 1 1+(2307388353/5000000000 : ℝ)*X 1 2+(4158981501/10000000000 : ℝ)*X 2 0+(373579941/1000000000 : ℝ)*X 2 1+(2307388353/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1554128211/10000000000 : ℝ)*X 0 0+(5153673019/10000000000 : ℝ)*X 0 1+(43824653/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1316637693/2500000000 : ℝ)*X 1 0+(-1397954009/10000000000 : ℝ)*X 1 1+(1095616331/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5266550701/10000000000 : ℝ)*X 2 0+(5478081637/10000000000 : ℝ)*X 2 1+(-174744267/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2079665981/5000000000 : ℝ)*X 0 0+(4606132183/10000000000 : ℝ)*X 0 1+(234035119/625000000 : ℝ)*X 0 2+(2079665981/5000000000 : ℝ)*X 1 0+(4606132183/10000000000 : ℝ)*X 1 1+(234035119/625000000 : ℝ)*X 1 2+(2079665981/5000000000 : ℝ)*X 2 0+(4606132183/10000000000 : ℝ)*X 2 1+(234035119/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85507210294936158148466049/10525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (581938039/25000000000000 : ℝ)*(base19) + (925414569/50000000000000 : ℝ)*(base23) + (334353229/100000000000000 : ℝ)*(upper3) + (1867869/2500000000000 : ℝ)*(upper4) + (27078517/10000000000000 : ℝ)*(upper5) + (2079619053805133/100000000000000 : ℝ)*(major0) + (2079619053805133/100000000000000 : ℝ)*(major1) + (2079619053805133/100000000000000 : ℝ)*(major2) + (151075638192263/5000000000000 : ℝ)*(sp0) + (755383023145129/25000000000000 : ℝ)*(sp1) + (1510766284751767/50000000000000 : ℝ)*(sp2) + (568847211380341/50000000000000 : ℝ)*(sp3) + (21656487413/100000000000000 : ℝ)*(sp4) + (8993710221/100000000000000 : ℝ)*(sp7) + (1137703416470903/100000000000000 : ℝ)*(f.failure) + (23605737658849/781250000000 : ℝ)*(f.sum) + (7778566748093/3536400000000000000000000000 : ℝ)*base65 + (184789201388399843/884100000000000000000000000000000 : ℝ)*base68 + (4629721128910500157/884100000000000000000000000000000 : ℝ)*base69 + (10728040743197400157/884100000000000000000000000000000 : ℝ)*base71 + (27981026837507/17682000000000000000000000000 : ℝ)*base74 + (7329969897217800157/884100000000000000000000000000000 : ℝ)*base75 + (7382960299705200157/884100000000000000000000000000000 : ℝ)*base77 + (1449215293925700157/884100000000000000000000000000000 : ℝ)*base79 + (51137682766987/17682000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (9241721/2000000000000000000000 : ℝ)*base90 + (9241721/2000000000000000000000 : ℝ)*base92 + (9241721/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (70160488807171185899621/5894000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1944439551/100000000000000 : ℝ)*(base19) + (964849343/50000000000000 : ℝ)*(base23) + (278331369/100000000000000 : ℝ)*(upper3) + (96243/400000000000 : ℝ)*(lower4) + (302679401/100000000000000 : ℝ)*(upper5) + (2121601879188329/100000000000000 : ℝ)*(major0) + (2121601879188329/100000000000000 : ℝ)*(major1) + (2121601879188329/100000000000000 : ℝ)*(major2) + (1862200709/10000000000000 : ℝ)*(sp1) + (17501205529/100000000000000 : ℝ)*(sp2) + (308253227525087/10000000000000 : ℝ)*(sp4) + (3082511708804229/100000000000000 : ℝ)*(sp5) + (616502568869331/20000000000000 : ℝ)*(sp6) + (36270971447979/3125000000000 : ℝ)*(sp7) + (36270971447979/3125000000000 : ℝ)*(f.failure) + (308253227525087/10000000000000 : ℝ)*(f.sum) + (4961014676179/17682000000000000000000000000 : ℝ)*base65 + (4146436090865911559/884100000000000000000000000000000 : ℝ)*base68 + (2121416756191288441/884100000000000000000000000000000 : ℝ)*base69 + (947100665789911559/884100000000000000000000000000000 : ℝ)*base72 + (18579890962459/3536400000000000000000000000 : ℝ)*base74 + (83514337418788441/884100000000000000000000000000000 : ℝ)*base75 + (1688834199391888441/884100000000000000000000000000000 : ℝ)*base77 + (759548722650511559/884100000000000000000000000000000 : ℝ)*base80 + (4145619501739/17682000000000000000000000000 : ℝ)*base81 + (116947/62500000000000000000 : ℝ)*base89 + (116947/62500000000000000000 : ℝ)*base91 + (116947/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1671_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (573/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5011/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3413/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1671_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1671_s2_0 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-390373597/2500000000 : ℝ)*x 0 + (5443886507/10000000000 : ℝ)*x 1 + (647868279/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390373597/2500000000 : ℝ)^5003 ≤ (4841357790657/50000000000000 : ℝ)^3979 := by
    have hnat : (390373597 : ℕ)^5003*50000000000000^3979 ≤ 4841357790657^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390373597 2500000000 4841357790657 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443886507/10000000000 : ℝ)^5003 ≤ (46552710341571/100000000000000 : ℝ)^3979 := by
    have hnat : (5443886507 : ℕ)^5003*100000000000000^3979 ≤ 46552710341571^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443886507 10000000000 46552710341571 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647868279/1250000000 : ℝ)^5003 ≤ (5470571758093/12500000000000 : ℝ)^3979 := by
    have hnat : (647868279 : ℕ)^5003*12500000000000^3979 ≤ 5470571758093^3979*1250000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647868279 1250000000 5470571758093 12500000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-390373597/2500000000 : ℝ), (5443886507/10000000000 : ℝ), (647868279/1250000000 : ℝ)] ![(4841357790657/50000000000000 : ℝ), (46552710341571/100000000000000 : ℝ), (5470571758093/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-390373597/2500000000 : ℝ)|^5003 ≤ (4841357790657/50000000000000 : ℝ)^3979
        have hw : |(-390373597/2500000000 : ℝ)|=(390373597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443886507/10000000000 : ℝ)|^5003 ≤ (46552710341571/100000000000000 : ℝ)^3979
        have hw : |(5443886507/10000000000 : ℝ)|=(5443886507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647868279/1250000000 : ℝ)|^5003 ≤ (5470571758093/12500000000000 : ℝ)^3979
        have hw : |(647868279/1250000000 : ℝ)|=(647868279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s2_1 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345222219/10000000000 : ℝ)*x 0 + (-169578279/1000000000 : ℝ)*x 1 + (5182946253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345222219/10000000000 : ℝ)^5003 ≤ (45494349246571/100000000000000 : ℝ)^3979 := by
    have hnat : (5345222219 : ℕ)^5003*100000000000000^3979 ≤ 45494349246571^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345222219 10000000000 45494349246571 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169578279/1000000000 : ℝ)^5003 ≤ (10741076455897/100000000000000 : ℝ)^3979 := by
    have hnat : (169578279 : ℕ)^5003*100000000000000^3979 ≤ 10741076455897^3979*1000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169578279 1000000000 10741076455897 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182946253/10000000000 : ℝ)^5003 ≤ (43764574287701/100000000000000 : ℝ)^3979 := by
    have hnat : (5182946253 : ℕ)^5003*100000000000000^3979 ≤ 43764574287701^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182946253 10000000000 43764574287701 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345222219/10000000000 : ℝ), (-169578279/1000000000 : ℝ), (5182946253/10000000000 : ℝ)] ![(45494349246571/100000000000000 : ℝ), (10741076455897/100000000000000 : ℝ), (43764574287701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345222219/10000000000 : ℝ)|^5003 ≤ (45494349246571/100000000000000 : ℝ)^3979
        have hw : |(5345222219/10000000000 : ℝ)|=(5345222219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-169578279/1000000000 : ℝ)|^5003 ≤ (10741076455897/100000000000000 : ℝ)^3979
        have hw : |(-169578279/1000000000 : ℝ)|=(169578279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182946253/10000000000 : ℝ)|^5003 ≤ (43764574287701/100000000000000 : ℝ)^3979
        have hw : |(5182946253/10000000000 : ℝ)|=(5182946253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s2_2 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16703819/31250000 : ℝ)*x 0 + (5182946269/10000000000 : ℝ)*x 1 + (-339156591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16703819/31250000 : ℝ)^5003 ≤ (909886955181/2000000000000 : ℝ)^3979 := by
    have hnat : (16703819 : ℕ)^5003*2000000000000^3979 ≤ 909886955181^3979*31250000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16703819 31250000 909886955181 2000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182946269/10000000000 : ℝ)^5003 ≤ (21882287228787/50000000000000 : ℝ)^3979 := by
    have hnat : (5182946269 : ℕ)^5003*50000000000000^3979 ≤ 21882287228787^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182946269 10000000000 21882287228787 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339156591/2000000000 : ℝ)^5003 ≤ (5370538884983/50000000000000 : ℝ)^3979 := by
    have hnat : (339156591 : ℕ)^5003*50000000000000^3979 ≤ 5370538884983^3979*2000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339156591 2000000000 5370538884983 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16703819/31250000 : ℝ), (5182946269/10000000000 : ℝ), (-339156591/2000000000 : ℝ)] ![(909886955181/2000000000000 : ℝ), (21882287228787/50000000000000 : ℝ), (5370538884983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16703819/31250000 : ℝ)|^5003 ≤ (909886955181/2000000000000 : ℝ)^3979
        have hw : |(16703819/31250000 : ℝ)|=(16703819/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182946269/10000000000 : ℝ)|^5003 ≤ (21882287228787/50000000000000 : ℝ)^3979
        have hw : |(5182946269/10000000000 : ℝ)|=(5182946269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-339156591/2000000000 : ℝ)|^5003 ≤ (5370538884983/50000000000000 : ℝ)^3979
        have hw : |(-339156591/2000000000 : ℝ)|=(339156591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s2_3 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4164597813/10000000000 : ℝ)*x 0 + (7656467/20000000 : ℝ)*x 1 + (282577731/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4164597813/10000000000 : ℝ)^5003 ≤ (33240670818161/100000000000000 : ℝ)^3979 := by
    have hnat : (4164597813 : ℕ)^5003*100000000000000^3979 ≤ 33240670818161^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164597813 10000000000 33240670818161 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7656467/20000000 : ℝ)^5003 ≤ (14950393066971/50000000000000 : ℝ)^3979 := by
    have hnat : (7656467 : ℕ)^5003*50000000000000^3979 ≤ 14950393066971^3979*20000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7656467 20000000 14950393066971 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282577731/625000000 : ℝ)^5003 ≤ (36858543026367/100000000000000 : ℝ)^3979 := by
    have hnat : (282577731 : ℕ)^5003*100000000000000^3979 ≤ 36858543026367^3979*625000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282577731 625000000 36858543026367 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4164597813/10000000000 : ℝ), (7656467/20000000 : ℝ), (282577731/625000000 : ℝ)] ![(33240670818161/100000000000000 : ℝ), (14950393066971/50000000000000 : ℝ), (36858543026367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4164597813/10000000000 : ℝ)|^5003 ≤ (33240670818161/100000000000000 : ℝ)^3979
        have hw : |(4164597813/10000000000 : ℝ)|=(4164597813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7656467/20000000 : ℝ)|^5003 ≤ (14950393066971/50000000000000 : ℝ)^3979
        have hw : |(7656467/20000000 : ℝ)|=(7656467/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282577731/625000000 : ℝ)|^5003 ≤ (36858543026367/100000000000000 : ℝ)^3979
        have hw : |(282577731/625000000 : ℝ)|=(282577731/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s2_4 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-390389957/2500000000 : ℝ)*x 0 + (518497421/1000000000 : ℝ)*x 1 + (5441836349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390389957/2500000000 : ℝ)^5003 ≤ (2420806450759/25000000000000 : ℝ)^3979 := by
    have hnat : (390389957 : ℕ)^5003*25000000000000^3979 ≤ 2420806450759^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390389957 2500000000 2420806450759 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518497421/1000000000 : ℝ)^5003 ≤ (8757221245649/20000000000000 : ℝ)^3979 := by
    have hnat : (518497421 : ℕ)^5003*20000000000000^3979 ≤ 8757221245649^3979*1000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518497421 1000000000 8757221245649 20000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5441836349/10000000000 : ℝ)^5003 ≤ (11632666986949/25000000000000 : ℝ)^3979 := by
    have hnat : (5441836349 : ℕ)^5003*25000000000000^3979 ≤ 11632666986949^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441836349 10000000000 11632666986949 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-390389957/2500000000 : ℝ), (518497421/1000000000 : ℝ), (5441836349/10000000000 : ℝ)] ![(2420806450759/25000000000000 : ℝ), (8757221245649/20000000000000 : ℝ), (11632666986949/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-390389957/2500000000 : ℝ)|^5003 ≤ (2420806450759/25000000000000 : ℝ)^3979
        have hw : |(-390389957/2500000000 : ℝ)|=(390389957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518497421/1000000000 : ℝ)|^5003 ≤ (8757221245649/20000000000000 : ℝ)^3979
        have hw : |(518497421/1000000000 : ℝ)|=(518497421/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5441836349/10000000000 : ℝ)|^5003 ≤ (11632666986949/25000000000000 : ℝ)^3979
        have hw : |(5441836349/10000000000 : ℝ)|=(5441836349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s2_5 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637677869/5000000000 : ℝ)*x 0 + (-718446157/5000000000 : ℝ)*x 1 + (1360459067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637677869/5000000000 : ℝ)^5003 ≤ (22373964259177/50000000000000 : ℝ)^3979 := by
    have hnat : (2637677869 : ℕ)^5003*50000000000000^3979 ≤ 22373964259177^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637677869 5000000000 22373964259177 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (718446157/5000000000 : ℝ)^5003 ≤ (8721404388599/100000000000000 : ℝ)^3979 := by
    have hnat : (718446157 : ℕ)^5003*100000000000000^3979 ≤ 8721404388599^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718446157 5000000000 8721404388599 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360459067/2500000000 : ℝ)^5003 ≤ (23265333538481/50000000000000 : ℝ)^3979 := by
    have hnat : (1360459067 : ℕ)^5003*50000000000000^3979 ≤ 23265333538481^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360459067 2500000000 23265333538481 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637677869/5000000000 : ℝ), (-718446157/5000000000 : ℝ), (1360459067/2500000000 : ℝ)] ![(22373964259177/50000000000000 : ℝ), (8721404388599/100000000000000 : ℝ), (23265333538481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637677869/5000000000 : ℝ)|^5003 ≤ (22373964259177/50000000000000 : ℝ)^3979
        have hw : |(2637677869/5000000000 : ℝ)|=(2637677869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-718446157/5000000000 : ℝ)|^5003 ≤ (8721404388599/100000000000000 : ℝ)^3979
        have hw : |(-718446157/5000000000 : ℝ)|=(718446157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360459067/2500000000 : ℝ)|^5003 ≤ (23265333538481/50000000000000 : ℝ)^3979
        have hw : |(1360459067/2500000000 : ℝ)|=(1360459067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s2_6 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211014199/400000000 : ℝ)*x 0 + (5441836787/10000000000 : ℝ)*x 1 + (-1436892649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211014199/400000000 : ℝ)^5003 ≤ (44747920380643/100000000000000 : ℝ)^3979 := by
    have hnat : (211014199 : ℕ)^5003*100000000000000^3979 ≤ 44747920380643^3979*400000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211014199 400000000 44747920380643 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441836787/10000000000 : ℝ)^5003 ≤ (186122690627/400000000000 : ℝ)^3979 := by
    have hnat : (5441836787 : ℕ)^5003*400000000000^3979 ≤ 186122690627^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441836787 10000000000 186122690627 400000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1436892649/10000000000 : ℝ)^5003 ≤ (2180351736301/25000000000000 : ℝ)^3979 := by
    have hnat : (1436892649 : ℕ)^5003*25000000000000^3979 ≤ 2180351736301^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1436892649 10000000000 2180351736301 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211014199/400000000 : ℝ), (5441836787/10000000000 : ℝ), (-1436892649/10000000000 : ℝ)] ![(44747920380643/100000000000000 : ℝ), (186122690627/400000000000 : ℝ), (2180351736301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211014199/400000000 : ℝ)|^5003 ≤ (44747920380643/100000000000000 : ℝ)^3979
        have hw : |(211014199/400000000 : ℝ)|=(211014199/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441836787/10000000000 : ℝ)|^5003 ≤ (186122690627/400000000000 : ℝ)^3979
        have hw : |(5441836787/10000000000 : ℝ)|=(5441836787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1436892649/10000000000 : ℝ)|^5003 ≤ (2180351736301/25000000000000 : ℝ)^3979
        have hw : |(-1436892649/10000000000 : ℝ)|=(1436892649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s2_7 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65074531/156250000 : ℝ)*x 0 + (4515857021/10000000000 : ℝ)*x 1 + (766735607/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65074531/156250000 : ℝ)^5003 ≤ (16621199353081/50000000000000 : ℝ)^3979 := by
    have hnat : (65074531 : ℕ)^5003*50000000000000^3979 ≤ 16621199353081^3979*156250000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65074531 156250000 16621199353081 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4515857021/10000000000 : ℝ)^5003 ≤ (36803336428989/100000000000000 : ℝ)^3979 := by
    have hnat : (4515857021 : ℕ)^5003*100000000000000^3979 ≤ 36803336428989^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515857021 10000000000 36803336428989 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (766735607/2000000000 : ℝ)^5003 ≤ (1497713242593/5000000000000 : ℝ)^3979 := by
    have hnat : (766735607 : ℕ)^5003*5000000000000^3979 ≤ 1497713242593^3979*2000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766735607 2000000000 1497713242593 5000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65074531/156250000 : ℝ), (4515857021/10000000000 : ℝ), (766735607/2000000000 : ℝ)] ![(16621199353081/50000000000000 : ℝ), (36803336428989/100000000000000 : ℝ), (1497713242593/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65074531/156250000 : ℝ)|^5003 ≤ (16621199353081/50000000000000 : ℝ)^3979
        have hw : |(65074531/156250000 : ℝ)|=(65074531/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4515857021/10000000000 : ℝ)|^5003 ≤ (36803336428989/100000000000000 : ℝ)^3979
        have hw : |(4515857021/10000000000 : ℝ)|=(4515857021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(766735607/2000000000 : ℝ)|^5003 ≤ (1497713242593/5000000000000 : ℝ)^3979
        have hw : |(766735607/2000000000 : ℝ)|=(766735607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1671_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3413/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5011/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (429/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (407/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3413/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5011/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3413/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5011/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3413/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5011/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3413/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5011/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3413/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5011/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3413/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5011/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5011/50000 : ℝ) ^ (4999/1024 : ℝ) ≤ (1326854430522553/100000000000000000000 : ℝ) := by
    have hpowers : (5011/50000 : ℝ)^4999 ≤ (1326854430522553/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5011 : ℕ)^4999*100000000000000000000^1024 ≤ 1326854430522553^1024*50000^4999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5011 50000 1326854430522553 100000000000000000000 4999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5011/50000 : ℝ)) (X := (1326854430522553/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3413/20000 : ℝ) ^ (4999/1024 : ℝ) ≤ (8917413543547329/50000000000000000000 : ℝ) := by
    have hpowers : (3413/20000 : ℝ)^4999 ≤ (8917413543547329/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3413 : ℕ)^4999*50000000000000000000^1024 ≤ 8917413543547329^1024*20000^4999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3413 20000 8917413543547329 50000000000000000000 4999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3413/20000 : ℝ)) (X := (8917413543547329/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001326854430522553/50000000000000000000 : ℝ) ≤ (10000054358255731/10000000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (50001326854430522553/50000000000000000000 : ℝ)^1024 ≤ (10000054358255731/10000000000000000 : ℝ)^4999 := by
      have hnat : (50001326854430522553 : ℕ)^1024*10000000000000000^4999 ≤ 10000054358255731^4999*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001326854430522553 50000000000000000000 10000054358255731 10000000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000054358255731/10000000000000000 : ℝ)) (X := (50001326854430522553/50000000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019161681517617211/100000000000000000000 : ℝ) ≤ (10000392479840319/10000000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (100019161681517617211/100000000000000000000 : ℝ)^1024 ≤ (10000392479840319/10000000000000000 : ℝ)^4999 := by
      have hnat : (100019161681517617211 : ℕ)^1024*10000000000000000^4999 ≤ 10000392479840319^4999*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019161681517617211 100000000000000000000 10000392479840319 10000000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000392479840319/10000000000000000 : ℝ)) (X := (100019161681517617211/100000000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25008917413543547329/25000000000000000000 : ℝ) ≤ (10000730601424907/10000000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (25008917413543547329/25000000000000000000 : ℝ)^1024 ≤ (10000730601424907/10000000000000000 : ℝ)^4999 := by
      have hnat : (25008917413543547329 : ℕ)^1024*10000000000000000^4999 ≤ 10000730601424907^4999*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008917413543547329 25000000000000000000 10000730601424907 10000000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000730601424907/10000000000000000 : ℝ)) (X := (25008917413543547329/25000000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1326854430522553/100000000000000000000 : ℝ) ≤ ((70423605536153631561/70430000000000000000 : ℝ)+2*(84530396147/176075000000000 : ℝ)*(5011/50000 : ℝ))^(4999/1024 : ℝ) := by
    rw [show (70423605536153631561/70430000000000000000 : ℝ)+2*(84530396147/176075000000000 : ℝ)*(5011/50000 : ℝ)=(10000054358255731/10000000000000000 : ℝ) by norm_num, show 1+2*(1326854430522553/100000000000000000000 : ℝ)=(50001326854430522553/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8917413543547329/50000000000000000000 : ℝ)+(1326854430522553/100000000000000000000 : ℝ) ≤ ((70423605536153631561/70430000000000000000 : ℝ)+(84530396147/176075000000000 : ℝ)*((3413/20000 : ℝ)+(5011/50000 : ℝ)))^(4999/1024 : ℝ) := by
    rw [show (70423605536153631561/70430000000000000000 : ℝ)+(84530396147/176075000000000 : ℝ)*((3413/20000 : ℝ)+(5011/50000 : ℝ))=(10000392479840319/10000000000000000 : ℝ) by norm_num, show 1+(8917413543547329/50000000000000000000 : ℝ)+(1326854430522553/100000000000000000000 : ℝ)=(100019161681517617211/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8917413543547329/50000000000000000000 : ℝ) ≤ ((70423605536153631561/70430000000000000000 : ℝ)+2*(84530396147/176075000000000 : ℝ)*(3413/20000 : ℝ))^(4999/1024 : ℝ) := by
    rw [show (70423605536153631561/70430000000000000000 : ℝ)+2*(84530396147/176075000000000 : ℝ)*(3413/20000 : ℝ)=(10000730601424907/10000000000000000 : ℝ) by norm_num, show 1+2*(8917413543547329/50000000000000000000 : ℝ)=(25008917413543547329/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (70423605536153631561/70430000000000000000 : ℝ)*(X 1 0+X 2 0)+(84530396147/176075000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (5011/50000 : ℝ)) (hi := (3413/20000 : ℝ)) (c := (70423605536153631561/70430000000000000000 : ℝ)) (alpha := (84530396147/176075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (70423605536153631561/70430000000000000000 : ℝ)*(X 0 1+X 2 1)+(84530396147/176075000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (5011/50000 : ℝ)) (hi := (3413/20000 : ℝ)) (c := (70423605536153631561/70430000000000000000 : ℝ)) (alpha := (84530396147/176075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (70423605536153631561/70430000000000000000 : ℝ)*(X 0 2+X 1 2)+(84530396147/176075000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (5011/50000 : ℝ)) (hi := (3413/20000 : ℝ)) (c := (70423605536153631561/70430000000000000000 : ℝ)) (alpha := (84530396147/176075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-390373597/2500000000 : ℝ)*X 0 0+(5443886507/10000000000 : ℝ)*X 0 1+(647868279/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345222219/10000000000 : ℝ)*X 1 0+(-169578279/1000000000 : ℝ)*X 1 1+(5182946253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((16703819/31250000 : ℝ)*X 2 0+(5182946269/10000000000 : ℝ)*X 2 1+(-339156591/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4164597813/10000000000 : ℝ)*X 0 0+(7656467/20000000 : ℝ)*X 0 1+(282577731/625000000 : ℝ)*X 0 2+(4164597813/10000000000 : ℝ)*X 1 0+(7656467/20000000 : ℝ)*X 1 1+(282577731/625000000 : ℝ)*X 1 2+(4164597813/10000000000 : ℝ)*X 2 0+(7656467/20000000 : ℝ)*X 2 1+(282577731/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-390389957/2500000000 : ℝ)*X 0 0+(518497421/1000000000 : ℝ)*X 0 1+(5441836349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2637677869/5000000000 : ℝ)*X 1 0+(-718446157/5000000000 : ℝ)*X 1 1+(1360459067/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211014199/400000000 : ℝ)*X 2 0+(5441836787/10000000000 : ℝ)*X 2 1+(-1436892649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((65074531/156250000 : ℝ)*X 0 0+(4515857021/10000000000 : ℝ)*X 0 1+(766735607/2000000000 : ℝ)*X 0 2+(65074531/156250000 : ℝ)*X 1 0+(4515857021/10000000000 : ℝ)*X 1 1+(766735607/2000000000 : ℝ)*X 1 2+(65074531/156250000 : ℝ)*X 2 0+(4515857021/10000000000 : ℝ)*X 2 1+(766735607/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6215370699005452273524774351/880375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44102287/4000000000000 : ℝ)*(base19) + (945219921/100000000000000 : ℝ)*(base23) + (7707751/25000000000000 : ℝ)*(lower2) + (124091749/50000000000000 : ℝ)*(upper3) + (59502153/100000000000000 : ℝ)*(upper5) + (1318828010735203/50000000000000 : ℝ)*(major0) + (1318828010735203/50000000000000 : ℝ)*(major1) + (1318828010735203/50000000000000 : ℝ)*(major2) + (119759693712077/3125000000000 : ℝ)*(sp0) + (958080083860361/25000000000000 : ℝ)*(sp1) + (1916160246389349/50000000000000 : ℝ)*(sp2) + (180373066616259/12500000000000 : ℝ)*(sp3) + (5619606077/50000000000000 : ℝ)*(sp4) + (5836681689/100000000000000 : ℝ)*(sp7) + (721495184805881/50000000000000 : ℝ)*(f.failure) + (3832321437998619/100000000000000 : ℝ)*(f.sum) + (4900842400049/4401875000000000000000000000 : ℝ)*base66 + (22837988781405441883/3521500000000000000000000000000000 : ℝ)*base67 + (7178841186279441883/3521500000000000000000000000000000 : ℝ)*base69 + (4841739645451058117/3521500000000000000000000000000000 : ℝ)*base72 + (4036937770293/35215000000000000000000000000 : ℝ)*base73 + (17885891724612441883/3521500000000000000000000000000000 : ℝ)*base75 + (4099322077062941883/3521500000000000000000000000000000 : ℝ)*base77 + (37313508326664441883/3521500000000000000000000000000000 : ℝ)*base79 + (86700951539227/35215000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (5133033/1000000000000000000000 : ℝ)*base89 + (5133033/1000000000000000000000 : ℝ)*base91 + (5133033/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3606459511740223887752805843/352150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2273771511/100000000000000 : ℝ)*(base19) + (1014674059/50000000000000 : ℝ)*(base23) + (19105553/10000000000000 : ℝ)*(upper2) + (149045817/50000000000000 : ℝ)*(upper3) + (93393353/25000000000000 : ℝ)*(upper5) + (535902405827479/20000000000000 : ℝ)*(major0) + (535902405827479/20000000000000 : ℝ)*(major1) + (535902405827479/20000000000000 : ℝ)*(major2) + (3412628021/12500000000000 : ℝ)*(sp1) + (24015755809/100000000000000 : ℝ)*(sp2) + (973283763992657/25000000000000 : ℝ)*(sp4) + (973276370293737/25000000000000 : ℝ)*(sp5) + (38931090108667/1000000000000 : ℝ)*(sp6) + (732944330464417/50000000000000 : ℝ)*(sp7) + (732944330464417/50000000000000 : ℝ)*(f.failure) + (973283763992657/25000000000000 : ℝ)*(f.sum) + (6593097840689/1760750000000000000000000000 : ℝ)*base65 + (3926218625272264719/1408600000000000000000000000000000 : ℝ)*base67 + (6432158919747464719/1408600000000000000000000000000000 : ℝ)*base69 + (6976102895641464719/1408600000000000000000000000000000 : ℝ)*base71 + (19205712379703/3521500000000000000000000000 : ℝ)*base73 + (13544603750541864719/1408600000000000000000000000000000 : ℝ)*base75 + (12753257738727064719/1408600000000000000000000000000000 : ℝ)*base77 + (3944215046640335281/1408600000000000000000000000000000 : ℝ)*base80 + (14117214824967/7043000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13681519/1000000000000000000000 : ℝ)*base90 + (13681519/1000000000000000000000 : ℝ)*base92 + (13681519/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1671_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3413/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5011/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (429/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (407/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1671_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1671_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (429/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (407/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1671_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1671_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1671_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (429/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (407/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1671_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

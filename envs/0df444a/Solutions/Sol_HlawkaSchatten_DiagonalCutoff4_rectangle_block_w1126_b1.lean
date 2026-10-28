-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1126_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:11:46.104995+00:00
-- url     : https://prove2.me/submissions/3433e7d7-b67d-41c1-b6a7-786e6ff7adb4

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
theorem support_rectangle_w1126_s3_0 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2170577507/10000000000 : ℝ)*x 0 + (1357714427/2500000000 : ℝ)*x 1 + (5230548681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170577507/10000000000 : ℝ)^8319 ≤ (13179904994341/100000000000000 : ℝ)^6271 := by
    have hnat : (2170577507 : ℕ)^8319*100000000000000^6271 ≤ 13179904994341^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170577507 10000000000 13179904994341 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357714427/2500000000 : ℝ)^8319 ≤ (444919092753/1000000000000 : ℝ)^6271 := by
    have hnat : (1357714427 : ℕ)^8319*1000000000000^6271 ≤ 444919092753^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357714427 2500000000 444919092753 1000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230548681/10000000000 : ℝ)^8319 ≤ (21164092854927/50000000000000 : ℝ)^6271 := by
    have hnat : (5230548681 : ℕ)^8319*50000000000000^6271 ≤ 21164092854927^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230548681 10000000000 21164092854927 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2170577507/10000000000 : ℝ), (1357714427/2500000000 : ℝ), (5230548681/10000000000 : ℝ)] ![(13179904994341/100000000000000 : ℝ), (444919092753/1000000000000 : ℝ), (21164092854927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2170577507/10000000000 : ℝ)|^8319 ≤ (13179904994341/100000000000000 : ℝ)^6271
        have hw : |(-2170577507/10000000000 : ℝ)|=(2170577507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357714427/2500000000 : ℝ)|^8319 ≤ (444919092753/1000000000000 : ℝ)^6271
        have hw : |(1357714427/2500000000 : ℝ)|=(1357714427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230548681/10000000000 : ℝ)|^8319 ≤ (21164092854927/50000000000000 : ℝ)^6271
        have hw : |(5230548681/10000000000 : ℝ)|=(5230548681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s3_1 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5354184059/10000000000 : ℝ)*x 0 + (-454601047/2000000000 : ℝ)*x 1 + (5230548593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354184059/10000000000 : ℝ)^8319 ≤ (10915138091907/25000000000000 : ℝ)^6271 := by
    have hnat : (5354184059 : ℕ)^8319*25000000000000^6271 ≤ 10915138091907^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354184059 10000000000 10915138091907 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454601047/2000000000 : ℝ)^8319 ≤ (7005631427283/50000000000000 : ℝ)^6271 := by
    have hnat : (454601047 : ℕ)^8319*50000000000000^6271 ≤ 7005631427283^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454601047 2000000000 7005631427283 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230548593/10000000000 : ℝ)^8319 ≤ (21164092382571/50000000000000 : ℝ)^6271 := by
    have hnat : (5230548593 : ℕ)^8319*50000000000000^6271 ≤ 21164092382571^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230548593 10000000000 21164092382571 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354184059/10000000000 : ℝ), (-454601047/2000000000 : ℝ), (5230548593/10000000000 : ℝ)] ![(10915138091907/25000000000000 : ℝ), (7005631427283/50000000000000 : ℝ), (21164092382571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354184059/10000000000 : ℝ)|^8319 ≤ (10915138091907/25000000000000 : ℝ)^6271
        have hw : |(5354184059/10000000000 : ℝ)|=(5354184059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-454601047/2000000000 : ℝ)|^8319 ≤ (7005631427283/50000000000000 : ℝ)^6271
        have hw : |(-454601047/2000000000 : ℝ)|=(454601047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230548593/10000000000 : ℝ)|^8319 ≤ (21164092382571/50000000000000 : ℝ)^6271
        have hw : |(5230548593/10000000000 : ℝ)|=(5230548593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s3_2 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338546039/2500000000 : ℝ)*x 0 + (1046109739/2000000000 : ℝ)*x 1 + (-568251243/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338546039/2500000000 : ℝ)^8319 ≤ (43660553416933/100000000000000 : ℝ)^6271 := by
    have hnat : (1338546039 : ℕ)^8319*100000000000000^6271 ≤ 43660553416933^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338546039 2500000000 43660553416933 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046109739/2000000000 : ℝ)^8319 ≤ (42328185860149/100000000000000 : ℝ)^6271 := by
    have hnat : (1046109739 : ℕ)^8319*100000000000000^6271 ≤ 42328185860149^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046109739 2000000000 42328185860149 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568251243/2500000000 : ℝ)^8319 ≤ (1401126070393/10000000000000 : ℝ)^6271 := by
    have hnat : (568251243 : ℕ)^8319*10000000000000^6271 ≤ 1401126070393^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568251243 2500000000 1401126070393 10000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338546039/2500000000 : ℝ), (1046109739/2000000000 : ℝ), (-568251243/2500000000 : ℝ)] ![(43660553416933/100000000000000 : ℝ), (42328185860149/100000000000000 : ℝ), (1401126070393/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338546039/2500000000 : ℝ)|^8319 ≤ (43660553416933/100000000000000 : ℝ)^6271
        have hw : |(1338546039/2500000000 : ℝ)|=(1338546039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046109739/2000000000 : ℝ)|^8319 ≤ (42328185860149/100000000000000 : ℝ)^6271
        have hw : |(1046109739/2000000000 : ℝ)|=(1046109739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-568251243/2500000000 : ℝ)|^8319 ≤ (1401126070393/10000000000000 : ℝ)^6271
        have hw : |(-568251243/2500000000 : ℝ)|=(568251243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s3_3 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174582763/400000000 : ℝ)*x 0 + (834089531/2000000000 : ℝ)*x 1 + (2283853261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174582763/400000000 : ℝ)^8319 ≤ (8323240947101/25000000000000 : ℝ)^6271 := by
    have hnat : (174582763 : ℕ)^8319*25000000000000^6271 ≤ 8323240947101^6271*400000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174582763 400000000 8323240947101 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834089531/2000000000 : ℝ)^8319 ≤ (7835756332697/25000000000000 : ℝ)^6271 := by
    have hnat : (834089531 : ℕ)^8319*25000000000000^6271 ≤ 7835756332697^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834089531 2000000000 7835756332697 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2283853261/5000000000 : ℝ)^8319 ≤ (35364010869013/100000000000000 : ℝ)^6271 := by
    have hnat : (2283853261 : ℕ)^8319*100000000000000^6271 ≤ 35364010869013^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283853261 5000000000 35364010869013 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174582763/400000000 : ℝ), (834089531/2000000000 : ℝ), (2283853261/5000000000 : ℝ)] ![(8323240947101/25000000000000 : ℝ), (7835756332697/25000000000000 : ℝ), (35364010869013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174582763/400000000 : ℝ)|^8319 ≤ (8323240947101/25000000000000 : ℝ)^6271
        have hw : |(174582763/400000000 : ℝ)|=(174582763/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(834089531/2000000000 : ℝ)|^8319 ≤ (7835756332697/25000000000000 : ℝ)^6271
        have hw : |(834089531/2000000000 : ℝ)|=(834089531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2283853261/5000000000 : ℝ)|^8319 ≤ (35364010869013/100000000000000 : ℝ)^6271
        have hw : |(2283853261/5000000000 : ℝ)|=(2283853261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s3_4 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1085298211/5000000000 : ℝ)*x 0 + (5231334691/10000000000 : ℝ)*x 1 + (5430067229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085298211/5000000000 : ℝ)^8319 ≤ (1647507169613/12500000000000 : ℝ)^6271 := by
    have hnat : (1085298211 : ℕ)^8319*12500000000000^6271 ≤ 1647507169613^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085298211 5000000000 1647507169613 12500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231334691/10000000000 : ℝ)^8319 ≤ (21168312009739/50000000000000 : ℝ)^6271 := by
    have hnat : (5231334691 : ℕ)^8319*50000000000000^6271 ≤ 21168312009739^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231334691 10000000000 21168312009739 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430067229/10000000000 : ℝ)^8319 ≤ (44483318606879/100000000000000 : ℝ)^6271 := by
    have hnat : (5430067229 : ℕ)^8319*100000000000000^6271 ≤ 44483318606879^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430067229 10000000000 44483318606879 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1085298211/5000000000 : ℝ), (5231334691/10000000000 : ℝ), (5430067229/10000000000 : ℝ)] ![(1647507169613/12500000000000 : ℝ), (21168312009739/50000000000000 : ℝ), (44483318606879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1085298211/5000000000 : ℝ)|^8319 ≤ (1647507169613/12500000000000 : ℝ)^6271
        have hw : |(-1085298211/5000000000 : ℝ)|=(1085298211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231334691/10000000000 : ℝ)|^8319 ≤ (21168312009739/50000000000000 : ℝ)^6271
        have hw : |(5231334691/10000000000 : ℝ)|=(5231334691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430067229/10000000000 : ℝ)|^8319 ≤ (44483318606879/100000000000000 : ℝ)^6271
        have hw : |(5430067229/10000000000 : ℝ)|=(5430067229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s3_5 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5303496251/10000000000 : ℝ)*x 0 + (-1036743407/5000000000 : ℝ)*x 1 + (5430067161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303496251/10000000000 : ℝ)^8319 ≤ (43113082216611/100000000000000 : ℝ)^6271 := by
    have hnat : (5303496251 : ℕ)^8319*100000000000000^6271 ≤ 43113082216611^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303496251 10000000000 43113082216611 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036743407/5000000000 : ℝ)^8319 ≤ (49614399557/400000000000 : ℝ)^6271 := by
    have hnat : (1036743407 : ℕ)^8319*400000000000^6271 ≤ 49614399557^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036743407 5000000000 49614399557 400000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430067161/10000000000 : ℝ)^8319 ≤ (22241658933947/50000000000000 : ℝ)^6271 := by
    have hnat : (5430067161 : ℕ)^8319*50000000000000^6271 ≤ 22241658933947^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430067161 10000000000 22241658933947 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303496251/10000000000 : ℝ), (-1036743407/5000000000 : ℝ), (5430067161/10000000000 : ℝ)] ![(43113082216611/100000000000000 : ℝ), (49614399557/400000000000 : ℝ), (22241658933947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303496251/10000000000 : ℝ)|^8319 ≤ (43113082216611/100000000000000 : ℝ)^6271
        have hw : |(5303496251/10000000000 : ℝ)|=(5303496251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036743407/5000000000 : ℝ)|^8319 ≤ (49614399557/400000000000 : ℝ)^6271
        have hw : |(-1036743407/5000000000 : ℝ)|=(1036743407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430067161/10000000000 : ℝ)|^8319 ≤ (22241658933947/50000000000000 : ℝ)^6271
        have hw : |(5430067161/10000000000 : ℝ)|=(5430067161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s3_6 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5303496343/10000000000 : ℝ)*x 0 + (1357516783/2500000000 : ℝ)*x 1 + (-2073486731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303496343/10000000000 : ℝ)^8319 ≤ (21556541604371/50000000000000 : ℝ)^6271 := by
    have hnat : (5303496343 : ℕ)^8319*50000000000000^6271 ≤ 21556541604371^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303496343 10000000000 21556541604371 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357516783/2500000000 : ℝ)^8319 ≤ (44483317552739/100000000000000 : ℝ)^6271 := by
    have hnat : (1357516783 : ℕ)^8319*100000000000000^6271 ≤ 44483317552739^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357516783 2500000000 44483317552739 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2073486731/10000000000 : ℝ)^8319 ≤ (6201799615297/50000000000000 : ℝ)^6271 := by
    have hnat : (2073486731 : ℕ)^8319*50000000000000^6271 ≤ 6201799615297^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073486731 10000000000 6201799615297 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303496343/10000000000 : ℝ), (1357516783/2500000000 : ℝ), (-2073486731/10000000000 : ℝ)] ![(21556541604371/50000000000000 : ℝ), (44483317552739/100000000000000 : ℝ), (6201799615297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303496343/10000000000 : ℝ)|^8319 ≤ (21556541604371/50000000000000 : ℝ)^6271
        have hw : |(5303496343/10000000000 : ℝ)|=(5303496343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357516783/2500000000 : ℝ)|^8319 ≤ (44483317552739/100000000000000 : ℝ)^6271
        have hw : |(1357516783/2500000000 : ℝ)|=(1357516783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2073486731/10000000000 : ℝ)|^8319 ≤ (6201799615297/50000000000000 : ℝ)^6271
        have hw : |(-2073486731/10000000000 : ℝ)|=(2073486731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s3_7 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182303161/5000000000 : ℝ)*x 0 + (913229589/2000000000 : ℝ)*x 1 + (4172015249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182303161/5000000000 : ℝ)^8319 ≤ (6658668139621/20000000000000 : ℝ)^6271 := by
    have hnat : (2182303161 : ℕ)^8319*20000000000000^6271 ≤ 6658668139621^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182303161 5000000000 6658668139621 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (913229589/2000000000 : ℝ)^8319 ≤ (35348004172563/100000000000000 : ℝ)^6271 := by
    have hnat : (913229589 : ℕ)^8319*100000000000000^6271 ≤ 35348004172563^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913229589 2000000000 35348004172563 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172015249/10000000000 : ℝ)^8319 ≤ (15679327554373/50000000000000 : ℝ)^6271 := by
    have hnat : (4172015249 : ℕ)^8319*50000000000000^6271 ≤ 15679327554373^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172015249 10000000000 15679327554373 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182303161/5000000000 : ℝ), (913229589/2000000000 : ℝ), (4172015249/10000000000 : ℝ)] ![(6658668139621/20000000000000 : ℝ), (35348004172563/100000000000000 : ℝ), (15679327554373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182303161/5000000000 : ℝ)|^8319 ≤ (6658668139621/20000000000000 : ℝ)^6271
        have hw : |(2182303161/5000000000 : ℝ)|=(2182303161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(913229589/2000000000 : ℝ)|^8319 ≤ (35348004172563/100000000000000 : ℝ)^6271
        have hw : |(913229589/2000000000 : ℝ)|=(913229589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172015249/10000000000 : ℝ)|^8319 ≤ (15679327554373/50000000000000 : ℝ)^6271
        have hw : |(4172015249/10000000000 : ℝ)|=(4172015249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1126_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16551/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10587/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (593/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16551/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8997/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16551/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8997/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16551/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8997/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16551/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8997/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16551/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8997/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16551/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8997/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8997/100000 : ℝ) ^ (4159/1024 : ℝ) ≤ (353120878070413/6250000000000000000 : ℝ) := by
    have hpowers : (8997/100000 : ℝ)^4159 ≤ (353120878070413/6250000000000000000 : ℝ)^1024 := by
      have hnat : (8997 : ℕ)^4159*6250000000000000000^1024 ≤ 353120878070413^1024*100000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8997 100000 353120878070413 6250000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8997/100000 : ℝ)) (X := (353120878070413/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16551/100000 : ℝ) ^ (4159/1024 : ℝ) ≤ (67179433393179543/100000000000000000000 : ℝ) := by
    have hpowers : (16551/100000 : ℝ)^4159 ≤ (67179433393179543/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16551 : ℕ)^4159*100000000000000000000^1024 ≤ 67179433393179543^1024*100000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16551 100000 67179433393179543 100000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16551/100000 : ℝ)) (X := (67179433393179543/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125353120878070413/3125000000000000000 : ℝ) ≤ (10000278205630471/10000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (3125353120878070413/3125000000000000000 : ℝ)^1024 ≤ (10000278205630471/10000000000000000 : ℝ)^4159 := by
      have hnat : (3125353120878070413 : ℕ)^1024*10000000000000000^4159 ≤ 10000278205630471^4159*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125353120878070413 3125000000000000000 10000278205630471 10000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000278205630471/10000000000000000 : ℝ)) (X := (3125353120878070413/3125000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100072829367442306151/100000000000000000000 : ℝ) ≤ (5000896330972839/5000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (100072829367442306151/100000000000000000000 : ℝ)^1024 ≤ (5000896330972839/5000000000000000 : ℝ)^4159 := by
      have hnat : (100072829367442306151 : ℕ)^1024*5000000000000000^4159 ≤ 5000896330972839^4159*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100072829367442306151 100000000000000000000 5000896330972839 5000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000896330972839/5000000000000000 : ℝ)) (X := (100072829367442306151/100000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50067179433393179543/50000000000000000000 : ℝ) ≤ (2000661423652177/2000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (50067179433393179543/50000000000000000000 : ℝ)^1024 ≤ (2000661423652177/2000000000000000 : ℝ)^4159 := by
      have hnat : (50067179433393179543 : ℕ)^1024*2000000000000000^4159 ≤ 2000661423652177^4159*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50067179433393179543 50000000000000000000 2000661423652177 2000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000661423652177/2000000000000000 : ℝ)) (X := (50067179433393179543/50000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(353120878070413/6250000000000000000 : ℝ) ≤ ((3146452101599864299/3147500000000000000 : ℝ)+2*(1514456315207/755400000000000 : ℝ)*(8997/100000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (3146452101599864299/3147500000000000000 : ℝ)+2*(1514456315207/755400000000000 : ℝ)*(8997/100000 : ℝ)=(10000278205630471/10000000000000000 : ℝ) by norm_num, show 1+2*(353120878070413/6250000000000000000 : ℝ)=(3125353120878070413/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(67179433393179543/100000000000000000000 : ℝ)+(353120878070413/6250000000000000000 : ℝ) ≤ ((3146452101599864299/3147500000000000000 : ℝ)+(1514456315207/755400000000000 : ℝ)*((16551/100000 : ℝ)+(8997/100000 : ℝ)))^(4159/1024 : ℝ) := by
    rw [show (3146452101599864299/3147500000000000000 : ℝ)+(1514456315207/755400000000000 : ℝ)*((16551/100000 : ℝ)+(8997/100000 : ℝ))=(5000896330972839/5000000000000000 : ℝ) by norm_num, show 1+(67179433393179543/100000000000000000000 : ℝ)+(353120878070413/6250000000000000000 : ℝ)=(100072829367442306151/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(67179433393179543/100000000000000000000 : ℝ) ≤ ((3146452101599864299/3147500000000000000 : ℝ)+2*(1514456315207/755400000000000 : ℝ)*(16551/100000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (3146452101599864299/3147500000000000000 : ℝ)+2*(1514456315207/755400000000000 : ℝ)*(16551/100000 : ℝ)=(2000661423652177/2000000000000000 : ℝ) by norm_num, show 1+2*(67179433393179543/100000000000000000000 : ℝ)=(50067179433393179543/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3146452101599864299/3147500000000000000 : ℝ)*(X 1 0+X 2 0)+(1514456315207/755400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (8997/100000 : ℝ)) (hi := (16551/100000 : ℝ)) (c := (3146452101599864299/3147500000000000000 : ℝ)) (alpha := (1514456315207/755400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3146452101599864299/3147500000000000000 : ℝ)*(X 0 1+X 2 1)+(1514456315207/755400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (8997/100000 : ℝ)) (hi := (16551/100000 : ℝ)) (c := (3146452101599864299/3147500000000000000 : ℝ)) (alpha := (1514456315207/755400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3146452101599864299/3147500000000000000 : ℝ)*(X 0 2+X 1 2)+(1514456315207/755400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (8997/100000 : ℝ)) (hi := (16551/100000 : ℝ)) (c := (3146452101599864299/3147500000000000000 : ℝ)) (alpha := (1514456315207/755400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2170577507/10000000000 : ℝ)*X 0 0+(1357714427/2500000000 : ℝ)*X 0 1+(5230548681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354184059/10000000000 : ℝ)*X 1 0+(-454601047/2000000000 : ℝ)*X 1 1+(5230548593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338546039/2500000000 : ℝ)*X 2 0+(1046109739/2000000000 : ℝ)*X 2 1+(-568251243/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((174582763/400000000 : ℝ)*X 0 0+(834089531/2000000000 : ℝ)*X 0 1+(2283853261/5000000000 : ℝ)*X 0 2+(174582763/400000000 : ℝ)*X 1 0+(834089531/2000000000 : ℝ)*X 1 1+(2283853261/5000000000 : ℝ)*X 1 2+(174582763/400000000 : ℝ)*X 2 0+(834089531/2000000000 : ℝ)*X 2 1+(2283853261/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1085298211/5000000000 : ℝ)*X 0 0+(5231334691/10000000000 : ℝ)*X 0 1+(5430067229/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303496251/10000000000 : ℝ)*X 1 0+(-1036743407/5000000000 : ℝ)*X 1 1+(5430067161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303496343/10000000000 : ℝ)*X 2 0+(1357516783/2500000000 : ℝ)*X 2 1+(-2073486731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182303161/5000000000 : ℝ)*X 0 0+(913229589/2000000000 : ℝ)*X 0 1+(4172015249/10000000000 : ℝ)*X 0 2+(2182303161/5000000000 : ℝ)*X 1 0+(913229589/2000000000 : ℝ)*X 1 1+(4172015249/10000000000 : ℝ)*X 1 2+(2182303161/5000000000 : ℝ)*X 2 0+(913229589/2000000000 : ℝ)*X 2 1+(4172015249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3689853705643991017009761/1229492187500000000000000000000 : ℝ) := by norm_num
    linear_combination (25570261/2500000000000 : ℝ)*(base19) + (487383447/50000000000000 : ℝ)*(base23) + (38240949/50000000000000 : ℝ)*(lower2) + (82026317/50000000000000 : ℝ)*(upper5) + (234674707947543/6250000000000 : ℝ)*(major0) + (234674707947543/6250000000000 : ℝ)*(major1) + (234674707947543/6250000000000 : ℝ)*(major2) + (998460304657553/20000000000000 : ℝ)*(sp0) + (1248080687158829/25000000000000 : ℝ)*(sp1) + (624040407117537/12500000000000 : ℝ)*(sp2) + (629314736214343/25000000000000 : ℝ)*(sp3) + (709638107/3125000000000 : ℝ)*(sp4) + (230130717/50000000000000 : ℝ)*(sp5) + (3688859733/50000000000000 : ℝ)*(sp7) + (2517266322576837/100000000000000 : ℝ)*(f.failure) + (499232423170719/10000000000000 : ℝ)*(f.sum) + (41579211340119/6295000000000000000000000000 : ℝ)*base66 + (151681556293163893/19671875000000000000000000000000 : ℝ)*base68 + (84635783964130817/4917968750000000000000000000000 : ℝ)*base70 + (307717017591038893/19671875000000000000000000000000 : ℝ)*base72 + (2243331200497/3147500000000000000000000000 : ℝ)*base74 + (266906728326195143/19671875000000000000000000000000 : ℝ)*base76 + (450350673761070143/19671875000000000000000000000000 : ℝ)*base78 + (236938146809476393/19671875000000000000000000000000 : ℝ)*base80 + (8731952848267/3147500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (8962911/1250000000000000000000 : ℝ)*base89 + (8962911/1250000000000000000000 : ℝ)*base91 + (8962911/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (161687000751478092123663549/39343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (722030679/100000000000000 : ℝ)*(base19) + (173194803/20000000000000 : ℝ)*(base23) + (14424121/20000000000000 : ℝ)*(upper3) + (17501969/100000000000000 : ℝ)*(lower4) + (12380339/12500000000000 : ℝ)*(upper5) + (946138308985667/25000000000000 : ℝ)*(major0) + (946138308985667/25000000000000 : ℝ)*(major1) + (946138308985667/25000000000000 : ℝ)*(major2) + (1401033223/12500000000000 : ℝ)*(sp1) + (13683207887/100000000000000 : ℝ)*(sp2) + (5031889901841743/100000000000000 : ℝ)*(sp4) + (5031877971545279/100000000000000 : ℝ)*(sp5) + (5031875352659841/100000000000000 : ℝ)*(sp6) + (1268608216528491/50000000000000 : ℝ)*(sp7) + (1268608216528491/50000000000000 : ℝ)*(f.failure) + (5031889901841743/100000000000000 : ℝ)*(f.sum) + (1312921350637/1180312500000000000000000000 : ℝ)*base66 + (185629689549317701/236062500000000000000000000000000 : ℝ)*base68 + (383225867022692701/236062500000000000000000000000000 : ℝ)*base70 + (1002917122274307299/236062500000000000000000000000000 : ℝ)*base71 + (7853085389599/9442500000000000000000000000 : ℝ)*base73 + (1087916026489442701/236062500000000000000000000000000 : ℝ)*base76 + (456452842377432299/236062500000000000000000000000000 : ℝ)*base77 + (942020458969817701/236062500000000000000000000000000 : ℝ)*base80 + (58275549176183/18885000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5021327/625000000000000000000 : ℝ)*base90 + (5021327/625000000000000000000 : ℝ)*base92 + (5021327/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1126_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16551/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10587/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (593/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1126_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1126_s4_0 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2173712751/10000000000 : ℝ)*x 0 + (5402669707/10000000000 : ℝ)*x 1 + (5256686221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173712751/10000000000 : ℝ)^8319 ≤ (330129141861/2500000000000 : ℝ)^6271 := by
    have hnat : (2173712751 : ℕ)^8319*2500000000000^6271 ≤ 330129141861^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173712751 10000000000 330129141861 2500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402669707/10000000000 : ℝ)^8319 ≤ (22092911959217/50000000000000 : ℝ)^6271 := by
    have hnat : (5402669707 : ℕ)^8319*50000000000000^6271 ≤ 22092911959217^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402669707 10000000000 22092911959217 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256686221/10000000000 : ℝ)^8319 ≤ (21304505195717/50000000000000 : ℝ)^6271 := by
    have hnat : (5256686221 : ℕ)^8319*50000000000000^6271 ≤ 21304505195717^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256686221 10000000000 21304505195717 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2173712751/10000000000 : ℝ), (5402669707/10000000000 : ℝ), (5256686221/10000000000 : ℝ)] ![(330129141861/2500000000000 : ℝ), (22092911959217/50000000000000 : ℝ), (21304505195717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2173712751/10000000000 : ℝ)|^8319 ≤ (330129141861/2500000000000 : ℝ)^6271
        have hw : |(-2173712751/10000000000 : ℝ)|=(2173712751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402669707/10000000000 : ℝ)|^8319 ≤ (22092911959217/50000000000000 : ℝ)^6271
        have hw : |(5402669707/10000000000 : ℝ)|=(5402669707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256686221/10000000000 : ℝ)|^8319 ≤ (21304505195717/50000000000000 : ℝ)^6271
        have hw : |(5256686221/10000000000 : ℝ)|=(5256686221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s4_1 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347156889/10000000000 : ℝ)*x 0 + (-1123955943/5000000000 : ℝ)*x 1 + (1314171571/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347156889/10000000000 : ℝ)^8319 ≤ (21792275833149/50000000000000 : ℝ)^6271 := by
    have hnat : (5347156889 : ℕ)^8319*50000000000000^6271 ≤ 21792275833149^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347156889 10000000000 21792275833149 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123955943/5000000000 : ℝ)^8319 ≤ (345160931349/2500000000000 : ℝ)^6271 := by
    have hnat : (1123955943 : ℕ)^8319*2500000000000^6271 ≤ 345160931349^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123955943 5000000000 345160931349 2500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314171571/2500000000 : ℝ)^8319 ≤ (665765797951/1562500000000 : ℝ)^6271 := by
    have hnat : (1314171571 : ℕ)^8319*1562500000000^6271 ≤ 665765797951^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314171571 2500000000 665765797951 1562500000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347156889/10000000000 : ℝ), (-1123955943/5000000000 : ℝ), (1314171571/2500000000 : ℝ)] ![(21792275833149/50000000000000 : ℝ), (345160931349/2500000000000 : ℝ), (665765797951/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347156889/10000000000 : ℝ)|^8319 ≤ (21792275833149/50000000000000 : ℝ)^6271
        have hw : |(5347156889/10000000000 : ℝ)|=(5347156889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1123955943/5000000000 : ℝ)|^8319 ≤ (345160931349/2500000000000 : ℝ)^6271
        have hw : |(-1123955943/5000000000 : ℝ)|=(1123955943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314171571/2500000000 : ℝ)|^8319 ≤ (665765797951/1562500000000 : ℝ)^6271
        have hw : |(1314171571/2500000000 : ℝ)|=(1314171571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s4_2 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347156471/10000000000 : ℝ)*x 0 + (2628343109/5000000000 : ℝ)*x 1 + (-2247912527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347156471/10000000000 : ℝ)^8319 ≤ (43584547146487/100000000000000 : ℝ)^6271 := by
    have hnat : (5347156471 : ℕ)^8319*100000000000000^6271 ≤ 43584547146487^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347156471 10000000000 43584547146487 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628343109/5000000000 : ℝ)^8319 ≤ (5326126294897/12500000000000 : ℝ)^6271 := by
    have hnat : (2628343109 : ℕ)^8319*12500000000000^6271 ≤ 5326126294897^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628343109 5000000000 5326126294897 12500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247912527/10000000000 : ℝ)^8319 ≤ (862902654791/6250000000000 : ℝ)^6271 := by
    have hnat : (2247912527 : ℕ)^8319*6250000000000^6271 ≤ 862902654791^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247912527 10000000000 862902654791 6250000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347156471/10000000000 : ℝ), (2628343109/5000000000 : ℝ), (-2247912527/10000000000 : ℝ)] ![(43584547146487/100000000000000 : ℝ), (5326126294897/12500000000000 : ℝ), (862902654791/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347156471/10000000000 : ℝ)|^8319 ≤ (43584547146487/100000000000000 : ℝ)^6271
        have hw : |(5347156471/10000000000 : ℝ)|=(5347156471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628343109/5000000000 : ℝ)|^8319 ≤ (5326126294897/12500000000000 : ℝ)^6271
        have hw : |(2628343109/5000000000 : ℝ)|=(2628343109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2247912527/10000000000 : ℝ)|^8319 ≤ (862902654791/6250000000000 : ℝ)^6271
        have hw : |(-2247912527/10000000000 : ℝ)|=(2247912527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s4_3 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183219059/5000000000 : ℝ)*x 0 + (4224074377/10000000000 : ℝ)*x 1 + (56419929/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183219059/5000000000 : ℝ)^8319 ≤ (33311878297253/100000000000000 : ℝ)^6271 := by
    have hnat : (2183219059 : ℕ)^8319*100000000000000^6271 ≤ 33311878297253^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183219059 5000000000 33311878297253 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224074377/10000000000 : ℝ)^8319 ≤ (15939399978849/50000000000000 : ℝ)^6271 := by
    have hnat : (4224074377 : ℕ)^8319*50000000000000^6271 ≤ 15939399978849^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224074377 10000000000 15939399978849 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56419929/125000000 : ℝ)^8319 ≤ (34809321727591/100000000000000 : ℝ)^6271 := by
    have hnat : (56419929 : ℕ)^8319*100000000000000^6271 ≤ 34809321727591^6271*125000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56419929 125000000 34809321727591 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183219059/5000000000 : ℝ), (4224074377/10000000000 : ℝ), (56419929/125000000 : ℝ)] ![(33311878297253/100000000000000 : ℝ), (15939399978849/50000000000000 : ℝ), (34809321727591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183219059/5000000000 : ℝ)|^8319 ≤ (33311878297253/100000000000000 : ℝ)^6271
        have hw : |(2183219059/5000000000 : ℝ)|=(2183219059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224074377/10000000000 : ℝ)|^8319 ≤ (15939399978849/50000000000000 : ℝ)^6271
        have hw : |(4224074377/10000000000 : ℝ)|=(4224074377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56419929/125000000 : ℝ)|^8319 ≤ (34809321727591/100000000000000 : ℝ)^6271
        have hw : |(56419929/125000000 : ℝ)|=(56419929/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s4_4 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-217371983/1000000000 : ℝ)*x 0 + (2628552247/5000000000 : ℝ)*x 1 + (540224989/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217371983/1000000000 : ℝ)^8319 ≤ (13205222723457/100000000000000 : ℝ)^6271 := by
    have hnat : (217371983 : ℕ)^8319*100000000000000^6271 ≤ 13205222723457^6271*1000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217371983 1000000000 13205222723457 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628552247/5000000000 : ℝ)^8319 ≤ (42613508078041/100000000000000 : ℝ)^6271 := by
    have hnat : (2628552247 : ℕ)^8319*100000000000000^6271 ≤ 42613508078041^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628552247 5000000000 42613508078041 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540224989/1000000000 : ℝ)^8319 ≤ (8836253836143/20000000000000 : ℝ)^6271 := by
    have hnat : (540224989 : ℕ)^8319*20000000000000^6271 ≤ 8836253836143^6271*1000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540224989 1000000000 8836253836143 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217371983/1000000000 : ℝ), (2628552247/5000000000 : ℝ), (540224989/1000000000 : ℝ)] ![(13205222723457/100000000000000 : ℝ), (42613508078041/100000000000000 : ℝ), (8836253836143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217371983/1000000000 : ℝ)|^8319 ≤ (13205222723457/100000000000000 : ℝ)^6271
        have hw : |(-217371983/1000000000 : ℝ)|=(217371983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628552247/5000000000 : ℝ)|^8319 ≤ (42613508078041/100000000000000 : ℝ)^6271
        have hw : |(2628552247/5000000000 : ℝ)|=(2628552247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540224989/1000000000 : ℝ)|^8319 ≤ (8836253836143/20000000000000 : ℝ)^6271
        have hw : |(540224989/1000000000 : ℝ)|=(540224989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s4_5 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062043387/2000000000 : ℝ)*x 0 + (-2102348799/10000000000 : ℝ)*x 1 + (2701124989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062043387/2000000000 : ℝ)^8319 ≤ (43185573274439/100000000000000 : ℝ)^6271 := by
    have hnat : (1062043387 : ℕ)^8319*100000000000000^6271 ≤ 43185573274439^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062043387 2000000000 43185573274439 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2102348799/10000000000 : ℝ)^8319 ≤ (631657828503/5000000000000 : ℝ)^6271 := by
    have hnat : (2102348799 : ℕ)^8319*5000000000000^6271 ≤ 631657828503^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102348799 10000000000 631657828503 5000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701124989/5000000000 : ℝ)^8319 ≤ (8836254027089/20000000000000 : ℝ)^6271 := by
    have hnat : (2701124989 : ℕ)^8319*20000000000000^6271 ≤ 8836254027089^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701124989 5000000000 8836254027089 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062043387/2000000000 : ℝ), (-2102348799/10000000000 : ℝ), (2701124989/5000000000 : ℝ)] ![(43185573274439/100000000000000 : ℝ), (631657828503/5000000000000 : ℝ), (8836254027089/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062043387/2000000000 : ℝ)|^8319 ≤ (43185573274439/100000000000000 : ℝ)^6271
        have hw : |(1062043387/2000000000 : ℝ)|=(1062043387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2102348799/10000000000 : ℝ)|^8319 ≤ (631657828503/5000000000000 : ℝ)^6271
        have hw : |(-2102348799/10000000000 : ℝ)|=(2102348799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701124989/5000000000 : ℝ)|^8319 ≤ (8836254027089/20000000000000 : ℝ)^6271
        have hw : |(2701124989/5000000000 : ℝ)|=(2701124989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s4_6 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655108497/5000000000 : ℝ)*x 0 + (1080449999/2000000000 : ℝ)*x 1 + (-262793587/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655108497/5000000000 : ℝ)^8319 ≤ (539819673887/1250000000000 : ℝ)^6271 := by
    have hnat : (2655108497 : ℕ)^8319*1250000000000^6271 ≤ 539819673887^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655108497 5000000000 539819673887 1250000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080449999/2000000000 : ℝ)^8319 ≤ (22090635159941/50000000000000 : ℝ)^6271 := by
    have hnat : (1080449999 : ℕ)^8319*50000000000000^6271 ≤ 22090635159941^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080449999 2000000000 22090635159941 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262793587/1250000000 : ℝ)^8319 ≤ (98696529289/781250000000 : ℝ)^6271 := by
    have hnat : (262793587 : ℕ)^8319*781250000000^6271 ≤ 98696529289^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262793587 1250000000 98696529289 781250000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655108497/5000000000 : ℝ), (1080449999/2000000000 : ℝ), (-262793587/1250000000 : ℝ)] ![(539819673887/1250000000000 : ℝ), (22090635159941/50000000000000 : ℝ), (98696529289/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655108497/5000000000 : ℝ)|^8319 ≤ (539819673887/1250000000000 : ℝ)^6271
        have hw : |(2655108497/5000000000 : ℝ)|=(2655108497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080449999/2000000000 : ℝ)|^8319 ≤ (22090635159941/50000000000000 : ℝ)^6271
        have hw : |(1080449999/2000000000 : ℝ)|=(1080449999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-262793587/1250000000 : ℝ)|^8319 ≤ (98696529289/781250000000 : ℝ)^6271
        have hw : |(-262793587/1250000000 : ℝ)|=(262793587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s4_7 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272903321/625000000 : ℝ)*x 0 + (564095543/1250000000 : ℝ)*x 1 + (2112453643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272903321/625000000 : ℝ)^8319 ≤ (6662406057693/20000000000000 : ℝ)^6271 := by
    have hnat : (272903321 : ℕ)^8319*20000000000000^6271 ≤ 6662406057693^6271*625000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272903321 625000000 6662406057693 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564095543/1250000000 : ℝ)^8319 ≤ (8700207676939/25000000000000 : ℝ)^6271 := by
    have hnat : (564095543 : ℕ)^8319*25000000000000^6271 ≤ 8700207676939^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564095543 1250000000 8700207676939 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112453643/5000000000 : ℝ)^8319 ≤ (15943569500883/50000000000000 : ℝ)^6271 := by
    have hnat : (2112453643 : ℕ)^8319*50000000000000^6271 ≤ 15943569500883^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112453643 5000000000 15943569500883 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272903321/625000000 : ℝ), (564095543/1250000000 : ℝ), (2112453643/5000000000 : ℝ)] ![(6662406057693/20000000000000 : ℝ), (8700207676939/25000000000000 : ℝ), (15943569500883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272903321/625000000 : ℝ)|^8319 ≤ (6662406057693/20000000000000 : ℝ)^6271
        have hw : |(272903321/625000000 : ℝ)|=(272903321/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564095543/1250000000 : ℝ)|^8319 ≤ (8700207676939/25000000000000 : ℝ)^6271
        have hw : |(564095543/1250000000 : ℝ)|=(564095543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112453643/5000000000 : ℝ)|^8319 ≤ (15943569500883/50000000000000 : ℝ)^6271
        have hw : |(2112453643/5000000000 : ℝ)|=(2112453643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1126_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (593/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10587/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2229/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (593/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10587/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (593/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10587/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (593/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10587/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (593/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10587/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (593/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10587/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (593/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10587/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10587/100000 : ℝ) ^ (4159/1024 : ℝ) ≤ (1094188962545491/10000000000000000000 : ℝ) := by
    have hpowers : (10587/100000 : ℝ)^4159 ≤ (1094188962545491/10000000000000000000 : ℝ)^1024 := by
      have hnat : (10587 : ℕ)^4159*10000000000000000000^1024 ≤ 1094188962545491^1024*100000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10587 100000 1094188962545491 10000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10587/100000 : ℝ)) (X := (1094188962545491/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (593/4000 : ℝ) ^ (4159/1024 : ℝ) ≤ (42951224779668289/100000000000000000000 : ℝ) := by
    have hpowers : (593/4000 : ℝ)^4159 ≤ (42951224779668289/100000000000000000000 : ℝ)^1024 := by
      have hnat : (593 : ℕ)^4159*100000000000000000000^1024 ≤ 42951224779668289^1024*4000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        593 4000 42951224779668289 100000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (593/4000 : ℝ)) (X := (42951224779668289/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001094188962545491/5000000000000000000 : ℝ) ≤ (1000053876272971/1000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (5001094188962545491/5000000000000000000 : ℝ)^1024 ≤ (1000053876272971/1000000000000000 : ℝ)^4159 := by
      have hnat : (5001094188962545491 : ℕ)^1024*1000000000000000^4159 ≤ 1000053876272971^4159*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001094188962545491 5000000000000000000 1000053876272971 1000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000053876272971/1000000000000000 : ℝ)) (X := (5001094188962545491/5000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053893114405123199/100000000000000000000 : ℝ) ≤ (2000265329854337/2000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (100053893114405123199/100000000000000000000 : ℝ)^1024 ≤ (2000265329854337/2000000000000000 : ℝ)^4159 := by
      have hnat : (100053893114405123199 : ℕ)^1024*2000000000000000^4159 ≤ 2000265329854337^4159*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053893114405123199 100000000000000000000 2000265329854337 2000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000265329854337/2000000000000000 : ℝ)) (X := (100053893114405123199/100000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50042951224779668289/50000000000000000000 : ℝ) ≤ (500105726790683/500000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (50042951224779668289/50000000000000000000 : ℝ)^1024 ≤ (500105726790683/500000000000000 : ℝ)^4159 := by
      have hnat : (50042951224779668289 : ℕ)^1024*500000000000000^4159 ≤ 500105726790683^4159*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50042951224779668289 50000000000000000000 500105726790683 500000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500105726790683/500000000000000 : ℝ)) (X := (50042951224779668289/50000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1094188962545491/10000000000000000000 : ℝ) ≤ ((325889235129297941/326000000000000000 : ℝ)+2*(2424266283/1304000000000 : ℝ)*(10587/100000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (325889235129297941/326000000000000000 : ℝ)+2*(2424266283/1304000000000 : ℝ)*(10587/100000 : ℝ)=(1000053876272971/1000000000000000 : ℝ) by norm_num, show 1+2*(1094188962545491/10000000000000000000 : ℝ)=(5001094188962545491/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42951224779668289/100000000000000000000 : ℝ)+(1094188962545491/10000000000000000000 : ℝ) ≤ ((325889235129297941/326000000000000000 : ℝ)+(2424266283/1304000000000 : ℝ)*((593/4000 : ℝ)+(10587/100000 : ℝ)))^(4159/1024 : ℝ) := by
    rw [show (325889235129297941/326000000000000000 : ℝ)+(2424266283/1304000000000 : ℝ)*((593/4000 : ℝ)+(10587/100000 : ℝ))=(2000265329854337/2000000000000000 : ℝ) by norm_num, show 1+(42951224779668289/100000000000000000000 : ℝ)+(1094188962545491/10000000000000000000 : ℝ)=(100053893114405123199/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42951224779668289/100000000000000000000 : ℝ) ≤ ((325889235129297941/326000000000000000 : ℝ)+2*(2424266283/1304000000000 : ℝ)*(593/4000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (325889235129297941/326000000000000000 : ℝ)+2*(2424266283/1304000000000 : ℝ)*(593/4000 : ℝ)=(500105726790683/500000000000000 : ℝ) by norm_num, show 1+2*(42951224779668289/100000000000000000000 : ℝ)=(50042951224779668289/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (325889235129297941/326000000000000000 : ℝ)*(X 1 0+X 2 0)+(2424266283/1304000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (10587/100000 : ℝ)) (hi := (593/4000 : ℝ)) (c := (325889235129297941/326000000000000000 : ℝ)) (alpha := (2424266283/1304000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (325889235129297941/326000000000000000 : ℝ)*(X 0 1+X 2 1)+(2424266283/1304000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (10587/100000 : ℝ)) (hi := (593/4000 : ℝ)) (c := (325889235129297941/326000000000000000 : ℝ)) (alpha := (2424266283/1304000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (325889235129297941/326000000000000000 : ℝ)*(X 0 2+X 1 2)+(2424266283/1304000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (10587/100000 : ℝ)) (hi := (593/4000 : ℝ)) (c := (325889235129297941/326000000000000000 : ℝ)) (alpha := (2424266283/1304000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2173712751/10000000000 : ℝ)*X 0 0+(5402669707/10000000000 : ℝ)*X 0 1+(5256686221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347156889/10000000000 : ℝ)*X 1 0+(-1123955943/5000000000 : ℝ)*X 1 1+(1314171571/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347156471/10000000000 : ℝ)*X 2 0+(2628343109/5000000000 : ℝ)*X 2 1+(-2247912527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183219059/5000000000 : ℝ)*X 0 0+(4224074377/10000000000 : ℝ)*X 0 1+(56419929/125000000 : ℝ)*X 0 2+(2183219059/5000000000 : ℝ)*X 1 0+(4224074377/10000000000 : ℝ)*X 1 1+(56419929/125000000 : ℝ)*X 1 2+(2183219059/5000000000 : ℝ)*X 2 0+(4224074377/10000000000 : ℝ)*X 2 1+(56419929/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-217371983/1000000000 : ℝ)*X 0 0+(2628552247/5000000000 : ℝ)*X 0 1+(540224989/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062043387/2000000000 : ℝ)*X 1 0+(-2102348799/10000000000 : ℝ)*X 1 1+(2701124989/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655108497/5000000000 : ℝ)*X 2 0+(1080449999/2000000000 : ℝ)*X 2 1+(-262793587/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272903321/625000000 : ℝ)*X 0 0+(564095543/1250000000 : ℝ)*X 0 1+(2112453643/5000000000 : ℝ)*X 0 2+(272903321/625000000 : ℝ)*X 1 0+(564095543/1250000000 : ℝ)*X 1 1+(2112453643/5000000000 : ℝ)*X 1 2+(272903321/625000000 : ℝ)*X 2 0+(564095543/1250000000 : ℝ)*X 2 1+(2112453643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2759010617345209269164547/4075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1126596771/100000000000000 : ℝ)*(base19) + (212723641/20000000000000 : ℝ)*(base23) + (15026503/5000000000000 : ℝ)*(upper2) + (114836639/50000000000000 : ℝ)*(upper3) + (2576049858809189/50000000000000 : ℝ)*(major0) + (2576049858809189/50000000000000 : ℝ)*(major1) + (2576049858809189/50000000000000 : ℝ)*(major2) + (6850137150824023/100000000000000 : ℝ)*(sp0) + (1370031984374997/20000000000000 : ℝ)*(sp1) + (3425073513044501/50000000000000 : ℝ)*(sp2) + (3454016470599477/100000000000000 : ℝ)*(sp3) + (11948823867/50000000000000 : ℝ)*(sp4) + (12958764549/100000000000000 : ℝ)*(sp6) + (21893596919/100000000000000 : ℝ)*(sp7) + (863509591049099/25000000000000 : ℝ)*(f.failure) + (1712540262117939/25000000000000 : ℝ)*(f.sum) + (25198109337/5093750000000000000000000 : ℝ)*base65 + (317419728127270151/16300000000000000000000000000000 : ℝ)*base68 + (274559106245770151/16300000000000000000000000000000 : ℝ)*base70 + (60020382669170151/16300000000000000000000000000000 : ℝ)*base72 + (29441917587/16300000000000000000000000 : ℝ)*base73 + (151527837416870151/16300000000000000000000000000000 : ℝ)*base76 + (294271855192070151/16300000000000000000000000000000 : ℝ)*base78 + (78573876378529849/16300000000000000000000000000000 : ℝ)*base79 + (452638212927/163000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2572097/312500000000000000000 : ℝ)*base89 + (2572097/312500000000000000000 : ℝ)*base91 + (2572097/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (109692268285317096955314897/16300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (124787629/10000000000000 : ℝ)*(base19) + (154135377/10000000000000 : ℝ)*(base23) + (233418773/100000000000000 : ℝ)*(upper3) + (16308531/20000000000000 : ℝ)*(lower4) + (29977111/12500000000000 : ℝ)*(upper5) + (5181794588094639/100000000000000 : ℝ)*(major0) + (5181794588094639/100000000000000 : ℝ)*(major1) + (5181794588094639/100000000000000 : ℝ)*(major2) + (1377240419/5000000000000 : ℝ)*(sp1) + (36655030361/100000000000000 : ℝ)*(sp2) + (215301335591829/3125000000000 : ℝ)*(sp4) + (6889613946253859/100000000000000 : ℝ)*(sp5) + (6889604542554397/100000000000000 : ℝ)*(sp6) + (434243276616397/12500000000000 : ℝ)*(sp7) + (434243276616397/12500000000000 : ℝ)*(f.failure) + (215301335591829/3125000000000 : ℝ)*(f.sum) + (3824775289/326000000000000000000000000 : ℝ)*base65 + (94550366087488299/32600000000000000000000000000000 : ℝ)*base67 + (70185879799488299/32600000000000000000000000000000 : ℝ)*base69 + (499596583279511701/32600000000000000000000000000000 : ℝ)*base72 + (333213854313/326000000000000000000000000 : ℝ)*base74 + (513832137325711701/32600000000000000000000000000000 : ℝ)*base76 + (91073160525911701/32600000000000000000000000000000 : ℝ)*base78 + (9189284833111701/32600000000000000000000000000000 : ℝ)*base80 + (2625998343117/326000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1756091/156250000000000000000 : ℝ)*base89 + (1756091/156250000000000000000 : ℝ)*base91 + (1756091/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1126_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (593/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10587/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2229/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1126_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1126_s5_0 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2174384769/10000000000 : ℝ)*x 0 + (1079067133/2000000000 : ℝ)*x 1 + (526357937/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174384769/10000000000 : ℝ)^8319 ≤ (132105816769/1000000000000 : ℝ)^6271 := by
    have hnat : (2174384769 : ℕ)^8319*1000000000000^6271 ≤ 132105816769^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174384769 10000000000 132105816769 1000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079067133/2000000000 : ℝ)^8319 ≤ (8821254206177/20000000000000 : ℝ)^6271 := by
    have hnat : (1079067133 : ℕ)^8319*20000000000000^6271 ≤ 8821254206177^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079067133 2000000000 8821254206177 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526357937/1000000000 : ℝ)^8319 ≤ (42683147277311/100000000000000 : ℝ)^6271 := by
    have hnat : (526357937 : ℕ)^8319*100000000000000^6271 ≤ 42683147277311^6271*1000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526357937 1000000000 42683147277311 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2174384769/10000000000 : ℝ), (1079067133/2000000000 : ℝ), (526357937/1000000000 : ℝ)] ![(132105816769/1000000000000 : ℝ), (8821254206177/20000000000000 : ℝ), (42683147277311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2174384769/10000000000 : ℝ)|^8319 ≤ (132105816769/1000000000000 : ℝ)^6271
        have hw : |(-2174384769/10000000000 : ℝ)|=(2174384769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079067133/2000000000 : ℝ)|^8319 ≤ (8821254206177/20000000000000 : ℝ)^6271
        have hw : |(1079067133/2000000000 : ℝ)|=(1079067133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526357937/1000000000 : ℝ)|^8319 ≤ (42683147277311/100000000000000 : ℝ)^6271
        have hw : |(526357937/1000000000 : ℝ)|=(526357937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s5_1 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345320317/10000000000 : ℝ)*x 0 + (-1120623511/5000000000 : ℝ)*x 1 + (5263579243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345320317/10000000000 : ℝ)^8319 ≤ (5445586753599/12500000000000 : ℝ)^6271 := by
    have hnat : (5345320317 : ℕ)^8319*12500000000000^6271 ≤ 5445586753599^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345320317 10000000000 5445586753599 12500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120623511/5000000000 : ℝ)^8319 ≤ (3438040011393/25000000000000 : ℝ)^6271 := by
    have hnat : (1120623511 : ℕ)^8319*25000000000000^6271 ≤ 3438040011393^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120623511 5000000000 3438040011393 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263579243/10000000000 : ℝ)^8319 ≤ (21341572955557/50000000000000 : ℝ)^6271 := by
    have hnat : (5263579243 : ℕ)^8319*50000000000000^6271 ≤ 21341572955557^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263579243 10000000000 21341572955557 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345320317/10000000000 : ℝ), (-1120623511/5000000000 : ℝ), (5263579243/10000000000 : ℝ)] ![(5445586753599/12500000000000 : ℝ), (3438040011393/25000000000000 : ℝ), (21341572955557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345320317/10000000000 : ℝ)|^8319 ≤ (5445586753599/12500000000000 : ℝ)^6271
        have hw : |(5345320317/10000000000 : ℝ)|=(5345320317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1120623511/5000000000 : ℝ)|^8319 ≤ (3438040011393/25000000000000 : ℝ)^6271
        have hw : |(-1120623511/5000000000 : ℝ)|=(1120623511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263579243/10000000000 : ℝ)|^8319 ≤ (21341572955557/50000000000000 : ℝ)^6271
        have hw : |(5263579243/10000000000 : ℝ)|=(5263579243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s5_2 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345320031/10000000000 : ℝ)*x 0 + (210543179/400000000 : ℝ)*x 1 + (-448249419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345320031/10000000000 : ℝ)^8319 ≤ (43564690936637/100000000000000 : ℝ)^6271 := by
    have hnat : (5345320031 : ℕ)^8319*100000000000000^6271 ≤ 43564690936637^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345320031 10000000000 43564690936637 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210543179/400000000 : ℝ)^8319 ≤ (10670787101711/25000000000000 : ℝ)^6271 := by
    have hnat : (210543179 : ℕ)^8319*25000000000000^6271 ≤ 10670787101711^6271*400000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210543179 400000000 10670787101711 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448249419/2000000000 : ℝ)^8319 ≤ (687608031989/5000000000000 : ℝ)^6271 := by
    have hnat : (448249419 : ℕ)^8319*5000000000000^6271 ≤ 687608031989^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448249419 2000000000 687608031989 5000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345320031/10000000000 : ℝ), (210543179/400000000 : ℝ), (-448249419/2000000000 : ℝ)] ![(43564690936637/100000000000000 : ℝ), (10670787101711/25000000000000 : ℝ), (687608031989/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345320031/10000000000 : ℝ)|^8319 ≤ (43564690936637/100000000000000 : ℝ)^6271
        have hw : |(5345320031/10000000000 : ℝ)|=(5345320031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210543179/400000000 : ℝ)|^8319 ≤ (10670787101711/25000000000000 : ℝ)^6271
        have hw : |(210543179/400000000 : ℝ)|=(210543179/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-448249419/2000000000 : ℝ)|^8319 ≤ (687608031989/5000000000000 : ℝ)^6271
        have hw : |(-448249419/2000000000 : ℝ)|=(448249419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s5_3 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873366183/2000000000 : ℝ)*x 0 + (4238131569/10000000000 : ℝ)*x 1 + (4499434899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873366183/2000000000 : ℝ)^8319 ≤ (16657926847909/50000000000000 : ℝ)^6271 := by
    have hnat : (873366183 : ℕ)^8319*50000000000000^6271 ≤ 16657926847909^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873366183 2000000000 16657926847909 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4238131569/10000000000 : ℝ)^8319 ≤ (32019611763947/100000000000000 : ℝ)^6271 := by
    have hnat : (4238131569 : ℕ)^8319*100000000000000^6271 ≤ 32019611763947^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238131569 10000000000 32019611763947 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499434899/10000000000 : ℝ)^8319 ≤ (34664534526237/100000000000000 : ℝ)^6271 := by
    have hnat : (4499434899 : ℕ)^8319*100000000000000^6271 ≤ 34664534526237^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499434899 10000000000 34664534526237 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873366183/2000000000 : ℝ), (4238131569/10000000000 : ℝ), (4499434899/10000000000 : ℝ)] ![(16657926847909/50000000000000 : ℝ), (32019611763947/100000000000000 : ℝ), (34664534526237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873366183/2000000000 : ℝ)|^8319 ≤ (16657926847909/50000000000000 : ℝ)^6271
        have hw : |(873366183/2000000000 : ℝ)|=(873366183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4238131569/10000000000 : ℝ)|^8319 ≤ (32019611763947/100000000000000 : ℝ)^6271
        have hw : |(4238131569/10000000000 : ℝ)|=(4238131569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499434899/10000000000 : ℝ)|^8319 ≤ (34664534526237/100000000000000 : ℝ)^6271
        have hw : |(4499434899/10000000000 : ℝ)|=(4499434899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s5_4 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2174389953/10000000000 : ℝ)*x 0 + (5263920327/10000000000 : ℝ)*x 1 + (539499359/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174389953/10000000000 : ℝ)^8319 ≤ (206415991539/1562500000000 : ℝ)^6271 := by
    have hnat : (2174389953 : ℕ)^8319*1562500000000^6271 ≤ 206415991539^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174389953 10000000000 206415991539 1562500000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263920327/10000000000 : ℝ)^8319 ≤ (21343407573033/50000000000000 : ℝ)^6271 := by
    have hnat : (5263920327 : ℕ)^8319*50000000000000^6271 ≤ 21343407573033^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263920327 10000000000 21343407573033 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539499359/1000000000 : ℝ)^8319 ≤ (22051280690019/50000000000000 : ℝ)^6271 := by
    have hnat : (539499359 : ℕ)^8319*50000000000000^6271 ≤ 22051280690019^6271*1000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539499359 1000000000 22051280690019 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2174389953/10000000000 : ℝ), (5263920327/10000000000 : ℝ), (539499359/1000000000 : ℝ)] ![(206415991539/1562500000000 : ℝ), (21343407573033/50000000000000 : ℝ), (22051280690019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2174389953/10000000000 : ℝ)|^8319 ≤ (206415991539/1562500000000 : ℝ)^6271
        have hw : |(-2174389953/10000000000 : ℝ)|=(2174389953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263920327/10000000000 : ℝ)|^8319 ≤ (21343407573033/50000000000000 : ℝ)^6271
        have hw : |(5263920327/10000000000 : ℝ)|=(5263920327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539499359/1000000000 : ℝ)|^8319 ≤ (22051280690019/50000000000000 : ℝ)^6271
        have hw : |(539499359/1000000000 : ℝ)|=(539499359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s5_5 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655989677/5000000000 : ℝ)*x 0 + (-2109832833/10000000000 : ℝ)*x 1 + (5394993597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655989677/5000000000 : ℝ)^8319 ≤ (8640917629667/20000000000000 : ℝ)^6271 := by
    have hnat : (2655989677 : ℕ)^8319*20000000000000^6271 ≤ 8640917629667^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655989677 5000000000 8640917629667 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109832833/10000000000 : ℝ)^8319 ≤ (6346425194227/50000000000000 : ℝ)^6271 := by
    have hnat : (2109832833 : ℕ)^8319*50000000000000^6271 ≤ 6346425194227^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109832833 10000000000 6346425194227 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394993597/10000000000 : ℝ)^8319 ≤ (44102561455949/100000000000000 : ℝ)^6271 := by
    have hnat : (5394993597 : ℕ)^8319*100000000000000^6271 ≤ 44102561455949^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394993597 10000000000 44102561455949 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655989677/5000000000 : ℝ), (-2109832833/10000000000 : ℝ), (5394993597/10000000000 : ℝ)] ![(8640917629667/20000000000000 : ℝ), (6346425194227/50000000000000 : ℝ), (44102561455949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655989677/5000000000 : ℝ)|^8319 ≤ (8640917629667/20000000000000 : ℝ)^6271
        have hw : |(2655989677/5000000000 : ℝ)|=(2655989677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109832833/10000000000 : ℝ)|^8319 ≤ (6346425194227/50000000000000 : ℝ)^6271
        have hw : |(-2109832833/10000000000 : ℝ)|=(2109832833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394993597/10000000000 : ℝ)|^8319 ≤ (44102561455949/100000000000000 : ℝ)^6271
        have hw : |(5394993597/10000000000 : ℝ)|=(5394993597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s5_6 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311979349/10000000000 : ℝ)*x 0 + (539499359/1000000000 : ℝ)*x 1 + (-2109832847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311979349/10000000000 : ℝ)^8319 ≤ (43204588094387/100000000000000 : ℝ)^6271 := by
    have hnat : (5311979349 : ℕ)^8319*100000000000000^6271 ≤ 43204588094387^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311979349 10000000000 43204588094387 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539499359/1000000000 : ℝ)^8319 ≤ (22051280690019/50000000000000 : ℝ)^6271 := by
    have hnat : (539499359 : ℕ)^8319*50000000000000^6271 ≤ 22051280690019^6271*1000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539499359 1000000000 22051280690019 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109832847/10000000000 : ℝ)^8319 ≤ (2538570100037/20000000000000 : ℝ)^6271 := by
    have hnat : (2109832847 : ℕ)^8319*20000000000000^6271 ≤ 2538570100037^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109832847 10000000000 2538570100037 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311979349/10000000000 : ℝ), (539499359/1000000000 : ℝ), (-2109832847/10000000000 : ℝ)] ![(43204588094387/100000000000000 : ℝ), (22051280690019/50000000000000 : ℝ), (2538570100037/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311979349/10000000000 : ℝ)|^8319 ≤ (43204588094387/100000000000000 : ℝ)^6271
        have hw : |(5311979349/10000000000 : ℝ)|=(5311979349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539499359/1000000000 : ℝ)|^8319 ≤ (22051280690019/50000000000000 : ℝ)^6271
        have hw : |(539499359/1000000000 : ℝ)|=(539499359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2109832847/10000000000 : ℝ)|^8319 ≤ (2538570100037/20000000000000 : ℝ)^6271
        have hw : |(-2109832847/10000000000 : ℝ)|=(2109832847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s5_7 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366841759/10000000000 : ℝ)*x 0 + (4498758779/10000000000 : ℝ)*x 1 + (847762009/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366841759/10000000000 : ℝ)^8319 ≤ (33315963446841/100000000000000 : ℝ)^6271 := by
    have hnat : (4366841759 : ℕ)^8319*100000000000000^6271 ≤ 33315963446841^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366841759 10000000000 33315963446841 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498758779/10000000000 : ℝ)^8319 ≤ (17328812288557/50000000000000 : ℝ)^6271 := by
    have hnat : (4498758779 : ℕ)^8319*50000000000000^6271 ≤ 17328812288557^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498758779 10000000000 17328812288557 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847762009/2000000000 : ℝ)^8319 ≤ (16013205982809/50000000000000 : ℝ)^6271 := by
    have hnat : (847762009 : ℕ)^8319*50000000000000^6271 ≤ 16013205982809^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847762009 2000000000 16013205982809 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366841759/10000000000 : ℝ), (4498758779/10000000000 : ℝ), (847762009/2000000000 : ℝ)] ![(33315963446841/100000000000000 : ℝ), (17328812288557/50000000000000 : ℝ), (16013205982809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366841759/10000000000 : ℝ)|^8319 ≤ (33315963446841/100000000000000 : ℝ)^6271
        have hw : |(4366841759/10000000000 : ℝ)|=(4366841759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498758779/10000000000 : ℝ)|^8319 ≤ (17328812288557/50000000000000 : ℝ)^6271
        have hw : |(4498758779/10000000000 : ℝ)|=(4498758779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847762009/2000000000 : ℝ)|^8319 ≤ (16013205982809/50000000000000 : ℝ)^6271
        have hw : |(847762009/2000000000 : ℝ)|=(847762009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1126_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2229/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2823/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7041/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2229/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2229/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2229/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2229/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2229/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2229/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2229/20000 : ℝ) ^ (4159/1024 : ℝ) ≤ (6740054154984171/50000000000000000000 : ℝ) := by
    have hpowers : (2229/20000 : ℝ)^4159 ≤ (6740054154984171/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2229 : ℕ)^4159*50000000000000000000^1024 ≤ 6740054154984171^1024*20000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2229 20000 6740054154984171 50000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2229/20000 : ℝ)) (X := (6740054154984171/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (4159/1024 : ℝ) ≤ (36430525476936369/100000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^4159 ≤ (36430525476936369/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3559 : ℕ)^4159*100000000000000000000^1024 ≤ 36430525476936369^1024*25000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 36430525476936369 100000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (36430525476936369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006740054154984171/25000000000000000000 : ℝ) ≤ (10000663728229169/10000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (25006740054154984171/25000000000000000000 : ℝ)^1024 ≤ (10000663728229169/10000000000000000 : ℝ)^4159 := by
      have hnat : (25006740054154984171 : ℕ)^1024*10000000000000000^4159 ≤ 10000663728229169^4159*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006740054154984171 25000000000000000000 10000663728229169 10000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000663728229169/10000000000000000 : ℝ)) (X := (25006740054154984171/25000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049910633786904711/100000000000000000000 : ℝ) ≤ (5000614316876507/5000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (100049910633786904711/100000000000000000000 : ℝ)^1024 ≤ (5000614316876507/5000000000000000 : ℝ)^4159 := by
      have hnat : (100049910633786904711 : ℕ)^1024*5000000000000000^4159 ≤ 5000614316876507^4159*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049910633786904711 100000000000000000000 5000614316876507 5000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000614316876507/5000000000000000 : ℝ)) (X := (100049910633786904711/100000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036430525476936369/50000000000000000000 : ℝ) ≤ (10001793539276859/10000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (50036430525476936369/50000000000000000000 : ℝ)^1024 ≤ (10001793539276859/10000000000000000 : ℝ)^4159 := by
      have hnat : (50036430525476936369 : ℕ)^1024*10000000000000000^4159 ≤ 10001793539276859^4159*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036430525476936369 50000000000000000000 10001793539276859 10000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001793539276859/10000000000000000 : ℝ)) (X := (50036430525476936369/50000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6740054154984171/50000000000000000000 : ℝ) ≤ ((30899459839829856329/30910000000000000000 : ℝ)+2*(112981104769/61820000000000 : ℝ)*(2229/20000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (30899459839829856329/30910000000000000000 : ℝ)+2*(112981104769/61820000000000 : ℝ)*(2229/20000 : ℝ)=(10000663728229169/10000000000000000 : ℝ) by norm_num, show 1+2*(6740054154984171/50000000000000000000 : ℝ)=(25006740054154984171/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36430525476936369/100000000000000000000 : ℝ)+(6740054154984171/50000000000000000000 : ℝ) ≤ ((30899459839829856329/30910000000000000000 : ℝ)+(112981104769/61820000000000 : ℝ)*((3559/25000 : ℝ)+(2229/20000 : ℝ)))^(4159/1024 : ℝ) := by
    rw [show (30899459839829856329/30910000000000000000 : ℝ)+(112981104769/61820000000000 : ℝ)*((3559/25000 : ℝ)+(2229/20000 : ℝ))=(5000614316876507/5000000000000000 : ℝ) by norm_num, show 1+(36430525476936369/100000000000000000000 : ℝ)+(6740054154984171/50000000000000000000 : ℝ)=(100049910633786904711/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36430525476936369/100000000000000000000 : ℝ) ≤ ((30899459839829856329/30910000000000000000 : ℝ)+2*(112981104769/61820000000000 : ℝ)*(3559/25000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (30899459839829856329/30910000000000000000 : ℝ)+2*(112981104769/61820000000000 : ℝ)*(3559/25000 : ℝ)=(10001793539276859/10000000000000000 : ℝ) by norm_num, show 1+2*(36430525476936369/100000000000000000000 : ℝ)=(50036430525476936369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30899459839829856329/30910000000000000000 : ℝ)*(X 1 0+X 2 0)+(112981104769/61820000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (2229/20000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (30899459839829856329/30910000000000000000 : ℝ)) (alpha := (112981104769/61820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30899459839829856329/30910000000000000000 : ℝ)*(X 0 1+X 2 1)+(112981104769/61820000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (2229/20000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (30899459839829856329/30910000000000000000 : ℝ)) (alpha := (112981104769/61820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30899459839829856329/30910000000000000000 : ℝ)*(X 0 2+X 1 2)+(112981104769/61820000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (2229/20000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (30899459839829856329/30910000000000000000 : ℝ)) (alpha := (112981104769/61820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2174384769/10000000000 : ℝ)*X 0 0+(1079067133/2000000000 : ℝ)*X 0 1+(526357937/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345320317/10000000000 : ℝ)*X 1 0+(-1120623511/5000000000 : ℝ)*X 1 1+(5263579243/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345320031/10000000000 : ℝ)*X 2 0+(210543179/400000000 : ℝ)*X 2 1+(-448249419/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873366183/2000000000 : ℝ)*X 0 0+(4238131569/10000000000 : ℝ)*X 0 1+(4499434899/10000000000 : ℝ)*X 0 2+(873366183/2000000000 : ℝ)*X 1 0+(4238131569/10000000000 : ℝ)*X 1 1+(4499434899/10000000000 : ℝ)*X 1 2+(873366183/2000000000 : ℝ)*X 2 0+(4238131569/10000000000 : ℝ)*X 2 1+(4499434899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2174389953/10000000000 : ℝ)*X 0 0+(5263920327/10000000000 : ℝ)*X 0 1+(539499359/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655989677/5000000000 : ℝ)*X 1 0+(-2109832833/10000000000 : ℝ)*X 1 1+(5394993597/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311979349/10000000000 : ℝ)*X 2 0+(539499359/1000000000 : ℝ)*X 2 1+(-2109832847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4366841759/10000000000 : ℝ)*X 0 0+(4498758779/10000000000 : ℝ)*X 0 1+(847762009/2000000000 : ℝ)*X 0 2+(4366841759/10000000000 : ℝ)*X 1 0+(4498758779/10000000000 : ℝ)*X 1 1+(847762009/2000000000 : ℝ)*X 1 2+(4366841759/10000000000 : ℝ)*X 2 0+(4498758779/10000000000 : ℝ)*X 2 1+(847762009/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (188438374859271292041/140500000000000000000000000 : ℝ) := by norm_num
    linear_combination (167343867/20000000000000 : ℝ)*(base19) + (18497233/4000000000000 : ℝ)*(base23) + (367597/312500000000 : ℝ)*(upper2) + (166629621/100000000000000 : ℝ)*(upper3) + (100631887/100000000000000 : ℝ)*(upper4) + (5708394532715919/100000000000000 : ℝ)*(major0) + (5708394532715919/100000000000000 : ℝ)*(major1) + (5708394532715919/100000000000000 : ℝ)*(major2) + (3794896417427431/50000000000000 : ℝ)*(sp0) + (7589802140520649/100000000000000 : ℝ)*(sp1) + (7589802514809159/100000000000000 : ℝ)*(sp2) + (3826977467224063/100000000000000 : ℝ)*(sp3) + (5071192561/50000000000000 : ℝ)*(sp4) + (8576261169/100000000000000 : ℝ)*(sp7) + (239186627717827/6250000000000 : ℝ)*(f.failure) + (474362686077499/6250000000000 : ℝ)*(f.sum) + (1364785353231/281000000000000000000000000 : ℝ)*base66 + (2587378236835881941/281000000000000000000000000000000 : ℝ)*base67 + (2049865549095881941/281000000000000000000000000000000 : ℝ)*base69 + (2537854954751118059/281000000000000000000000000000000 : ℝ)*base72 + (157539791119/281000000000000000000000000 : ℝ)*base74 + (260101635051118059/281000000000000000000000000000000 : ℝ)*base76 + (922031112172881941/281000000000000000000000000000000 : ℝ)*base77 + (3833186098845118059/281000000000000000000000000000000 : ℝ)*base80 + (87364744551/70250000000000000000000000 : ℝ)*base81 + (584869/78125000000000000000 : ℝ)*base90 + (584869/78125000000000000000 : ℝ)*base92 + (584869/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12448613817392378100117/3091000000000000000000000000 : ℝ) := by norm_num
    linear_combination (409345627/50000000000000 : ℝ)*(base19) + (840665753/100000000000000 : ℝ)*(base23) + (42849717/50000000000000 : ℝ)*(upper3) + (414169/2500000000000 : ℝ)*(lower4) + (3679419/4000000000000 : ℝ)*(upper5) + (358632281193997/6250000000000 : ℝ)*(major0) + (358632281193997/6250000000000 : ℝ)*(major1) + (358632281193997/6250000000000 : ℝ)*(major2) + (705423647/3125000000000 : ℝ)*(sp1) + (22250031243/100000000000000 : ℝ)*(sp2) + (7629320806270927/100000000000000 : ℝ)*(sp4) + (7629297414022969/100000000000000 : ℝ)*(sp5) + (7629297715573931/100000000000000 : ℝ)*(sp6) + (96172801442279/2500000000000 : ℝ)*(sp7) + (96172801442279/2500000000000 : ℝ)*(f.failure) + (7629320806270927/100000000000000 : ℝ)*(f.sum) + (19999571705269/3091000000000000000000000000 : ℝ)*base65 + (207916437247569513/193187500000000000000000000000000 : ℝ)*base67 + (818166776430617987/193187500000000000000000000000000 : ℝ)*base70 + (1196464435140382013/193187500000000000000000000000000 : ℝ)*base71 + (2776943277363/3091000000000000000000000000 : ℝ)*base73 + (944794736979680487/193187500000000000000000000000000 : ℝ)*base76 + (1215663534826992987/193187500000000000000000000000000 : ℝ)*base78 + (2530956214914694513/193187500000000000000000000000000 : ℝ)*base79 + (118505286869/309100000000000000000000000 : ℝ)*base82 + (262363/31250000000000000000 : ℝ)*base90 + (262363/31250000000000000000 : ℝ)*base92 + (262363/31250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1126_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2229/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1126_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1126_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16551/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1126_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1126_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1126_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16551/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1126_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

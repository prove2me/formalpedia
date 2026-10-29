-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1379_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:22:49.800187+00:00
-- url     : https://prove2.me/submissions/e1c1eaa6-284d-47b1-8ce6-fdeeb11af60f

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
theorem support_rectangle_w1379_s3_0 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-402202977/2000000000 : ℝ)*x 0 + (1355668797/2500000000 : ℝ)*x 1 + (523473057/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402202977/2000000000 : ℝ)^4339 ≤ (765809976069/6250000000000 : ℝ)^3315 := by
    have hnat : (402202977 : ℕ)^4339*6250000000000^3315 ≤ 765809976069^3315*2000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402202977 2000000000 765809976069 6250000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355668797/2500000000 : ℝ)^4339 ≤ (11221539930151/25000000000000 : ℝ)^3315 := by
    have hnat : (1355668797 : ℕ)^4339*25000000000000^3315 ≤ 11221539930151^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355668797 2500000000 11221539930151 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523473057/1000000000 : ℝ)^4339 ≤ (42860880640381/100000000000000 : ℝ)^3315 := by
    have hnat : (523473057 : ℕ)^4339*100000000000000^3315 ≤ 42860880640381^3315*1000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523473057 1000000000 42860880640381 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-402202977/2000000000 : ℝ), (1355668797/2500000000 : ℝ), (523473057/1000000000 : ℝ)] ![(765809976069/6250000000000 : ℝ), (11221539930151/25000000000000 : ℝ), (42860880640381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-402202977/2000000000 : ℝ)|^4339 ≤ (765809976069/6250000000000 : ℝ)^3315
        have hw : |(-402202977/2000000000 : ℝ)|=(402202977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355668797/2500000000 : ℝ)|^4339 ≤ (11221539930151/25000000000000 : ℝ)^3315
        have hw : |(1355668797/2500000000 : ℝ)|=(1355668797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523473057/1000000000 : ℝ)|^4339 ≤ (42860880640381/100000000000000 : ℝ)^3315
        have hw : |(523473057/1000000000 : ℝ)|=(523473057/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s3_1 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675686731/5000000000 : ℝ)*x 0 + (-2106983563/10000000000 : ℝ)*x 1 + (1308682771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675686731/5000000000 : ℝ)^4339 ≤ (4411522171903/10000000000000 : ℝ)^3315 := by
    have hnat : (2675686731 : ℕ)^4339*10000000000000^3315 ≤ 4411522171903^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675686731 5000000000 4411522171903 10000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106983563/10000000000 : ℝ)^4339 ≤ (3255973029893/25000000000000 : ℝ)^3315 := by
    have hnat : (2106983563 : ℕ)^4339*25000000000000^3315 ≤ 3255973029893^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106983563 10000000000 3255973029893 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308682771/2500000000 : ℝ)^4339 ≤ (8572177229783/20000000000000 : ℝ)^3315 := by
    have hnat : (1308682771 : ℕ)^4339*20000000000000^3315 ≤ 8572177229783^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308682771 2500000000 8572177229783 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675686731/5000000000 : ℝ), (-2106983563/10000000000 : ℝ), (1308682771/2500000000 : ℝ)] ![(4411522171903/10000000000000 : ℝ), (3255973029893/25000000000000 : ℝ), (8572177229783/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675686731/5000000000 : ℝ)|^4339 ≤ (4411522171903/10000000000000 : ℝ)^3315
        have hw : |(2675686731/5000000000 : ℝ)|=(2675686731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2106983563/10000000000 : ℝ)|^4339 ≤ (3255973029893/25000000000000 : ℝ)^3315
        have hw : |(-2106983563/10000000000 : ℝ)|=(2106983563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1308682771/2500000000 : ℝ)|^4339 ≤ (8572177229783/20000000000000 : ℝ)^3315
        have hw : |(1308682771/2500000000 : ℝ)|=(1308682771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s3_2 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337843353/2500000000 : ℝ)*x 0 + (261736563/500000000 : ℝ)*x 1 + (-2106983397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337843353/2500000000 : ℝ)^4339 ≤ (44115221179521/100000000000000 : ℝ)^3315 := by
    have hnat : (1337843353 : ℕ)^4339*100000000000000^3315 ≤ 44115221179521^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337843353 2500000000 44115221179521 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261736563/500000000 : ℝ)^4339 ≤ (8572177607021/20000000000000 : ℝ)^3315 := by
    have hnat : (261736563 : ℕ)^4339*20000000000000^3315 ≤ 8572177607021^3315*500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261736563 500000000 8572177607021 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106983397/10000000000 : ℝ)^4339 ≤ (13023890776517/100000000000000 : ℝ)^3315 := by
    have hnat : (2106983397 : ℕ)^4339*100000000000000^3315 ≤ 13023890776517^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106983397 10000000000 13023890776517 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337843353/2500000000 : ℝ), (261736563/500000000 : ℝ), (-2106983397/10000000000 : ℝ)] ![(44115221179521/100000000000000 : ℝ), (8572177607021/20000000000000 : ℝ), (13023890776517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337843353/2500000000 : ℝ)|^4339 ≤ (44115221179521/100000000000000 : ℝ)^3315
        have hw : |(1337843353/2500000000 : ℝ)|=(1337843353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261736563/500000000 : ℝ)|^4339 ≤ (8572177607021/20000000000000 : ℝ)^3315
        have hw : |(261736563/500000000 : ℝ)|=(261736563/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2106983397/10000000000 : ℝ)|^4339 ≤ (13023890776517/100000000000000 : ℝ)^3315
        have hw : |(-2106983397/10000000000 : ℝ)|=(2106983397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s3_3 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107904397/250000000 : ℝ)*x 0 + (4120841783/10000000000 : ℝ)*x 1 + (4519989407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107904397/250000000 : ℝ)^4339 ≤ (33295201000699/100000000000000 : ℝ)^3315 := by
    have hnat : (107904397 : ℕ)^4339*100000000000000^3315 ≤ 33295201000699^3315*250000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107904397 250000000 33295201000699 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4120841783/10000000000 : ℝ)^4339 ≤ (3917107739231/12500000000000 : ℝ)^3315 := by
    have hnat : (4120841783 : ℕ)^4339*12500000000000^3315 ≤ 3917107739231^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4120841783 10000000000 3917107739231 12500000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4519989407/10000000000 : ℝ)^4339 ≤ (17683968537653/50000000000000 : ℝ)^3315 := by
    have hnat : (4519989407 : ℕ)^4339*50000000000000^3315 ≤ 17683968537653^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519989407 10000000000 17683968537653 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107904397/250000000 : ℝ), (4120841783/10000000000 : ℝ), (4519989407/10000000000 : ℝ)] ![(33295201000699/100000000000000 : ℝ), (3917107739231/12500000000000 : ℝ), (17683968537653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107904397/250000000 : ℝ)|^4339 ≤ (33295201000699/100000000000000 : ℝ)^3315
        have hw : |(107904397/250000000 : ℝ)|=(107904397/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4120841783/10000000000 : ℝ)|^4339 ≤ (3917107739231/12500000000000 : ℝ)^3315
        have hw : |(4120841783/10000000000 : ℝ)|=(4120841783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4519989407/10000000000 : ℝ)|^4339 ≤ (17683968537653/50000000000000 : ℝ)^3315
        have hw : |(4519989407/10000000000 : ℝ)|=(4519989407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s3_4 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-201103307/1000000000 : ℝ)*x 0 + (654437327/1250000000 : ℝ)*x 1 + (2710951023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201103307/1000000000 : ℝ)^4339 ≤ (12253104643063/100000000000000 : ℝ)^3315 := by
    have hnat : (201103307 : ℕ)^4339*100000000000000^3315 ≤ 12253104643063^3315*1000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201103307 1000000000 12253104643063 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654437327/1250000000 : ℝ)^4339 ≤ (42869111969119/100000000000000 : ℝ)^3315 := by
    have hnat : (654437327 : ℕ)^4339*100000000000000^3315 ≤ 42869111969119^3315*1250000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654437327 1250000000 42869111969119 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710951023/5000000000 : ℝ)^4339 ≤ (22438891686621/50000000000000 : ℝ)^3315 := by
    have hnat : (2710951023 : ℕ)^4339*50000000000000^3315 ≤ 22438891686621^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710951023 5000000000 22438891686621 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-201103307/1000000000 : ℝ), (654437327/1250000000 : ℝ), (2710951023/5000000000 : ℝ)] ![(12253104643063/100000000000000 : ℝ), (42869111969119/100000000000000 : ℝ), (22438891686621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-201103307/1000000000 : ℝ)|^4339 ≤ (12253104643063/100000000000000 : ℝ)^3315
        have hw : |(-201103307/1000000000 : ℝ)|=(201103307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654437327/1250000000 : ℝ)|^4339 ≤ (42869111969119/100000000000000 : ℝ)^3315
        have hw : |(654437327/1250000000 : ℝ)|=(654437327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710951023/5000000000 : ℝ)|^4339 ≤ (22438891686621/50000000000000 : ℝ)^3315
        have hw : |(2710951023/5000000000 : ℝ)|=(2710951023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s3_5 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302763467/10000000000 : ℝ)*x 0 + (-1919811679/10000000000 : ℝ)*x 1 + (1084380551/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302763467/10000000000 : ℝ)^4339 ≤ (5448930971851/12500000000000 : ℝ)^3315 := by
    have hnat : (5302763467 : ℕ)^4339*12500000000000^3315 ≤ 5448930971851^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302763467 10000000000 5448930971851 12500000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1919811679/10000000000 : ℝ)^4339 ≤ (5765380581547/50000000000000 : ℝ)^3315 := by
    have hnat : (1919811679 : ℕ)^4339*50000000000000^3315 ≤ 5765380581547^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919811679 10000000000 5765380581547 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084380551/2000000000 : ℝ)^4339 ≤ (1402430970453/3125000000000 : ℝ)^3315 := by
    have hnat : (1084380551 : ℕ)^4339*3125000000000^3315 ≤ 1402430970453^3315*2000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084380551 2000000000 1402430970453 3125000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302763467/10000000000 : ℝ), (-1919811679/10000000000 : ℝ), (1084380551/2000000000 : ℝ)] ![(5448930971851/12500000000000 : ℝ), (5765380581547/50000000000000 : ℝ), (1402430970453/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302763467/10000000000 : ℝ)|^4339 ≤ (5448930971851/12500000000000 : ℝ)^3315
        have hw : |(5302763467/10000000000 : ℝ)|=(5302763467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1919811679/10000000000 : ℝ)|^4339 ≤ (5765380581547/50000000000000 : ℝ)^3315
        have hw : |(-1919811679/10000000000 : ℝ)|=(1919811679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084380551/2000000000 : ℝ)|^4339 ≤ (1402430970453/3125000000000 : ℝ)^3315
        have hw : |(1084380551/2000000000 : ℝ)|=(1084380551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s3_6 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302764807/10000000000 : ℝ)*x 0 + (677737713/1250000000 : ℝ)*x 1 + (-479952823/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302764807/10000000000 : ℝ)^4339 ≤ (43591462192973/100000000000000 : ℝ)^3315 := by
    have hnat : (5302764807 : ℕ)^4339*100000000000000^3315 ≤ 43591462192973^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302764807 10000000000 43591462192973 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677737713/1250000000 : ℝ)^4339 ≤ (1121944491701/2500000000000 : ℝ)^3315 := by
    have hnat : (677737713 : ℕ)^4339*2500000000000^3315 ≤ 1121944491701^3315*1250000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677737713 1250000000 1121944491701 2500000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (479952823/2500000000 : ℝ)^4339 ≤ (11530758120693/100000000000000 : ℝ)^3315 := by
    have hnat : (479952823 : ℕ)^4339*100000000000000^3315 ≤ 11530758120693^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479952823 2500000000 11530758120693 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302764807/10000000000 : ℝ), (677737713/1250000000 : ℝ), (-479952823/2500000000 : ℝ)] ![(43591462192973/100000000000000 : ℝ), (1121944491701/2500000000000 : ℝ), (11530758120693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302764807/10000000000 : ℝ)|^4339 ≤ (43591462192973/100000000000000 : ℝ)^3315
        have hw : |(5302764807/10000000000 : ℝ)|=(5302764807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677737713/1250000000 : ℝ)|^4339 ≤ (1121944491701/2500000000000 : ℝ)^3315
        have hw : |(677737713/1250000000 : ℝ)|=(677737713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-479952823/2500000000 : ℝ)|^4339 ≤ (11530758120693/100000000000000 : ℝ)^3315
        have hw : |(-479952823/2500000000 : ℝ)|=(479952823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s3_7 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2158107153/5000000000 : ℝ)*x 0 + (4518358941/10000000000 : ℝ)*x 1 + (412248031/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158107153/5000000000 : ℝ)^4339 ≤ (16647794492611/50000000000000 : ℝ)^3315 := by
    have hnat : (2158107153 : ℕ)^4339*50000000000000^3315 ≤ 16647794492611^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158107153 5000000000 16647794492611 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518358941/10000000000 : ℝ)^4339 ≤ (4418904877103/12500000000000 : ℝ)^3315 := by
    have hnat : (4518358941 : ℕ)^4339*12500000000000^3315 ≤ 4418904877103^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518358941 10000000000 4418904877103 12500000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412248031/1000000000 : ℝ)^4339 ≤ (7838292997143/25000000000000 : ℝ)^3315 := by
    have hnat : (412248031 : ℕ)^4339*25000000000000^3315 ≤ 7838292997143^3315*1000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412248031 1000000000 7838292997143 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158107153/5000000000 : ℝ), (4518358941/10000000000 : ℝ), (412248031/1000000000 : ℝ)] ![(16647794492611/50000000000000 : ℝ), (4418904877103/12500000000000 : ℝ), (7838292997143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158107153/5000000000 : ℝ)|^4339 ≤ (16647794492611/50000000000000 : ℝ)^3315
        have hw : |(2158107153/5000000000 : ℝ)|=(2158107153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518358941/10000000000 : ℝ)|^4339 ≤ (4418904877103/12500000000000 : ℝ)^3315
        have hw : |(4518358941/10000000000 : ℝ)|=(4518358941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(412248031/1000000000 : ℝ)|^4339 ≤ (7838292997143/25000000000000 : ℝ)^3315
        have hw : |(412248031/1000000000 : ℝ)|=(412248031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1379_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3193/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2521/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11/100 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7489/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3193/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2521/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3193/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2521/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3193/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2521/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3193/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2521/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3193/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2521/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3193/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2521/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2521/25000 : ℝ) ^ (2169/512 : ℝ) ≤ (1202518482808599/20000000000000000000 : ℝ) := by
    have hpowers : (2521/25000 : ℝ)^2169 ≤ (1202518482808599/20000000000000000000 : ℝ)^512 := by
      have hnat : (2521 : ℕ)^2169*20000000000000000000^512 ≤ 1202518482808599^512*25000^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2521 25000 1202518482808599 20000000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2521/25000 : ℝ)) (X := (1202518482808599/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3193/20000 : ℝ) ^ (2169/512 : ℝ) ≤ (1684310237752499/4000000000000000000 : ℝ) := by
    have hpowers : (3193/20000 : ℝ)^2169 ≤ (1684310237752499/4000000000000000000 : ℝ)^512 := by
      have hnat : (3193 : ℕ)^2169*4000000000000000000^512 ≤ 1684310237752499^512*20000^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3193 20000 1684310237752499 4000000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3193/20000 : ℝ)) (X := (1684310237752499/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001202518482808599/10000000000000000000 : ℝ) ≤ (5000141922818059/5000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (10001202518482808599/10000000000000000000 : ℝ)^512 ≤ (5000141922818059/5000000000000000 : ℝ)^2169 := by
      have hnat : (10001202518482808599 : ℕ)^512*5000000000000000^2169 ≤ 5000141922818059^2169*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001202518482808599 10000000000000000000 5000141922818059 5000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141922818059/5000000000000000 : ℝ)) (X := (10001202518482808599/10000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004812034835785547/10000000000000000000 : ℝ) ≤ (2500283922211581/2500000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (10004812034835785547/10000000000000000000 : ℝ)^512 ≤ (2500283922211581/2500000000000000 : ℝ)^2169 := by
      have hnat : (10004812034835785547 : ℕ)^512*2500000000000000^2169 ≤ 2500283922211581^2169*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004812034835785547 10000000000000000000 2500283922211581 2500000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500283922211581/2500000000000000 : ℝ)) (X := (10004812034835785547/10000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001684310237752499/2000000000000000000 : ℝ) ≤ (1000198753205653/1000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (2001684310237752499/2000000000000000000 : ℝ)^512 ≤ (1000198753205653/1000000000000000 : ℝ)^2169 := by
      have hnat : (2001684310237752499 : ℕ)^512*1000000000000000^2169 ≤ 1000198753205653^2169*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001684310237752499 2000000000000000000 1000198753205653 1000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000198753205653/1000000000000000 : ℝ)) (X := (2001684310237752499/2000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1202518482808599/20000000000000000000 : ℝ) ≤ ((1175889786446451507/1176200000000000000 : ℝ)+2*(425921605103/294050000000000 : ℝ)*(2521/25000 : ℝ))^(2169/512 : ℝ) := by
    rw [show (1175889786446451507/1176200000000000000 : ℝ)+2*(425921605103/294050000000000 : ℝ)*(2521/25000 : ℝ)=(5000141922818059/5000000000000000 : ℝ) by norm_num, show 1+2*(1202518482808599/20000000000000000000 : ℝ)=(10001202518482808599/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1684310237752499/4000000000000000000 : ℝ)+(1202518482808599/20000000000000000000 : ℝ) ≤ ((1175889786446451507/1176200000000000000 : ℝ)+(425921605103/294050000000000 : ℝ)*((3193/20000 : ℝ)+(2521/25000 : ℝ)))^(2169/512 : ℝ) := by
    rw [show (1175889786446451507/1176200000000000000 : ℝ)+(425921605103/294050000000000 : ℝ)*((3193/20000 : ℝ)+(2521/25000 : ℝ))=(2500283922211581/2500000000000000 : ℝ) by norm_num, show 1+(1684310237752499/4000000000000000000 : ℝ)+(1202518482808599/20000000000000000000 : ℝ)=(10004812034835785547/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1684310237752499/4000000000000000000 : ℝ) ≤ ((1175889786446451507/1176200000000000000 : ℝ)+2*(425921605103/294050000000000 : ℝ)*(3193/20000 : ℝ))^(2169/512 : ℝ) := by
    rw [show (1175889786446451507/1176200000000000000 : ℝ)+2*(425921605103/294050000000000 : ℝ)*(3193/20000 : ℝ)=(1000198753205653/1000000000000000 : ℝ) by norm_num, show 1+2*(1684310237752499/4000000000000000000 : ℝ)=(2001684310237752499/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1175889786446451507/1176200000000000000 : ℝ)*(X 1 0+X 2 0)+(425921605103/294050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (2521/25000 : ℝ)) (hi := (3193/20000 : ℝ)) (c := (1175889786446451507/1176200000000000000 : ℝ)) (alpha := (425921605103/294050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1175889786446451507/1176200000000000000 : ℝ)*(X 0 1+X 2 1)+(425921605103/294050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (2521/25000 : ℝ)) (hi := (3193/20000 : ℝ)) (c := (1175889786446451507/1176200000000000000 : ℝ)) (alpha := (425921605103/294050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1175889786446451507/1176200000000000000 : ℝ)*(X 0 2+X 1 2)+(425921605103/294050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (2521/25000 : ℝ)) (hi := (3193/20000 : ℝ)) (c := (1175889786446451507/1176200000000000000 : ℝ)) (alpha := (425921605103/294050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-402202977/2000000000 : ℝ)*X 0 0+(1355668797/2500000000 : ℝ)*X 0 1+(523473057/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675686731/5000000000 : ℝ)*X 1 0+(-2106983563/10000000000 : ℝ)*X 1 1+(1308682771/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337843353/2500000000 : ℝ)*X 2 0+(261736563/500000000 : ℝ)*X 2 1+(-2106983397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((107904397/250000000 : ℝ)*X 0 0+(4120841783/10000000000 : ℝ)*X 0 1+(4519989407/10000000000 : ℝ)*X 0 2+(107904397/250000000 : ℝ)*X 1 0+(4120841783/10000000000 : ℝ)*X 1 1+(4519989407/10000000000 : ℝ)*X 1 2+(107904397/250000000 : ℝ)*X 2 0+(4120841783/10000000000 : ℝ)*X 2 1+(4519989407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-201103307/1000000000 : ℝ)*X 0 0+(654437327/1250000000 : ℝ)*X 0 1+(2710951023/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302763467/10000000000 : ℝ)*X 1 0+(-1919811679/10000000000 : ℝ)*X 1 1+(1084380551/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302764807/10000000000 : ℝ)*X 2 0+(677737713/1250000000 : ℝ)*X 2 1+(-479952823/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2158107153/5000000000 : ℝ)*X 0 0+(4518358941/10000000000 : ℝ)*X 0 1+(412248031/1000000000 : ℝ)*X 0 2+(2158107153/5000000000 : ℝ)*X 1 0+(4518358941/10000000000 : ℝ)*X 1 1+(412248031/1000000000 : ℝ)*X 1 2+(2158107153/5000000000 : ℝ)*X 2 0+(4518358941/10000000000 : ℝ)*X 2 1+(412248031/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14800609846833272360677803/2940500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8880461/3125000000000 : ℝ)*(base19) + (180540343/100000000000000 : ℝ)*(lower2) + (2990483/3125000000000 : ℝ)*(upper3) + (932053/2000000000000 : ℝ)*(lower4) + (18305159/100000000000000 : ℝ)*(upper5) + (195652259003519/5000000000000 : ℝ)*(major0) + (195652259003519/5000000000000 : ℝ)*(major1) + (195652259003519/5000000000000 : ℝ)*(major2) + (665091853067711/12500000000000 : ℝ)*(sp0) + (5320751274124441/100000000000000 : ℝ)*(sp1) + (212830132020799/4000000000000 : ℝ)*(sp2) + (156583555740121/6250000000000 : ℝ)*(sp3) + (18475978287/100000000000000 : ℝ)*(sp4) + (871110391/50000000000000 : ℝ)*(sp5) + (156583555740121/6250000000000 : ℝ)*(f.failure) + (212830132020799/4000000000000 : ℝ)*(f.sum) + (32089732039073/2940500000000000000000000000 : ℝ)*base65 + (39506097264537133/5881000000000000000000000000000 : ℝ)*base67 + (15962400090047133/5881000000000000000000000000000 : ℝ)*base69 + (74056621803985133/5881000000000000000000000000000 : ℝ)*base71 + (14102579362731/5881000000000000000000000000 : ℝ)*base74 + (31364732667995133/5881000000000000000000000000000 : ℝ)*base75 + (221674727922901133/5881000000000000000000000000000 : ℝ)*base77 + (30313327593853133/5881000000000000000000000000000 : ℝ)*base79 + (21008277106019/5881000000000000000000000000 : ℝ)*base81 + (7785657/625000000000000000000 : ℝ)*base90 + (7785657/625000000000000000000 : ℝ)*base92 + (7785657/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10644077854727155329130599/29405000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103402539/5000000000000 : ℝ)*(base19) + (123680227/3125000000000 : ℝ)*(base23) + (486286083/100000000000000 : ℝ)*(upper3) + (74137441/50000000000000 : ℝ)*(lower4) + (16828349/6250000000000 : ℝ)*(upper5) + (1972685428571427/50000000000000 : ℝ)*(major0) + (1972685428571427/50000000000000 : ℝ)*(major1) + (1972685428571427/50000000000000 : ℝ)*(major2) + (44923758093/100000000000000 : ℝ)*(sp1) + (14536564747/20000000000000 : ℝ)*(sp2) + (5364708215373911/100000000000000 : ℝ)*(sp4) + (2682330611782519/50000000000000 : ℝ)*(sp5) + (5364631574782911/100000000000000 : ℝ)*(sp6) + (631508371711431/25000000000000 : ℝ)*(sp7) + (631508371711431/25000000000000 : ℝ)*(f.failure) + (5364708215373911/100000000000000 : ℝ)*(f.sum) + (44880136720773/14702500000000000000000000000 : ℝ)*base66 + (697680306906614489/58810000000000000000000000000000 : ℝ)*base67 + (716505923900954489/58810000000000000000000000000000 : ℝ)*base69 + (723556895333854489/58810000000000000000000000000000 : ℝ)*base71 + (192907819018891/29405000000000000000000000000 : ℝ)*base74 + (524101916650194489/58810000000000000000000000000000 : ℝ)*base75 + (812680375453004489/58810000000000000000000000000000 : ℝ)*base77 + (798102541655534489/58810000000000000000000000000000 : ℝ)*base79 + (95089778520441/29405000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (506073/2500000000000000000000 : ℝ)*base89 + (506073/2500000000000000000000 : ℝ)*base91 + (506073/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1379_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3193/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2521/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7489/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1379_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1379_s4_0 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2012205547/10000000000 : ℝ)*x 0 + (2706382047/5000000000 : ℝ)*x 1 + (5243858851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2012205547/10000000000 : ℝ)^4339 ≤ (613122801987/5000000000000 : ℝ)^3315 := by
    have hnat : (2012205547 : ℕ)^4339*5000000000000^3315 ≤ 613122801987^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012205547 10000000000 613122801987 5000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706382047/5000000000 : ℝ)^4339 ≤ (11194702315389/25000000000000 : ℝ)^3315 := by
    have hnat : (2706382047 : ℕ)^4339*25000000000000^3315 ≤ 11194702315389^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706382047 5000000000 11194702315389 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243858851/10000000000 : ℝ)^4339 ≤ (21479367342303/50000000000000 : ℝ)^3315 := by
    have hnat : (5243858851 : ℕ)^4339*50000000000000^3315 ≤ 21479367342303^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243858851 10000000000 21479367342303 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2012205547/10000000000 : ℝ), (2706382047/5000000000 : ℝ), (5243858851/10000000000 : ℝ)] ![(613122801987/5000000000000 : ℝ), (11194702315389/25000000000000 : ℝ), (21479367342303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2012205547/10000000000 : ℝ)|^4339 ≤ (613122801987/5000000000000 : ℝ)^3315
        have hw : |(-2012205547/10000000000 : ℝ)|=(2012205547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706382047/5000000000 : ℝ)|^4339 ≤ (11194702315389/25000000000000 : ℝ)^3315
        have hw : |(2706382047/5000000000 : ℝ)|=(2706382047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243858851/10000000000 : ℝ)|^4339 ≤ (21479367342303/50000000000000 : ℝ)^3315
        have hw : |(5243858851/10000000000 : ℝ)|=(5243858851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s4_1 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66860419/125000000 : ℝ)*x 0 + (-2098270673/10000000000 : ℝ)*x 1 + (5243859241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66860419/125000000 : ℝ)^4339 ≤ (44087817256987/100000000000000 : ℝ)^3315 := by
    have hnat : (66860419 : ℕ)^4339*100000000000000^3315 ≤ 44087817256987^3315*125000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66860419 125000000 44087817256987 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2098270673/10000000000 : ℝ)^4339 ≤ (2590688772279/20000000000000 : ℝ)^3315 := by
    have hnat : (2098270673 : ℕ)^4339*20000000000000^3315 ≤ 2590688772279^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098270673 10000000000 2590688772279 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243859241/10000000000 : ℝ)^4339 ≤ (42958738866483/100000000000000 : ℝ)^3315 := by
    have hnat : (5243859241 : ℕ)^4339*100000000000000^3315 ≤ 42958738866483^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243859241 10000000000 42958738866483 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66860419/125000000 : ℝ), (-2098270673/10000000000 : ℝ), (5243859241/10000000000 : ℝ)] ![(44087817256987/100000000000000 : ℝ), (2590688772279/20000000000000 : ℝ), (42958738866483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66860419/125000000 : ℝ)|^4339 ≤ (44087817256987/100000000000000 : ℝ)^3315
        have hw : |(66860419/125000000 : ℝ)|=(66860419/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2098270673/10000000000 : ℝ)|^4339 ≤ (2590688772279/20000000000000 : ℝ)^3315
        have hw : |(-2098270673/10000000000 : ℝ)|=(2098270673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243859241/10000000000 : ℝ)|^4339 ≤ (42958738866483/100000000000000 : ℝ)^3315
        have hw : |(5243859241/10000000000 : ℝ)|=(5243859241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s4_2 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348833661/10000000000 : ℝ)*x 0 + (1310964671/2500000000 : ℝ)*x 1 + (-262283903/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348833661/10000000000 : ℝ)^4339 ≤ (44087818778181/100000000000000 : ℝ)^3315 := by
    have hnat : (5348833661 : ℕ)^4339*100000000000000^3315 ≤ 44087818778181^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348833661 10000000000 44087818778181 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310964671/2500000000 : ℝ)^4339 ≤ (8591746578781/20000000000000 : ℝ)^3315 := by
    have hnat : (1310964671 : ℕ)^4339*20000000000000^3315 ≤ 8591746578781^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310964671 2500000000 8591746578781 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262283903/1250000000 : ℝ)^4339 ≤ (202397629901/1562500000000 : ℝ)^3315 := by
    have hnat : (262283903 : ℕ)^4339*1562500000000^3315 ≤ 202397629901^3315*1250000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262283903 1250000000 202397629901 1562500000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348833661/10000000000 : ℝ), (1310964671/2500000000 : ℝ), (-262283903/1250000000 : ℝ)] ![(44087818778181/100000000000000 : ℝ), (8591746578781/20000000000000 : ℝ), (202397629901/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348833661/10000000000 : ℝ)|^4339 ≤ (44087818778181/100000000000000 : ℝ)^3315
        have hw : |(5348833661/10000000000 : ℝ)|=(5348833661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310964671/2500000000 : ℝ)|^4339 ≤ (8591746578781/20000000000000 : ℝ)^3315
        have hw : |(1310964671/2500000000 : ℝ)|=(1310964671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-262283903/1250000000 : ℝ)|^4339 ≤ (202397629901/1562500000000 : ℝ)^3315
        have hw : |(-262283903/1250000000 : ℝ)|=(262283903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s4_3 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2158451043/5000000000 : ℝ)*x 0 + (1035242063/2500000000 : ℝ)*x 1 + (2812303/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158451043/5000000000 : ℝ)^4339 ≤ (33302533630221/100000000000000 : ℝ)^3315 := by
    have hnat : (2158451043 : ℕ)^4339*100000000000000^3315 ≤ 33302533630221^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158451043 5000000000 33302533630221 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035242063/2500000000 : ℝ)^4339 ≤ (1576867080257/5000000000000 : ℝ)^3315 := by
    have hnat : (1035242063 : ℕ)^4339*5000000000000^3315 ≤ 1576867080257^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035242063 2500000000 1576867080257 5000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2812303/6250000 : ℝ)^4339 ≤ (35160124760251/100000000000000 : ℝ)^3315 := by
    have hnat : (2812303 : ℕ)^4339*100000000000000^3315 ≤ 35160124760251^3315*6250000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2812303 6250000 35160124760251 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158451043/5000000000 : ℝ), (1035242063/2500000000 : ℝ), (2812303/6250000 : ℝ)] ![(33302533630221/100000000000000 : ℝ), (1576867080257/5000000000000 : ℝ), (35160124760251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158451043/5000000000 : ℝ)|^4339 ≤ (33302533630221/100000000000000 : ℝ)^3315
        have hw : |(2158451043/5000000000 : ℝ)|=(2158451043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035242063/2500000000 : ℝ)|^4339 ≤ (1576867080257/5000000000000 : ℝ)^3315
        have hw : |(1035242063/2500000000 : ℝ)|=(1035242063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2812303/6250000 : ℝ)|^4339 ≤ (35160124760251/100000000000000 : ℝ)^3315
        have hw : |(2812303/6250000 : ℝ)|=(2812303/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s4_4 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-62881811/312500000 : ℝ)*x 0 + (1311119781/2500000000 : ℝ)*x 1 + (1082428141/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62881811/312500000 : ℝ)^4339 ≤ (613127749403/5000000000000 : ℝ)^3315 := by
    have hnat : (62881811 : ℕ)^4339*5000000000000^3315 ≤ 613127749403^3315*312500000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62881811 312500000 613127749403 5000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311119781/2500000000 : ℝ)^4339 ≤ (21482692922463/50000000000000 : ℝ)^3315 := by
    have hnat : (1311119781 : ℕ)^4339*50000000000000^3315 ≤ 21482692922463^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311119781 2500000000 21482692922463 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082428141/2000000000 : ℝ)^4339 ≤ (22386029574863/50000000000000 : ℝ)^3315 := by
    have hnat : (1082428141 : ℕ)^4339*50000000000000^3315 ≤ 22386029574863^3315*2000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082428141 2000000000 22386029574863 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62881811/312500000 : ℝ), (1311119781/2500000000 : ℝ), (1082428141/2000000000 : ℝ)] ![(613127749403/5000000000000 : ℝ), (21482692922463/50000000000000 : ℝ), (22386029574863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62881811/312500000 : ℝ)|^4339 ≤ (613127749403/5000000000000 : ℝ)^3315
        have hw : |(-62881811/312500000 : ℝ)|=(62881811/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311119781/2500000000 : ℝ)|^4339 ≤ (21482692922463/50000000000000 : ℝ)^3315
        have hw : |(1311119781/2500000000 : ℝ)|=(1311119781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082428141/2000000000 : ℝ)|^4339 ≤ (22386029574863/50000000000000 : ℝ)^3315
        have hw : |(1082428141/2000000000 : ℝ)|=(1082428141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s4_5 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305147893/10000000000 : ℝ)*x 0 + (-1929988959/10000000000 : ℝ)*x 1 + (169129397/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305147893/10000000000 : ℝ)^4339 ≤ (1744684222391/4000000000000 : ℝ)^3315 := by
    have hnat : (5305147893 : ℕ)^4339*4000000000000^3315 ≤ 1744684222391^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305147893 10000000000 1744684222391 4000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1929988959/10000000000 : ℝ)^4339 ≤ (11610835286819/100000000000000 : ℝ)^3315 := by
    have hnat : (1929988959 : ℕ)^4339*100000000000000^3315 ≤ 11610835286819^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929988959 10000000000 11610835286819 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169129397/312500000 : ℝ)^4339 ≤ (22386029569449/50000000000000 : ℝ)^3315 := by
    have hnat : (169129397 : ℕ)^4339*50000000000000^3315 ≤ 22386029569449^3315*312500000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169129397 312500000 22386029569449 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305147893/10000000000 : ℝ), (-1929988959/10000000000 : ℝ), (169129397/312500000 : ℝ)] ![(1744684222391/4000000000000 : ℝ), (11610835286819/100000000000000 : ℝ), (22386029569449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305147893/10000000000 : ℝ)|^4339 ≤ (1744684222391/4000000000000 : ℝ)^3315
        have hw : |(5305147893/10000000000 : ℝ)|=(5305147893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1929988959/10000000000 : ℝ)|^4339 ≤ (11610835286819/100000000000000 : ℝ)^3315
        have hw : |(-1929988959/10000000000 : ℝ)|=(1929988959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169129397/312500000 : ℝ)|^4339 ≤ (22386029569449/50000000000000 : ℝ)^3315
        have hw : |(169129397/312500000 : ℝ)|=(169129397/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s4_6 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305147867/10000000000 : ℝ)*x 0 + (2706070361/5000000000 : ℝ)*x 1 + (-1929988971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305147867/10000000000 : ℝ)^4339 ≤ (43617105279981/100000000000000 : ℝ)^3315 := by
    have hnat : (5305147867 : ℕ)^4339*100000000000000^3315 ≤ 43617105279981^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305147867 10000000000 43617105279981 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706070361/5000000000 : ℝ)^4339 ≤ (44772059333801/100000000000000 : ℝ)^3315 := by
    have hnat : (2706070361 : ℕ)^4339*100000000000000^3315 ≤ 44772059333801^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706070361 5000000000 44772059333801 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1929988971/10000000000 : ℝ)^4339 ≤ (11610835381311/100000000000000 : ℝ)^3315 := by
    have hnat : (1929988971 : ℕ)^4339*100000000000000^3315 ≤ 11610835381311^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929988971 10000000000 11610835381311 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305147867/10000000000 : ℝ), (2706070361/5000000000 : ℝ), (-1929988971/10000000000 : ℝ)] ![(43617105279981/100000000000000 : ℝ), (44772059333801/100000000000000 : ℝ), (11610835381311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305147867/10000000000 : ℝ)|^4339 ≤ (43617105279981/100000000000000 : ℝ)^3315
        have hw : |(5305147867/10000000000 : ℝ)|=(5305147867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706070361/5000000000 : ℝ)|^4339 ≤ (44772059333801/100000000000000 : ℝ)^3315
        have hw : |(2706070361/5000000000 : ℝ)|=(2706070361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1929988971/10000000000 : ℝ)|^4339 ≤ (11610835381311/100000000000000 : ℝ)^3315
        have hw : |(-1929988971/10000000000 : ℝ)|=(1929988971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s4_7 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4316928351/10000000000 : ℝ)*x 0 + (2249183707/5000000000 : ℝ)*x 1 + (82845863/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316928351/10000000000 : ℝ)^4339 ≤ (33302798839679/100000000000000 : ℝ)^3315 := by
    have hnat : (4316928351 : ℕ)^4339*100000000000000^3315 ≤ 33302798839679^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316928351 10000000000 33302798839679 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249183707/5000000000 : ℝ)^4339 ≤ (35146651650861/100000000000000 : ℝ)^3315 := by
    have hnat : (2249183707 : ℕ)^4339*100000000000000^3315 ≤ 35146651650861^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249183707 5000000000 35146651650861 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82845863/200000000 : ℝ)^4339 ≤ (3155054948781/10000000000000 : ℝ)^3315 := by
    have hnat : (82845863 : ℕ)^4339*10000000000000^3315 ≤ 3155054948781^3315*200000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82845863 200000000 3155054948781 10000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316928351/10000000000 : ℝ), (2249183707/5000000000 : ℝ), (82845863/200000000 : ℝ)] ![(33302798839679/100000000000000 : ℝ), (35146651650861/100000000000000 : ℝ), (3155054948781/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316928351/10000000000 : ℝ)|^4339 ≤ (33302798839679/100000000000000 : ℝ)^3315
        have hw : |(4316928351/10000000000 : ℝ)|=(4316928351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249183707/5000000000 : ℝ)|^4339 ≤ (35146651650861/100000000000000 : ℝ)^3315
        have hw : |(2249183707/5000000000 : ℝ)|=(2249183707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82845863/200000000 : ℝ)|^4339 ≤ (3155054948781/10000000000000 : ℝ)^3315
        have hw : |(82845863/200000000 : ℝ)|=(82845863/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1379_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7489/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h) :
    (2239/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14771/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7489/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11/100 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7489/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11/100 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7489/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11/100 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7489/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11/100 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7489/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11/100 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7489/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11/100 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11/100 : ℝ) ^ (2169/512 : ℝ) ≤ (4345050972972941/50000000000000000000 : ℝ) := by
    have hpowers : (11/100 : ℝ)^2169 ≤ (4345050972972941/50000000000000000000 : ℝ)^512 := by
      have hnat : (11 : ℕ)^2169*50000000000000000000^512 ≤ 4345050972972941^512*100^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11 100 4345050972972941 50000000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11/100 : ℝ)) (X := (4345050972972941/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7489/50000 : ℝ) ^ (2169/512 : ℝ) ≤ (32133042895388403/100000000000000000000 : ℝ) := by
    have hpowers : (7489/50000 : ℝ)^2169 ≤ (32133042895388403/100000000000000000000 : ℝ)^512 := by
      have hnat : (7489 : ℕ)^2169*100000000000000000000^512 ≤ 32133042895388403^512*50000^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7489 50000 32133042895388403 100000000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7489/50000 : ℝ)) (X := (32133042895388403/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004345050972972941/25000000000000000000 : ℝ) ≤ (1250051279816107/1250000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (25004345050972972941/25000000000000000000 : ℝ)^512 ≤ (1250051279816107/1250000000000000 : ℝ)^2169 := by
      have hnat : (25004345050972972941 : ℕ)^512*1250000000000000^2169 ≤ 1250051279816107^2169*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004345050972972941 25000000000000000000 1250051279816107 1250000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250051279816107/1250000000000000 : ℝ)) (X := (25004345050972972941/25000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008164628968266857/20000000000000000000 : ℝ) ≤ (625060218394723/625000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (20008164628968266857/20000000000000000000 : ℝ)^512 ≤ (625060218394723/625000000000000 : ℝ)^2169 := by
      have hnat : (20008164628968266857 : ℕ)^512*625000000000000^2169 ≤ 625060218394723^2169*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008164628968266857 20000000000000000000 625060218394723 625000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625060218394723/625000000000000 : ℝ)) (X := (20008164628968266857/20000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032133042895388403/50000000000000000000 : ℝ) ≤ (250037918752557/250000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (50032133042895388403/50000000000000000000 : ℝ)^512 ≤ (250037918752557/250000000000000 : ℝ)^2169 := by
      have hnat : (50032133042895388403 : ℕ)^512*250000000000000^2169 ≤ 250037918752557^2169*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032133042895388403 50000000000000000000 250037918752557 250000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250037918752557/250000000000000 : ℝ)) (X := (50032133042895388403/50000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4345050972972941/50000000000000000000 : ℝ) ≤ ((2485591268847507823/2486250000000000000 : ℝ)+2*(69156973339/49725000000000 : ℝ)*(11/100 : ℝ))^(2169/512 : ℝ) := by
    rw [show (2485591268847507823/2486250000000000000 : ℝ)+2*(69156973339/49725000000000 : ℝ)*(11/100 : ℝ)=(1250051279816107/1250000000000000 : ℝ) by norm_num, show 1+2*(4345050972972941/50000000000000000000 : ℝ)=(25004345050972972941/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32133042895388403/100000000000000000000 : ℝ)+(4345050972972941/50000000000000000000 : ℝ) ≤ ((2485591268847507823/2486250000000000000 : ℝ)+(69156973339/49725000000000 : ℝ)*((7489/50000 : ℝ)+(11/100 : ℝ)))^(2169/512 : ℝ) := by
    rw [show (2485591268847507823/2486250000000000000 : ℝ)+(69156973339/49725000000000 : ℝ)*((7489/50000 : ℝ)+(11/100 : ℝ))=(625060218394723/625000000000000 : ℝ) by norm_num, show 1+(32133042895388403/100000000000000000000 : ℝ)+(4345050972972941/50000000000000000000 : ℝ)=(20008164628968266857/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32133042895388403/100000000000000000000 : ℝ) ≤ ((2485591268847507823/2486250000000000000 : ℝ)+2*(69156973339/49725000000000 : ℝ)*(7489/50000 : ℝ))^(2169/512 : ℝ) := by
    rw [show (2485591268847507823/2486250000000000000 : ℝ)+2*(69156973339/49725000000000 : ℝ)*(7489/50000 : ℝ)=(250037918752557/250000000000000 : ℝ) by norm_num, show 1+2*(32133042895388403/100000000000000000000 : ℝ)=(50032133042895388403/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2485591268847507823/2486250000000000000 : ℝ)*(X 1 0+X 2 0)+(69156973339/49725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (11/100 : ℝ)) (hi := (7489/50000 : ℝ)) (c := (2485591268847507823/2486250000000000000 : ℝ)) (alpha := (69156973339/49725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2485591268847507823/2486250000000000000 : ℝ)*(X 0 1+X 2 1)+(69156973339/49725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (11/100 : ℝ)) (hi := (7489/50000 : ℝ)) (c := (2485591268847507823/2486250000000000000 : ℝ)) (alpha := (69156973339/49725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2485591268847507823/2486250000000000000 : ℝ)*(X 0 2+X 1 2)+(69156973339/49725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (11/100 : ℝ)) (hi := (7489/50000 : ℝ)) (c := (2485591268847507823/2486250000000000000 : ℝ)) (alpha := (69156973339/49725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2012205547/10000000000 : ℝ)*X 0 0+(2706382047/5000000000 : ℝ)*X 0 1+(5243858851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66860419/125000000 : ℝ)*X 1 0+(-2098270673/10000000000 : ℝ)*X 1 1+(5243859241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348833661/10000000000 : ℝ)*X 2 0+(1310964671/2500000000 : ℝ)*X 2 1+(-262283903/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158451043/5000000000 : ℝ)*X 0 0+(1035242063/2500000000 : ℝ)*X 0 1+(2812303/6250000 : ℝ)*X 0 2+(2158451043/5000000000 : ℝ)*X 1 0+(1035242063/2500000000 : ℝ)*X 1 1+(2812303/6250000 : ℝ)*X 1 2+(2158451043/5000000000 : ℝ)*X 2 0+(1035242063/2500000000 : ℝ)*X 2 1+(2812303/6250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-62881811/312500000 : ℝ)*X 0 0+(1311119781/2500000000 : ℝ)*X 0 1+(1082428141/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305147893/10000000000 : ℝ)*X 1 0+(-1929988959/10000000000 : ℝ)*X 1 1+(169129397/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305147867/10000000000 : ℝ)*X 2 0+(2706070361/5000000000 : ℝ)*X 2 1+(-1929988971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4316928351/10000000000 : ℝ)*X 0 0+(2249183707/5000000000 : ℝ)*X 0 1+(82845863/200000000 : ℝ)*X 0 2+(4316928351/10000000000 : ℝ)*X 1 0+(2249183707/5000000000 : ℝ)*X 1 1+(82845863/200000000 : ℝ)*X 1 2+(4316928351/10000000000 : ℝ)*X 2 0+(2249183707/5000000000 : ℝ)*X 2 1+(82845863/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (610469406386776436590147/318750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (470996127/100000000000000 : ℝ)*(base19) + (299707159/50000000000000 : ℝ)*(base23) + (198187771/50000000000000 : ℝ)*(upper3) + (15408381/100000000000000 : ℝ)*(lower4) + (435411772945981/10000000000000 : ℝ)*(major0) + (435411772945981/10000000000000 : ℝ)*(major1) + (435411772945981/10000000000000 : ℝ)*(major2) + (592049722992489/10000000000000 : ℝ)*(sp0) + (2960250118700427/50000000000000 : ℝ)*(sp1) + (74006164953529/1250000000000 : ℝ)*(sp2) + (174232657393811/6250000000000 : ℝ)*(sp3) + (3478472091/100000000000000 : ℝ)*(sp4) + (6912700343/100000000000000 : ℝ)*(sp6) + (12168381713/100000000000000 : ℝ)*(sp7) + (278773468668269/10000000000000 : ℝ)*(f.failure) + (5920500708396981/100000000000000 : ℝ)*(f.sum) + (7265626417/153000000000000000000000000 : ℝ)*base66 + (7733490686348317/637500000000000000000000000000 : ℝ)*base67 + (10194206123010817/637500000000000000000000000000 : ℝ)*base69 + (7462575370710817/637500000000000000000000000000 : ℝ)*base71 + (80208176671/19125000000000000000000000 : ℝ)*base73 + (9767128126523317/637500000000000000000000000000 : ℝ)*base75 + (8992597159823317/637500000000000000000000000000 : ℝ)*base77 + (11554470240323317/637500000000000000000000000000 : ℝ)*base79 + (267168135743/153000000000000000000000000 : ℝ)*base81 + (1480973/1000000000000000000000 : ℝ)*base90 + (1480973/1000000000000000000000 : ℝ)*base92 + (1480973/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222820678152328385209/27625000000000000000000000 : ℝ) := by norm_num
    linear_combination (37803229/2500000000000 : ℝ)*(base19) + (388789423/25000000000000 : ℝ)*(base23) + (181771643/100000000000000 : ℝ)*(upper3) + (17046367/50000000000000 : ℝ)*(lower4) + (88059127/50000000000000 : ℝ)*(upper5) + (175455947133863/4000000000000 : ℝ)*(major0) + (175455947133863/4000000000000 : ℝ)*(major1) + (175455947133863/4000000000000 : ℝ)*(major2) + (15194053167/50000000000000 : ℝ)*(sp1) + (31359006071/100000000000000 : ℝ)*(sp2) + (5964394443475057/100000000000000 : ℝ)*(sp4) + (2982181271619781/50000000000000 : ℝ)*(sp5) + (2982180764655647/50000000000000 : ℝ)*(sp6) + (1404201322177263/50000000000000 : ℝ)*(sp7) + (1404201322177263/50000000000000 : ℝ)*(f.failure) + (5964394443475057/100000000000000 : ℝ)*(f.sum) + (4028944612061/994500000000000000000000000 : ℝ)*base65 + (377463529504609/255000000000000000000000000000 : ℝ)*base68 + (888773075980391/255000000000000000000000000000 : ℝ)*base69 + (295991638795391/255000000000000000000000000000 : ℝ)*base71 + (519175092601/497250000000000000000000000 : ℝ)*base73 + (399690991945391/255000000000000000000000000000 : ℝ)*base75 + (991556218369609/255000000000000000000000000000 : ℝ)*base78 + (1255371094324609/255000000000000000000000000000 : ℝ)*base80 + (1910645529941/994500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2664271/5000000000000000000000 : ℝ)*base90 + (2664271/5000000000000000000000 : ℝ)*base92 + (2664271/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1379_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7489/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2239/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1379_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1379_s5_0 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1006198991/5000000000 : ℝ)*x 0 + (5411077539/10000000000 : ℝ)*x 1 + (2622709349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006198991/5000000000 : ℝ)^4339 ≤ (6131995508097/50000000000000 : ℝ)^3315 := by
    have hnat : (1006198991 : ℕ)^4339*50000000000000^3315 ≤ 6131995508097^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006198991 5000000000 6131995508097 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411077539/10000000000 : ℝ)^4339 ≤ (44760547647299/100000000000000 : ℝ)^3315 := by
    have hnat : (5411077539 : ℕ)^4339*100000000000000^3315 ≤ 44760547647299^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411077539 10000000000 44760547647299 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622709349/5000000000 : ℝ)^4339 ≤ (1074386532969/2500000000000 : ℝ)^3315 := by
    have hnat : (2622709349 : ℕ)^4339*2500000000000^3315 ≤ 1074386532969^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622709349 5000000000 1074386532969 2500000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1006198991/5000000000 : ℝ), (5411077539/10000000000 : ℝ), (2622709349/5000000000 : ℝ)] ![(6131995508097/50000000000000 : ℝ), (44760547647299/100000000000000 : ℝ), (1074386532969/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1006198991/5000000000 : ℝ)|^4339 ≤ (6131995508097/50000000000000 : ℝ)^3315
        have hw : |(-1006198991/5000000000 : ℝ)|=(1006198991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411077539/10000000000 : ℝ)|^4339 ≤ (44760547647299/100000000000000 : ℝ)^3315
        have hw : |(5411077539/10000000000 : ℝ)|=(5411077539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622709349/5000000000 : ℝ)|^4339 ≤ (1074386532969/2500000000000 : ℝ)^3315
        have hw : |(2622709349/5000000000 : ℝ)|=(2622709349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s5_1 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348400681/10000000000 : ℝ)*x 0 + (-209677889/1000000000 : ℝ)*x 1 + (52454187/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348400681/10000000000 : ℝ)^4339 ≤ (22041573791339/50000000000000 : ℝ)^3315 := by
    have hnat : (5348400681 : ℕ)^4339*50000000000000^3315 ≤ 22041573791339^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348400681 10000000000 22041573791339 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209677889/1000000000 : ℝ)^4339 ≤ (12941391065319/100000000000000 : ℝ)^3315 := by
    have hnat : (209677889 : ℕ)^4339*100000000000000^3315 ≤ 12941391065319^3315*1000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209677889 1000000000 12941391065319 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52454187/100000000 : ℝ)^4339 ≤ (42975461340207/100000000000000 : ℝ)^3315 := by
    have hnat : (52454187 : ℕ)^4339*100000000000000^3315 ≤ 42975461340207^3315*100000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52454187 100000000 42975461340207 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348400681/10000000000 : ℝ), (-209677889/1000000000 : ℝ), (52454187/100000000 : ℝ)] ![(22041573791339/50000000000000 : ℝ), (12941391065319/100000000000000 : ℝ), (42975461340207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348400681/10000000000 : ℝ)|^4339 ≤ (22041573791339/50000000000000 : ℝ)^3315
        have hw : |(5348400681/10000000000 : ℝ)|=(5348400681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-209677889/1000000000 : ℝ)|^4339 ≤ (12941391065319/100000000000000 : ℝ)^3315
        have hw : |(-209677889/1000000000 : ℝ)|=(209677889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52454187/100000000 : ℝ)|^4339 ≤ (42975461340207/100000000000000 : ℝ)^3315
        have hw : |(52454187/100000000 : ℝ)|=(52454187/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s5_2 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348400683/10000000000 : ℝ)*x 0 + (655677337/1250000000 : ℝ)*x 1 + (-524194723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348400683/10000000000 : ℝ)^4339 ≤ (8816629520851/20000000000000 : ℝ)^3315 := by
    have hnat : (5348400683 : ℕ)^4339*20000000000000^3315 ≤ 8816629520851^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348400683 10000000000 8816629520851 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655677337/1250000000 : ℝ)^4339 ≤ (42975461297313/100000000000000 : ℝ)^3315 := by
    have hnat : (655677337 : ℕ)^4339*100000000000000^3315 ≤ 42975461297313^3315*1250000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655677337 1250000000 42975461297313 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524194723/2500000000 : ℝ)^4339 ≤ (3235347770369/25000000000000 : ℝ)^3315 := by
    have hnat : (524194723 : ℕ)^4339*25000000000000^3315 ≤ 3235347770369^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524194723 2500000000 3235347770369 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348400683/10000000000 : ℝ), (655677337/1250000000 : ℝ), (-524194723/2500000000 : ℝ)] ![(8816629520851/20000000000000 : ℝ), (42975461297313/100000000000000 : ℝ), (3235347770369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348400683/10000000000 : ℝ)|^4339 ≤ (8816629520851/20000000000000 : ℝ)^3315
        have hw : |(5348400683/10000000000 : ℝ)|=(5348400683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655677337/1250000000 : ℝ)|^4339 ≤ (42975461297313/100000000000000 : ℝ)^3315
        have hw : |(655677337/1250000000 : ℝ)|=(655677337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-524194723/2500000000 : ℝ)|^4339 ≤ (3235347770369/25000000000000 : ℝ)^3315
        have hw : |(-524194723/2500000000 : ℝ)|=(524194723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s5_3 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539627199/1250000000 : ℝ)*x 0 + (82888043/200000000 : ℝ)*x 1 + (2248111513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539627199/1250000000 : ℝ)^4339 ≤ (2081481246857/6250000000000 : ℝ)^3315 := by
    have hnat : (539627199 : ℕ)^4339*6250000000000^3315 ≤ 2081481246857^3315*1250000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539627199 1250000000 2081481246857 6250000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82888043/200000000 : ℝ)^4339 ≤ (7892894190039/25000000000000 : ℝ)^3315 := by
    have hnat : (82888043 : ℕ)^4339*25000000000000^3315 ≤ 7892894190039^3315*200000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82888043 200000000 7892894190039 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248111513/5000000000 : ℝ)^4339 ≤ (8781180817851/25000000000000 : ℝ)^3315 := by
    have hnat : (2248111513 : ℕ)^4339*25000000000000^3315 ≤ 8781180817851^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248111513 5000000000 8781180817851 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539627199/1250000000 : ℝ), (82888043/200000000 : ℝ), (2248111513/5000000000 : ℝ)] ![(2081481246857/6250000000000 : ℝ), (7892894190039/25000000000000 : ℝ), (8781180817851/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539627199/1250000000 : ℝ)|^4339 ≤ (2081481246857/6250000000000 : ℝ)^3315
        have hw : |(539627199/1250000000 : ℝ)|=(539627199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82888043/200000000 : ℝ)|^4339 ≤ (7892894190039/25000000000000 : ℝ)^3315
        have hw : |(82888043/200000000 : ℝ)|=(82888043/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248111513/5000000000 : ℝ)|^4339 ≤ (8781180817851/25000000000000 : ℝ)^3315
        have hw : |(2248111513/5000000000 : ℝ)|=(2248111513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s5_4 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1006204923/5000000000 : ℝ)*x 0 + (5246015421/10000000000 : ℝ)*x 1 + (2705238879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006204923/5000000000 : ℝ)^4339 ≤ (490563426081/4000000000000 : ℝ)^3315 := by
    have hnat : (1006204923 : ℕ)^4339*4000000000000^3315 ≤ 490563426081^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006204923 5000000000 490563426081 4000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246015421/10000000000 : ℝ)^4339 ≤ (42981860536867/100000000000000 : ℝ)^3315 := by
    have hnat : (5246015421 : ℕ)^4339*100000000000000^3315 ≤ 42981860536867^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246015421 10000000000 42981860536867 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705238879/5000000000 : ℝ)^4339 ≤ (44754053785821/100000000000000 : ℝ)^3315 := by
    have hnat : (2705238879 : ℕ)^4339*100000000000000^3315 ≤ 44754053785821^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705238879 5000000000 44754053785821 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1006204923/5000000000 : ℝ), (5246015421/10000000000 : ℝ), (2705238879/5000000000 : ℝ)] ![(490563426081/4000000000000 : ℝ), (42981860536867/100000000000000 : ℝ), (44754053785821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1006204923/5000000000 : ℝ)|^4339 ≤ (490563426081/4000000000000 : ℝ)^3315
        have hw : |(-1006204923/5000000000 : ℝ)|=(1006204923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246015421/10000000000 : ℝ)|^4339 ≤ (42981860536867/100000000000000 : ℝ)^3315
        have hw : |(5246015421/10000000000 : ℝ)|=(5246015421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705238879/5000000000 : ℝ)|^4339 ≤ (44754053785821/100000000000000 : ℝ)^3315
        have hw : |(2705238879/5000000000 : ℝ)|=(2705238879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s5_5 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305554471/10000000000 : ℝ)*x 0 + (-482929933/2500000000 : ℝ)*x 1 + (5410477701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305554471/10000000000 : ℝ)^4339 ≤ (21810740463353/50000000000000 : ℝ)^3315 := by
    have hnat : (5305554471 : ℕ)^4339*50000000000000^3315 ≤ 21810740463353^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305554471 10000000000 21810740463353 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482929933/2500000000 : ℝ)^4339 ≤ (11624465887809/100000000000000 : ℝ)^3315 := by
    have hnat : (482929933 : ℕ)^4339*100000000000000^3315 ≤ 11624465887809^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482929933 2500000000 11624465887809 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410477701/10000000000 : ℝ)^4339 ≤ (44754053168689/100000000000000 : ℝ)^3315 := by
    have hnat : (5410477701 : ℕ)^4339*100000000000000^3315 ≤ 44754053168689^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410477701 10000000000 44754053168689 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305554471/10000000000 : ℝ), (-482929933/2500000000 : ℝ), (5410477701/10000000000 : ℝ)] ![(21810740463353/50000000000000 : ℝ), (11624465887809/100000000000000 : ℝ), (44754053168689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305554471/10000000000 : ℝ)|^4339 ≤ (21810740463353/50000000000000 : ℝ)^3315
        have hw : |(5305554471/10000000000 : ℝ)|=(5305554471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-482929933/2500000000 : ℝ)|^4339 ≤ (11624465887809/100000000000000 : ℝ)^3315
        have hw : |(-482929933/2500000000 : ℝ)|=(482929933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410477701/10000000000 : ℝ)|^4339 ≤ (44754053168689/100000000000000 : ℝ)^3315
        have hw : |(5410477701/10000000000 : ℝ)|=(5410477701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s5_6 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26527773/50000000 : ℝ)*x 0 + (5410477369/10000000000 : ℝ)*x 1 + (-1931720013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26527773/50000000 : ℝ)^4339 ≤ (43621482314949/100000000000000 : ℝ)^3315 := by
    have hnat : (26527773 : ℕ)^4339*100000000000000^3315 ≤ 43621482314949^3315*50000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26527773 50000000 43621482314949 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410477369/10000000000 : ℝ)^4339 ≤ (44754049574169/100000000000000 : ℝ)^3315 := by
    have hnat : (5410477369 : ℕ)^4339*100000000000000^3315 ≤ 44754049574169^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410477369 10000000000 44754049574169 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1931720013/10000000000 : ℝ)^4339 ≤ (2324893620223/20000000000000 : ℝ)^3315 := by
    have hnat : (1931720013 : ℕ)^4339*20000000000000^3315 ≤ 2324893620223^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931720013 10000000000 2324893620223 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26527773/50000000 : ℝ), (5410477369/10000000000 : ℝ), (-1931720013/10000000000 : ℝ)] ![(43621482314949/100000000000000 : ℝ), (44754049574169/100000000000000 : ℝ), (2324893620223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26527773/50000000 : ℝ)|^4339 ≤ (43621482314949/100000000000000 : ℝ)^3315
        have hw : |(26527773/50000000 : ℝ)|=(26527773/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410477369/10000000000 : ℝ)|^4339 ≤ (44754049574169/100000000000000 : ℝ)^3315
        have hw : |(5410477369/10000000000 : ℝ)|=(5410477369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1931720013/10000000000 : ℝ)|^4339 ≤ (2324893620223/20000000000000 : ℝ)^3315
        have hw : |(-1931720013/10000000000 : ℝ)|=(1931720013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s5_7 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079260869/2500000000 : ℝ)*x 0 + (1123738801/2500000000 : ℝ)*x 1 + (4145675957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079260869/2500000000 : ℝ)^4339 ≤ (166519806571/500000000000 : ℝ)^3315 := by
    have hnat : (1079260869 : ℕ)^4339*500000000000^3315 ≤ 166519806571^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079260869 2500000000 166519806571 500000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123738801/2500000000 : ℝ)^4339 ≤ (35111760121253/100000000000000 : ℝ)^3315 := by
    have hnat : (1123738801 : ℕ)^4339*100000000000000^3315 ≤ 35111760121253^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123738801 2500000000 35111760121253 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4145675957/10000000000 : ℝ)^4339 ≤ (31584278544791/100000000000000 : ℝ)^3315 := by
    have hnat : (4145675957 : ℕ)^4339*100000000000000^3315 ≤ 31584278544791^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145675957 10000000000 31584278544791 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079260869/2500000000 : ℝ), (1123738801/2500000000 : ℝ), (4145675957/10000000000 : ℝ)] ![(166519806571/500000000000 : ℝ), (35111760121253/100000000000000 : ℝ), (31584278544791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079260869/2500000000 : ℝ)|^4339 ≤ (166519806571/500000000000 : ℝ)^3315
        have hw : |(1079260869/2500000000 : ℝ)|=(1079260869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123738801/2500000000 : ℝ)|^4339 ≤ (35111760121253/100000000000000 : ℝ)^3315
        have hw : |(1123738801/2500000000 : ℝ)|=(1123738801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4145675957/10000000000 : ℝ)|^4339 ≤ (31584278544791/100000000000000 : ℝ)^3315
        have hw : |(4145675957/10000000000 : ℝ)|=(4145675957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1379_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2239/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2807/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (921/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2239/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2239/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2239/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2239/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2239/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2239/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2239/20000 : ℝ) ^ (2169/512 : ℝ) ≤ (4680842670422649/50000000000000000000 : ℝ) := by
    have hpowers : (2239/20000 : ℝ)^2169 ≤ (4680842670422649/50000000000000000000 : ℝ)^512 := by
      have hnat : (2239 : ℕ)^2169*50000000000000000000^512 ≤ 4680842670422649^512*20000^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2239 20000 4680842670422649 50000000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2239/20000 : ℝ)) (X := (4680842670422649/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14771/100000 : ℝ) ^ (2169/512 : ℝ) ≤ (6058676815727211/20000000000000000000 : ℝ) := by
    have hpowers : (14771/100000 : ℝ)^2169 ≤ (6058676815727211/20000000000000000000 : ℝ)^512 := by
      have hnat : (14771 : ℕ)^2169*20000000000000000000^512 ≤ 6058676815727211^512*100000^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14771 100000 6058676815727211 20000000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14771/100000 : ℝ)) (X := (6058676815727211/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004680842670422649/25000000000000000000 : ℝ) ≤ (10000441940076727/10000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (25004680842670422649/25000000000000000000 : ℝ)^512 ≤ (10000441940076727/10000000000000000 : ℝ)^2169 := by
      have hnat : (25004680842670422649 : ℕ)^512*10000000000000000^2169 ≤ 10000441940076727^2169*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004680842670422649 25000000000000000000 10000441940076727 10000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000441940076727/10000000000000000 : ℝ)) (X := (25004680842670422649/25000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039655069419481353/100000000000000000000 : ℝ) ≤ (2500233982490417/2500000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (100039655069419481353/100000000000000000000 : ℝ)^512 ≤ (2500233982490417/2500000000000000 : ℝ)^2169 := by
      have hnat : (100039655069419481353 : ℕ)^512*2500000000000000^2169 ≤ 2500233982490417^2169*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039655069419481353 100000000000000000000 2500233982490417 2500000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500233982490417/2500000000000000 : ℝ)) (X := (100039655069419481353/100000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006058676815727211/10000000000000000000 : ℝ) ≤ (10001429919846609/10000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (10006058676815727211/10000000000000000000 : ℝ)^512 ≤ (10001429919846609/10000000000000000 : ℝ)^2169 := by
      have hnat : (10006058676815727211 : ℕ)^512*10000000000000000^2169 ≤ 10001429919846609^2169*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006058676815727211 10000000000000000000 10001429919846609 10000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001429919846609/10000000000000000 : ℝ)) (X := (10006058676815727211/10000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4680842670422649/50000000000000000000 : ℝ) ≤ ((17875259972095273381/17880000000000000000 : ℝ)+2*(493989884941/357600000000000 : ℝ)*(2239/20000 : ℝ))^(2169/512 : ℝ) := by
    rw [show (17875259972095273381/17880000000000000000 : ℝ)+2*(493989884941/357600000000000 : ℝ)*(2239/20000 : ℝ)=(10000441940076727/10000000000000000 : ℝ) by norm_num, show 1+2*(4680842670422649/50000000000000000000 : ℝ)=(25004680842670422649/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6058676815727211/20000000000000000000 : ℝ)+(4680842670422649/50000000000000000000 : ℝ) ≤ ((17875259972095273381/17880000000000000000 : ℝ)+(493989884941/357600000000000 : ℝ)*((14771/100000 : ℝ)+(2239/20000 : ℝ)))^(2169/512 : ℝ) := by
    rw [show (17875259972095273381/17880000000000000000 : ℝ)+(493989884941/357600000000000 : ℝ)*((14771/100000 : ℝ)+(2239/20000 : ℝ))=(2500233982490417/2500000000000000 : ℝ) by norm_num, show 1+(6058676815727211/20000000000000000000 : ℝ)+(4680842670422649/50000000000000000000 : ℝ)=(100039655069419481353/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6058676815727211/20000000000000000000 : ℝ) ≤ ((17875259972095273381/17880000000000000000 : ℝ)+2*(493989884941/357600000000000 : ℝ)*(14771/100000 : ℝ))^(2169/512 : ℝ) := by
    rw [show (17875259972095273381/17880000000000000000 : ℝ)+2*(493989884941/357600000000000 : ℝ)*(14771/100000 : ℝ)=(10001429919846609/10000000000000000 : ℝ) by norm_num, show 1+2*(6058676815727211/20000000000000000000 : ℝ)=(10006058676815727211/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17875259972095273381/17880000000000000000 : ℝ)*(X 1 0+X 2 0)+(493989884941/357600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (2239/20000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (17875259972095273381/17880000000000000000 : ℝ)) (alpha := (493989884941/357600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17875259972095273381/17880000000000000000 : ℝ)*(X 0 1+X 2 1)+(493989884941/357600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (2239/20000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (17875259972095273381/17880000000000000000 : ℝ)) (alpha := (493989884941/357600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17875259972095273381/17880000000000000000 : ℝ)*(X 0 2+X 1 2)+(493989884941/357600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (2239/20000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (17875259972095273381/17880000000000000000 : ℝ)) (alpha := (493989884941/357600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1006198991/5000000000 : ℝ)*X 0 0+(5411077539/10000000000 : ℝ)*X 0 1+(2622709349/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348400681/10000000000 : ℝ)*X 1 0+(-209677889/1000000000 : ℝ)*X 1 1+(52454187/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348400683/10000000000 : ℝ)*X 2 0+(655677337/1250000000 : ℝ)*X 2 1+(-524194723/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((539627199/1250000000 : ℝ)*X 0 0+(82888043/200000000 : ℝ)*X 0 1+(2248111513/5000000000 : ℝ)*X 0 2+(539627199/1250000000 : ℝ)*X 1 0+(82888043/200000000 : ℝ)*X 1 1+(2248111513/5000000000 : ℝ)*X 1 2+(539627199/1250000000 : ℝ)*X 2 0+(82888043/200000000 : ℝ)*X 2 1+(2248111513/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1006204923/5000000000 : ℝ)*X 0 0+(5246015421/10000000000 : ℝ)*X 0 1+(2705238879/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305554471/10000000000 : ℝ)*X 1 0+(-482929933/2500000000 : ℝ)*X 1 1+(5410477701/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((26527773/50000000 : ℝ)*X 2 0+(5410477369/10000000000 : ℝ)*X 2 1+(-1931720013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079260869/2500000000 : ℝ)*X 0 0+(1123738801/2500000000 : ℝ)*X 0 1+(4145675957/10000000000 : ℝ)*X 0 2+(1079260869/2500000000 : ℝ)*X 1 0+(1123738801/2500000000 : ℝ)*X 1 1+(4145675957/10000000000 : ℝ)*X 1 2+(1079260869/2500000000 : ℝ)*X 2 0+(1123738801/2500000000 : ℝ)*X 2 1+(4145675957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98800558367191250031229041/18625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24617273/2500000000000 : ℝ)*(base19) + (918511769/100000000000000 : ℝ)*(base23) + (36602571/100000000000000 : ℝ)*(lower2) + (135190587/100000000000000 : ℝ)*(upper3) + (2579653/3125000000000 : ℝ)*(upper5) + (554932444583861/12500000000000 : ℝ)*(major0) + (554932444583861/12500000000000 : ℝ)*(major1) + (554932444583861/12500000000000 : ℝ)*(major2) + (1207304737203811/20000000000000 : ℝ)*(sp0) + (3018271474192729/50000000000000 : ℝ)*(sp1) + (6036543014564609/100000000000000 : ℝ)*(sp2) + (177647792371087/6250000000000 : ℝ)*(sp3) + (20247057323/100000000000000 : ℝ)*(sp4) + (10325503733/100000000000000 : ℝ)*(sp7) + (1421187501720563/50000000000000 : ℝ)*(f.failure) + (3018271966538189/50000000000000 : ℝ)*(f.sum) + (2419426653761/2235000000000000000000000000 : ℝ)*base65 + (575582922708148653/74500000000000000000000000000000 : ℝ)*base68 + (282693245514648653/74500000000000000000000000000000 : ℝ)*base70 + (950715746003148653/74500000000000000000000000000000 : ℝ)*base72 + (1637532000881/2235000000000000000000000000 : ℝ)*base73 + (497063447526648653/74500000000000000000000000000000 : ℝ)*base76 + (377477809153648653/74500000000000000000000000000000 : ℝ)*base78 + (379280132709851347/74500000000000000000000000000000 : ℝ)*base79 + (1305309036313/1117500000000000000000000000 : ℝ)*base81 + (52819629/5000000000000000000000 : ℝ)*base89 + (52819629/5000000000000000000000 : ℝ)*base91 + (52819629/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (568457807252368173109534871/59600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (418440243/20000000000000 : ℝ)*(base19) + (2699377627/100000000000000 : ℝ)*(base23) + (189321259/100000000000000 : ℝ)*(upper3) + (261871727/100000000000000 : ℝ)*(lower4) + (346414461/100000000000000 : ℝ)*(upper5) + (894345510798709/20000000000000 : ℝ)*(major0) + (894345510798709/20000000000000 : ℝ)*(major1) + (894345510798709/20000000000000 : ℝ)*(major2) + (8920940467/20000000000000 : ℝ)*(sp1) + (40364456629/100000000000000 : ℝ)*(sp2) + (6080420121215777/100000000000000 : ℝ)*(sp4) + (3040186712156113/50000000000000 : ℝ)*(sp5) + (6080377057381521/100000000000000 : ℝ)*(sp6) + (572606933768377/20000000000000 : ℝ)*(sp7) + (572606933768377/20000000000000 : ℝ)*(f.failure) + (6080420121215777/100000000000000 : ℝ)*(f.sum) + (7377641282401/3576000000000000000000000000 : ℝ)*base65 + (711905525489294957/119200000000000000000000000000000 : ℝ)*base68 + (275770148233905043/119200000000000000000000000000000 : ℝ)*base69 + (1217962954977905043/119200000000000000000000000000000 : ℝ)*base71 + (8319983276639/3576000000000000000000000000 : ℝ)*base74 + (2588232392201905043/119200000000000000000000000000000 : ℝ)*base75 + (104378862841294957/119200000000000000000000000000000 : ℝ)*base78 + (3707274123505043/119200000000000000000000000000000 : ℝ)*base79 + (284473226947/715200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (164391/2000000000000000000000 : ℝ)*base89 + (164391/2000000000000000000000 : ℝ)*base91 + (164391/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1379_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2239/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (921/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1379_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1379_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3193/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2521/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (921/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1379_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1379_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1379_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3193/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2521/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (921/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1379_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

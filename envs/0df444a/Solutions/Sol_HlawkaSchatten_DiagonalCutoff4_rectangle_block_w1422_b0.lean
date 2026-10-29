-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1422_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:06.404786+00:00
-- url     : https://prove2.me/submissions/3b76b08d-661c-4eac-8b72-b87365cbd6a1

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
theorem support_rectangle_w1422_s0_0 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-881391847/5000000000 : ℝ)*x 0 + (5963075001/10000000000 : ℝ)*x 1 + (4829634369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (881391847/5000000000 : ℝ)^2191 ≤ (2595806925487/25000000000000 : ℝ)^1679 := by
    have hnat : (881391847 : ℕ)^2191*25000000000000^1679 ≤ 2595806925487^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881391847 5000000000 2595806925487 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5963075001/10000000000 : ℝ)^2191 ≤ (50933252328909/100000000000000 : ℝ)^1679 := by
    have hnat : (5963075001 : ℕ)^2191*100000000000000^1679 ≤ 50933252328909^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5963075001 10000000000 50933252328909 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4829634369/10000000000 : ℝ)^2191 ≤ (19341759977301/50000000000000 : ℝ)^1679 := by
    have hnat : (4829634369 : ℕ)^2191*50000000000000^1679 ≤ 19341759977301^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829634369 10000000000 19341759977301 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-881391847/5000000000 : ℝ), (5963075001/10000000000 : ℝ), (4829634369/10000000000 : ℝ)] ![(2595806925487/25000000000000 : ℝ), (50933252328909/100000000000000 : ℝ), (19341759977301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-881391847/5000000000 : ℝ)|^2191 ≤ (2595806925487/25000000000000 : ℝ)^1679
        have hw : |(-881391847/5000000000 : ℝ)|=(881391847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5963075001/10000000000 : ℝ)|^2191 ≤ (50933252328909/100000000000000 : ℝ)^1679
        have hw : |(5963075001/10000000000 : ℝ)|=(5963075001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4829634369/10000000000 : ℝ)|^2191 ≤ (19341759977301/50000000000000 : ℝ)^1679
        have hw : |(4829634369/10000000000 : ℝ)|=(4829634369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s0_1 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1098575613/2000000000 : ℝ)*x 0 + (-96134867/400000000 : ℝ)*x 1 + (1207408691/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098575613/2000000000 : ℝ)^2191 ≤ (45756591769617/100000000000000 : ℝ)^1679 := by
    have hnat : (1098575613 : ℕ)^2191*100000000000000^1679 ≤ 45756591769617^1679*2000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098575613 2000000000 45756591769617 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96134867/400000000 : ℝ)^2191 ≤ (15559884132481/100000000000000 : ℝ)^1679 := by
    have hnat : (96134867 : ℕ)^2191*100000000000000^1679 ≤ 15559884132481^1679*400000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96134867 400000000 15559884132481 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207408691/2500000000 : ℝ)^2191 ≤ (1934176204159/5000000000000 : ℝ)^1679 := by
    have hnat : (1207408691 : ℕ)^2191*5000000000000^1679 ≤ 1934176204159^1679*2500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207408691 2500000000 1934176204159 5000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1098575613/2000000000 : ℝ), (-96134867/400000000 : ℝ), (1207408691/2500000000 : ℝ)] ![(45756591769617/100000000000000 : ℝ), (15559884132481/100000000000000 : ℝ), (1934176204159/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1098575613/2000000000 : ℝ)|^2191 ≤ (45756591769617/100000000000000 : ℝ)^1679
        have hw : |(1098575613/2000000000 : ℝ)|=(1098575613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-96134867/400000000 : ℝ)|^2191 ≤ (15559884132481/100000000000000 : ℝ)^1679
        have hw : |(-96134867/400000000 : ℝ)|=(96134867/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1207408691/2500000000 : ℝ)|^2191 ≤ (1934176204159/5000000000000 : ℝ)^1679
        have hw : |(1207408691/2500000000 : ℝ)|=(1207408691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s0_2 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5492878427/10000000000 : ℝ)*x 0 + (24148173/50000000 : ℝ)*x 1 + (-2403371413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5492878427/10000000000 : ℝ)^2191 ≤ (45756595704701/100000000000000 : ℝ)^1679 := by
    have hnat : (5492878427 : ℕ)^2191*100000000000000^1679 ≤ 45756595704701^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492878427 10000000000 45756595704701 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24148173/50000000 : ℝ)^2191 ≤ (9670880592259/25000000000000 : ℝ)^1679 := by
    have hnat : (24148173 : ℕ)^2191*25000000000000^1679 ≤ 9670880592259^1679*50000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24148173 50000000 9670880592259 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2403371413/10000000000 : ℝ)^2191 ≤ (15559881918987/100000000000000 : ℝ)^1679 := by
    have hnat : (2403371413 : ℕ)^2191*100000000000000^1679 ≤ 15559881918987^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2403371413 10000000000 15559881918987 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5492878427/10000000000 : ℝ), (24148173/50000000 : ℝ), (-2403371413/10000000000 : ℝ)] ![(45756595704701/100000000000000 : ℝ), (9670880592259/25000000000000 : ℝ), (15559881918987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5492878427/10000000000 : ℝ)|^2191 ≤ (45756595704701/100000000000000 : ℝ)^1679
        have hw : |(5492878427/10000000000 : ℝ)|=(5492878427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(24148173/50000000 : ℝ)|^2191 ≤ (9670880592259/25000000000000 : ℝ)^1679
        have hw : |(24148173/50000000 : ℝ)|=(24148173/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2403371413/10000000000 : ℝ)|^2191 ≤ (15559881918987/100000000000000 : ℝ)^1679
        have hw : |(-2403371413/10000000000 : ℝ)|=(2403371413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s0_3 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2083503209/5000000000 : ℝ)*x 0 + (3103536211/10000000000 : ℝ)*x 1 + (5549260567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083503209/5000000000 : ℝ)^2191 ≤ (31907446656781/100000000000000 : ℝ)^1679 := by
    have hnat : (2083503209 : ℕ)^2191*100000000000000^1679 ≤ 31907446656781^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083503209 5000000000 31907446656781 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3103536211/10000000000 : ℝ)^2191 ≤ (10861052221669/50000000000000 : ℝ)^1679 := by
    have hnat : (3103536211 : ℕ)^2191*50000000000000^1679 ≤ 10861052221669^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3103536211 10000000000 10861052221669 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5549260567/10000000000 : ℝ)^2191 ≤ (23185224445141/50000000000000 : ℝ)^1679 := by
    have hnat : (5549260567 : ℕ)^2191*50000000000000^1679 ≤ 23185224445141^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5549260567 10000000000 23185224445141 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2083503209/5000000000 : ℝ), (3103536211/10000000000 : ℝ), (5549260567/10000000000 : ℝ)] ![(31907446656781/100000000000000 : ℝ), (10861052221669/50000000000000 : ℝ), (23185224445141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2083503209/5000000000 : ℝ)|^2191 ≤ (31907446656781/100000000000000 : ℝ)^1679
        have hw : |(2083503209/5000000000 : ℝ)|=(2083503209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3103536211/10000000000 : ℝ)|^2191 ≤ (10861052221669/50000000000000 : ℝ)^1679
        have hw : |(3103536211/10000000000 : ℝ)|=(3103536211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5549260567/10000000000 : ℝ)|^2191 ≤ (23185224445141/50000000000000 : ℝ)^1679
        have hw : |(5549260567/10000000000 : ℝ)|=(5549260567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s0_4 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-70673393/400000000 : ℝ)*x 0 + (4858649957/10000000000 : ℝ)*x 1 + (5933023361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (70673393/400000000 : ℝ)^2191 ≤ (2082875473557/20000000000000 : ℝ)^1679 := by
    have hnat : (70673393 : ℕ)^2191*20000000000000^1679 ≤ 2082875473557^1679*400000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70673393 400000000 2082875473557 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4858649957/10000000000 : ℝ)^2191 ≤ (19493535551077/50000000000000 : ℝ)^1679 := by
    have hnat : (4858649957 : ℕ)^2191*50000000000000^1679 ≤ 19493535551077^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4858649957 10000000000 19493535551077 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5933023361/10000000000 : ℝ)^2191 ≤ (25299275758711/50000000000000 : ℝ)^1679 := by
    have hnat : (5933023361 : ℕ)^2191*50000000000000^1679 ≤ 25299275758711^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5933023361 10000000000 25299275758711 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-70673393/400000000 : ℝ), (4858649957/10000000000 : ℝ), (5933023361/10000000000 : ℝ)] ![(2082875473557/20000000000000 : ℝ), (19493535551077/50000000000000 : ℝ), (25299275758711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-70673393/400000000 : ℝ)|^2191 ≤ (2082875473557/20000000000000 : ℝ)^1679
        have hw : |(-70673393/400000000 : ℝ)|=(70673393/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4858649957/10000000000 : ℝ)|^2191 ≤ (19493535551077/50000000000000 : ℝ)^1679
        have hw : |(4858649957/10000000000 : ℝ)|=(4858649957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5933023361/10000000000 : ℝ)|^2191 ≤ (25299275758711/50000000000000 : ℝ)^1679
        have hw : |(5933023361/10000000000 : ℝ)|=(5933023361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s0_5 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5183549483/10000000000 : ℝ)*x 0 + (-649991249/5000000000 : ℝ)*x 1 + (5933023443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183549483/10000000000 : ℝ)^2191 ≤ (10605831305711/25000000000000 : ℝ)^1679 := by
    have hnat : (5183549483 : ℕ)^2191*25000000000000^1679 ≤ 10605831305711^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183549483 10000000000 10605831305711 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649991249/5000000000 : ℝ)^2191 ≤ (1744530584263/25000000000000 : ℝ)^1679 := by
    have hnat : (649991249 : ℕ)^2191*25000000000000^1679 ≤ 1744530584263^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649991249 5000000000 1744530584263 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5933023443/10000000000 : ℝ)^2191 ≤ (10119710485999/20000000000000 : ℝ)^1679 := by
    have hnat : (5933023443 : ℕ)^2191*20000000000000^1679 ≤ 10119710485999^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5933023443 10000000000 10119710485999 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183549483/10000000000 : ℝ), (-649991249/5000000000 : ℝ), (5933023443/10000000000 : ℝ)] ![(10605831305711/25000000000000 : ℝ), (1744530584263/25000000000000 : ℝ), (10119710485999/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183549483/10000000000 : ℝ)|^2191 ≤ (10605831305711/25000000000000 : ℝ)^1679
        have hw : |(5183549483/10000000000 : ℝ)|=(5183549483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-649991249/5000000000 : ℝ)|^2191 ≤ (1744530584263/25000000000000 : ℝ)^1679
        have hw : |(-649991249/5000000000 : ℝ)|=(649991249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5933023443/10000000000 : ℝ)|^2191 ≤ (10119710485999/20000000000000 : ℝ)^1679
        have hw : |(5933023443/10000000000 : ℝ)|=(5933023443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s0_6 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5183549501/10000000000 : ℝ)*x 0 + (5933023271/10000000000 : ℝ)*x 1 + (-649991371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183549501/10000000000 : ℝ)^2191 ≤ (42423325415083/100000000000000 : ℝ)^1679 := by
    have hnat : (5183549501 : ℕ)^2191*100000000000000^1679 ≤ 42423325415083^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183549501 10000000000 42423325415083 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5933023271/10000000000 : ℝ)^2191 ≤ (25299275257909/50000000000000 : ℝ)^1679 := by
    have hnat : (5933023271 : ℕ)^2191*50000000000000^1679 ≤ 25299275257909^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5933023271 10000000000 25299275257909 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649991371/5000000000 : ℝ)^2191 ≤ (6978124046211/100000000000000 : ℝ)^1679 := by
    have hnat : (649991371 : ℕ)^2191*100000000000000^1679 ≤ 6978124046211^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649991371 5000000000 6978124046211 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183549501/10000000000 : ℝ), (5933023271/10000000000 : ℝ), (-649991371/5000000000 : ℝ)] ![(42423325415083/100000000000000 : ℝ), (25299275257909/50000000000000 : ℝ), (6978124046211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183549501/10000000000 : ℝ)|^2191 ≤ (42423325415083/100000000000000 : ℝ)^1679
        have hw : |(5183549501/10000000000 : ℝ)|=(5183549501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5933023271/10000000000 : ℝ)|^2191 ≤ (25299275257909/50000000000000 : ℝ)^1679
        have hw : |(5933023271/10000000000 : ℝ)|=(5933023271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-649991371/5000000000 : ℝ)|^2191 ≤ (6978124046211/100000000000000 : ℝ)^1679
        have hw : |(-649991371/5000000000 : ℝ)|=(649991371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s0_7 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2087874933/5000000000 : ℝ)*x 0 + (5486650947/10000000000 : ℝ)*x 1 + (3168381631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087874933/5000000000 : ℝ)^2191 ≤ (3199484056219/10000000000000 : ℝ)^1679 := by
    have hnat : (2087874933 : ℕ)^2191*10000000000000^1679 ≤ 3199484056219^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087874933 5000000000 3199484056219 10000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5486650947/10000000000 : ℝ)^2191 ≤ (22844456115347/50000000000000 : ℝ)^1679 := by
    have hnat : (5486650947 : ℕ)^2191*50000000000000^1679 ≤ 22844456115347^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486650947 10000000000 22844456115347 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3168381631/10000000000 : ℝ)^2191 ≤ (22316247199169/100000000000000 : ℝ)^1679 := by
    have hnat : (3168381631 : ℕ)^2191*100000000000000^1679 ≤ 22316247199169^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3168381631 10000000000 22316247199169 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2087874933/5000000000 : ℝ), (5486650947/10000000000 : ℝ), (3168381631/10000000000 : ℝ)] ![(3199484056219/10000000000000 : ℝ), (22844456115347/50000000000000 : ℝ), (22316247199169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2087874933/5000000000 : ℝ)|^2191 ≤ (3199484056219/10000000000000 : ℝ)^1679
        have hw : |(2087874933/5000000000 : ℝ)|=(2087874933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5486650947/10000000000 : ℝ)|^2191 ≤ (22844456115347/50000000000000 : ℝ)^1679
        have hw : |(5486650947/10000000000 : ℝ)|=(5486650947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3168381631/10000000000 : ℝ)|^2191 ≤ (22316247199169/100000000000000 : ℝ)^1679
        have hw : |(3168381631/10000000000 : ℝ)|=(3168381631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1422_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (999/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13153/50000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4381/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4381 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4381*1^1024 ≤ 0^1024*1^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4381/1024 : ℝ) ≤ (495935487884929683/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4381 ≤ (495935487884929683/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4381*25000000000000000000^1024 ≤ 495935487884929683^1024*5^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 495935487884929683 25000000000000000000 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (495935487884929683/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4381 := by
      have hnat : (1 : ℕ)^1024*1^4381 ≤ 1^4381*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25495935487884929683/25000000000000000000 : ℝ) ≤ (2511504740159749/2500000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (25495935487884929683/25000000000000000000 : ℝ)^1024 ≤ (2511504740159749/2500000000000000 : ℝ)^4381 := by
      have hnat : (25495935487884929683 : ℕ)^1024*2500000000000000^4381 ≤ 2511504740159749^4381*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25495935487884929683 25000000000000000000 2511504740159749 2500000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511504740159749/2500000000000000 : ℝ)) (X := (25495935487884929683/25000000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12995935487884929683/12500000000000000000 : ℝ) ≤ (1261504740159749/1250000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (12995935487884929683/12500000000000000000 : ℝ)^1024 ≤ (1261504740159749/1250000000000000 : ℝ)^4381 := by
      have hnat : (12995935487884929683 : ℕ)^1024*1250000000000000^4381 ≤ 1261504740159749^4381*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12995935487884929683 12500000000000000000 1261504740159749 1250000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1261504740159749/1250000000000000 : ℝ)) (X := (12995935487884929683/12500000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11504740159749/1000000000000000 : ℝ)*(0 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11504740159749/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(495935487884929683/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11504740159749/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4381/1024 : ℝ) := by
    rw [show (1 : ℝ)+(11504740159749/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2511504740159749/2500000000000000 : ℝ) by norm_num, show 1+(495935487884929683/25000000000000000000 : ℝ)+(0 : ℝ)=(25495935487884929683/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(495935487884929683/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11504740159749/1000000000000000 : ℝ)*(2/5 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11504740159749/1000000000000000 : ℝ)*(2/5 : ℝ)=(1261504740159749/1250000000000000 : ℝ) by norm_num, show 1+2*(495935487884929683/25000000000000000000 : ℝ)=(12995935487884929683/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11504740159749/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11504740159749/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11504740159749/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11504740159749/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11504740159749/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11504740159749/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-881391847/5000000000 : ℝ)*X 0 0+(5963075001/10000000000 : ℝ)*X 0 1+(4829634369/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1098575613/2000000000 : ℝ)*X 1 0+(-96134867/400000000 : ℝ)*X 1 1+(1207408691/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5492878427/10000000000 : ℝ)*X 2 0+(24148173/50000000 : ℝ)*X 2 1+(-2403371413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2083503209/5000000000 : ℝ)*X 0 0+(3103536211/10000000000 : ℝ)*X 0 1+(5549260567/10000000000 : ℝ)*X 0 2+(2083503209/5000000000 : ℝ)*X 1 0+(3103536211/10000000000 : ℝ)*X 1 1+(5549260567/10000000000 : ℝ)*X 1 2+(2083503209/5000000000 : ℝ)*X 2 0+(3103536211/10000000000 : ℝ)*X 2 1+(5549260567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-70673393/400000000 : ℝ)*X 0 0+(4858649957/10000000000 : ℝ)*X 0 1+(5933023361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5183549483/10000000000 : ℝ)*X 1 0+(-649991249/5000000000 : ℝ)*X 1 1+(5933023443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5183549501/10000000000 : ℝ)*X 2 0+(5933023271/10000000000 : ℝ)*X 2 1+(-649991371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2087874933/5000000000 : ℝ)*X 0 0+(5486650947/10000000000 : ℝ)*X 0 1+(3168381631/10000000000 : ℝ)*X 0 2+(2087874933/5000000000 : ℝ)*X 1 0+(5486650947/10000000000 : ℝ)*X 1 1+(3168381631/10000000000 : ℝ)*X 1 2+(2087874933/5000000000 : ℝ)*X 2 0+(5486650947/10000000000 : ℝ)*X 2 1+(3168381631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34447647584329764708033/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1333276491/100000000000000 : ℝ)*(base19) + (135635561/10000000000000 : ℝ)*(base23) + (149164901/100000000000000 : ℝ)*(upper3) + (19261373/100000000000000 : ℝ)*(upper4) + (102774441/50000000000000 : ℝ)*(upper5) + (161395083905761/25000000000000 : ℝ)*(major0) + (161395083905761/25000000000000 : ℝ)*(major1) + (161395083905761/25000000000000 : ℝ)*(major2) + (882273832190701/100000000000000 : ℝ)*(sp0) + (176455542094787/20000000000000 : ℝ)*(sp1) + (1723198608193/195312500000 : ℝ)*(sp2) + (51109891099589/12500000000000 : ℝ)*(sp3) + (1302889931/25000000000000 : ℝ)*(sp4) + (578744539/25000000000000 : ℝ)*(sp7) + (102220360943717/25000000000000 : ℝ)*(f.failure) + (441139521875213/50000000000000 : ℝ)*(f.sum) + (52073414938989/12500000000000000000000000000 : ℝ)*base65 + (78947263088989/25000000000000000000000000000 : ℝ)*base67 + (129365422088989/25000000000000000000000000000 : ℝ)*base69 + (154391989238989/25000000000000000000000000000 : ℝ)*base71 + (10017259073511/12500000000000000000000000000 : ℝ)*base74 + (9168610586011/25000000000000000000000000000 : ℝ)*base76 + (3665477186011/25000000000000000000000000000 : ℝ)*base78 + (76423862313989/25000000000000000000000000000 : ℝ)*base79 + (12082087263989/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1741171/250000000000000000000 : ℝ)*base90 + (1741171/250000000000000000000 : ℝ)*base92 + (1741171/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56940853224516175634661/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (253724971/50000000000000 : ℝ)*(base19) + (510589223/100000000000000 : ℝ)*(base23) + (10521541/10000000000000 : ℝ)*(base32) + (17028623/20000000000000 : ℝ)*(upper3) + (2998797/12500000000000 : ℝ)*(upper5) + (681065409051879/100000000000000 : ℝ)*(major0) + (681065409051879/100000000000000 : ℝ)*(major1) + (681065409051879/100000000000000 : ℝ)*(major2) + (1167928773/100000000000000 : ℝ)*(sp1) + (72898217/6250000000000 : ℝ)*(sp2) + (116346831832043/12500000000000 : ℝ)*(sp4) + (930772979277629/100000000000000 : ℝ)*(sp5) + (930772977695649/100000000000000 : ℝ)*(sp6) + (431355982310861/100000000000000 : ℝ)*(sp7) + (3369969433799/781250000000 : ℝ)*(f.failure) + (116346831832043/12500000000000 : ℝ)*(f.sum) + (72201347318371/50000000000000000000000000000 : ℝ)*base65 + (394495831118371/100000000000000000000000000000 : ℝ)*base67 + (502132441118371/100000000000000000000000000000 : ℝ)*base69 + (192279620818371/100000000000000000000000000000 : ℝ)*base71 + (286167421118371/50000000000000000000000000000 : ℝ)*base73 + (138105537618371/100000000000000000000000000000 : ℝ)*base75 + (221242056718371/100000000000000000000000000000 : ℝ)*base77 + (247375644018371/100000000000000000000000000000 : ℝ)*base79 + (254828348768371/50000000000000000000000000000 : ℝ)*base81 + (8697/1953125000000000000 : ℝ)*base89 + (8697/1953125000000000000 : ℝ)*base91 + (8697/1953125000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1422_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (999/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13153/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1422_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1422_s1_0 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1936136491/10000000000 : ℝ)*x 0 + (5608034841/10000000000 : ℝ)*x 1 + (5073553287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1936136491/10000000000 : ℝ)^2191 ≤ (11735234906121/100000000000000 : ℝ)^1679 := by
    have hnat : (1936136491 : ℕ)^2191*100000000000000^1679 ≤ 11735234906121^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936136491 10000000000 11735234906121 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5608034841/10000000000 : ℝ)^2191 ≤ (23506186876023/50000000000000 : ℝ)^1679 := by
    have hnat : (5608034841 : ℕ)^2191*50000000000000^1679 ≤ 23506186876023^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5608034841 10000000000 23506186876023 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5073553287/10000000000 : ℝ)^2191 ≤ (4125239132417/10000000000000 : ℝ)^1679 := by
    have hnat : (5073553287 : ℕ)^2191*10000000000000^1679 ≤ 4125239132417^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073553287 10000000000 4125239132417 10000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1936136491/10000000000 : ℝ), (5608034841/10000000000 : ℝ), (5073553287/10000000000 : ℝ)] ![(11735234906121/100000000000000 : ℝ), (23506186876023/50000000000000 : ℝ), (4125239132417/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1936136491/10000000000 : ℝ)|^2191 ≤ (11735234906121/100000000000000 : ℝ)^1679
        have hw : |(-1936136491/10000000000 : ℝ)|=(1936136491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5608034841/10000000000 : ℝ)|^2191 ≤ (23506186876023/50000000000000 : ℝ)^1679
        have hw : |(5608034841/10000000000 : ℝ)|=(5608034841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5073553287/10000000000 : ℝ)|^2191 ≤ (4125239132417/10000000000000 : ℝ)^1679
        have hw : |(5073553287/10000000000 : ℝ)|=(5073553287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s1_1 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1079502187/2000000000 : ℝ)*x 0 + (-1109751357/5000000000 : ℝ)*x 1 + (5073554381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079502187/2000000000 : ℝ)^2191 ≤ (44722668663989/100000000000000 : ℝ)^1679 := by
    have hnat : (1079502187 : ℕ)^2191*100000000000000^1679 ≤ 44722668663989^1679*2000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079502187 2000000000 44722668663989 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1109751357/5000000000 : ℝ)^2191 ≤ (14024928395767/100000000000000 : ℝ)^1679 := by
    have hnat : (1109751357 : ℕ)^2191*100000000000000^1679 ≤ 14024928395767^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109751357 5000000000 14024928395767 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5073554381/10000000000 : ℝ)^2191 ≤ (41252402931863/100000000000000 : ℝ)^1679 := by
    have hnat : (5073554381 : ℕ)^2191*100000000000000^1679 ≤ 41252402931863^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073554381 10000000000 41252402931863 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079502187/2000000000 : ℝ), (-1109751357/5000000000 : ℝ), (5073554381/10000000000 : ℝ)] ![(44722668663989/100000000000000 : ℝ), (14024928395767/100000000000000 : ℝ), (41252402931863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079502187/2000000000 : ℝ)|^2191 ≤ (44722668663989/100000000000000 : ℝ)^1679
        have hw : |(1079502187/2000000000 : ℝ)|=(1079502187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1109751357/5000000000 : ℝ)|^2191 ≤ (14024928395767/100000000000000 : ℝ)^1679
        have hw : |(-1109751357/5000000000 : ℝ)|=(1109751357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5073554381/10000000000 : ℝ)|^2191 ≤ (41252402931863/100000000000000 : ℝ)^1679
        have hw : |(5073554381/10000000000 : ℝ)|=(5073554381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s1_2 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5397511807/10000000000 : ℝ)*x 0 + (507355341/1000000000 : ℝ)*x 1 + (-110975141/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397511807/10000000000 : ℝ)^2191 ≤ (11180669523121/25000000000000 : ℝ)^1679 := by
    have hnat : (5397511807 : ℕ)^2191*25000000000000^1679 ≤ 11180669523121^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397511807 10000000000 11180669523121 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507355341/1000000000 : ℝ)^2191 ≤ (41252392629239/100000000000000 : ℝ)^1679 := by
    have hnat : (507355341 : ℕ)^2191*100000000000000^1679 ≤ 41252392629239^1679*1000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507355341 1000000000 41252392629239 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110975141/500000000 : ℝ)^2191 ≤ (1402492926983/10000000000000 : ℝ)^1679 := by
    have hnat : (110975141 : ℕ)^2191*10000000000000^1679 ≤ 1402492926983^1679*500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110975141 500000000 1402492926983 10000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397511807/10000000000 : ℝ), (507355341/1000000000 : ℝ), (-110975141/500000000 : ℝ)] ![(11180669523121/25000000000000 : ℝ), (41252392629239/100000000000000 : ℝ), (1402492926983/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397511807/10000000000 : ℝ)|^2191 ≤ (11180669523121/25000000000000 : ℝ)^1679
        have hw : |(5397511807/10000000000 : ℝ)|=(5397511807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(507355341/1000000000 : ℝ)|^2191 ≤ (41252392629239/100000000000000 : ℝ)^1679
        have hw : |(507355341/1000000000 : ℝ)|=(507355341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-110975141/500000000 : ℝ)|^2191 ≤ (1402492926983/10000000000000 : ℝ)^1679
        have hw : |(-110975141/500000000 : ℝ)|=(110975141/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s1_3 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (42779119/100000000 : ℝ)*x 0 + (747212313/2000000000 : ℝ)*x 1 + (4889357051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42779119/100000000 : ℝ)^2191 ≤ (8255025526691/25000000000000 : ℝ)^1679 := by
    have hnat : (42779119 : ℕ)^2191*25000000000000^1679 ≤ 8255025526691^1679*100000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42779119 100000000 8255025526691 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (747212313/2000000000 : ℝ)^2191 ≤ (6917744274593/25000000000000 : ℝ)^1679 := by
    have hnat : (747212313 : ℕ)^2191*25000000000000^1679 ≤ 6917744274593^1679*2000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747212313 2000000000 6917744274593 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4889357051/10000000000 : ℝ)^2191 ≤ (2456807549167/6250000000000 : ℝ)^1679 := by
    have hnat : (4889357051 : ℕ)^2191*6250000000000^1679 ≤ 2456807549167^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4889357051 10000000000 2456807549167 6250000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42779119/100000000 : ℝ), (747212313/2000000000 : ℝ), (4889357051/10000000000 : ℝ)] ![(8255025526691/25000000000000 : ℝ), (6917744274593/25000000000000 : ℝ), (2456807549167/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42779119/100000000 : ℝ)|^2191 ≤ (8255025526691/25000000000000 : ℝ)^1679
        have hw : |(42779119/100000000 : ℝ)|=(42779119/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(747212313/2000000000 : ℝ)|^2191 ≤ (6917744274593/25000000000000 : ℝ)^1679
        have hw : |(747212313/2000000000 : ℝ)|=(747212313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4889357051/10000000000 : ℝ)|^2191 ≤ (2456807549167/6250000000000 : ℝ)^1679
        have hw : |(4889357051/10000000000 : ℝ)|=(4889357051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s1_4 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-968272069/5000000000 : ℝ)*x 0 + (203194203/400000000 : ℝ)*x 1 + (2800812797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (968272069/5000000000 : ℝ)^2191 ≤ (2934614820549/25000000000000 : ℝ)^1679 := by
    have hnat : (968272069 : ℕ)^2191*25000000000000^1679 ≤ 2934614820549^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968272069 5000000000 2934614820549 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203194203/400000000 : ℝ)^2191 ≤ (10329816996599/25000000000000 : ℝ)^1679 := by
    have hnat : (203194203 : ℕ)^2191*25000000000000^1679 ≤ 10329816996599^1679*400000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203194203 400000000 10329816996599 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2800812797/5000000000 : ℝ)^2191 ≤ (23471136355903/50000000000000 : ℝ)^1679 := by
    have hnat : (2800812797 : ℕ)^2191*50000000000000^1679 ≤ 23471136355903^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2800812797 5000000000 23471136355903 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-968272069/5000000000 : ℝ), (203194203/400000000 : ℝ), (2800812797/5000000000 : ℝ)] ![(2934614820549/25000000000000 : ℝ), (10329816996599/25000000000000 : ℝ), (23471136355903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-968272069/5000000000 : ℝ)|^2191 ≤ (2934614820549/25000000000000 : ℝ)^1679
        have hw : |(-968272069/5000000000 : ℝ)|=(968272069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(203194203/400000000 : ℝ)|^2191 ≤ (10329816996599/25000000000000 : ℝ)^1679
        have hw : |(203194203/400000000 : ℝ)|=(203194203/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2800812797/5000000000 : ℝ)|^2191 ≤ (23471136355903/50000000000000 : ℝ)^1679
        have hw : |(2800812797/5000000000 : ℝ)|=(2800812797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s1_5 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (105158773/200000000 : ℝ)*x 0 + (-1691430993/10000000000 : ℝ)*x 1 + (1120325121/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105158773/200000000 : ℝ)^2191 ≤ (21609765158999/50000000000000 : ℝ)^1679 := by
    have hnat : (105158773 : ℕ)^2191*50000000000000^1679 ≤ 21609765158999^1679*200000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105158773 200000000 21609765158999 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1691430993/10000000000 : ℝ)^2191 ≤ (4919098415687/50000000000000 : ℝ)^1679 := by
    have hnat : (1691430993 : ℕ)^2191*50000000000000^1679 ≤ 4919098415687^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691430993 10000000000 4919098415687 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120325121/2000000000 : ℝ)^2191 ≤ (46942272832097/100000000000000 : ℝ)^1679 := by
    have hnat : (1120325121 : ℕ)^2191*100000000000000^1679 ≤ 46942272832097^1679*2000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120325121 2000000000 46942272832097 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105158773/200000000 : ℝ), (-1691430993/10000000000 : ℝ), (1120325121/2000000000 : ℝ)] ![(21609765158999/50000000000000 : ℝ), (4919098415687/50000000000000 : ℝ), (46942272832097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105158773/200000000 : ℝ)|^2191 ≤ (21609765158999/50000000000000 : ℝ)^1679
        have hw : |(105158773/200000000 : ℝ)|=(105158773/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1691430993/10000000000 : ℝ)|^2191 ≤ (4919098415687/50000000000000 : ℝ)^1679
        have hw : |(-1691430993/10000000000 : ℝ)|=(1691430993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1120325121/2000000000 : ℝ)|^2191 ≤ (46942272832097/100000000000000 : ℝ)^1679
        have hw : |(1120325121/2000000000 : ℝ)|=(1120325121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s1_6 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2628969309/5000000000 : ℝ)*x 0 + (5601625569/10000000000 : ℝ)*x 1 + (-1691431091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628969309/5000000000 : ℝ)^2191 ≤ (1350610311711/3125000000000 : ℝ)^1679 := by
    have hnat : (2628969309 : ℕ)^2191*3125000000000^1679 ≤ 1350610311711^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628969309 5000000000 1350610311711 3125000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5601625569/10000000000 : ℝ)^2191 ≤ (2933892027401/6250000000000 : ℝ)^1679 := by
    have hnat : (5601625569 : ℕ)^2191*6250000000000^1679 ≤ 2933892027401^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5601625569 10000000000 2933892027401 6250000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1691431091/10000000000 : ℝ)^2191 ≤ (9838197575213/100000000000000 : ℝ)^1679 := by
    have hnat : (1691431091 : ℕ)^2191*100000000000000^1679 ≤ 9838197575213^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691431091 10000000000 9838197575213 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628969309/5000000000 : ℝ), (5601625569/10000000000 : ℝ), (-1691431091/10000000000 : ℝ)] ![(1350610311711/3125000000000 : ℝ), (2933892027401/6250000000000 : ℝ), (9838197575213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628969309/5000000000 : ℝ)|^2191 ≤ (1350610311711/3125000000000 : ℝ)^1679
        have hw : |(2628969309/5000000000 : ℝ)|=(2628969309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5601625569/10000000000 : ℝ)|^2191 ≤ (2933892027401/6250000000000 : ℝ)^1679
        have hw : |(5601625569/10000000000 : ℝ)|=(5601625569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1691431091/10000000000 : ℝ)|^2191 ≤ (9838197575213/100000000000000 : ℝ)^1679
        have hw : |(-1691431091/10000000000 : ℝ)|=(1691431091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s1_7 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534848971/1250000000 : ℝ)*x 0 + (975152013/2000000000 : ℝ)*x 1 + (1874945003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534848971/1250000000 : ℝ)^2191 ≤ (33028964875123/100000000000000 : ℝ)^1679 := by
    have hnat : (534848971 : ℕ)^2191*100000000000000^1679 ≤ 33028964875123^1679*1250000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534848971 1250000000 33028964875123 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (975152013/2000000000 : ℝ)^2191 ≤ (39166330679879/100000000000000 : ℝ)^1679 := by
    have hnat : (975152013 : ℕ)^2191*100000000000000^1679 ≤ 39166330679879^1679*2000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975152013 2000000000 39166330679879 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1874945003/5000000000 : ℝ)^2191 ≤ (3475588054119/12500000000000 : ℝ)^1679 := by
    have hnat : (1874945003 : ℕ)^2191*12500000000000^1679 ≤ 3475588054119^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874945003 5000000000 3475588054119 12500000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534848971/1250000000 : ℝ), (975152013/2000000000 : ℝ), (1874945003/5000000000 : ℝ)] ![(33028964875123/100000000000000 : ℝ), (39166330679879/100000000000000 : ℝ), (3475588054119/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534848971/1250000000 : ℝ)|^2191 ≤ (33028964875123/100000000000000 : ℝ)^1679
        have hw : |(534848971/1250000000 : ℝ)|=(534848971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(975152013/2000000000 : ℝ)|^2191 ≤ (39166330679879/100000000000000 : ℝ)^1679
        have hw : |(975152013/2000000000 : ℝ)|=(975152013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1874945003/5000000000 : ℝ)|^2191 ≤ (3475588054119/12500000000000 : ℝ)^1679
        have hw : |(1874945003/5000000000 : ℝ)|=(1874945003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1422_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13153/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (999/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3797/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18893/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13153/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (999/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13153/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (999/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13153/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (999/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13153/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (999/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13153/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (999/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13153/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (999/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (999/50000 : ℝ) ^ (4381/1024 : ℝ) ≤ (5362942487289/100000000000000000000 : ℝ) := by
    have hpowers : (999/50000 : ℝ)^4381 ≤ (5362942487289/100000000000000000000 : ℝ)^1024 := by
      have hnat : (999 : ℕ)^4381*100000000000000000000^1024 ≤ 5362942487289^1024*50000^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        999 50000 5362942487289 100000000000000000000 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (999/50000 : ℝ)) (X := (5362942487289/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13153/50000 : ℝ) ^ (4381/1024 : ℝ) ≤ (41278009933050211/12500000000000000000 : ℝ) := by
    have hpowers : (13153/50000 : ℝ)^4381 ≤ (41278009933050211/12500000000000000000 : ℝ)^1024 := by
      have hnat : (13153 : ℕ)^4381*12500000000000000000^1024 ≤ 41278009933050211^1024*50000^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13153 50000 41278009933050211 12500000000000000000 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13153/50000 : ℝ)) (X := (41278009933050211/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000005362942487289/50000000000000000000 : ℝ) ≤ (156250003917237/156250000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (50000005362942487289/50000000000000000000 : ℝ)^1024 ≤ (156250003917237/156250000000000 : ℝ)^4381 := by
      have hnat : (50000005362942487289 : ℕ)^1024*156250000000000^4381 ≤ 156250003917237^4381*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000005362942487289 50000000000000000000 156250003917237 156250000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156250003917237/156250000000000 : ℝ)) (X := (50000005362942487289/50000000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100330229442406888977/100000000000000000000 : ℝ) ≤ (5003854461774461/5000000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (100330229442406888977/100000000000000000000 : ℝ)^1024 ≤ (5003854461774461/5000000000000000 : ℝ)^4381 := by
      have hnat : (100330229442406888977 : ℕ)^1024*5000000000000000^4381 ≤ 5003854461774461^4381*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100330229442406888977 100000000000000000000 5003854461774461 5000000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003854461774461/5000000000000000 : ℝ)) (X := (100330229442406888977/100000000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6291278009933050211/6250000000000000000 : ℝ) ≤ (2503854399098669/2500000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (6291278009933050211/6250000000000000000 : ℝ)^1024 ≤ (2503854399098669/2500000000000000 : ℝ)^4381 := by
      have hnat : (6291278009933050211 : ℕ)^1024*2500000000000000^4381 ≤ 2503854399098669^4381*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6291278009933050211 6250000000000000000 2503854399098669 2500000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503854399098669/2500000000000000 : ℝ)) (X := (6291278009933050211/6250000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5362942487289/100000000000000000000 : ℝ) ≤ ((6076230055935024369/6077000000000000000 : ℝ)+2*(3854336422877/1215400000000000 : ℝ)*(999/50000 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (6076230055935024369/6077000000000000000 : ℝ)+2*(3854336422877/1215400000000000 : ℝ)*(999/50000 : ℝ)=(156250003917237/156250000000000 : ℝ) by norm_num, show 1+2*(5362942487289/100000000000000000000 : ℝ)=(50000005362942487289/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(41278009933050211/12500000000000000000 : ℝ)+(5362942487289/100000000000000000000 : ℝ) ≤ ((6076230055935024369/6077000000000000000 : ℝ)+(3854336422877/1215400000000000 : ℝ)*((13153/50000 : ℝ)+(999/50000 : ℝ)))^(4381/1024 : ℝ) := by
    rw [show (6076230055935024369/6077000000000000000 : ℝ)+(3854336422877/1215400000000000 : ℝ)*((13153/50000 : ℝ)+(999/50000 : ℝ))=(5003854461774461/5000000000000000 : ℝ) by norm_num, show 1+(41278009933050211/12500000000000000000 : ℝ)+(5362942487289/100000000000000000000 : ℝ)=(100330229442406888977/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(41278009933050211/12500000000000000000 : ℝ) ≤ ((6076230055935024369/6077000000000000000 : ℝ)+2*(3854336422877/1215400000000000 : ℝ)*(13153/50000 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (6076230055935024369/6077000000000000000 : ℝ)+2*(3854336422877/1215400000000000 : ℝ)*(13153/50000 : ℝ)=(2503854399098669/2500000000000000 : ℝ) by norm_num, show 1+2*(41278009933050211/12500000000000000000 : ℝ)=(6291278009933050211/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6076230055935024369/6077000000000000000 : ℝ)*(X 1 0+X 2 0)+(3854336422877/1215400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (999/50000 : ℝ)) (hi := (13153/50000 : ℝ)) (c := (6076230055935024369/6077000000000000000 : ℝ)) (alpha := (3854336422877/1215400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6076230055935024369/6077000000000000000 : ℝ)*(X 0 1+X 2 1)+(3854336422877/1215400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (999/50000 : ℝ)) (hi := (13153/50000 : ℝ)) (c := (6076230055935024369/6077000000000000000 : ℝ)) (alpha := (3854336422877/1215400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6076230055935024369/6077000000000000000 : ℝ)*(X 0 2+X 1 2)+(3854336422877/1215400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (999/50000 : ℝ)) (hi := (13153/50000 : ℝ)) (c := (6076230055935024369/6077000000000000000 : ℝ)) (alpha := (3854336422877/1215400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1936136491/10000000000 : ℝ)*X 0 0+(5608034841/10000000000 : ℝ)*X 0 1+(5073553287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1079502187/2000000000 : ℝ)*X 1 0+(-1109751357/5000000000 : ℝ)*X 1 1+(5073554381/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5397511807/10000000000 : ℝ)*X 2 0+(507355341/1000000000 : ℝ)*X 2 1+(-110975141/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((42779119/100000000 : ℝ)*X 0 0+(747212313/2000000000 : ℝ)*X 0 1+(4889357051/10000000000 : ℝ)*X 0 2+(42779119/100000000 : ℝ)*X 1 0+(747212313/2000000000 : ℝ)*X 1 1+(4889357051/10000000000 : ℝ)*X 1 2+(42779119/100000000 : ℝ)*X 2 0+(747212313/2000000000 : ℝ)*X 2 1+(4889357051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-968272069/5000000000 : ℝ)*X 0 0+(203194203/400000000 : ℝ)*X 0 1+(2800812797/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((105158773/200000000 : ℝ)*X 1 0+(-1691430993/10000000000 : ℝ)*X 1 1+(1120325121/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2628969309/5000000000 : ℝ)*X 2 0+(5601625569/10000000000 : ℝ)*X 2 1+(-1691431091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((534848971/1250000000 : ℝ)*X 0 0+(975152013/2000000000 : ℝ)*X 0 1+(1874945003/5000000000 : ℝ)*X 0 2+(534848971/1250000000 : ℝ)*X 1 0+(975152013/2000000000 : ℝ)*X 1 1+(1874945003/5000000000 : ℝ)*X 1 2+(534848971/1250000000 : ℝ)*X 2 0+(975152013/2000000000 : ℝ)*X 2 1+(1874945003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (67441747229130837501200181/15192500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (675860673/100000000000000 : ℝ)*(base19) + (977028517/100000000000000 : ℝ)*(base23) + (36201267/50000000000000 : ℝ)*(upper3) + (594429/100000000000000 : ℝ)*(upper4) + (91215479/100000000000000 : ℝ)*(upper5) + (68451878589661/5000000000000 : ℝ)*(major0) + (68451878589661/5000000000000 : ℝ)*(major1) + (68451878589661/5000000000000 : ℝ)*(major2) + (1870979584331019/100000000000000 : ℝ)*(sp0) + (1870987718678233/100000000000000 : ℝ)*(sp1) + (467746854377597/25000000000000 : ℝ)*(sp2) + (867083378413719/100000000000000 : ℝ)*(sp3) + (8810207887/100000000000000 : ℝ)*(sp4) + (201416389/6250000000000 : ℝ)*(sp7) + (108385825134493/12500000000000 : ℝ)*(f.failure) + (935494197269453/50000000000000 : ℝ)*(f.sum) + (1766547614713/243080000000000000000000000 : ℝ)*base65 + (134781855365181091/30385000000000000000000000000000 : ℝ)*base68 + (142657071417506091/30385000000000000000000000000000 : ℝ)*base70 + (111525227655061091/30385000000000000000000000000000 : ℝ)*base72 + (23119810928053/6077000000000000000000000000 : ℝ)*base73 + (481240755662676091/30385000000000000000000000000000 : ℝ)*base76 + (154403727190546091/30385000000000000000000000000000 : ℝ)*base78 + (254401935871941091/30385000000000000000000000000000 : ℝ)*base80 + (42674676748713/6077000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1503941/125000000000000000000 : ℝ)*base89 + (1503941/125000000000000000000 : ℝ)*base91 + (1503941/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (132029393647751020429026837/18990625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60208659/100000000000000 : ℝ)*(base1) + (721980039/50000000000000 : ℝ)*(base19) + (14261337/1000000000000 : ℝ)*(base23) + (166762857/100000000000000 : ℝ)*(upper3) + (150458191/100000000000000 : ℝ)*(upper5) + (175297084827641/12500000000000 : ℝ)*(major0) + (175297084827641/12500000000000 : ℝ)*(major1) + (175297084827641/12500000000000 : ℝ)*(major2) + (8270218033/100000000000000 : ℝ)*(sp1) + (8038025223/100000000000000 : ℝ)*(sp2) + (1916551099257077/100000000000000 : ℝ)*(sp4) + (479135331217577/25000000000000 : ℝ)*(sp5) + (239567696861187/12500000000000 : ℝ)*(sp6) + (222050506560077/25000000000000 : ℝ)*(sp7) + (444101043224483/50000000000000 : ℝ)*(f.failure) + (1916551039048419/100000000000000 : ℝ)*(f.sum) + (30667087917901/15192500000000000000000000000 : ℝ)*base66 + (93182016387881029/75962500000000000000000000000000 : ℝ)*base67 + (274793611173456471/75962500000000000000000000000000 : ℝ)*base70 + (737761425323468971/75962500000000000000000000000000 : ℝ)*base72 + (55520227473119/15192500000000000000000000000 : ℝ)*base73 + (794419663466893971/75962500000000000000000000000000 : ℝ)*base76 + (706234665953693971/75962500000000000000000000000000 : ℝ)*base78 + (486614517370656471/75962500000000000000000000000000 : ℝ)*base80 + (3226469691731/949531250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1055429/500000000000000000000 : ℝ)*base90 + (1055429/500000000000000000000 : ℝ)*base92 + (1055429/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1422_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13153/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (999/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3797/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18893/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1422_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1422_s2_0 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1969789229/10000000000 : ℝ)*x 0 + (2729875669/5000000000 : ℝ)*x 1 + (1300045919/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1969789229/10000000000 : ℝ)^2191 ≤ (93766506941/781250000000 : ℝ)^1679 := by
    have hnat : (1969789229 : ℕ)^2191*781250000000^1679 ≤ 93766506941^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1969789229 10000000000 93766506941 781250000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729875669/5000000000 : ℝ)^2191 ≤ (11349205674063/25000000000000 : ℝ)^1679 := by
    have hnat : (2729875669 : ℕ)^2191*25000000000000^1679 ≤ 11349205674063^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729875669 5000000000 11349205674063 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1300045919/2500000000 : ℝ)^2191 ≤ (21300532198961/50000000000000 : ℝ)^1679 := by
    have hnat : (1300045919 : ℕ)^2191*50000000000000^1679 ≤ 21300532198961^1679*2500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300045919 2500000000 21300532198961 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1969789229/10000000000 : ℝ), (2729875669/5000000000 : ℝ), (1300045919/2500000000 : ℝ)] ![(93766506941/781250000000 : ℝ), (11349205674063/25000000000000 : ℝ), (21300532198961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1969789229/10000000000 : ℝ)|^2191 ≤ (93766506941/781250000000 : ℝ)^1679
        have hw : |(-1969789229/10000000000 : ℝ)|=(1969789229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729875669/5000000000 : ℝ)|^2191 ≤ (11349205674063/25000000000000 : ℝ)^1679
        have hw : |(2729875669/5000000000 : ℝ)|=(2729875669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1300045919/2500000000 : ℝ)|^2191 ≤ (21300532198961/50000000000000 : ℝ)^1679
        have hw : |(1300045919/2500000000 : ℝ)|=(1300045919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s2_1 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (670073207/1250000000 : ℝ)*x 0 + (-420675423/2000000000 : ℝ)*x 1 + (13000459/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670073207/1250000000 : ℝ)^2191 ≤ (4432383144123/10000000000000 : ℝ)^1679 := by
    have hnat : (670073207 : ℕ)^2191*10000000000000^1679 ≤ 4432383144123^1679*1250000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670073207 1250000000 4432383144123 10000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420675423/2000000000 : ℝ)^2191 ≤ (13075104956139/100000000000000 : ℝ)^1679 := by
    have hnat : (420675423 : ℕ)^2191*100000000000000^1679 ≤ 13075104956139^1679*2000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420675423 2000000000 13075104956139 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13000459/25000000 : ℝ)^2191 ≤ (10650265896363/25000000000000 : ℝ)^1679 := by
    have hnat : (13000459 : ℕ)^2191*25000000000000^1679 ≤ 10650265896363^1679*25000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13000459 25000000 10650265896363 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670073207/1250000000 : ℝ), (-420675423/2000000000 : ℝ), (13000459/25000000 : ℝ)] ![(4432383144123/10000000000000 : ℝ), (13075104956139/100000000000000 : ℝ), (10650265896363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670073207/1250000000 : ℝ)|^2191 ≤ (4432383144123/10000000000000 : ℝ)^1679
        have hw : |(670073207/1250000000 : ℝ)|=(670073207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420675423/2000000000 : ℝ)|^2191 ≤ (13075104956139/100000000000000 : ℝ)^1679
        have hw : |(-420675423/2000000000 : ℝ)|=(420675423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13000459/25000000 : ℝ)|^2191 ≤ (10650265896363/25000000000000 : ℝ)^1679
        have hw : |(13000459/25000000 : ℝ)|=(13000459/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s2_2 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167518291/312500000 : ℝ)*x 0 + (1300045997/2500000000 : ℝ)*x 1 + (-2103377061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167518291/312500000 : ℝ)^2191 ≤ (4432382772951/10000000000000 : ℝ)^1679 := by
    have hnat : (167518291 : ℕ)^2191*10000000000000^1679 ≤ 4432382772951^1679*312500000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167518291 312500000 4432382772951 10000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1300045997/2500000000 : ℝ)^2191 ≤ (42601067733323/100000000000000 : ℝ)^1679 := by
    have hnat : (1300045997 : ℕ)^2191*100000000000000^1679 ≤ 42601067733323^1679*2500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300045997 2500000000 42601067733323 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2103377061/10000000000 : ℝ)^2191 ≤ (13075104518099/100000000000000 : ℝ)^1679 := by
    have hnat : (2103377061 : ℕ)^2191*100000000000000^1679 ≤ 13075104518099^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103377061 10000000000 13075104518099 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167518291/312500000 : ℝ), (1300045997/2500000000 : ℝ), (-2103377061/10000000000 : ℝ)] ![(4432382772951/10000000000000 : ℝ), (42601067733323/100000000000000 : ℝ), (13075104518099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167518291/312500000 : ℝ)|^2191 ≤ (4432382772951/10000000000000 : ℝ)^1679
        have hw : |(167518291/312500000 : ℝ)|=(167518291/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1300045997/2500000000 : ℝ)|^2191 ≤ (42601067733323/100000000000000 : ℝ)^1679
        have hw : |(1300045997/2500000000 : ℝ)|=(1300045997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2103377061/10000000000 : ℝ)|^2191 ≤ (13075104518099/100000000000000 : ℝ)^1679
        have hw : |(-2103377061/10000000000 : ℝ)|=(2103377061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s2_3 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1075413071/2500000000 : ℝ)*x 0 + (2014906959/5000000000 : ℝ)*x 1 + (1147476419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075413071/2500000000 : ℝ)^2191 ≤ (16629714870097/50000000000000 : ℝ)^1679 := by
    have hnat : (1075413071 : ℕ)^2191*50000000000000^1679 ≤ 16629714870097^1679*2500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075413071 2500000000 16629714870097 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2014906959/5000000000 : ℝ)^2191 ≤ (30543531437721/100000000000000 : ℝ)^1679 := by
    have hnat : (2014906959 : ℕ)^2191*100000000000000^1679 ≤ 30543531437721^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014906959 5000000000 30543531437721 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147476419/2500000000 : ℝ)^2191 ≤ (18098519401589/50000000000000 : ℝ)^1679 := by
    have hnat : (1147476419 : ℕ)^2191*50000000000000^1679 ≤ 18098519401589^1679*2500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147476419 2500000000 18098519401589 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075413071/2500000000 : ℝ), (2014906959/5000000000 : ℝ), (1147476419/2500000000 : ℝ)] ![(16629714870097/50000000000000 : ℝ), (30543531437721/100000000000000 : ℝ), (18098519401589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075413071/2500000000 : ℝ)|^2191 ≤ (16629714870097/50000000000000 : ℝ)^1679
        have hw : |(1075413071/2500000000 : ℝ)|=(1075413071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2014906959/5000000000 : ℝ)|^2191 ≤ (30543531437721/100000000000000 : ℝ)^1679
        have hw : |(2014906959/5000000000 : ℝ)|=(2014906959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1147476419/2500000000 : ℝ)|^2191 ≤ (18098519401589/50000000000000 : ℝ)^1679
        have hw : |(1147476419/2500000000 : ℝ)|=(1147476419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s2_4 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1969836181/10000000000 : ℝ)*x 0 + (520167901/1000000000 : ℝ)*x 1 + (5458243517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1969836181/10000000000 : ℝ)^2191 ≤ (1500310776491/12500000000000 : ℝ)^1679 := by
    have hnat : (1969836181 : ℕ)^2191*12500000000000^1679 ≤ 1500310776491^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1969836181 10000000000 1500310776491 12500000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520167901/1000000000 : ℝ)^2191 ≤ (21308525399333/50000000000000 : ℝ)^1679 := by
    have hnat : (520167901 : ℕ)^2191*50000000000000^1679 ≤ 21308525399333^1679*1000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520167901 1000000000 21308525399333 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458243517/10000000000 : ℝ)^2191 ≤ (4538046297971/10000000000000 : ℝ)^1679 := by
    have hnat : (5458243517 : ℕ)^2191*10000000000000^1679 ≤ 4538046297971^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458243517 10000000000 4538046297971 10000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1969836181/10000000000 : ℝ), (520167901/1000000000 : ℝ), (5458243517/10000000000 : ℝ)] ![(1500310776491/12500000000000 : ℝ), (21308525399333/50000000000000 : ℝ), (4538046297971/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1969836181/10000000000 : ℝ)|^2191 ≤ (1500310776491/12500000000000 : ℝ)^1679
        have hw : |(-1969836181/10000000000 : ℝ)|=(1969836181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520167901/1000000000 : ℝ)|^2191 ≤ (21308525399333/50000000000000 : ℝ)^1679
        have hw : |(520167901/1000000000 : ℝ)|=(520167901/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458243517/10000000000 : ℝ)|^2191 ≤ (4538046297971/10000000000000 : ℝ)^1679
        have hw : |(5458243517/10000000000 : ℝ)|=(5458243517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s2_5 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2646567083/5000000000 : ℝ)*x 0 + (-1845317037/10000000000 : ℝ)*x 1 + (218329753/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646567083/5000000000 : ℝ)^2191 ≤ (43597438141193/100000000000000 : ℝ)^1679 := by
    have hnat : (2646567083 : ℕ)^2191*100000000000000^1679 ≤ 43597438141193^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646567083 5000000000 43597438141193 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1845317037/10000000000 : ℝ)^2191 ≤ (5511047760603/50000000000000 : ℝ)^1679 := by
    have hnat : (1845317037 : ℕ)^2191*50000000000000^1679 ≤ 5511047760603^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845317037 10000000000 5511047760603 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218329753/400000000 : ℝ)^2191 ≤ (2269023316067/5000000000000 : ℝ)^1679 := by
    have hnat : (218329753 : ℕ)^2191*5000000000000^1679 ≤ 2269023316067^1679*400000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218329753 400000000 2269023316067 5000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646567083/5000000000 : ℝ), (-1845317037/10000000000 : ℝ), (218329753/400000000 : ℝ)] ![(43597438141193/100000000000000 : ℝ), (5511047760603/50000000000000 : ℝ), (2269023316067/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646567083/5000000000 : ℝ)|^2191 ≤ (43597438141193/100000000000000 : ℝ)^1679
        have hw : |(2646567083/5000000000 : ℝ)|=(2646567083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1845317037/10000000000 : ℝ)|^2191 ≤ (5511047760603/50000000000000 : ℝ)^1679
        have hw : |(-1845317037/10000000000 : ℝ)|=(1845317037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218329753/400000000 : ℝ)|^2191 ≤ (2269023316067/5000000000000 : ℝ)^1679
        have hw : |(218329753/400000000 : ℝ)|=(218329753/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s2_6 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (132328353/250000000 : ℝ)*x 0 + (2729121903/5000000000 : ℝ)*x 1 + (-1845317127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132328353/250000000 : ℝ)^2191 ≤ (43597437646771/100000000000000 : ℝ)^1679 := by
    have hnat : (132328353 : ℕ)^2191*100000000000000^1679 ≤ 43597437646771^1679*250000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132328353 250000000 43597437646771 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729121903/5000000000 : ℝ)^2191 ≤ (45380466115201/100000000000000 : ℝ)^1679 := by
    have hnat : (2729121903 : ℕ)^2191*100000000000000^1679 ≤ 45380466115201^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729121903 5000000000 45380466115201 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1845317127/10000000000 : ℝ)^2191 ≤ (2204419244541/20000000000000 : ℝ)^1679 := by
    have hnat : (1845317127 : ℕ)^2191*20000000000000^1679 ≤ 2204419244541^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845317127 10000000000 2204419244541 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132328353/250000000 : ℝ), (2729121903/5000000000 : ℝ), (-1845317127/10000000000 : ℝ)] ![(43597437646771/100000000000000 : ℝ), (45380466115201/100000000000000 : ℝ), (2204419244541/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132328353/250000000 : ℝ)|^2191 ≤ (43597437646771/100000000000000 : ℝ)^1679
        have hw : |(132328353/250000000 : ℝ)|=(132328353/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729121903/5000000000 : ℝ)|^2191 ≤ (45380466115201/100000000000000 : ℝ)^1679
        have hw : |(2729121903/5000000000 : ℝ)|=(2729121903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1845317127/10000000000 : ℝ)|^2191 ≤ (2204419244541/20000000000000 : ℝ)^1679
        have hw : |(-1845317127/10000000000 : ℝ)|=(1845317127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s2_7 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4301753339/10000000000 : ℝ)*x 0 + (458667923/1000000000 : ℝ)*x 1 + (4033067133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301753339/10000000000 : ℝ)^2191 ≤ (8315112335467/25000000000000 : ℝ)^1679 := by
    have hnat : (4301753339 : ℕ)^2191*25000000000000^1679 ≤ 8315112335467^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301753339 10000000000 8315112335467 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458667923/1000000000 : ℝ)^2191 ≤ (9040959686961/25000000000000 : ℝ)^1679 := by
    have hnat : (458667923 : ℕ)^2191*25000000000000^1679 ≤ 9040959686961^1679*1000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458667923 1000000000 9040959686961 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033067133/10000000000 : ℝ)^2191 ≤ (6115142378051/20000000000000 : ℝ)^1679 := by
    have hnat : (4033067133 : ℕ)^2191*20000000000000^1679 ≤ 6115142378051^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033067133 10000000000 6115142378051 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301753339/10000000000 : ℝ), (458667923/1000000000 : ℝ), (4033067133/10000000000 : ℝ)] ![(8315112335467/25000000000000 : ℝ), (9040959686961/25000000000000 : ℝ), (6115142378051/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301753339/10000000000 : ℝ)|^2191 ≤ (8315112335467/25000000000000 : ℝ)^1679
        have hw : |(4301753339/10000000000 : ℝ)|=(4301753339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(458667923/1000000000 : ℝ)|^2191 ≤ (9040959686961/25000000000000 : ℝ)^1679
        have hw : |(458667923/1000000000 : ℝ)|=(458667923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033067133/10000000000 : ℝ)|^2191 ≤ (6115142378051/20000000000000 : ℝ)^1679
        have hw : |(4033067133/10000000000 : ℝ)|=(4033067133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1422_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18893/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3797/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1033/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15821/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18893/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3797/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18893/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3797/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18893/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3797/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18893/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3797/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18893/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3797/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18893/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3797/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3797/50000 : ℝ) ^ (4381/1024 : ℝ) ≤ (8114552998221/500000000000000000 : ℝ) := by
    have hpowers : (3797/50000 : ℝ)^4381 ≤ (8114552998221/500000000000000000 : ℝ)^1024 := by
      have hnat : (3797 : ℕ)^4381*500000000000000000^1024 ≤ 8114552998221^1024*50000^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3797 50000 8114552998221 500000000000000000 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3797/50000 : ℝ)) (X := (8114552998221/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18893/100000 : ℝ) ^ (4381/1024 : ℝ) ≤ (80127860257802927/100000000000000000000 : ℝ) := by
    have hpowers : (18893/100000 : ℝ)^4381 ≤ (80127860257802927/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18893 : ℕ)^4381*100000000000000000000^1024 ≤ 80127860257802927^1024*100000^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18893 100000 80127860257802927 100000000000000000000 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18893/100000 : ℝ)) (X := (80127860257802927/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (250008114552998221/250000000000000000 : ℝ) ≤ (5000037932887193/5000000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (250008114552998221/250000000000000000 : ℝ)^1024 ≤ (5000037932887193/5000000000000000 : ℝ)^4381 := by
      have hnat : (250008114552998221 : ℕ)^1024*5000000000000000^4381 ≤ 5000037932887193^4381*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250008114552998221 250000000000000000 5000037932887193 5000000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000037932887193/5000000000000000 : ℝ)) (X := (250008114552998221/250000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100081750770857447127/100000000000000000000 : ℝ) ≤ (5000955108217607/5000000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (100081750770857447127/100000000000000000000 : ℝ)^1024 ≤ (5000955108217607/5000000000000000 : ℝ)^4381 := by
      have hnat : (100081750770857447127 : ℕ)^1024*5000000000000000^4381 ≤ 5000955108217607^4381*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100081750770857447127 100000000000000000000 5000955108217607 5000000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000955108217607/5000000000000000 : ℝ)) (X := (100081750770857447127/100000000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50080127860257802927/50000000000000000000 : ℝ) ≤ (5001872283548021/5000000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (50080127860257802927/50000000000000000000 : ℝ)^1024 ≤ (5001872283548021/5000000000000000 : ℝ)^4381 := by
      have hnat : (50080127860257802927 : ℕ)^1024*5000000000000000^4381 ≤ 5001872283548021^4381*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50080127860257802927 50000000000000000000 5001872283548021 5000000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001872283548021/5000000000000000 : ℝ)) (X := (50080127860257802927/50000000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8114552998221/500000000000000000 : ℝ) ≤ ((451851988358192527/451960000000000000 : ℝ)+2*(458587665207/282475000000000 : ℝ)*(3797/50000 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (451851988358192527/451960000000000000 : ℝ)+2*(458587665207/282475000000000 : ℝ)*(3797/50000 : ℝ)=(5000037932887193/5000000000000000 : ℝ) by norm_num, show 1+2*(8114552998221/500000000000000000 : ℝ)=(250008114552998221/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(80127860257802927/100000000000000000000 : ℝ)+(8114552998221/500000000000000000 : ℝ) ≤ ((451851988358192527/451960000000000000 : ℝ)+(458587665207/282475000000000 : ℝ)*((18893/100000 : ℝ)+(3797/50000 : ℝ)))^(4381/1024 : ℝ) := by
    rw [show (451851988358192527/451960000000000000 : ℝ)+(458587665207/282475000000000 : ℝ)*((18893/100000 : ℝ)+(3797/50000 : ℝ))=(5000955108217607/5000000000000000 : ℝ) by norm_num, show 1+(80127860257802927/100000000000000000000 : ℝ)+(8114552998221/500000000000000000 : ℝ)=(100081750770857447127/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(80127860257802927/100000000000000000000 : ℝ) ≤ ((451851988358192527/451960000000000000 : ℝ)+2*(458587665207/282475000000000 : ℝ)*(18893/100000 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (451851988358192527/451960000000000000 : ℝ)+2*(458587665207/282475000000000 : ℝ)*(18893/100000 : ℝ)=(5001872283548021/5000000000000000 : ℝ) by norm_num, show 1+2*(80127860257802927/100000000000000000000 : ℝ)=(50080127860257802927/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (451851988358192527/451960000000000000 : ℝ)*(X 1 0+X 2 0)+(458587665207/282475000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (3797/50000 : ℝ)) (hi := (18893/100000 : ℝ)) (c := (451851988358192527/451960000000000000 : ℝ)) (alpha := (458587665207/282475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (451851988358192527/451960000000000000 : ℝ)*(X 0 1+X 2 1)+(458587665207/282475000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (3797/50000 : ℝ)) (hi := (18893/100000 : ℝ)) (c := (451851988358192527/451960000000000000 : ℝ)) (alpha := (458587665207/282475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (451851988358192527/451960000000000000 : ℝ)*(X 0 2+X 1 2)+(458587665207/282475000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (3797/50000 : ℝ)) (hi := (18893/100000 : ℝ)) (c := (451851988358192527/451960000000000000 : ℝ)) (alpha := (458587665207/282475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1969789229/10000000000 : ℝ)*X 0 0+(2729875669/5000000000 : ℝ)*X 0 1+(1300045919/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((670073207/1250000000 : ℝ)*X 1 0+(-420675423/2000000000 : ℝ)*X 1 1+(13000459/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167518291/312500000 : ℝ)*X 2 0+(1300045997/2500000000 : ℝ)*X 2 1+(-2103377061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1075413071/2500000000 : ℝ)*X 0 0+(2014906959/5000000000 : ℝ)*X 0 1+(1147476419/2500000000 : ℝ)*X 0 2+(1075413071/2500000000 : ℝ)*X 1 0+(2014906959/5000000000 : ℝ)*X 1 1+(1147476419/2500000000 : ℝ)*X 1 2+(1075413071/2500000000 : ℝ)*X 2 0+(2014906959/5000000000 : ℝ)*X 2 1+(1147476419/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1969836181/10000000000 : ℝ)*X 0 0+(520167901/1000000000 : ℝ)*X 0 1+(5458243517/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646567083/5000000000 : ℝ)*X 1 0+(-1845317037/10000000000 : ℝ)*X 1 1+(218329753/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132328353/250000000 : ℝ)*X 2 0+(2729121903/5000000000 : ℝ)*X 2 1+(-1845317127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4301753339/10000000000 : ℝ)*X 0 0+(458667923/1000000000 : ℝ)*X 0 1+(4033067133/10000000000 : ℝ)*X 0 2+(4301753339/10000000000 : ℝ)*X 1 0+(458667923/1000000000 : ℝ)*X 1 1+(4033067133/10000000000 : ℝ)*X 1 2+(4301753339/10000000000 : ℝ)*X 2 0+(458667923/1000000000 : ℝ)*X 2 1+(4033067133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16622443765847174242528191/2824750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (723510693/100000000000000 : ℝ)*(base19) + (33866021/12500000000000 : ℝ)*(base23) + (22016441/20000000000000 : ℝ)*(lower2) + (185968501/100000000000000 : ℝ)*(upper3) + (21022101/100000000000000 : ℝ)*(upper5) + (352375137012087/12500000000000 : ℝ)*(major0) + (352375137012087/12500000000000 : ℝ)*(major1) + (352375137012087/12500000000000 : ℝ)*(major2) + (481571104058253/12500000000000 : ℝ)*(sp0) + (3852573224969727/100000000000000 : ℝ)*(sp1) + (963143419388063/25000000000000 : ℝ)*(sp2) + (1785424061319591/100000000000000 : ℝ)*(sp3) + (1279003599/25000000000000 : ℝ)*(sp4) + (3986240987/100000000000000 : ℝ)*(sp7) + (892714023780289/50000000000000 : ℝ)*(f.failure) + (192628697424021/5000000000000 : ℝ)*(f.sum) + (206193055126887/56495000000000000000000000000 : ℝ)*base66 + (44689196341901751/5649500000000000000000000000000 : ℝ)*base68 + (46814188667790251/5649500000000000000000000000000 : ℝ)*base70 + (31173907259887251/5649500000000000000000000000000 : ℝ)*base72 + (215136164994503/56495000000000000000000000000 : ℝ)*base73 + (36457424955268251/5649500000000000000000000000000 : ℝ)*base76 + (11927680539331251/5649500000000000000000000000000 : ℝ)*base78 + (16324033663049751/5649500000000000000000000000000 : ℝ)*base80 + (373344989586137/56495000000000000000000000000 : ℝ)*base82 + (4862793/500000000000000000000 : ℝ)*base89 + (4862793/500000000000000000000 : ℝ)*base91 + (4862793/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16178267614171871372773773/2824750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48920577/10000000000000 : ℝ)*(base19) + (593045493/100000000000000 : ℝ)*(base23) + (154717671/100000000000000 : ℝ)*(upper3) + (63369353/100000000000000 : ℝ)*(lower4) + (88327607/100000000000000 : ℝ)*(upper5) + (712996487147967/25000000000000 : ℝ)*(major0) + (712996487147967/25000000000000 : ℝ)*(major1) + (712996487147967/25000000000000 : ℝ)*(major2) + (290653641/4000000000000 : ℝ)*(sp1) + (8678298347/100000000000000 : ℝ)*(sp2) + (389765254204291/10000000000000 : ℝ)*(sp4) + (1948822393248057/50000000000000 : ℝ)*(sp5) + (389764327069907/10000000000000 : ℝ)*(sp6) + (451579791057477/25000000000000 : ℝ)*(sp7) + (451579791057477/25000000000000 : ℝ)*(f.failure) + (389765254204291/10000000000000 : ℝ)*(f.sum) + (112529586067893/28247500000000000000000000000 : ℝ)*base66 + (33288792125253009/11299000000000000000000000000000 : ℝ)*base67 + (9674506198652991/11299000000000000000000000000000 : ℝ)*base70 + (110718565811649009/11299000000000000000000000000000 : ℝ)*base71 + (291109603390061/56495000000000000000000000000 : ℝ)*base74 + (53646540818927009/11299000000000000000000000000000 : ℝ)*base75 + (120973771648989009/11299000000000000000000000000000 : ℝ)*base77 + (35464876071609009/11299000000000000000000000000000 : ℝ)*base79 + (233662660380261/56495000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2268051/250000000000000000000 : ℝ)*base90 + (2268051/250000000000000000000 : ℝ)*base92 + (2268051/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1422_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18893/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3797/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1033/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15821/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1422_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1422_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1033/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15821/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1422_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1422_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1422_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1033/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15821/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1422_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

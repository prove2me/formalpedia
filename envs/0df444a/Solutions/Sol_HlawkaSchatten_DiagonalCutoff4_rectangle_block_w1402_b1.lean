-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1402_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:45:34.306554+00:00
-- url     : https://prove2.me/submissions/385dd871-05ff-4957-bb6d-f9affd2b436c

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
theorem support_rectangle_w1402_s3_0 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1992009397/10000000000 : ℝ)*x 0 + (542010469/1000000000 : ℝ)*x 1 + (5236593587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1992009397/10000000000 : ℝ)^2181 ≤ (3035810395107/25000000000000 : ℝ)^1669 := by
    have hnat : (1992009397 : ℕ)^2181*25000000000000^1669 ≤ 3035810395107^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992009397 10000000000 3035810395107 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542010469/1000000000 : ℝ)^2181 ≤ (2807301697307/6250000000000 : ℝ)^1669 := by
    have hnat : (542010469 : ℕ)^2181*6250000000000^1669 ≤ 2807301697307^1669*1000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542010469 1000000000 2807301697307 6250000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236593587/10000000000 : ℝ)^2181 ≤ (42939931252599/100000000000000 : ℝ)^1669 := by
    have hnat : (5236593587 : ℕ)^2181*100000000000000^1669 ≤ 42939931252599^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236593587 10000000000 42939931252599 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1992009397/10000000000 : ℝ), (542010469/1000000000 : ℝ), (5236593587/10000000000 : ℝ)] ![(3035810395107/25000000000000 : ℝ), (2807301697307/6250000000000 : ℝ), (42939931252599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1992009397/10000000000 : ℝ)|^2181 ≤ (3035810395107/25000000000000 : ℝ)^1669
        have hw : |(-1992009397/10000000000 : ℝ)|=(1992009397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542010469/1000000000 : ℝ)|^2181 ≤ (2807301697307/6250000000000 : ℝ)^1669
        have hw : |(542010469/1000000000 : ℝ)|=(542010469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236593587/10000000000 : ℝ)|^2181 ≤ (42939931252599/100000000000000 : ℝ)^1669
        have hw : |(5236593587/10000000000 : ℝ)|=(5236593587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s3_1 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350580663/10000000000 : ℝ)*x 0 + (-130354251/625000000 : ℝ)*x 1 + (1047318711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350580663/10000000000 : ℝ)^2181 ≤ (11041353937227/25000000000000 : ℝ)^1669 := by
    have hnat : (5350580663 : ℕ)^2181*25000000000000^1669 ≤ 11041353937227^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350580663 10000000000 11041353937227 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130354251/625000000 : ℝ)^2181 ≤ (12894653326977/100000000000000 : ℝ)^1669 := by
    have hnat : (130354251 : ℕ)^2181*100000000000000^1669 ≤ 12894653326977^1669*625000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130354251 625000000 12894653326977 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047318711/2000000000 : ℝ)^2181 ≤ (5367491363713/12500000000000 : ℝ)^1669 := by
    have hnat : (1047318711 : ℕ)^2181*12500000000000^1669 ≤ 5367491363713^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047318711 2000000000 5367491363713 12500000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350580663/10000000000 : ℝ), (-130354251/625000000 : ℝ), (1047318711/2000000000 : ℝ)] ![(11041353937227/25000000000000 : ℝ), (12894653326977/100000000000000 : ℝ), (5367491363713/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350580663/10000000000 : ℝ)|^2181 ≤ (11041353937227/25000000000000 : ℝ)^1669
        have hw : |(5350580663/10000000000 : ℝ)|=(5350580663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130354251/625000000 : ℝ)|^2181 ≤ (12894653326977/100000000000000 : ℝ)^1669
        have hw : |(-130354251/625000000 : ℝ)|=(130354251/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047318711/2000000000 : ℝ)|^2181 ≤ (5367491363713/12500000000000 : ℝ)^1669
        have hw : |(1047318711/2000000000 : ℝ)|=(1047318711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s3_2 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337645173/2500000000 : ℝ)*x 0 + (654574197/1250000000 : ℝ)*x 1 + (-41713359/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337645173/2500000000 : ℝ)^2181 ≤ (44165416061717/100000000000000 : ℝ)^1669 := by
    have hnat : (1337645173 : ℕ)^2181*100000000000000^1669 ≤ 44165416061717^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337645173 2500000000 44165416061717 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654574197/1250000000 : ℝ)^2181 ≤ (42939931134729/100000000000000 : ℝ)^1669 := by
    have hnat : (654574197 : ℕ)^2181*100000000000000^1669 ≤ 42939931134729^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654574197 1250000000 42939931134729 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41713359/200000000 : ℝ)^2181 ≤ (2578930558751/20000000000000 : ℝ)^1669 := by
    have hnat : (41713359 : ℕ)^2181*20000000000000^1669 ≤ 2578930558751^1669*200000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41713359 200000000 2578930558751 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337645173/2500000000 : ℝ), (654574197/1250000000 : ℝ), (-41713359/200000000 : ℝ)] ![(44165416061717/100000000000000 : ℝ), (42939931134729/100000000000000 : ℝ), (2578930558751/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337645173/2500000000 : ℝ)|^2181 ≤ (44165416061717/100000000000000 : ℝ)^1669
        have hw : |(1337645173/2500000000 : ℝ)|=(1337645173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654574197/1250000000 : ℝ)|^2181 ≤ (42939931134729/100000000000000 : ℝ)^1669
        have hw : |(654574197/1250000000 : ℝ)|=(654574197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41713359/200000000 : ℝ)|^2181 ≤ (2578930558751/20000000000000 : ℝ)^1669
        have hw : |(-41713359/200000000 : ℝ)|=(41713359/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s3_3 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4310416997/10000000000 : ℝ)*x 0 + (4117957153/10000000000 : ℝ)*x 1 + (1127757281/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310416997/10000000000 : ℝ)^2181 ≤ (665933056087/2000000000000 : ℝ)^1669 := by
    have hnat : (4310416997 : ℕ)^2181*2000000000000^1669 ≤ 665933056087^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310416997 10000000000 665933056087 2000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4117957153/10000000000 : ℝ)^2181 ≤ (15683665458773/50000000000000 : ℝ)^1669 := by
    have hnat : (4117957153 : ℕ)^2181*50000000000000^1669 ≤ 15683665458773^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4117957153 10000000000 15683665458773 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127757281/2500000000 : ℝ)^2181 ≤ (35336016259879/100000000000000 : ℝ)^1669 := by
    have hnat : (1127757281 : ℕ)^2181*100000000000000^1669 ≤ 35336016259879^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127757281 2500000000 35336016259879 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310416997/10000000000 : ℝ), (4117957153/10000000000 : ℝ), (1127757281/2500000000 : ℝ)] ![(665933056087/2000000000000 : ℝ), (15683665458773/50000000000000 : ℝ), (35336016259879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310416997/10000000000 : ℝ)|^2181 ≤ (665933056087/2000000000000 : ℝ)^1669
        have hw : |(4310416997/10000000000 : ℝ)|=(4310416997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4117957153/10000000000 : ℝ)|^2181 ≤ (15683665458773/50000000000000 : ℝ)^1669
        have hw : |(4117957153/10000000000 : ℝ)|=(4117957153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127757281/2500000000 : ℝ)|^2181 ≤ (35336016259879/100000000000000 : ℝ)^1669
        have hw : |(1127757281/2500000000 : ℝ)|=(1127757281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s3_4 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-398405229/2000000000 : ℝ)*x 0 + (5237334881/10000000000 : ℝ)*x 1 + (1083871767/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398405229/2000000000 : ℝ)^2181 ≤ (3035843748967/25000000000000 : ℝ)^1669 := by
    have hnat : (398405229 : ℕ)^2181*25000000000000^1669 ≤ 3035843748967^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398405229 2000000000 3035843748967 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237334881/10000000000 : ℝ)^2181 ≤ (8589574949857/20000000000000 : ℝ)^1669 := by
    have hnat : (5237334881 : ℕ)^2181*20000000000000^1669 ≤ 8589574949857^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237334881 10000000000 8589574949857 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083871767/2000000000 : ℝ)^2181 ≤ (11227187558383/25000000000000 : ℝ)^1669 := by
    have hnat : (1083871767 : ℕ)^2181*25000000000000^1669 ≤ 11227187558383^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083871767 2000000000 11227187558383 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398405229/2000000000 : ℝ), (5237334881/10000000000 : ℝ), (1083871767/2000000000 : ℝ)] ![(3035843748967/25000000000000 : ℝ), (8589574949857/20000000000000 : ℝ), (11227187558383/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398405229/2000000000 : ℝ)|^2181 ≤ (3035843748967/25000000000000 : ℝ)^1669
        have hw : |(-398405229/2000000000 : ℝ)|=(398405229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237334881/10000000000 : ℝ)|^2181 ≤ (8589574949857/20000000000000 : ℝ)^1669
        have hw : |(5237334881/10000000000 : ℝ)|=(5237334881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083871767/2000000000 : ℝ)|^2181 ≤ (11227187558383/25000000000000 : ℝ)^1669
        have hw : |(1083871767/2000000000 : ℝ)|=(1083871767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s3_5 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5303002347/10000000000 : ℝ)*x 0 + (-237862773/1250000000 : ℝ)*x 1 + (5419359283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303002347/10000000000 : ℝ)^2181 ≤ (10913228359481/25000000000000 : ℝ)^1669 := by
    have hnat : (5303002347 : ℕ)^2181*25000000000000^1669 ≤ 10913228359481^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303002347 10000000000 10913228359481 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (237862773/1250000000 : ℝ)^2181 ≤ (5719165735303/50000000000000 : ℝ)^1669 := by
    have hnat : (237862773 : ℕ)^2181*50000000000000^1669 ≤ 5719165735303^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237862773 1250000000 5719165735303 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419359283/10000000000 : ℝ)^2181 ≤ (22454377542429/50000000000000 : ℝ)^1669 := by
    have hnat : (5419359283 : ℕ)^2181*50000000000000^1669 ≤ 22454377542429^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419359283 10000000000 22454377542429 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303002347/10000000000 : ℝ), (-237862773/1250000000 : ℝ), (5419359283/10000000000 : ℝ)] ![(10913228359481/25000000000000 : ℝ), (5719165735303/50000000000000 : ℝ), (22454377542429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303002347/10000000000 : ℝ)|^2181 ≤ (10913228359481/25000000000000 : ℝ)^1669
        have hw : |(5303002347/10000000000 : ℝ)|=(5303002347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-237862773/1250000000 : ℝ)|^2181 ≤ (5719165735303/50000000000000 : ℝ)^1669
        have hw : |(-237862773/1250000000 : ℝ)|=(237862773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419359283/10000000000 : ℝ)|^2181 ≤ (22454377542429/50000000000000 : ℝ)^1669
        have hw : |(5419359283/10000000000 : ℝ)|=(5419359283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s3_6 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2651501647/5000000000 : ℝ)*x 0 + (677419821/1250000000 : ℝ)*x 1 + (-1902901871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651501647/5000000000 : ℝ)^2181 ≤ (21826461812397/50000000000000 : ℝ)^1669 := by
    have hnat : (2651501647 : ℕ)^2181*50000000000000^1669 ≤ 21826461812397^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651501647 5000000000 21826461812397 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677419821/1250000000 : ℝ)^2181 ≤ (44908747342229/100000000000000 : ℝ)^1669 := by
    have hnat : (677419821 : ℕ)^2181*100000000000000^1669 ≤ 44908747342229^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677419821 1250000000 44908747342229 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1902901871/10000000000 : ℝ)^2181 ≤ (2287665802399/20000000000000 : ℝ)^1669 := by
    have hnat : (1902901871 : ℕ)^2181*20000000000000^1669 ≤ 2287665802399^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902901871 10000000000 2287665802399 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651501647/5000000000 : ℝ), (677419821/1250000000 : ℝ), (-1902901871/10000000000 : ℝ)] ![(21826461812397/50000000000000 : ℝ), (44908747342229/100000000000000 : ℝ), (2287665802399/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651501647/5000000000 : ℝ)|^2181 ≤ (21826461812397/50000000000000 : ℝ)^1669
        have hw : |(2651501647/5000000000 : ℝ)|=(2651501647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677419821/1250000000 : ℝ)|^2181 ≤ (44908747342229/100000000000000 : ℝ)^1669
        have hw : |(677419821/1250000000 : ℝ)|=(677419821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1902901871/10000000000 : ℝ)|^2181 ≤ (2287665802399/20000000000000 : ℝ)^1669
        have hw : |(-1902901871/10000000000 : ℝ)|=(1902901871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s3_7 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4310453179/10000000000 : ℝ)*x 0 + (4509440991/10000000000 : ℝ)*x 1 + (2059776727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310453179/10000000000 : ℝ)^2181 ≤ (33297018040493/100000000000000 : ℝ)^1669 := by
    have hnat : (4310453179 : ℕ)^2181*100000000000000^1669 ≤ 33297018040493^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310453179 10000000000 33297018040493 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509440991/10000000000 : ℝ)^2181 ≤ (551871259319/1562500000000 : ℝ)^1669 := by
    have hnat : (4509440991 : ℕ)^2181*1562500000000^1669 ≤ 551871259319^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509440991 10000000000 551871259319 1562500000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2059776727/5000000000 : ℝ)^2181 ≤ (31383221348527/100000000000000 : ℝ)^1669 := by
    have hnat : (2059776727 : ℕ)^2181*100000000000000^1669 ≤ 31383221348527^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059776727 5000000000 31383221348527 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310453179/10000000000 : ℝ), (4509440991/10000000000 : ℝ), (2059776727/5000000000 : ℝ)] ![(33297018040493/100000000000000 : ℝ), (551871259319/1562500000000 : ℝ), (31383221348527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310453179/10000000000 : ℝ)|^2181 ≤ (33297018040493/100000000000000 : ℝ)^1669
        have hw : |(4310453179/10000000000 : ℝ)|=(4310453179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509440991/10000000000 : ℝ)|^2181 ≤ (551871259319/1562500000000 : ℝ)^1669
        have hw : |(4509440991/10000000000 : ℝ)|=(4509440991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2059776727/5000000000 : ℝ)|^2181 ≤ (31383221348527/100000000000000 : ℝ)^1669
        have hw : |(2059776727/5000000000 : ℝ)|=(2059776727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1402_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7943/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11077/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7481/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7943/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7943/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7943/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7943/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7943/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7943/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10219/100000 : ℝ) ^ (4361/1024 : ℝ) ≤ (1510842988932079/25000000000000000000 : ℝ) := by
    have hpowers : (10219/100000 : ℝ)^4361 ≤ (1510842988932079/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10219 : ℕ)^4361*25000000000000000000^1024 ≤ 1510842988932079^1024*100000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10219 100000 1510842988932079 25000000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10219/100000 : ℝ)) (X := (1510842988932079/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7943/50000 : ℝ) ^ (4361/1024 : ℝ) ≤ (1236344670599349/3125000000000000000 : ℝ) := by
    have hpowers : (7943/50000 : ℝ)^4361 ≤ (1236344670599349/3125000000000000000 : ℝ)^1024 := by
      have hnat : (7943 : ℕ)^4361*3125000000000000000^1024 ≤ 1236344670599349^1024*50000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7943 50000 1236344670599349 3125000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7943/50000 : ℝ)) (X := (1236344670599349/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501510842988932079/12500000000000000000 : ℝ) ≤ (10000283793933959/10000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (12501510842988932079/12500000000000000000 : ℝ)^1024 ≤ (10000283793933959/10000000000000000 : ℝ)^4361 := by
      have hnat : (12501510842988932079 : ℕ)^1024*10000000000000000^4361 ≤ 10000283793933959^4361*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501510842988932079 12500000000000000000 10000283793933959 10000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283793933959/10000000000000000 : ℝ)) (X := (12501510842988932079/12500000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011401600353726871/25000000000000000000 : ℝ) ≤ (1000107069040293/1000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (25011401600353726871/25000000000000000000 : ℝ)^1024 ≤ (1000107069040293/1000000000000000 : ℝ)^4361 := by
      have hnat : (25011401600353726871 : ℕ)^1024*1000000000000000^4361 ≤ 1000107069040293^4361*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011401600353726871 25000000000000000000 1000107069040293 1000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000107069040293/1000000000000000 : ℝ)) (X := (25011401600353726871/25000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563736344670599349/1562500000000000000 : ℝ) ≤ (10001857586871901/10000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (1563736344670599349/1562500000000000000 : ℝ)^1024 ≤ (10001857586871901/10000000000000000 : ℝ)^4361 := by
      have hnat : (1563736344670599349 : ℕ)^1024*10000000000000000^4361 ≤ 10001857586871901^4361*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563736344670599349 1562500000000000000 10001857586871901 10000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001857586871901/10000000000000000 : ℝ)) (X := (1563736344670599349/1562500000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1510842988932079/25000000000000000000 : ℝ) ≤ ((11331105134038183271/11334000000000000000 : ℝ)+2*(786896468971/566700000000000 : ℝ)*(10219/100000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (11331105134038183271/11334000000000000000 : ℝ)+2*(786896468971/566700000000000 : ℝ)*(10219/100000 : ℝ)=(10000283793933959/10000000000000000 : ℝ) by norm_num, show 1+2*(1510842988932079/25000000000000000000 : ℝ)=(12501510842988932079/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1236344670599349/3125000000000000000 : ℝ)+(1510842988932079/25000000000000000000 : ℝ) ≤ ((11331105134038183271/11334000000000000000 : ℝ)+(786896468971/566700000000000 : ℝ)*((7943/50000 : ℝ)+(10219/100000 : ℝ)))^(4361/1024 : ℝ) := by
    rw [show (11331105134038183271/11334000000000000000 : ℝ)+(786896468971/566700000000000 : ℝ)*((7943/50000 : ℝ)+(10219/100000 : ℝ))=(1000107069040293/1000000000000000 : ℝ) by norm_num, show 1+(1236344670599349/3125000000000000000 : ℝ)+(1510842988932079/25000000000000000000 : ℝ)=(25011401600353726871/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1236344670599349/3125000000000000000 : ℝ) ≤ ((11331105134038183271/11334000000000000000 : ℝ)+2*(786896468971/566700000000000 : ℝ)*(7943/50000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (11331105134038183271/11334000000000000000 : ℝ)+2*(786896468971/566700000000000 : ℝ)*(7943/50000 : ℝ)=(10001857586871901/10000000000000000 : ℝ) by norm_num, show 1+2*(1236344670599349/3125000000000000000 : ℝ)=(1563736344670599349/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11331105134038183271/11334000000000000000 : ℝ)*(X 1 0+X 2 0)+(786896468971/566700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (10219/100000 : ℝ)) (hi := (7943/50000 : ℝ)) (c := (11331105134038183271/11334000000000000000 : ℝ)) (alpha := (786896468971/566700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11331105134038183271/11334000000000000000 : ℝ)*(X 0 1+X 2 1)+(786896468971/566700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (10219/100000 : ℝ)) (hi := (7943/50000 : ℝ)) (c := (11331105134038183271/11334000000000000000 : ℝ)) (alpha := (786896468971/566700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11331105134038183271/11334000000000000000 : ℝ)*(X 0 2+X 1 2)+(786896468971/566700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (10219/100000 : ℝ)) (hi := (7943/50000 : ℝ)) (c := (11331105134038183271/11334000000000000000 : ℝ)) (alpha := (786896468971/566700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1992009397/10000000000 : ℝ)*X 0 0+(542010469/1000000000 : ℝ)*X 0 1+(5236593587/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350580663/10000000000 : ℝ)*X 1 0+(-130354251/625000000 : ℝ)*X 1 1+(1047318711/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337645173/2500000000 : ℝ)*X 2 0+(654574197/1250000000 : ℝ)*X 2 1+(-41713359/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4310416997/10000000000 : ℝ)*X 0 0+(4117957153/10000000000 : ℝ)*X 0 1+(1127757281/2500000000 : ℝ)*X 0 2+(4310416997/10000000000 : ℝ)*X 1 0+(4117957153/10000000000 : ℝ)*X 1 1+(1127757281/2500000000 : ℝ)*X 1 2+(4310416997/10000000000 : ℝ)*X 2 0+(4117957153/10000000000 : ℝ)*X 2 1+(1127757281/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-398405229/2000000000 : ℝ)*X 0 0+(5237334881/10000000000 : ℝ)*X 0 1+(1083871767/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303002347/10000000000 : ℝ)*X 1 0+(-237862773/1250000000 : ℝ)*X 1 1+(5419359283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651501647/5000000000 : ℝ)*X 2 0+(677419821/1250000000 : ℝ)*X 2 1+(-1902901871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310453179/10000000000 : ℝ)*X 0 0+(4509440991/10000000000 : ℝ)*X 0 1+(2059776727/5000000000 : ℝ)*X 0 2+(4310453179/10000000000 : ℝ)*X 1 0+(4509440991/10000000000 : ℝ)*X 1 1+(2059776727/5000000000 : ℝ)*X 1 2+(4310453179/10000000000 : ℝ)*X 2 0+(4509440991/10000000000 : ℝ)*X 2 1+(2059776727/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (120208488916742180783902177/23612500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (470461379/50000000000000 : ℝ)*(base19) + (96750023/10000000000000 : ℝ)*(base23) + (92142021/100000000000000 : ℝ)*(upper3) + (12363/781250000000 : ℝ)*(upper4) + (42611129/25000000000000 : ℝ)*(upper5) + (499585906562729/12500000000000 : ℝ)*(major0) + (499585906562729/12500000000000 : ℝ)*(major1) + (499585906562729/12500000000000 : ℝ)*(major2) + (681159623400961/12500000000000 : ℝ)*(sp0) + (544929457387647/10000000000000 : ℝ)*(sp1) + (5449294547298997/100000000000000 : ℝ)*(sp2) + (636017882422081/25000000000000 : ℝ)*(sp3) + (18527591539/100000000000000 : ℝ)*(sp4) + (7290819983/100000000000000 : ℝ)*(sp7) + (1272039410254153/50000000000000 : ℝ)*(f.failure) + (1362323878699807/25000000000000 : ℝ)*(f.sum) + (128255876077309/14167500000000000000000000000 : ℝ)*base66 + (486434827847113441/141675000000000000000000000000000 : ℝ)*base68 + (924420267472738441/141675000000000000000000000000000 : ℝ)*base70 + (2206069726449538441/141675000000000000000000000000000 : ℝ)*base72 + (22904400311197/28335000000000000000000000000 : ℝ)*base73 + (1774379160388813441/141675000000000000000000000000000 : ℝ)*base76 + (614558841485488441/141675000000000000000000000000000 : ℝ)*base78 + (1617485104477888441/141675000000000000000000000000000 : ℝ)*base80 + (23685999006827/7083750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (21161707/5000000000000000000000 : ℝ)*base89 + (21161707/5000000000000000000000 : ℝ)*base91 + (21161707/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28204215729877244244424371/47225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (881226359/50000000000000 : ℝ)*(base19) + (3017409017/100000000000000 : ℝ)*(base23) + (374892189/100000000000000 : ℝ)*(upper3) + (47441853/100000000000000 : ℝ)*(lower4) + (180563553/100000000000000 : ℝ)*(upper5) + (2014657618420899/50000000000000 : ℝ)*(major0) + (2014657618420899/50000000000000 : ℝ)*(major1) + (2014657618420899/50000000000000 : ℝ)*(major2) + (37126519133/100000000000000 : ℝ)*(sp1) + (14420848793/25000000000000 : ℝ)*(sp2) + (2746891195737677/50000000000000 : ℝ)*(sp4) + (2746871751251751/50000000000000 : ℝ)*(sp5) + (1098744338134233/20000000000000 : ℝ)*(sp6) + (641212015575137/25000000000000 : ℝ)*(sp7) + (641212015575137/25000000000000 : ℝ)*(f.failure) + (2746891195737677/50000000000000 : ℝ)*(f.sum) + (8165114327201/2361250000000000000000000000 : ℝ)*base66 + (318135040315253543/188900000000000000000000000000000 : ℝ)*base67 + (819577752099253543/188900000000000000000000000000000 : ℝ)*base69 + (846905808479446457/188900000000000000000000000000000 : ℝ)*base72 + (23856107950373/4722500000000000000000000000 : ℝ)*base73 + (749487485529353543/188900000000000000000000000000000 : ℝ)*base75 + (217736072307653543/188900000000000000000000000000000 : ℝ)*base77 + (1315171168205053543/188900000000000000000000000000000 : ℝ)*base79 + (40432566164021/9445000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (11701197/2500000000000000000000 : ℝ)*base90 + (11701197/2500000000000000000000 : ℝ)*base92 + (11701197/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1402_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7943/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11077/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7481/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1402_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1402_s4_0 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-996529509/5000000000 : ℝ)*x 0 + (5411279881/10000000000 : ℝ)*x 1 + (2622363803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (996529509/5000000000 : ℝ)^2181 ≤ (12151603580881/100000000000000 : ℝ)^1669 := by
    have hnat : (996529509 : ℕ)^2181*100000000000000^1669 ≤ 12151603580881^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996529509 5000000000 12151603580881 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411279881/10000000000 : ℝ)^2181 ≤ (44821284453453/100000000000000 : ℝ)^1669 := by
    have hnat : (5411279881 : ℕ)^2181*100000000000000^1669 ≤ 44821284453453^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411279881 10000000000 44821284453453 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622363803/5000000000 : ℝ)^2181 ≤ (10756777991051/25000000000000 : ℝ)^1669 := by
    have hnat : (2622363803 : ℕ)^2181*25000000000000^1669 ≤ 10756777991051^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622363803 5000000000 10756777991051 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-996529509/5000000000 : ℝ), (5411279881/10000000000 : ℝ), (2622363803/5000000000 : ℝ)] ![(12151603580881/100000000000000 : ℝ), (44821284453453/100000000000000 : ℝ), (10756777991051/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-996529509/5000000000 : ℝ)|^2181 ≤ (12151603580881/100000000000000 : ℝ)^1669
        have hw : |(-996529509/5000000000 : ℝ)|=(996529509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411279881/10000000000 : ℝ)|^2181 ≤ (44821284453453/100000000000000 : ℝ)^1669
        have hw : |(5411279881/10000000000 : ℝ)|=(5411279881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622363803/5000000000 : ℝ)|^2181 ≤ (10756777991051/25000000000000 : ℝ)^1669
        have hw : |(2622363803/5000000000 : ℝ)|=(2622363803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s4_1 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674155153/5000000000 : ℝ)*x 0 + (-2077902257/10000000000 : ℝ)*x 1 + (655591081/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674155153/5000000000 : ℝ)^2181 ≤ (1765637125061/4000000000000 : ℝ)^1669 := by
    have hnat : (2674155153 : ℕ)^2181*4000000000000^1669 ≤ 1765637125061^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674155153 5000000000 1765637125061 4000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077902257/10000000000 : ℝ)^2181 ≤ (12831948725669/100000000000000 : ℝ)^1669 := by
    have hnat : (2077902257 : ℕ)^2181*100000000000000^1669 ≤ 12831948725669^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077902257 10000000000 12831948725669 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655591081/1250000000 : ℝ)^2181 ≤ (2689195195941/6250000000000 : ℝ)^1669 := by
    have hnat : (655591081 : ℕ)^2181*6250000000000^1669 ≤ 2689195195941^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655591081 1250000000 2689195195941 6250000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674155153/5000000000 : ℝ), (-2077902257/10000000000 : ℝ), (655591081/1250000000 : ℝ)] ![(1765637125061/4000000000000 : ℝ), (12831948725669/100000000000000 : ℝ), (2689195195941/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674155153/5000000000 : ℝ)|^2181 ≤ (1765637125061/4000000000000 : ℝ)^1669
        have hw : |(2674155153/5000000000 : ℝ)|=(2674155153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2077902257/10000000000 : ℝ)|^2181 ≤ (12831948725669/100000000000000 : ℝ)^1669
        have hw : |(-2077902257/10000000000 : ℝ)|=(2077902257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655591081/1250000000 : ℝ)|^2181 ≤ (2689195195941/6250000000000 : ℝ)^1669
        have hw : |(655591081/1250000000 : ℝ)|=(655591081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s4_2 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348310273/10000000000 : ℝ)*x 0 + (2622364153/5000000000 : ℝ)*x 1 + (-415580551/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348310273/10000000000 : ℝ)^2181 ≤ (44140927770617/100000000000000 : ℝ)^1669 := by
    have hnat : (5348310273 : ℕ)^2181*100000000000000^1669 ≤ 44140927770617^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348310273 10000000000 44140927770617 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622364153/5000000000 : ℝ)^2181 ≤ (8605423893723/20000000000000 : ℝ)^1669 := by
    have hnat : (2622364153 : ℕ)^2181*20000000000000^1669 ≤ 8605423893723^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622364153 5000000000 8605423893723 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415580551/2000000000 : ℝ)^2181 ≤ (12831952744467/100000000000000 : ℝ)^1669 := by
    have hnat : (415580551 : ℕ)^2181*100000000000000^1669 ≤ 12831952744467^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415580551 2000000000 12831952744467 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348310273/10000000000 : ℝ), (2622364153/5000000000 : ℝ), (-415580551/2000000000 : ℝ)] ![(44140927770617/100000000000000 : ℝ), (8605423893723/20000000000000 : ℝ), (12831952744467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348310273/10000000000 : ℝ)|^2181 ≤ (44140927770617/100000000000000 : ℝ)^1669
        have hw : |(5348310273/10000000000 : ℝ)|=(5348310273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622364153/5000000000 : ℝ)|^2181 ≤ (8605423893723/20000000000000 : ℝ)^1669
        have hw : |(2622364153/5000000000 : ℝ)|=(2622364153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-415580551/2000000000 : ℝ)|^2181 ≤ (12831952744467/100000000000000 : ℝ)^1669
        have hw : |(-415580551/2000000000 : ℝ)|=(415580551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s4_3 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (172442289/400000000 : ℝ)*x 0 + (517005213/1250000000 : ℝ)*x 1 + (2246394411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172442289/400000000 : ℝ)^2181 ≤ (33303115670739/100000000000000 : ℝ)^1669 := by
    have hnat : (172442289 : ℕ)^2181*100000000000000^1669 ≤ 33303115670739^1669*400000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172442289 400000000 33303115670739 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517005213/1250000000 : ℝ)^2181 ≤ (15773732305291/50000000000000 : ℝ)^1669 := by
    have hnat : (517005213 : ℕ)^2181*50000000000000^1669 ≤ 15773732305291^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517005213 1250000000 15773732305291 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246394411/5000000000 : ℝ)^2181 ≤ (1098419365821/3125000000000 : ℝ)^1669 := by
    have hnat : (2246394411 : ℕ)^2181*3125000000000^1669 ≤ 1098419365821^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246394411 5000000000 1098419365821 3125000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172442289/400000000 : ℝ), (517005213/1250000000 : ℝ), (2246394411/5000000000 : ℝ)] ![(33303115670739/100000000000000 : ℝ), (15773732305291/50000000000000 : ℝ), (1098419365821/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172442289/400000000 : ℝ)|^2181 ≤ (33303115670739/100000000000000 : ℝ)^1669
        have hw : |(172442289/400000000 : ℝ)|=(172442289/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517005213/1250000000 : ℝ)|^2181 ≤ (15773732305291/50000000000000 : ℝ)^1669
        have hw : |(517005213/1250000000 : ℝ)|=(517005213/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246394411/5000000000 : ℝ)|^2181 ≤ (1098419365821/3125000000000 : ℝ)^1669
        have hw : |(2246394411/5000000000 : ℝ)|=(2246394411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s4_4 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-996535391/5000000000 : ℝ)*x 0 + (52453389/100000000 : ℝ)*x 1 + (270533287/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (996535391/5000000000 : ℝ)^2181 ≤ (12151697308627/100000000000000 : ℝ)^1669 := by
    have hnat : (996535391 : ℕ)^2181*100000000000000^1669 ≤ 12151697308627^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996535391 5000000000 12151697308627 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52453389/100000000 : ℝ)^2181 ≤ (43033665512213/100000000000000 : ℝ)^1669 := by
    have hnat : (52453389 : ℕ)^2181*100000000000000^1669 ≤ 43033665512213^1669*100000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52453389 100000000 43033665512213 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270533287/500000000 : ℝ)^2181 ≤ (5601829646321/12500000000000 : ℝ)^1669 := by
    have hnat : (270533287 : ℕ)^2181*12500000000000^1669 ≤ 5601829646321^1669*500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270533287 500000000 5601829646321 12500000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-996535391/5000000000 : ℝ), (52453389/100000000 : ℝ), (270533287/500000000 : ℝ)] ![(12151697308627/100000000000000 : ℝ), (43033665512213/100000000000000 : ℝ), (5601829646321/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-996535391/5000000000 : ℝ)|^2181 ≤ (12151697308627/100000000000000 : ℝ)^1669
        have hw : |(-996535391/5000000000 : ℝ)|=(996535391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52453389/100000000 : ℝ)|^2181 ≤ (43033665512213/100000000000000 : ℝ)^1669
        have hw : |(52453389/100000000 : ℝ)|=(52453389/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270533287/500000000 : ℝ)|^2181 ≤ (5601829646321/12500000000000 : ℝ)^1669
        have hw : |(270533287/500000000 : ℝ)|=(270533287/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s4_5 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305129317/10000000000 : ℝ)*x 0 + (-1911964643/10000000000 : ℝ)*x 1 + (5410665671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305129317/10000000000 : ℝ)^2181 ≤ (43675794639291/100000000000000 : ℝ)^1669 := by
    have hnat : (5305129317 : ℕ)^2181*100000000000000^1669 ≤ 43675794639291^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305129317 10000000000 43675794639291 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1911964643/10000000000 : ℝ)^2181 ≤ (719348057689/6250000000000 : ℝ)^1669 := by
    have hnat : (1911964643 : ℕ)^2181*6250000000000^1669 ≤ 719348057689^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911964643 10000000000 719348057689 6250000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410665671/10000000000 : ℝ)^2181 ≤ (8962927284749/20000000000000 : ℝ)^1669 := by
    have hnat : (5410665671 : ℕ)^2181*20000000000000^1669 ≤ 8962927284749^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410665671 10000000000 8962927284749 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305129317/10000000000 : ℝ), (-1911964643/10000000000 : ℝ), (5410665671/10000000000 : ℝ)] ![(43675794639291/100000000000000 : ℝ), (719348057689/6250000000000 : ℝ), (8962927284749/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305129317/10000000000 : ℝ)|^2181 ≤ (43675794639291/100000000000000 : ℝ)^1669
        have hw : |(5305129317/10000000000 : ℝ)|=(5305129317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1911964643/10000000000 : ℝ)|^2181 ≤ (719348057689/6250000000000 : ℝ)^1669
        have hw : |(-1911964643/10000000000 : ℝ)|=(1911964643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410665671/10000000000 : ℝ)|^2181 ≤ (8962927284749/20000000000000 : ℝ)^1669
        have hw : |(5410665671/10000000000 : ℝ)|=(5410665671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s4_6 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652564667/5000000000 : ℝ)*x 0 + (2705332849/5000000000 : ℝ)*x 1 + (-1911964583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652564667/5000000000 : ℝ)^2181 ≤ (21837897411091/50000000000000 : ℝ)^1669 := by
    have hnat : (2652564667 : ℕ)^2181*50000000000000^1669 ≤ 21837897411091^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652564667 5000000000 21837897411091 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705332849/5000000000 : ℝ)^2181 ≤ (2240731835799/5000000000000 : ℝ)^1669 := by
    have hnat : (2705332849 : ℕ)^2181*5000000000000^1669 ≤ 2240731835799^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705332849 5000000000 2240731835799 5000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1911964583/10000000000 : ℝ)^2181 ≤ (11509568451037/100000000000000 : ℝ)^1669 := by
    have hnat : (1911964583 : ℕ)^2181*100000000000000^1669 ≤ 11509568451037^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911964583 10000000000 11509568451037 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652564667/5000000000 : ℝ), (2705332849/5000000000 : ℝ), (-1911964583/10000000000 : ℝ)] ![(21837897411091/50000000000000 : ℝ), (2240731835799/5000000000000 : ℝ), (11509568451037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652564667/5000000000 : ℝ)|^2181 ≤ (21837897411091/50000000000000 : ℝ)^1669
        have hw : |(2652564667/5000000000 : ℝ)|=(2652564667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705332849/5000000000 : ℝ)|^2181 ≤ (2240731835799/5000000000000 : ℝ)^1669
        have hw : |(2705332849/5000000000 : ℝ)|=(2705332849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1911964583/10000000000 : ℝ)|^2181 ≤ (11509568451037/100000000000000 : ℝ)^1669
        have hw : |(-1911964583/10000000000 : ℝ)|=(1911964583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s4_7 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4311083359/10000000000 : ℝ)*x 0 + (4491479941/10000000000 : ℝ)*x 1 + (2068678819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311083359/10000000000 : ℝ)^2181 ≤ (832584487253/2500000000000 : ℝ)^1669 := by
    have hnat : (4311083359 : ℕ)^2181*2500000000000^1669 ≤ 832584487253^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311083359 10000000000 832584487253 2500000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491479941/10000000000 : ℝ)^2181 ≤ (35136038901393/100000000000000 : ℝ)^1669 := by
    have hnat : (4491479941 : ℕ)^2181*100000000000000^1669 ≤ 35136038901393^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491479941 10000000000 35136038901393 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068678819/5000000000 : ℝ)^2181 ≤ (3156058160041/10000000000000 : ℝ)^1669 := by
    have hnat : (2068678819 : ℕ)^2181*10000000000000^1669 ≤ 3156058160041^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068678819 5000000000 3156058160041 10000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311083359/10000000000 : ℝ), (4491479941/10000000000 : ℝ), (2068678819/5000000000 : ℝ)] ![(832584487253/2500000000000 : ℝ), (35136038901393/100000000000000 : ℝ), (3156058160041/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311083359/10000000000 : ℝ)|^2181 ≤ (832584487253/2500000000000 : ℝ)^1669
        have hw : |(4311083359/10000000000 : ℝ)|=(4311083359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491479941/10000000000 : ℝ)|^2181 ≤ (35136038901393/100000000000000 : ℝ)^1669
        have hw : |(4491479941/10000000000 : ℝ)|=(4491479941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2068678819/5000000000 : ℝ)|^2181 ≤ (3156058160041/10000000000000 : ℝ)^1669
        have hw : |(2068678819/5000000000 : ℝ)|=(2068678819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1402_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7481/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11077/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11251/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7389/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7481/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11077/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7481/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11077/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7481/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11077/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7481/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11077/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7481/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11077/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7481/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11077/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (11077/100000 : ℝ) ^ (4361/1024 : ℝ) ≤ (851913554834767/10000000000000000000 : ℝ) := by
    have hpowers : (11077/100000 : ℝ)^4361 ≤ (851913554834767/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11077 : ℕ)^4361*10000000000000000000^1024 ≤ 851913554834767^1024*100000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11077 100000 851913554834767 10000000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11077/100000 : ℝ)) (X := (851913554834767/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7481/50000 : ℝ) ^ (4361/1024 : ℝ) ≤ (30651726848465639/100000000000000000000 : ℝ) := by
    have hpowers : (7481/50000 : ℝ)^4361 ≤ (30651726848465639/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7481 : ℕ)^4361*100000000000000000000^1024 ≤ 30651726848465639^1024*50000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7481 50000 30651726848465639 100000000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7481/50000 : ℝ)) (X := (30651726848465639/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000851913554834767/5000000000000000000 : ℝ) ≤ (400016001882481/400000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (5000851913554834767/5000000000000000000 : ℝ)^1024 ≤ (400016001882481/400000000000000 : ℝ)^4361 := by
      have hnat : (5000851913554834767 : ℕ)^1024*400000000000000^4361 ≤ 400016001882481^4361*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000851913554834767 5000000000000000000 400016001882481 400000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400016001882481/400000000000000 : ℝ)) (X := (5000851913554834767/5000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039170862396813309/100000000000000000000 : ℝ) ≤ (10000919627452601/10000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (100039170862396813309/100000000000000000000 : ℝ)^1024 ≤ (10000919627452601/10000000000000000 : ℝ)^4361 := by
      have hnat : (100039170862396813309 : ℕ)^1024*10000000000000000^4361 ≤ 10000919627452601^4361*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039170862396813309 100000000000000000000 10000919627452601 10000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000919627452601/10000000000000000 : ℝ)) (X := (100039170862396813309/100000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030651726848465639/50000000000000000000 : ℝ) ≤ (10001439207843177/10000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (50030651726848465639/50000000000000000000 : ℝ)^1024 ≤ (10001439207843177/10000000000000000 : ℝ)^4361 := by
      have hnat : (50030651726848465639 : ℕ)^1024*10000000000000000^4361 ≤ 10001439207843177^4361*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030651726848465639 50000000000000000000 10001439207843177 10000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001439207843177/10000000000000000 : ℝ)) (X := (50030651726848465639/50000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(851913554834767/10000000000000000000 : ℝ) ≤ ((38840043398863146421/38850000000000000000 : ℝ)+2*(32473774411/24281250000000 : ℝ)*(11077/100000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (38840043398863146421/38850000000000000000 : ℝ)+2*(32473774411/24281250000000 : ℝ)*(11077/100000 : ℝ)=(400016001882481/400000000000000 : ℝ) by norm_num, show 1+2*(851913554834767/10000000000000000000 : ℝ)=(5000851913554834767/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30651726848465639/100000000000000000000 : ℝ)+(851913554834767/10000000000000000000 : ℝ) ≤ ((38840043398863146421/38850000000000000000 : ℝ)+(32473774411/24281250000000 : ℝ)*((7481/50000 : ℝ)+(11077/100000 : ℝ)))^(4361/1024 : ℝ) := by
    rw [show (38840043398863146421/38850000000000000000 : ℝ)+(32473774411/24281250000000 : ℝ)*((7481/50000 : ℝ)+(11077/100000 : ℝ))=(10000919627452601/10000000000000000 : ℝ) by norm_num, show 1+(30651726848465639/100000000000000000000 : ℝ)+(851913554834767/10000000000000000000 : ℝ)=(100039170862396813309/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30651726848465639/100000000000000000000 : ℝ) ≤ ((38840043398863146421/38850000000000000000 : ℝ)+2*(32473774411/24281250000000 : ℝ)*(7481/50000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (38840043398863146421/38850000000000000000 : ℝ)+2*(32473774411/24281250000000 : ℝ)*(7481/50000 : ℝ)=(10001439207843177/10000000000000000 : ℝ) by norm_num, show 1+2*(30651726848465639/100000000000000000000 : ℝ)=(50030651726848465639/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38840043398863146421/38850000000000000000 : ℝ)*(X 1 0+X 2 0)+(32473774411/24281250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (11077/100000 : ℝ)) (hi := (7481/50000 : ℝ)) (c := (38840043398863146421/38850000000000000000 : ℝ)) (alpha := (32473774411/24281250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38840043398863146421/38850000000000000000 : ℝ)*(X 0 1+X 2 1)+(32473774411/24281250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (11077/100000 : ℝ)) (hi := (7481/50000 : ℝ)) (c := (38840043398863146421/38850000000000000000 : ℝ)) (alpha := (32473774411/24281250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38840043398863146421/38850000000000000000 : ℝ)*(X 0 2+X 1 2)+(32473774411/24281250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (11077/100000 : ℝ)) (hi := (7481/50000 : ℝ)) (c := (38840043398863146421/38850000000000000000 : ℝ)) (alpha := (32473774411/24281250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-996529509/5000000000 : ℝ)*X 0 0+(5411279881/10000000000 : ℝ)*X 0 1+(2622363803/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674155153/5000000000 : ℝ)*X 1 0+(-2077902257/10000000000 : ℝ)*X 1 1+(655591081/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348310273/10000000000 : ℝ)*X 2 0+(2622364153/5000000000 : ℝ)*X 2 1+(-415580551/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((172442289/400000000 : ℝ)*X 0 0+(517005213/1250000000 : ℝ)*X 0 1+(2246394411/5000000000 : ℝ)*X 0 2+(172442289/400000000 : ℝ)*X 1 0+(517005213/1250000000 : ℝ)*X 1 1+(2246394411/5000000000 : ℝ)*X 1 2+(172442289/400000000 : ℝ)*X 2 0+(517005213/1250000000 : ℝ)*X 2 1+(2246394411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-996535391/5000000000 : ℝ)*X 0 0+(52453389/100000000 : ℝ)*X 0 1+(270533287/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305129317/10000000000 : ℝ)*X 1 0+(-1911964643/10000000000 : ℝ)*X 1 1+(5410665671/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652564667/5000000000 : ℝ)*X 2 0+(2705332849/5000000000 : ℝ)*X 2 1+(-1911964583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4311083359/10000000000 : ℝ)*X 0 0+(4491479941/10000000000 : ℝ)*X 0 1+(2068678819/5000000000 : ℝ)*X 0 2+(4311083359/10000000000 : ℝ)*X 1 0+(4491479941/10000000000 : ℝ)*X 1 1+(2068678819/5000000000 : ℝ)*X 1 2+(4311083359/10000000000 : ℝ)*X 2 0+(4491479941/10000000000 : ℝ)*X 2 1+(2068678819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101189013994737505541337923/32375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36709139/50000000000000 : ℝ)*(base15) + (67113433/50000000000000 : ℝ)*(upper2) + (459886977/100000000000000 : ℝ)*(upper3) + (33622293/50000000000000 : ℝ)*(upper4) + (220182008606821/5000000000000 : ℝ)*(major0) + (220182008606821/5000000000000 : ℝ)*(major1) + (220182008606821/5000000000000 : ℝ)*(major2) + (6004149138350873/100000000000000 : ℝ)*(sp0) + (1200831346573337/20000000000000 : ℝ)*(sp1) + (3002076895919773/50000000000000 : ℝ)*(sp2) + (1401555975437391/50000000000000 : ℝ)*(sp3) + (766793409/10000000000000 : ℝ)*(sp4) + (3014445417/100000000000000 : ℝ)*(sp6) + (1148292877/10000000000000 : ℝ)*(sp7) + (87597607306361/3125000000000 : ℝ)*(f.failure) + (6004156806284963/100000000000000 : ℝ)*(f.sum) + (4504082409737/1942500000000000000000000000 : ℝ)*base65 + (4382464378854812359/194250000000000000000000000000000 : ℝ)*base68 + (2817782666731562359/194250000000000000000000000000000 : ℝ)*base70 + (3921974508925562359/194250000000000000000000000000000 : ℝ)*base72 + (8085624485321/3885000000000000000000000000 : ℝ)*base74 + (3149156702490062359/194250000000000000000000000000000 : ℝ)*base76 + (2872725893451062359/194250000000000000000000000000000 : ℝ)*base78 + (1560945838488062359/194250000000000000000000000000000 : ℝ)*base80 + (23617476406729/3885000000000000000000000000 : ℝ)*base81 + (4154459/312500000000000000000 : ℝ)*base89 + (4154459/312500000000000000000 : ℝ)*base91 + (4154459/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46789591064919709432390039/4375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1799515069/100000000000000 : ℝ)*(base19) + (522023443/25000000000000 : ℝ)*(base23) + (53292793/25000000000000 : ℝ)*(upper3) + (111484241/100000000000000 : ℝ)*(lower4) + (49502361/25000000000000 : ℝ)*(upper5) + (2218126280791417/50000000000000 : ℝ)*(major0) + (2218126280791417/50000000000000 : ℝ)*(major1) + (2218126280791417/50000000000000 : ℝ)*(major2) + (34407689999/100000000000000 : ℝ)*(sp1) + (20831372807/50000000000000 : ℝ)*(sp2) + (6048622017958651/100000000000000 : ℝ)*(sp4) + (6048585810753583/100000000000000 : ℝ)*(sp5) + (189018070847477/3125000000000 : ℝ)*(sp6) + (1411941374357441/50000000000000 : ℝ)*(sp7) + (1411941374357441/50000000000000 : ℝ)*(f.failure) + (6048622017958651/100000000000000 : ℝ)*(f.sum) + (18716138411771/4856250000000000000000000000 : ℝ)*base65 + (5235500919684731443/1942500000000000000000000000000000 : ℝ)*base68 + (6602910718970268557/1942500000000000000000000000000000 : ℝ)*base69 + (11081178021972768557/1942500000000000000000000000000000 : ℝ)*base71 + (44837331636817/9712500000000000000000000000 : ℝ)*base73 + (14888792477757768557/1942500000000000000000000000000000 : ℝ)*base75 + (12006079402820268557/1942500000000000000000000000000000 : ℝ)*base77 + (34117349673035268557/1942500000000000000000000000000000 : ℝ)*base79 + (3501059025967/9712500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (63967021/5000000000000000000000 : ℝ)*base90 + (63967021/5000000000000000000000 : ℝ)*base92 + (63967021/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1402_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7481/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11077/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7389/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1402_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1402_s5_0 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1993219989/10000000000 : ℝ)*x 0 + (5409842289/10000000000 : ℝ)*x 1 + (5246059307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1993219989/10000000000 : ℝ)^2181 ≤ (303822152643/2500000000000 : ℝ)^1669 := by
    have hnat : (1993219989 : ℕ)^2181*2500000000000^1669 ≤ 303822152643^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993219989 10000000000 303822152643 2500000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409842289/10000000000 : ℝ)^2181 ≤ (22402862370289/50000000000000 : ℝ)^1669 := by
    have hnat : (5409842289 : ℕ)^2181*50000000000000^1669 ≤ 22402862370289^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409842289 10000000000 22402862370289 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246059307/10000000000 : ℝ)^2181 ≤ (43041389137369/100000000000000 : ℝ)^1669 := by
    have hnat : (5246059307 : ℕ)^2181*100000000000000^1669 ≤ 43041389137369^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246059307 10000000000 43041389137369 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1993219989/10000000000 : ℝ), (5409842289/10000000000 : ℝ), (5246059307/10000000000 : ℝ)] ![(303822152643/2500000000000 : ℝ), (22402862370289/50000000000000 : ℝ), (43041389137369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1993219989/10000000000 : ℝ)|^2181 ≤ (303822152643/2500000000000 : ℝ)^1669
        have hw : |(-1993219989/10000000000 : ℝ)|=(1993219989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409842289/10000000000 : ℝ)|^2181 ≤ (22402862370289/50000000000000 : ℝ)^1669
        have hw : |(5409842289/10000000000 : ℝ)|=(5409842289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246059307/10000000000 : ℝ)|^2181 ≤ (43041389137369/100000000000000 : ℝ)^1669
        have hw : |(5246059307/10000000000 : ℝ)|=(5246059307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s5_1 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347941121/10000000000 : ℝ)*x 0 + (-2076627709/10000000000 : ℝ)*x 1 + (5246059319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347941121/10000000000 : ℝ)^2181 ≤ (4413694647139/10000000000000 : ℝ)^1669 := by
    have hnat : (5347941121 : ℕ)^2181*10000000000000^1669 ≤ 4413694647139^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347941121 10000000000 4413694647139 10000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076627709/10000000000 : ℝ)^2181 ≤ (12821664249937/100000000000000 : ℝ)^1669 := by
    have hnat : (2076627709 : ℕ)^2181*100000000000000^1669 ≤ 12821664249937^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076627709 10000000000 12821664249937 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246059319/10000000000 : ℝ)^2181 ≤ (21520694633013/50000000000000 : ℝ)^1669 := by
    have hnat : (5246059319 : ℕ)^2181*50000000000000^1669 ≤ 21520694633013^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246059319 10000000000 21520694633013 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347941121/10000000000 : ℝ), (-2076627709/10000000000 : ℝ), (5246059319/10000000000 : ℝ)] ![(4413694647139/10000000000000 : ℝ), (12821664249937/100000000000000 : ℝ), (21520694633013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347941121/10000000000 : ℝ)|^2181 ≤ (4413694647139/10000000000000 : ℝ)^1669
        have hw : |(5347941121/10000000000 : ℝ)|=(5347941121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2076627709/10000000000 : ℝ)|^2181 ≤ (12821664249937/100000000000000 : ℝ)^1669
        have hw : |(-2076627709/10000000000 : ℝ)|=(2076627709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246059319/10000000000 : ℝ)|^2181 ≤ (21520694633013/50000000000000 : ℝ)^1669
        have hw : |(5246059319/10000000000 : ℝ)|=(5246059319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s5_2 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673970557/5000000000 : ℝ)*x 0 + (5246059167/10000000000 : ℝ)*x 1 + (-2076627921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673970557/5000000000 : ℝ)^2181 ≤ (5517118299487/12500000000000 : ℝ)^1669 := by
    have hnat : (2673970557 : ℕ)^2181*12500000000000^1669 ≤ 5517118299487^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673970557 5000000000 5517118299487 12500000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246059167/10000000000 : ℝ)^2181 ≤ (43041387636369/100000000000000 : ℝ)^1669 := by
    have hnat : (5246059167 : ℕ)^2181*100000000000000^1669 ≤ 43041387636369^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246059167 10000000000 43041387636369 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2076627921/10000000000 : ℝ)^2181 ≤ (12821665960429/100000000000000 : ℝ)^1669 := by
    have hnat : (2076627921 : ℕ)^2181*100000000000000^1669 ≤ 12821665960429^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076627921 10000000000 12821665960429 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673970557/5000000000 : ℝ), (5246059167/10000000000 : ℝ), (-2076627921/10000000000 : ℝ)] ![(5517118299487/12500000000000 : ℝ), (43041387636369/100000000000000 : ℝ), (12821665960429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673970557/5000000000 : ℝ)|^2181 ≤ (5517118299487/12500000000000 : ℝ)^1669
        have hw : |(2673970557/5000000000 : ℝ)|=(2673970557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246059167/10000000000 : ℝ)|^2181 ≤ (43041387636369/100000000000000 : ℝ)^1669
        have hw : |(5246059167/10000000000 : ℝ)|=(5246059167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2076627921/10000000000 : ℝ)|^2181 ≤ (12821665960429/100000000000000 : ℝ)^1669
        have hw : |(-2076627921/10000000000 : ℝ)|=(2076627921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s5_3 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (862231013/2000000000 : ℝ)*x 0 + (1324479/3200000 : ℝ)*x 1 + (4489810483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862231013/2000000000 : ℝ)^2181 ≤ (16652051677761/50000000000000 : ℝ)^1669 := by
    have hnat : (862231013 : ℕ)^2181*50000000000000^1669 ≤ 16652051677761^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862231013 2000000000 16652051677761 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1324479/3200000 : ℝ)^2181 ≤ (6315384601139/20000000000000 : ℝ)^1669 := by
    have hnat : (1324479 : ℕ)^2181*20000000000000^1669 ≤ 6315384601139^1669*3200000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324479 3200000 6315384601139 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489810483/10000000000 : ℝ)^2181 ≤ (35118973622183/100000000000000 : ℝ)^1669 := by
    have hnat : (4489810483 : ℕ)^2181*100000000000000^1669 ≤ 35118973622183^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489810483 10000000000 35118973622183 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862231013/2000000000 : ℝ), (1324479/3200000 : ℝ), (4489810483/10000000000 : ℝ)] ![(16652051677761/50000000000000 : ℝ), (6315384601139/20000000000000 : ℝ), (35118973622183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862231013/2000000000 : ℝ)|^2181 ≤ (16652051677761/50000000000000 : ℝ)^1669
        have hw : |(862231013/2000000000 : ℝ)|=(862231013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1324479/3200000 : ℝ)|^2181 ≤ (6315384601139/20000000000000 : ℝ)^1669
        have hw : |(1324479/3200000 : ℝ)|=(1324479/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489810483/10000000000 : ℝ)|^2181 ≤ (35118973622183/100000000000000 : ℝ)^1669
        have hw : |(4489810483/10000000000 : ℝ)|=(4489810483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s5_4 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-996616077/5000000000 : ℝ)*x 0 + (5246650279/10000000000 : ℝ)*x 1 + (540924789/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (996616077/5000000000 : ℝ)^2181 ≤ (3038245757693/25000000000000 : ℝ)^1669 := by
    have hnat : (996616077 : ℕ)^2181*25000000000000^1669 ≤ 3038245757693^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996616077 5000000000 3038245757693 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246650279/10000000000 : ℝ)^2181 ≤ (4304772530737/10000000000000 : ℝ)^1669 := by
    have hnat : (5246650279 : ℕ)^2181*10000000000000^1669 ≤ 4304772530737^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246650279 10000000000 4304772530737 10000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540924789/1000000000 : ℝ)^2181 ≤ (22399645830071/50000000000000 : ℝ)^1669 := by
    have hnat : (540924789 : ℕ)^2181*50000000000000^1669 ≤ 22399645830071^1669*1000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540924789 1000000000 22399645830071 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-996616077/5000000000 : ℝ), (5246650279/10000000000 : ℝ), (540924789/1000000000 : ℝ)] ![(3038245757693/25000000000000 : ℝ), (4304772530737/10000000000000 : ℝ), (22399645830071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-996616077/5000000000 : ℝ)|^2181 ≤ (3038245757693/25000000000000 : ℝ)^1669
        have hw : |(-996616077/5000000000 : ℝ)|=(996616077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246650279/10000000000 : ℝ)|^2181 ≤ (4304772530737/10000000000000 : ℝ)^1669
        have hw : |(5246650279/10000000000 : ℝ)|=(5246650279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540924789/1000000000 : ℝ)|^2181 ≤ (22399645830071/50000000000000 : ℝ)^1669
        have hw : |(540924789/1000000000 : ℝ)|=(540924789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s5_5 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305477201/10000000000 : ℝ)*x 0 + (-1913439427/10000000000 : ℝ)*x 1 + (2704623917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305477201/10000000000 : ℝ)^2181 ≤ (10919884330461/25000000000000 : ℝ)^1669 := by
    have hnat : (5305477201 : ℕ)^2181*25000000000000^1669 ≤ 10919884330461^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305477201 10000000000 10919884330461 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1913439427/10000000000 : ℝ)^2181 ≤ (11521171603107/100000000000000 : ℝ)^1669 := by
    have hnat : (1913439427 : ℕ)^2181*100000000000000^1669 ≤ 11521171603107^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913439427 10000000000 11521171603107 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704623917/5000000000 : ℝ)^2181 ≤ (44799291054073/100000000000000 : ℝ)^1669 := by
    have hnat : (2704623917 : ℕ)^2181*100000000000000^1669 ≤ 44799291054073^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704623917 5000000000 44799291054073 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305477201/10000000000 : ℝ), (-1913439427/10000000000 : ℝ), (2704623917/5000000000 : ℝ)] ![(10919884330461/25000000000000 : ℝ), (11521171603107/100000000000000 : ℝ), (44799291054073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305477201/10000000000 : ℝ)|^2181 ≤ (10919884330461/25000000000000 : ℝ)^1669
        have hw : |(5305477201/10000000000 : ℝ)|=(5305477201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1913439427/10000000000 : ℝ)|^2181 ≤ (11521171603107/100000000000000 : ℝ)^1669
        have hw : |(-1913439427/10000000000 : ℝ)|=(1913439427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704623917/5000000000 : ℝ)|^2181 ≤ (44799291054073/100000000000000 : ℝ)^1669
        have hw : |(2704623917/5000000000 : ℝ)|=(2704623917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s5_6 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305477149/10000000000 : ℝ)*x 0 + (1352311969/2500000000 : ℝ)*x 1 + (-956719721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305477149/10000000000 : ℝ)^2181 ≤ (54599420953/125000000000 : ℝ)^1669 := by
    have hnat : (5305477149 : ℕ)^2181*125000000000^1669 ≤ 54599420953^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305477149 10000000000 54599420953 125000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352311969/2500000000 : ℝ)^2181 ≤ (358394332069/800000000000 : ℝ)^1669 := by
    have hnat : (1352311969 : ℕ)^2181*800000000000^1669 ≤ 358394332069^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352311969 2500000000 358394332069 800000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (956719721/5000000000 : ℝ)^2181 ≤ (2880292930283/25000000000000 : ℝ)^1669 := by
    have hnat : (956719721 : ℕ)^2181*25000000000000^1669 ≤ 2880292930283^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956719721 5000000000 2880292930283 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305477149/10000000000 : ℝ), (1352311969/2500000000 : ℝ), (-956719721/5000000000 : ℝ)] ![(54599420953/125000000000 : ℝ), (358394332069/800000000000 : ℝ), (2880292930283/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305477149/10000000000 : ℝ)|^2181 ≤ (54599420953/125000000000 : ℝ)^1669
        have hw : |(5305477149/10000000000 : ℝ)|=(5305477149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352311969/2500000000 : ℝ)|^2181 ≤ (358394332069/800000000000 : ℝ)^1669
        have hw : |(1352311969/2500000000 : ℝ)|=(1352311969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-956719721/5000000000 : ℝ)|^2181 ≤ (2880292930283/25000000000000 : ℝ)^1669
        have hw : |(-956719721/5000000000 : ℝ)|=(956719721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s5_7 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4311180603/10000000000 : ℝ)*x 0 + (4488544801/10000000000 : ℝ)*x 1 + (517533571/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311180603/10000000000 : ℝ)^2181 ≤ (33304361160149/100000000000000 : ℝ)^1669 := by
    have hnat : (4311180603 : ℕ)^2181*100000000000000^1669 ≤ 33304361160149^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311180603 10000000000 33304361160149 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488544801/10000000000 : ℝ)^2181 ≤ (35106037057699/100000000000000 : ℝ)^1669 := by
    have hnat : (4488544801 : ℕ)^2181*100000000000000^1669 ≤ 35106037057699^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488544801 10000000000 35106037057699 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517533571/1250000000 : ℝ)^2181 ≤ (31589601765793/100000000000000 : ℝ)^1669 := by
    have hnat : (517533571 : ℕ)^2181*100000000000000^1669 ≤ 31589601765793^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517533571 1250000000 31589601765793 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311180603/10000000000 : ℝ), (4488544801/10000000000 : ℝ), (517533571/1250000000 : ℝ)] ![(33304361160149/100000000000000 : ℝ), (35106037057699/100000000000000 : ℝ), (31589601765793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311180603/10000000000 : ℝ)|^2181 ≤ (33304361160149/100000000000000 : ℝ)^1669
        have hw : |(4311180603/10000000000 : ℝ)|=(4311180603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488544801/10000000000 : ℝ)|^2181 ≤ (35106037057699/100000000000000 : ℝ)^1669
        have hw : |(4488544801/10000000000 : ℝ)|=(4488544801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517533571/1250000000 : ℝ)|^2181 ≤ (31589601765793/100000000000000 : ℝ)^1669
        have hw : |(517533571/1250000000 : ℝ)|=(517533571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1402_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7389/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11279/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3687/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7389/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11251/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7389/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11251/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7389/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11251/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7389/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11251/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7389/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11251/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7389/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11251/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11251/100000 : ℝ) ^ (4361/1024 : ℝ) ≤ (1820761807796923/20000000000000000000 : ℝ) := by
    have hpowers : (11251/100000 : ℝ)^4361 ≤ (1820761807796923/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11251 : ℕ)^4361*20000000000000000000^1024 ≤ 1820761807796923^1024*100000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11251 100000 1820761807796923 20000000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11251/100000 : ℝ)) (X := (1820761807796923/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7389/50000 : ℝ) ^ (4361/1024 : ℝ) ≤ (29078249901611533/100000000000000000000 : ℝ) := by
    have hpowers : (7389/50000 : ℝ)^4361 ≤ (29078249901611533/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7389 : ℕ)^4361*100000000000000000000^1024 ≤ 29078249901611533^1024*50000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7389 50000 29078249901611533 100000000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7389/50000 : ℝ)) (X := (29078249901611533/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001820761807796923/10000000000000000000 : ℝ) ≤ (50002137503123/50000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (10001820761807796923/10000000000000000000 : ℝ)^1024 ≤ (50002137503123/50000000000000 : ℝ)^4361 := by
      have hnat : (10001820761807796923 : ℕ)^1024*50000000000000^4361 ≤ 50002137503123^4361*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001820761807796923 10000000000000000000 50002137503123 50000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50002137503123/50000000000000 : ℝ)) (X := (10001820761807796923/10000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009545514735149037/25000000000000000000 : ℝ) ≤ (10000896416372967/10000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (25009545514735149037/25000000000000000000 : ℝ)^1024 ≤ (10000896416372967/10000000000000000 : ℝ)^4361 := by
      have hnat : (25009545514735149037 : ℕ)^1024*10000000000000000^4361 ≤ 10000896416372967^4361*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009545514735149037 25000000000000000000 10000896416372967 10000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000896416372967/10000000000000000 : ℝ)) (X := (25009545514735149037/25000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029078249901611533/50000000000000000000 : ℝ) ≤ (5000682666060667/5000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (50029078249901611533/50000000000000000000 : ℝ)^1024 ≤ (5000682666060667/5000000000000000 : ℝ)^4361 := by
      have hnat : (50029078249901611533 : ℕ)^1024*5000000000000000^4361 ≤ 5000682666060667^4361*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029078249901611533 50000000000000000000 5000682666060667 5000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000682666060667/5000000000000000 : ℝ)) (X := (50029078249901611533/50000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1820761807796923/20000000000000000000 : ℝ) ≤ ((17630478126266604983/17635000000000000000 : ℝ)+2*(468915748367/352700000000000 : ℝ)*(11251/100000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (17630478126266604983/17635000000000000000 : ℝ)+2*(468915748367/352700000000000 : ℝ)*(11251/100000 : ℝ)=(50002137503123/50000000000000 : ℝ) by norm_num, show 1+2*(1820761807796923/20000000000000000000 : ℝ)=(10001820761807796923/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29078249901611533/100000000000000000000 : ℝ)+(1820761807796923/20000000000000000000 : ℝ) ≤ ((17630478126266604983/17635000000000000000 : ℝ)+(468915748367/352700000000000 : ℝ)*((7389/50000 : ℝ)+(11251/100000 : ℝ)))^(4361/1024 : ℝ) := by
    rw [show (17630478126266604983/17635000000000000000 : ℝ)+(468915748367/352700000000000 : ℝ)*((7389/50000 : ℝ)+(11251/100000 : ℝ))=(10000896416372967/10000000000000000 : ℝ) by norm_num, show 1+(29078249901611533/100000000000000000000 : ℝ)+(1820761807796923/20000000000000000000 : ℝ)=(25009545514735149037/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29078249901611533/100000000000000000000 : ℝ) ≤ ((17630478126266604983/17635000000000000000 : ℝ)+2*(468915748367/352700000000000 : ℝ)*(7389/50000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (17630478126266604983/17635000000000000000 : ℝ)+2*(468915748367/352700000000000 : ℝ)*(7389/50000 : ℝ)=(5000682666060667/5000000000000000 : ℝ) by norm_num, show 1+2*(29078249901611533/100000000000000000000 : ℝ)=(50029078249901611533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17630478126266604983/17635000000000000000 : ℝ)*(X 1 0+X 2 0)+(468915748367/352700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (7389/50000 : ℝ)) (c := (17630478126266604983/17635000000000000000 : ℝ)) (alpha := (468915748367/352700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17630478126266604983/17635000000000000000 : ℝ)*(X 0 1+X 2 1)+(468915748367/352700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (7389/50000 : ℝ)) (c := (17630478126266604983/17635000000000000000 : ℝ)) (alpha := (468915748367/352700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17630478126266604983/17635000000000000000 : ℝ)*(X 0 2+X 1 2)+(468915748367/352700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (7389/50000 : ℝ)) (c := (17630478126266604983/17635000000000000000 : ℝ)) (alpha := (468915748367/352700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1993219989/10000000000 : ℝ)*X 0 0+(5409842289/10000000000 : ℝ)*X 0 1+(5246059307/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347941121/10000000000 : ℝ)*X 1 0+(-2076627709/10000000000 : ℝ)*X 1 1+(5246059319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673970557/5000000000 : ℝ)*X 2 0+(5246059167/10000000000 : ℝ)*X 2 1+(-2076627921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((862231013/2000000000 : ℝ)*X 0 0+(1324479/3200000 : ℝ)*X 0 1+(4489810483/10000000000 : ℝ)*X 0 2+(862231013/2000000000 : ℝ)*X 1 0+(1324479/3200000 : ℝ)*X 1 1+(4489810483/10000000000 : ℝ)*X 1 2+(862231013/2000000000 : ℝ)*X 2 0+(1324479/3200000 : ℝ)*X 2 1+(4489810483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-996616077/5000000000 : ℝ)*X 0 0+(5246650279/10000000000 : ℝ)*X 0 1+(540924789/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305477201/10000000000 : ℝ)*X 1 0+(-1913439427/10000000000 : ℝ)*X 1 1+(2704623917/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305477149/10000000000 : ℝ)*X 2 0+(1352311969/2500000000 : ℝ)*X 2 1+(-956719721/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4311180603/10000000000 : ℝ)*X 0 0+(4488544801/10000000000 : ℝ)*X 0 1+(517533571/1250000000 : ℝ)*X 0 2+(4311180603/10000000000 : ℝ)*X 1 0+(4488544801/10000000000 : ℝ)*X 1 1+(517533571/1250000000 : ℝ)*X 1 2+(4311180603/10000000000 : ℝ)*X 2 0+(4488544801/10000000000 : ℝ)*X 2 1+(517533571/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (129247236488331854464131/17635000000000000000000000000 : ℝ) := by norm_num
    linear_combination (776299233/100000000000000 : ℝ)*(base19) + (873614417/100000000000000 : ℝ)*(base23) + (54755681/100000000000000 : ℝ)*(lower2) + (27768313/25000000000000 : ℝ)*(lower4) + (182663179/100000000000000 : ℝ)*(lower5) + (2239055710398257/50000000000000 : ℝ)*(major0) + (2239055710398257/50000000000000 : ℝ)*(major1) + (2239055710398257/50000000000000 : ℝ)*(major2) + (244226866333577/4000000000000 : ℝ)*(sp0) + (6105693945840273/100000000000000 : ℝ)*(sp1) + (6105693848525089/100000000000000 : ℝ)*(sp2) + (142526057398941/5000000000000 : ℝ)*(sp3) + (23063800081/100000000000000 : ℝ)*(sp4) + (672717409/10000000000000 : ℝ)*(sp7) + (285052787515291/10000000000000 : ℝ)*(f.failure) + (3052847361069753/50000000000000 : ℝ)*(f.sum) + (45919673916053/17635000000000000000000000000 : ℝ)*base65 + (1487489327202164631/881750000000000000000000000000000 : ℝ)*base67 + (7624445277357085369/881750000000000000000000000000000 : ℝ)*base70 + (2085322513398585369/881750000000000000000000000000000 : ℝ)*base72 + (35276241395683/17635000000000000000000000000 : ℝ)*base73 + (3626864139369414631/881750000000000000000000000000000 : ℝ)*base75 + (16564533721713664631/881750000000000000000000000000000 : ℝ)*base77 + (203816896886085369/881750000000000000000000000000000 : ℝ)*base80 + (11719167433347/17635000000000000000000000000 : ℝ)*base82 + (2192129/1000000000000000000000 : ℝ)*base89 + (2192129/1000000000000000000000 : ℝ)*base91 + (2192129/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (206555479727280870655953/17635000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2056706779/100000000000000 : ℝ)*(base19) + (521732201/25000000000000 : ℝ)*(base23) + (213436129/100000000000000 : ℝ)*(upper3) + (187371/400000000000 : ℝ)*(lower4) + (119614977/50000000000000 : ℝ)*(upper5) + (4510717387747373/100000000000000 : ℝ)*(major0) + (4510717387747373/100000000000000 : ℝ)*(major1) + (4510717387747373/100000000000000 : ℝ)*(major2) + (42668819963/100000000000000 : ℝ)*(sp1) + (42944832649/100000000000000 : ℝ)*(sp2) + (6150151283222891/100000000000000 : ℝ)*(sp4) + (6150106557696149/100000000000000 : ℝ)*(sp5) + (3075053125730719/50000000000000 : ℝ)*(sp6) + (1435641550922351/50000000000000 : ℝ)*(sp7) + (1435641550922351/50000000000000 : ℝ)*(f.failure) + (6150151283222891/100000000000000 : ℝ)*(f.sum) + (32328474862529/17635000000000000000000000000 : ℝ)*base66 + (16187603779003009659/1763500000000000000000000000000000 : ℝ)*base67 + (4504504301019490341/1763500000000000000000000000000000 : ℝ)*base70 + (16859472528721490341/1763500000000000000000000000000000 : ℝ)*base72 + (8232116486771/17635000000000000000000000000 : ℝ)*base73 + (44703623963845009659/1763500000000000000000000000000000 : ℝ)*base75 + (207832527302509659/1763500000000000000000000000000000 : ℝ)*base77 + (1236503633003990341/1763500000000000000000000000000000 : ℝ)*base80 + (12815512459047/8817500000000000000000000000 : ℝ)*base82 + (54017731/5000000000000000000000 : ℝ)*base90 + (54017731/5000000000000000000000 : ℝ)*base92 + (54017731/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1402_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7389/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1402_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1402_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7943/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1402_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1402_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1402_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7943/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1402_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

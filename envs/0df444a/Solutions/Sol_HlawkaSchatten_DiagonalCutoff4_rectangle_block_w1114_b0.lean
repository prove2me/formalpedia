-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1114_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:06:30.836906+00:00
-- url     : https://prove2.me/submissions/45e63a93-6fef-49c6-9f06-f646ef4d224d

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
theorem support_rectangle_w1114_s0_0 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-950352199/5000000000 : ℝ)*x 0 + (3030412187/5000000000 : ℝ)*x 1 + (2388460447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (950352199/5000000000 : ℝ)^8307 ≤ (11039999929137/100000000000000 : ℝ)^6259 := by
    have hnat : (950352199 : ℕ)^8307*100000000000000^6259 ≤ 11039999929137^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950352199 5000000000 11039999929137 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3030412187/5000000000 : ℝ)^8307 ≤ (25724335083537/50000000000000 : ℝ)^6259 := by
    have hnat : (3030412187 : ℕ)^8307*50000000000000^6259 ≤ 25724335083537^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3030412187 5000000000 25724335083537 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2388460447/5000000000 : ℝ)^8307 ≤ (37511329890909/100000000000000 : ℝ)^6259 := by
    have hnat : (2388460447 : ℕ)^8307*100000000000000^6259 ≤ 37511329890909^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388460447 5000000000 37511329890909 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-950352199/5000000000 : ℝ), (3030412187/5000000000 : ℝ), (2388460447/5000000000 : ℝ)] ![(11039999929137/100000000000000 : ℝ), (25724335083537/50000000000000 : ℝ), (37511329890909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-950352199/5000000000 : ℝ)|^8307 ≤ (11039999929137/100000000000000 : ℝ)^6259
        have hw : |(-950352199/5000000000 : ℝ)|=(950352199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3030412187/5000000000 : ℝ)|^8307 ≤ (25724335083537/50000000000000 : ℝ)^6259
        have hw : |(3030412187/5000000000 : ℝ)|=(3030412187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2388460447/5000000000 : ℝ)|^8307 ≤ (37511329890909/100000000000000 : ℝ)^6259
        have hw : |(2388460447/5000000000 : ℝ)|=(2388460447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s0_1 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5518370709/10000000000 : ℝ)*x 0 + (-659580829/2500000000 : ℝ)*x 1 + (1194230237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518370709/10000000000 : ℝ)^8307 ≤ (22714287392187/50000000000000 : ℝ)^6259 := by
    have hnat : (5518370709 : ℕ)^8307*50000000000000^6259 ≤ 22714287392187^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518370709 10000000000 22714287392187 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659580829/2500000000 : ℝ)^8307 ≤ (4265023686149/25000000000000 : ℝ)^6259 := by
    have hnat : (659580829 : ℕ)^8307*25000000000000^6259 ≤ 4265023686149^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659580829 2500000000 4265023686149 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194230237/2500000000 : ℝ)^8307 ≤ (375113304537/1000000000000 : ℝ)^6259 := by
    have hnat : (1194230237 : ℕ)^8307*1000000000000^6259 ≤ 375113304537^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194230237 2500000000 375113304537 1000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518370709/10000000000 : ℝ), (-659580829/2500000000 : ℝ), (1194230237/2500000000 : ℝ)] ![(22714287392187/50000000000000 : ℝ), (4265023686149/25000000000000 : ℝ), (375113304537/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518370709/10000000000 : ℝ)|^8307 ≤ (22714287392187/50000000000000 : ℝ)^6259
        have hw : |(5518370709/10000000000 : ℝ)|=(5518370709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-659580829/2500000000 : ℝ)|^8307 ≤ (4265023686149/25000000000000 : ℝ)^6259
        have hw : |(-659580829/2500000000 : ℝ)|=(659580829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1194230237/2500000000 : ℝ)|^8307 ≤ (375113304537/1000000000000 : ℝ)^6259
        have hw : |(1194230237/2500000000 : ℝ)|=(1194230237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s0_2 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5518370877/10000000000 : ℝ)*x 0 + (4776920789/10000000000 : ℝ)*x 1 + (-82447603/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518370877/10000000000 : ℝ)^8307 ≤ (22714288309963/50000000000000 : ℝ)^6259 := by
    have hnat : (5518370877 : ℕ)^8307*50000000000000^6259 ≤ 22714288309963^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518370877 10000000000 22714288309963 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4776920789/10000000000 : ℝ)^8307 ≤ (37511328796593/100000000000000 : ℝ)^6259 := by
    have hnat : (4776920789 : ℕ)^8307*100000000000000^6259 ≤ 37511328796593^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4776920789 10000000000 37511328796593 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82447603/312500000 : ℝ)^8307 ≤ (8530047286477/50000000000000 : ℝ)^6259 := by
    have hnat : (82447603 : ℕ)^8307*50000000000000^6259 ≤ 8530047286477^6259*312500000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82447603 312500000 8530047286477 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518370877/10000000000 : ℝ), (4776920789/10000000000 : ℝ), (-82447603/312500000 : ℝ)] ![(22714288309963/50000000000000 : ℝ), (37511328796593/100000000000000 : ℝ), (8530047286477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518370877/10000000000 : ℝ)|^8307 ≤ (22714288309963/50000000000000 : ℝ)^6259
        have hw : |(5518370877/10000000000 : ℝ)|=(5518370877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4776920789/10000000000 : ℝ)|^8307 ≤ (37511328796593/100000000000000 : ℝ)^6259
        have hw : |(4776920789/10000000000 : ℝ)|=(4776920789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-82447603/312500000 : ℝ)|^8307 ≤ (8530047286477/50000000000000 : ℝ)^6259
        have hw : |(-82447603/312500000 : ℝ)|=(82447603/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s0_3 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2101632541/5000000000 : ℝ)*x 0 + (312241137/1000000000 : ℝ)*x 1 + (1132536741/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101632541/5000000000 : ℝ)^8307 ≤ (1582672510001/5000000000000 : ℝ)^6259 := by
    have hnat : (2101632541 : ℕ)^8307*5000000000000^6259 ≤ 1582672510001^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101632541 5000000000 1582672510001 5000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312241137/1000000000 : ℝ)^8307 ≤ (21334517663157/100000000000000 : ℝ)^6259 := by
    have hnat : (312241137 : ℕ)^8307*100000000000000^6259 ≤ 21334517663157^6259*1000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312241137 1000000000 21334517663157 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132536741/2000000000 : ℝ)^8307 ≤ (11753008028579/25000000000000 : ℝ)^6259 := by
    have hnat : (1132536741 : ℕ)^8307*25000000000000^6259 ≤ 11753008028579^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132536741 2000000000 11753008028579 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2101632541/5000000000 : ℝ), (312241137/1000000000 : ℝ), (1132536741/2000000000 : ℝ)] ![(1582672510001/5000000000000 : ℝ), (21334517663157/100000000000000 : ℝ), (11753008028579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2101632541/5000000000 : ℝ)|^8307 ≤ (1582672510001/5000000000000 : ℝ)^6259
        have hw : |(2101632541/5000000000 : ℝ)|=(2101632541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(312241137/1000000000 : ℝ)|^8307 ≤ (21334517663157/100000000000000 : ℝ)^6259
        have hw : |(312241137/1000000000 : ℝ)|=(312241137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132536741/2000000000 : ℝ)|^8307 ≤ (11753008028579/25000000000000 : ℝ)^6259
        have hw : |(1132536741/2000000000 : ℝ)|=(1132536741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s0_4 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-952967027/5000000000 : ℝ)*x 0 + (4810055523/10000000000 : ℝ)*x 1 + (1506631551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (952967027/5000000000 : ℝ)^8307 ≤ (11080333084933/100000000000000 : ℝ)^6259 := by
    have hnat : (952967027 : ℕ)^8307*100000000000000^6259 ≤ 11080333084933^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952967027 5000000000 11080333084933 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4810055523/10000000000 : ℝ)^8307 ≤ (18928526173103/50000000000000 : ℝ)^6259 := by
    have hnat : (4810055523 : ℕ)^8307*50000000000000^6259 ≤ 18928526173103^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4810055523 10000000000 18928526173103 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1506631551/2500000000 : ℝ)^8307 ≤ (25531307274091/50000000000000 : ℝ)^6259 := by
    have hnat : (1506631551 : ℕ)^8307*50000000000000^6259 ≤ 25531307274091^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506631551 2500000000 25531307274091 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-952967027/5000000000 : ℝ), (4810055523/10000000000 : ℝ), (1506631551/2500000000 : ℝ)] ![(11080333084933/100000000000000 : ℝ), (18928526173103/50000000000000 : ℝ), (25531307274091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-952967027/5000000000 : ℝ)|^8307 ≤ (11080333084933/100000000000000 : ℝ)^6259
        have hw : |(-952967027/5000000000 : ℝ)|=(952967027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4810055523/10000000000 : ℝ)|^8307 ≤ (18928526173103/50000000000000 : ℝ)^6259
        have hw : |(4810055523/10000000000 : ℝ)|=(4810055523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1506631551/2500000000 : ℝ)|^8307 ≤ (25531307274091/50000000000000 : ℝ)^6259
        have hw : |(1506631551/2500000000 : ℝ)|=(1506631551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s0_5 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5169643729/10000000000 : ℝ)*x 0 + (-1388718833/10000000000 : ℝ)*x 1 + (6026528799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5169643729/10000000000 : ℝ)^8307 ≤ (5207297775911/12500000000000 : ℝ)^6259 := by
    have hnat : (5169643729 : ℕ)^8307*12500000000000^6259 ≤ 5207297775911^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169643729 10000000000 5207297775911 12500000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1388718833/10000000000 : ℝ)^8307 ≤ (7278974045947/100000000000000 : ℝ)^6259 := by
    have hnat : (1388718833 : ℕ)^8307*100000000000000^6259 ≤ 7278974045947^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388718833 10000000000 7278974045947 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6026528799/10000000000 : ℝ)^8307 ≤ (2553132186501/5000000000000 : ℝ)^6259 := by
    have hnat : (6026528799 : ℕ)^8307*5000000000000^6259 ≤ 2553132186501^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6026528799 10000000000 2553132186501 5000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5169643729/10000000000 : ℝ), (-1388718833/10000000000 : ℝ), (6026528799/10000000000 : ℝ)] ![(5207297775911/12500000000000 : ℝ), (7278974045947/100000000000000 : ℝ), (2553132186501/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5169643729/10000000000 : ℝ)|^8307 ≤ (5207297775911/12500000000000 : ℝ)^6259
        have hw : |(5169643729/10000000000 : ℝ)|=(5169643729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1388718833/10000000000 : ℝ)|^8307 ≤ (7278974045947/100000000000000 : ℝ)^6259
        have hw : |(-1388718833/10000000000 : ℝ)|=(1388718833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6026528799/10000000000 : ℝ)|^8307 ≤ (2553132186501/5000000000000 : ℝ)^6259
        have hw : |(6026528799/10000000000 : ℝ)|=(6026528799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s0_6 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2584823527/5000000000 : ℝ)*x 0 + (6026526689/10000000000 : ℝ)*x 1 + (-347179283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584823527/5000000000 : ℝ)^8307 ≤ (41658417768187/100000000000000 : ℝ)^6259 := by
    have hnat : (2584823527 : ℕ)^8307*100000000000000^6259 ≤ 41658417768187^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584823527 5000000000 41658417768187 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6026526689/10000000000 : ℝ)^8307 ≤ (10212524000441/20000000000000 : ℝ)^6259 := by
    have hnat : (6026526689 : ℕ)^8307*20000000000000^6259 ≤ 10212524000441^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6026526689 10000000000 10212524000441 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (347179283/2500000000 : ℝ)^8307 ≤ (3639481106413/50000000000000 : ℝ)^6259 := by
    have hnat : (347179283 : ℕ)^8307*50000000000000^6259 ≤ 3639481106413^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347179283 2500000000 3639481106413 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584823527/5000000000 : ℝ), (6026526689/10000000000 : ℝ), (-347179283/2500000000 : ℝ)] ![(41658417768187/100000000000000 : ℝ), (10212524000441/20000000000000 : ℝ), (3639481106413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584823527/5000000000 : ℝ)|^8307 ≤ (41658417768187/100000000000000 : ℝ)^6259
        have hw : |(2584823527/5000000000 : ℝ)|=(2584823527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6026526689/10000000000 : ℝ)|^8307 ≤ (10212524000441/20000000000000 : ℝ)^6259
        have hw : |(6026526689/10000000000 : ℝ)|=(6026526689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-347179283/2500000000 : ℝ)|^8307 ≤ (3639481106413/50000000000000 : ℝ)^6259
        have hw : |(-347179283/2500000000 : ℝ)|=(347179283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s0_7 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (105340219/250000000 : ℝ)*x 0 + (349820497/625000000 : ℝ)*x 1 + (3190268609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105340219/250000000 : ℝ)^8307 ≤ (7939218664007/25000000000000 : ℝ)^6259 := by
    have hnat : (105340219 : ℕ)^8307*25000000000000^6259 ≤ 7939218664007^6259*250000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105340219 250000000 7939218664007 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349820497/625000000 : ℝ)^8307 ≤ (23145535950537/50000000000000 : ℝ)^6259 := by
    have hnat : (349820497 : ℕ)^8307*50000000000000^6259 ≤ 23145535950537^6259*625000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349820497 625000000 23145535950537 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3190268609/10000000000 : ℝ)^8307 ≤ (21952053431967/100000000000000 : ℝ)^6259 := by
    have hnat : (3190268609 : ℕ)^8307*100000000000000^6259 ≤ 21952053431967^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3190268609 10000000000 21952053431967 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105340219/250000000 : ℝ), (349820497/625000000 : ℝ), (3190268609/10000000000 : ℝ)] ![(7939218664007/25000000000000 : ℝ), (23145535950537/50000000000000 : ℝ), (21952053431967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105340219/250000000 : ℝ)|^8307 ≤ (7939218664007/25000000000000 : ℝ)^6259
        have hw : |(105340219/250000000 : ℝ)|=(105340219/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(349820497/625000000 : ℝ)|^8307 ≤ (23145535950537/50000000000000 : ℝ)^6259
        have hw : |(349820497/625000000 : ℝ)|=(349820497/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3190268609/10000000000 : ℝ)|^8307 ≤ (21952053431967/100000000000000 : ℝ)^6259
        have hw : |(3190268609/10000000000 : ℝ)|=(3190268609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1114_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (149/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27923/100000 : ℝ)*pair X 0 0 := by
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
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (4153/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4153 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4153*1^1024 ≤ 0^1024*1^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4153/1024 : ℝ) ≤ (243270253557478713/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4153 ≤ (243270253557478713/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4153*10000000000000000000^1024 ≤ 243270253557478713^1024*5^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 243270253557478713 10000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (243270253557478713/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4153 := by
      have hnat : (1 : ℕ)^1024*1^4153 ≤ 1^4153*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10243270253557478713/10000000000000000000 : ℝ) ≤ (5029720411867629/5000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (10243270253557478713/10000000000000000000 : ℝ)^1024 ≤ (5029720411867629/5000000000000000 : ℝ)^4153 := by
      have hnat : (10243270253557478713 : ℕ)^1024*5000000000000000^4153 ≤ 5029720411867629^4153*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10243270253557478713 10000000000000000000 5029720411867629 5000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029720411867629/5000000000000000 : ℝ)) (X := (10243270253557478713/10000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5243270253557478713/5000000000000000000 : ℝ) ≤ (2529720411867629/2500000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (5243270253557478713/5000000000000000000 : ℝ)^1024 ≤ (2529720411867629/2500000000000000 : ℝ)^4153 := by
      have hnat : (5243270253557478713 : ℕ)^1024*2500000000000000^4153 ≤ 2529720411867629^4153*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5243270253557478713 5000000000000000000 2529720411867629 2500000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2529720411867629/2500000000000000 : ℝ)) (X := (5243270253557478713/5000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(29720411867629/2000000000000000 : ℝ)*(0 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(29720411867629/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(243270253557478713/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(29720411867629/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4153/1024 : ℝ) := by
    rw [show (1 : ℝ)+(29720411867629/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5029720411867629/5000000000000000 : ℝ) by norm_num, show 1+(243270253557478713/10000000000000000000 : ℝ)+(0 : ℝ)=(10243270253557478713/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(243270253557478713/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(29720411867629/2000000000000000 : ℝ)*(2/5 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(29720411867629/2000000000000000 : ℝ)*(2/5 : ℝ)=(2529720411867629/2500000000000000 : ℝ) by norm_num, show 1+2*(243270253557478713/10000000000000000000 : ℝ)=(5243270253557478713/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(29720411867629/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29720411867629/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(29720411867629/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29720411867629/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(29720411867629/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29720411867629/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-950352199/5000000000 : ℝ)*X 0 0+(3030412187/5000000000 : ℝ)*X 0 1+(2388460447/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5518370709/10000000000 : ℝ)*X 1 0+(-659580829/2500000000 : ℝ)*X 1 1+(1194230237/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5518370877/10000000000 : ℝ)*X 2 0+(4776920789/10000000000 : ℝ)*X 2 1+(-82447603/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2101632541/5000000000 : ℝ)*X 0 0+(312241137/1000000000 : ℝ)*X 0 1+(1132536741/2000000000 : ℝ)*X 0 2+(2101632541/5000000000 : ℝ)*X 1 0+(312241137/1000000000 : ℝ)*X 1 1+(1132536741/2000000000 : ℝ)*X 1 2+(2101632541/5000000000 : ℝ)*X 2 0+(312241137/1000000000 : ℝ)*X 2 1+(1132536741/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-952967027/5000000000 : ℝ)*X 0 0+(4810055523/10000000000 : ℝ)*X 0 1+(1506631551/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5169643729/10000000000 : ℝ)*X 1 0+(-1388718833/10000000000 : ℝ)*X 1 1+(6026528799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2584823527/5000000000 : ℝ)*X 2 0+(6026526689/10000000000 : ℝ)*X 2 1+(-347179283/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((105340219/250000000 : ℝ)*X 0 0+(349820497/625000000 : ℝ)*X 0 1+(3190268609/10000000000 : ℝ)*X 0 2+(105340219/250000000 : ℝ)*X 1 0+(349820497/625000000 : ℝ)*X 1 1+(3190268609/10000000000 : ℝ)*X 1 2+(105340219/250000000 : ℝ)*X 2 0+(349820497/625000000 : ℝ)*X 2 1+(3190268609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (151827775127960427/62500000000000000000000 : ℝ) := by norm_num
    linear_combination (431571/1562500000000 : ℝ)*(base1) + (18738849/3125000000000 : ℝ)*(base19) + (115306039/20000000000000 : ℝ)*(base23) + (9364987/20000000000000 : ℝ)*(base24) + (8941181/6250000000000 : ℝ)*(upper3) + (586269180437427/100000000000000 : ℝ)*(major0) + (586269180437427/100000000000000 : ℝ)*(major1) + (586269180437427/100000000000000 : ℝ)*(major2) + (389438359934007/50000000000000 : ℝ)*(sp0) + (389438691110937/50000000000000 : ℝ)*(sp1) + (97359669813739/12500000000000 : ℝ)*(sp2) + (15746367682093/4000000000000 : ℝ)*(sp3) + (1289617571/100000000000000 : ℝ)*(sp4) + (539181063/50000000000000 : ℝ)*(sp7) + (78732059606999/20000000000000 : ℝ)*(f.failure) + (389438990932521/50000000000000 : ℝ)*(f.sum) + (43048859049417/100000000000000000000000000000 : ℝ)*base66 + (375326427150583/200000000000000000000000000000 : ℝ)*base67 + (1279699869550583/200000000000000000000000000000 : ℝ)*base69 + (237790626150583/200000000000000000000000000000 : ℝ)*base71 + (63850460449417/100000000000000000000000000000 : ℝ)*base74 + (105340440849417/200000000000000000000000000000 : ℝ)*base76 + (302601794550583/200000000000000000000000000000 : ℝ)*base77 + (711632112649417/200000000000000000000000000000 : ℝ)*base80 + (500910550650583/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1211039/250000000000000000000 : ℝ)*base89 + (1211039/250000000000000000000 : ℝ)*base91 + (1211039/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (65266195470236542439991/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (142197211/20000000000000 : ℝ)*(base19) + (1779015849/100000000000000 : ℝ)*(base23) + (49614787/10000000000000 : ℝ)*(base39) + (72347127/25000000000000 : ℝ)*(base45) + (51610107/25000000000000 : ℝ)*(upper3) + (147310549/50000000000000 : ℝ)*(upper5) + (61876188671389/10000000000000 : ℝ)*(major0) + (61876188671389/10000000000000 : ℝ)*(major1) + (30938069528301/5000000000000 : ℝ)*(major2) + (212818181/25000000000000 : ℝ)*(sp2) + (822044987768013/100000000000000 : ℝ)*(sp4) + (411022138390979/50000000000000 : ℝ)*(sp5) + (82204285362731/10000000000000 : ℝ)*(sp6) + (415478071957909/100000000000000 : ℝ)*(sp7) + (415478071957909/100000000000000 : ℝ)*(f.failure) + (822045483915883/100000000000000 : ℝ)*(f.sum) + (28622752656661/20000000000000000000000000000 : ℝ)*base66 + (13869100401671/10000000000000000000000000000 : ℝ)*base68 + (39331822906681/20000000000000000000000000000 : ℝ)*base69 + (3708760951671/10000000000000000000000000000 : ℝ)*base72 + (105364536976661/20000000000000000000000000000 : ℝ)*base74 + (97069907106681/20000000000000000000000000000 : ℝ)*base75 + (10782082993319/20000000000000000000000000000 : ℝ)*base78 + (112923483686681/20000000000000000000000000000 : ℝ)*base79 + (74611606003319/10000000000000000000000000000 : ℝ)*base82 + (2585549/1250000000000000000000 : ℝ)*base89 + (2585549/1250000000000000000000 : ℝ)*base91 + (2585549/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1114_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (149/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27923/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1114_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1114_s1_0 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-526846763/2500000000 : ℝ)*x 0 + (2854530897/5000000000 : ℝ)*x 1 + (1249088259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526846763/2500000000 : ℝ)^8307 ≤ (3165246150757/25000000000000 : ℝ)^6259 := by
    have hnat : (526846763 : ℕ)^8307*25000000000000^6259 ≤ 3165246150757^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526846763 2500000000 3165246150757 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2854530897/5000000000 : ℝ)^8307 ≤ (47523736694011/100000000000000 : ℝ)^6259 := by
    have hnat : (2854530897 : ℕ)^8307*100000000000000^6259 ≤ 47523736694011^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2854530897 5000000000 47523736694011 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1249088259/2500000000 : ℝ)^8307 ≤ (3981527868173/10000000000000 : ℝ)^6259 := by
    have hnat : (1249088259 : ℕ)^8307*10000000000000^6259 ≤ 3981527868173^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249088259 2500000000 3981527868173 10000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526846763/2500000000 : ℝ), (2854530897/5000000000 : ℝ), (1249088259/2500000000 : ℝ)] ![(3165246150757/25000000000000 : ℝ), (47523736694011/100000000000000 : ℝ), (3981527868173/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526846763/2500000000 : ℝ)|^8307 ≤ (3165246150757/25000000000000 : ℝ)^6259
        have hw : |(-526846763/2500000000 : ℝ)|=(526846763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2854530897/5000000000 : ℝ)|^8307 ≤ (47523736694011/100000000000000 : ℝ)^6259
        have hw : |(2854530897/5000000000 : ℝ)|=(2854530897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1249088259/2500000000 : ℝ)|^8307 ≤ (3981527868173/10000000000000 : ℝ)^6259
        have hw : |(1249088259/2500000000 : ℝ)|=(1249088259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s1_1 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5420664267/10000000000 : ℝ)*x 0 + (-99702313/400000000 : ℝ)*x 1 + (4996352943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420664267/10000000000 : ℝ)^8307 ≤ (8872829600619/20000000000000 : ℝ)^6259 := by
    have hnat : (5420664267 : ℕ)^8307*20000000000000^6259 ≤ 8872829600619^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420664267 10000000000 8872829600619 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99702313/400000000 : ℝ)^8307 ≤ (3164114858163/20000000000000 : ℝ)^6259 := by
    have hnat : (99702313 : ℕ)^8307*20000000000000^6259 ≤ 3164114858163^6259*400000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99702313 400000000 3164114858163 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4996352943/10000000000 : ℝ)^8307 ≤ (3981527769813/10000000000000 : ℝ)^6259 := by
    have hnat : (4996352943 : ℕ)^8307*10000000000000^6259 ≤ 3981527769813^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4996352943 10000000000 3981527769813 10000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420664267/10000000000 : ℝ), (-99702313/400000000 : ℝ), (4996352943/10000000000 : ℝ)] ![(8872829600619/20000000000000 : ℝ), (3164114858163/20000000000000 : ℝ), (3981527769813/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420664267/10000000000 : ℝ)|^8307 ≤ (8872829600619/20000000000000 : ℝ)^6259
        have hw : |(5420664267/10000000000 : ℝ)|=(5420664267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-99702313/400000000 : ℝ)|^8307 ≤ (3164114858163/20000000000000 : ℝ)^6259
        have hw : |(-99702313/400000000 : ℝ)|=(99702313/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4996352943/10000000000 : ℝ)|^8307 ≤ (3981527769813/10000000000000 : ℝ)^6259
        have hw : |(4996352943/10000000000 : ℝ)|=(4996352943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s1_2 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5420665637/10000000000 : ℝ)*x 0 + (249817583/500000000 : ℝ)*x 1 + (-623139417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420665637/10000000000 : ℝ)^8307 ≤ (44364162884347/100000000000000 : ℝ)^6259 := by
    have hnat : (5420665637 : ℕ)^8307*100000000000000^6259 ≤ 44364162884347^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420665637 10000000000 44364162884347 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249817583/500000000 : ℝ)^8307 ≤ (39815264128671/100000000000000 : ℝ)^6259 := by
    have hnat : (249817583 : ℕ)^8307*100000000000000^6259 ≤ 39815264128671^6259*500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249817583 500000000 39815264128671 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (623139417/2500000000 : ℝ)^8307 ≤ (7910286484127/50000000000000 : ℝ)^6259 := by
    have hnat : (623139417 : ℕ)^8307*50000000000000^6259 ≤ 7910286484127^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623139417 2500000000 7910286484127 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420665637/10000000000 : ℝ), (249817583/500000000 : ℝ), (-623139417/2500000000 : ℝ)] ![(44364162884347/100000000000000 : ℝ), (39815264128671/100000000000000 : ℝ), (7910286484127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420665637/10000000000 : ℝ)|^8307 ≤ (44364162884347/100000000000000 : ℝ)^6259
        have hw : |(5420665637/10000000000 : ℝ)|=(5420665637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(249817583/500000000 : ℝ)|^8307 ≤ (39815264128671/100000000000000 : ℝ)^6259
        have hw : |(249817583/500000000 : ℝ)|=(249817583/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-623139417/2500000000 : ℝ)|^8307 ≤ (7910286484127/50000000000000 : ℝ)^6259
        have hw : |(-623139417/2500000000 : ℝ)|=(623139417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s1_3 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4319799543/10000000000 : ℝ)*x 0 + (1835872991/5000000000 : ℝ)*x 1 + (635234613/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319799543/10000000000 : ℝ)^8307 ≤ (8205859484261/25000000000000 : ℝ)^6259 := by
    have hnat : (4319799543 : ℕ)^8307*25000000000000^6259 ≤ 8205859484261^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319799543 10000000000 8205859484261 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1835872991/5000000000 : ℝ)^8307 ≤ (826694667811/3125000000000 : ℝ)^6259 := by
    have hnat : (1835872991 : ℕ)^8307*3125000000000^6259 ≤ 826694667811^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1835872991 5000000000 826694667811 3125000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (635234613/1250000000 : ℝ)^8307 ≤ (2036116633489/5000000000000 : ℝ)^6259 := by
    have hnat : (635234613 : ℕ)^8307*5000000000000^6259 ≤ 2036116633489^6259*1250000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635234613 1250000000 2036116633489 5000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319799543/10000000000 : ℝ), (1835872991/5000000000 : ℝ), (635234613/1250000000 : ℝ)] ![(8205859484261/25000000000000 : ℝ), (826694667811/3125000000000 : ℝ), (2036116633489/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319799543/10000000000 : ℝ)|^8307 ≤ (8205859484261/25000000000000 : ℝ)^6259
        have hw : |(4319799543/10000000000 : ℝ)|=(4319799543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1835872991/5000000000 : ℝ)|^8307 ≤ (826694667811/3125000000000 : ℝ)^6259
        have hw : |(1835872991/5000000000 : ℝ)|=(1835872991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(635234613/1250000000 : ℝ)|^8307 ≤ (2036116633489/5000000000000 : ℝ)^6259
        have hw : |(635234613/1250000000 : ℝ)|=(635234613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s1_4 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-263529151/1250000000 : ℝ)*x 0 + (5006189087/10000000000 : ℝ)*x 1 + (2849514513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263529151/1250000000 : ℝ)^8307 ≤ (2533546415953/20000000000000 : ℝ)^6259 := by
    have hnat : (263529151 : ℕ)^8307*20000000000000^6259 ≤ 2533546415953^6259*1250000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263529151 1250000000 2533546415953 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5006189087/10000000000 : ℝ)^8307 ≤ (7983868342303/20000000000000 : ℝ)^6259 := by
    have hnat : (5006189087 : ℕ)^8307*20000000000000^6259 ≤ 7983868342303^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5006189087 10000000000 7983868342303 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2849514513/5000000000 : ℝ)^8307 ≤ (47412926188753/100000000000000 : ℝ)^6259 := by
    have hnat : (2849514513 : ℕ)^8307*100000000000000^6259 ≤ 47412926188753^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2849514513 5000000000 47412926188753 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-263529151/1250000000 : ℝ), (5006189087/10000000000 : ℝ), (2849514513/5000000000 : ℝ)] ![(2533546415953/20000000000000 : ℝ), (7983868342303/20000000000000 : ℝ), (47412926188753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-263529151/1250000000 : ℝ)|^8307 ≤ (2533546415953/20000000000000 : ℝ)^6259
        have hw : |(-263529151/1250000000 : ℝ)|=(263529151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5006189087/10000000000 : ℝ)|^8307 ≤ (7983868342303/20000000000000 : ℝ)^6259
        have hw : |(5006189087/10000000000 : ℝ)|=(5006189087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2849514513/5000000000 : ℝ)|^8307 ≤ (47412926188753/100000000000000 : ℝ)^6259
        have hw : |(2849514513/5000000000 : ℝ)|=(2849514513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s1_5 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1309549153/2500000000 : ℝ)*x 0 + (-894940599/5000000000 : ℝ)*x 1 + (1424757279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309549153/2500000000 : ℝ)^8307 ≤ (42393141640377/100000000000000 : ℝ)^6259 := by
    have hnat : (1309549153 : ℕ)^8307*100000000000000^6259 ≤ 42393141640377^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309549153 2500000000 42393141640377 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894940599/5000000000 : ℝ)^8307 ≤ (10193931163331/100000000000000 : ℝ)^6259 := by
    have hnat : (894940599 : ℕ)^8307*100000000000000^6259 ≤ 10193931163331^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894940599 5000000000 10193931163331 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1424757279/2500000000 : ℝ)^8307 ≤ (5926615897813/12500000000000 : ℝ)^6259 := by
    have hnat : (1424757279 : ℕ)^8307*12500000000000^6259 ≤ 5926615897813^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424757279 2500000000 5926615897813 12500000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309549153/2500000000 : ℝ), (-894940599/5000000000 : ℝ), (1424757279/2500000000 : ℝ)] ![(42393141640377/100000000000000 : ℝ), (10193931163331/100000000000000 : ℝ), (5926615897813/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309549153/2500000000 : ℝ)|^8307 ≤ (42393141640377/100000000000000 : ℝ)^6259
        have hw : |(1309549153/2500000000 : ℝ)|=(1309549153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-894940599/5000000000 : ℝ)|^8307 ≤ (10193931163331/100000000000000 : ℝ)^6259
        have hw : |(-894940599/5000000000 : ℝ)|=(894940599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1424757279/2500000000 : ℝ)|^8307 ≤ (5926615897813/12500000000000 : ℝ)^6259
        have hw : |(1424757279/2500000000 : ℝ)|=(1424757279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s1_6 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2619098259/5000000000 : ℝ)*x 0 + (227961163/400000000 : ℝ)*x 1 + (-111867587/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2619098259/5000000000 : ℝ)^8307 ≤ (42393140630703/100000000000000 : ℝ)^6259 := by
    have hnat : (2619098259 : ℕ)^8307*100000000000000^6259 ≤ 42393140630703^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619098259 5000000000 42393140630703 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227961163/400000000 : ℝ)^8307 ≤ (9482585345959/20000000000000 : ℝ)^6259 := by
    have hnat : (227961163 : ℕ)^8307*20000000000000^6259 ≤ 9482585345959^6259*400000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227961163 400000000 9482585345959 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111867587/625000000 : ℝ)^8307 ≤ (1274241578719/12500000000000 : ℝ)^6259 := by
    have hnat : (111867587 : ℕ)^8307*12500000000000^6259 ≤ 1274241578719^6259*625000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111867587 625000000 1274241578719 12500000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2619098259/5000000000 : ℝ), (227961163/400000000 : ℝ), (-111867587/625000000 : ℝ)] ![(42393140630703/100000000000000 : ℝ), (9482585345959/20000000000000 : ℝ), (1274241578719/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2619098259/5000000000 : ℝ)|^8307 ≤ (42393140630703/100000000000000 : ℝ)^6259
        have hw : |(2619098259/5000000000 : ℝ)|=(2619098259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(227961163/400000000 : ℝ)|^8307 ≤ (9482585345959/20000000000000 : ℝ)^6259
        have hw : |(227961163/400000000 : ℝ)|=(227961163/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111867587/625000000 : ℝ)|^8307 ≤ (1274241578719/12500000000000 : ℝ)^6259
        have hw : |(-111867587/625000000 : ℝ)|=(111867587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s1_7 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (432147171/1000000000 : ℝ)*x 0 + (5062416283/10000000000 : ℝ)*x 1 + (738319103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432147171/1000000000 : ℝ)^8307 ≤ (16420151090599/50000000000000 : ℝ)^6259 := by
    have hnat : (432147171 : ℕ)^8307*50000000000000^6259 ≤ 16420151090599^6259*1000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432147171 1000000000 16420151090599 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5062416283/10000000000 : ℝ)^8307 ≤ (40515493850033/100000000000000 : ℝ)^6259 := by
    have hnat : (5062416283 : ℕ)^8307*100000000000000^6259 ≤ 40515493850033^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5062416283 10000000000 40515493850033 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (738319103/2000000000 : ℝ)^8307 ≤ (26644203960069/100000000000000 : ℝ)^6259 := by
    have hnat : (738319103 : ℕ)^8307*100000000000000^6259 ≤ 26644203960069^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738319103 2000000000 26644203960069 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432147171/1000000000 : ℝ), (5062416283/10000000000 : ℝ), (738319103/2000000000 : ℝ)] ![(16420151090599/50000000000000 : ℝ), (40515493850033/100000000000000 : ℝ), (26644203960069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432147171/1000000000 : ℝ)|^8307 ≤ (16420151090599/50000000000000 : ℝ)^6259
        have hw : |(432147171/1000000000 : ℝ)|=(432147171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5062416283/10000000000 : ℝ)|^8307 ≤ (40515493850033/100000000000000 : ℝ)^6259
        have hw : |(5062416283/10000000000 : ℝ)|=(5062416283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(738319103/2000000000 : ℝ)|^8307 ≤ (26644203960069/100000000000000 : ℝ)^6259
        have hw : |(738319103/2000000000 : ℝ)|=(738319103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1114_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27923/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (149/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5491/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4113/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27923/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (149/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27923/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (149/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27923/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (149/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27923/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (149/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27923/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (149/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27923/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (149/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (149/50000 : ℝ) ^ (4153/1024 : ℝ) ≤ (178287007/3125000000000000000 : ℝ) := by
    have hpowers : (149/50000 : ℝ)^4153 ≤ (178287007/3125000000000000000 : ℝ)^1024 := by
      have hnat : (149 : ℕ)^4153*3125000000000000000^1024 ≤ 178287007^1024*50000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        149 50000 178287007 3125000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (149/50000 : ℝ)) (X := (178287007/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27923/100000 : ℝ) ^ (4153/1024 : ℝ) ≤ (113250023120879881/20000000000000000000 : ℝ) := by
    have hpowers : (27923/100000 : ℝ)^4153 ≤ (113250023120879881/20000000000000000000 : ℝ)^1024 := by
      have hnat : (27923 : ℕ)^4153*20000000000000000000^1024 ≤ 113250023120879881^1024*100000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27923 100000 113250023120879881 20000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27923/100000 : ℝ)) (X := (113250023120879881/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562500000178287007/1562500000000000000 : ℝ) ≤ (2000000000056269/2000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (1562500000178287007/1562500000000000000 : ℝ)^1024 ≤ (2000000000056269/2000000000000000 : ℝ)^4153 := by
      have hnat : (1562500000178287007 : ℕ)^1024*2000000000000000^4153 ≤ 2000000000056269^4153*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562500000178287007 1562500000000000000 2000000000056269 2000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000000056269/2000000000000000 : ℝ)) (X := (1562500000178287007/1562500000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100566250121309583629/100000000000000000000 : ℝ) ≤ (156467691771917/156250000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (100566250121309583629/100000000000000000000 : ℝ)^1024 ≤ (156467691771917/156250000000000 : ℝ)^4153 := by
      have hnat : (100566250121309583629 : ℕ)^1024*156250000000000^4153 ≤ 156467691771917^4153*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100566250121309583629 100000000000000000000 156467691771917 156250000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156467691771917/156250000000000 : ℝ)) (X := (100566250121309583629/100000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10113250023120879881/10000000000000000000 : ℝ) ≤ (10027864546524031/10000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (10113250023120879881/10000000000000000000 : ℝ)^1024 ≤ (10027864546524031/10000000000000000 : ℝ)^4153 := by
      have hnat : (10113250023120879881 : ℕ)^1024*10000000000000000^4153 ≤ 10027864546524031^4153*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10113250023120879881 10000000000000000000 10027864546524031 10000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027864546524031/10000000000000000 : ℝ)) (X := (10113250023120879881/10000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(178287007/3125000000000000000 : ℝ) ≤ ((276241696372991835197/276250000000000000000 : ℝ)+2*(13932273121343/2762500000000000 : ℝ)*(149/50000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (276241696372991835197/276250000000000000000 : ℝ)+2*(13932273121343/2762500000000000 : ℝ)*(149/50000 : ℝ)=(2000000000056269/2000000000000000 : ℝ) by norm_num, show 1+2*(178287007/3125000000000000000 : ℝ)=(1562500000178287007/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(113250023120879881/20000000000000000000 : ℝ)+(178287007/3125000000000000000 : ℝ) ≤ ((276241696372991835197/276250000000000000000 : ℝ)+(13932273121343/2762500000000000 : ℝ)*((27923/100000 : ℝ)+(149/50000 : ℝ)))^(4153/1024 : ℝ) := by
    rw [show (276241696372991835197/276250000000000000000 : ℝ)+(13932273121343/2762500000000000 : ℝ)*((27923/100000 : ℝ)+(149/50000 : ℝ))=(156467691771917/156250000000000 : ℝ) by norm_num, show 1+(113250023120879881/20000000000000000000 : ℝ)+(178287007/3125000000000000000 : ℝ)=(100566250121309583629/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(113250023120879881/20000000000000000000 : ℝ) ≤ ((276241696372991835197/276250000000000000000 : ℝ)+2*(13932273121343/2762500000000000 : ℝ)*(27923/100000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (276241696372991835197/276250000000000000000 : ℝ)+2*(13932273121343/2762500000000000 : ℝ)*(27923/100000 : ℝ)=(10027864546524031/10000000000000000 : ℝ) by norm_num, show 1+2*(113250023120879881/20000000000000000000 : ℝ)=(10113250023120879881/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (276241696372991835197/276250000000000000000 : ℝ)*(X 1 0+X 2 0)+(13932273121343/2762500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (149/50000 : ℝ)) (hi := (27923/100000 : ℝ)) (c := (276241696372991835197/276250000000000000000 : ℝ)) (alpha := (13932273121343/2762500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (276241696372991835197/276250000000000000000 : ℝ)*(X 0 1+X 2 1)+(13932273121343/2762500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (149/50000 : ℝ)) (hi := (27923/100000 : ℝ)) (c := (276241696372991835197/276250000000000000000 : ℝ)) (alpha := (13932273121343/2762500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (276241696372991835197/276250000000000000000 : ℝ)*(X 0 2+X 1 2)+(13932273121343/2762500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (149/50000 : ℝ)) (hi := (27923/100000 : ℝ)) (c := (276241696372991835197/276250000000000000000 : ℝ)) (alpha := (13932273121343/2762500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-526846763/2500000000 : ℝ)*X 0 0+(2854530897/5000000000 : ℝ)*X 0 1+(1249088259/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5420664267/10000000000 : ℝ)*X 1 0+(-99702313/400000000 : ℝ)*X 1 1+(4996352943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5420665637/10000000000 : ℝ)*X 2 0+(249817583/500000000 : ℝ)*X 2 1+(-623139417/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4319799543/10000000000 : ℝ)*X 0 0+(1835872991/5000000000 : ℝ)*X 0 1+(635234613/1250000000 : ℝ)*X 0 2+(4319799543/10000000000 : ℝ)*X 1 0+(1835872991/5000000000 : ℝ)*X 1 1+(635234613/1250000000 : ℝ)*X 1 2+(4319799543/10000000000 : ℝ)*X 2 0+(1835872991/5000000000 : ℝ)*X 2 1+(635234613/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-263529151/1250000000 : ℝ)*X 0 0+(5006189087/10000000000 : ℝ)*X 0 1+(2849514513/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1309549153/2500000000 : ℝ)*X 1 0+(-894940599/5000000000 : ℝ)*X 1 1+(1424757279/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2619098259/5000000000 : ℝ)*X 2 0+(227961163/400000000 : ℝ)*X 2 1+(-111867587/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((432147171/1000000000 : ℝ)*X 0 0+(5062416283/10000000000 : ℝ)*X 0 1+(738319103/2000000000 : ℝ)*X 0 2+(432147171/1000000000 : ℝ)*X 1 0+(5062416283/10000000000 : ℝ)*X 1 1+(738319103/2000000000 : ℝ)*X 1 2+(432147171/1000000000 : ℝ)*X 2 0+(5062416283/10000000000 : ℝ)*X 2 1+(738319103/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53756977590261446960205883437/6906250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18221781/6250000000000 : ℝ)*(base1) + (1443430123/100000000000000 : ℝ)*(base19) + (28094479/1562500000000 : ℝ)*(base23) + (4096673/6250000000000 : ℝ)*(upper3) + (26895207/12500000000000 : ℝ)*(upper5) + (1056134310637307/100000000000000 : ℝ)*(major0) + (1056134310637307/100000000000000 : ℝ)*(major1) + (1056134310637307/100000000000000 : ℝ)*(major2) + (70155121351281/5000000000000 : ℝ)*(sp0) + (1403107778924743/100000000000000 : ℝ)*(sp1) + (140310742430821/10000000000000 : ℝ)*(sp2) + (5540285440933/781250000000 : ℝ)*(sp3) + (3543438871/50000000000000 : ℝ)*(sp4) + (2311471297/100000000000000 : ℝ)*(sp7) + (709159139459217/100000000000000 : ℝ)*(f.failure) + (701554611177433/50000000000000 : ℝ)*(f.sum) + (332510475160449/138125000000000000000000000000 : ℝ)*base66 + (288802738373211005521/27625000000000000000000000000000000 : ℝ)*base68 + (30549703525538994479/27625000000000000000000000000000000 : ℝ)*base69 + (263124257476961005521/27625000000000000000000000000000000 : ℝ)*base72 + (761167174459199/138125000000000000000000000000 : ℝ)*base74 + (45569520871586005521/27625000000000000000000000000000000 : ℝ)*base76 + (328919310848086005521/27625000000000000000000000000000000 : ℝ)*base78 + (186047815033961005521/27625000000000000000000000000000000 : ℝ)*base80 + (115376150749463/69062500000000000000000000000 : ℝ)*base81 + (7262537/1250000000000000000000 : ℝ)*base89 + (7262537/1250000000000000000000 : ℝ)*base91 + (7262537/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35559040938083546239945112769/13812500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14088689/100000000000000 : ℝ)*(base1) + (542054027/100000000000000 : ℝ)*(base19) + (31160331/6250000000000 : ℝ)*(base23) + (28290547/50000000000000 : ℝ)*(upper3) + (14244373/20000000000000 : ℝ)*(upper5) + (1086412404120653/100000000000000 : ℝ)*(major0) + (1086412404120653/100000000000000 : ℝ)*(major1) + (1086412404120653/100000000000000 : ℝ)*(major2) + (322900507/12500000000000 : ℝ)*(sp1) + (519570229/25000000000000 : ℝ)*(sp2) + (1443334862127979/100000000000000 : ℝ)*(sp4) + (721665861390603/50000000000000 : ℝ)*(sp5) + (721666135596539/50000000000000 : ℝ)*(sp6) + (729489860299647/100000000000000 : ℝ)*(sp7) + (45593117149271/6250000000000 : ℝ)*(f.failure) + (144333484803929/10000000000000 : ℝ)*(f.sum) + (167320667585729/138125000000000000000000000000 : ℝ)*base65 + (12790606387072076359/27625000000000000000000000000000000 : ℝ)*base68 + (363810000022697076359/27625000000000000000000000000000000 : ℝ)*base70 + (187538348452072076359/27625000000000000000000000000000000 : ℝ)*base72 + (343992161331927/69062500000000000000000000000 : ℝ)*base73 + (104383963428947076359/27625000000000000000000000000000000 : ℝ)*base76 + (216938113041072076359/27625000000000000000000000000000000 : ℝ)*base78 + (371818870184197076359/27625000000000000000000000000000000 : ℝ)*base80 + (73543527351823/69062500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (41819/78125000000000000000 : ℝ)*base90 + (41819/78125000000000000000 : ℝ)*base92 + (41819/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1114_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27923/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (149/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5491/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4113/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1114_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1114_s2_0 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-540536001/2500000000 : ℝ)*x 0 + (2758108981/5000000000 : ℝ)*x 1 + (1030881259/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540536001/2500000000 : ℝ)^8307 ≤ (523977920961/4000000000000 : ℝ)^6259 := by
    have hnat : (540536001 : ℕ)^8307*4000000000000^6259 ≤ 523977920961^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540536001 2500000000 523977920961 4000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2758108981/5000000000 : ℝ)^8307 ≤ (45405055572173/100000000000000 : ℝ)^6259 := by
    have hnat : (2758108981 : ℕ)^8307*100000000000000^6259 ≤ 45405055572173^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758108981 5000000000 45405055572173 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030881259/2000000000 : ℝ)^8307 ≤ (8299099278307/20000000000000 : ℝ)^6259 := by
    have hnat : (1030881259 : ℕ)^8307*20000000000000^6259 ≤ 8299099278307^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030881259 2000000000 8299099278307 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-540536001/2500000000 : ℝ), (2758108981/5000000000 : ℝ), (1030881259/2000000000 : ℝ)] ![(523977920961/4000000000000 : ℝ), (45405055572173/100000000000000 : ℝ), (8299099278307/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-540536001/2500000000 : ℝ)|^8307 ≤ (523977920961/4000000000000 : ℝ)^6259
        have hw : |(-540536001/2500000000 : ℝ)|=(540536001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2758108981/5000000000 : ℝ)|^8307 ≤ (45405055572173/100000000000000 : ℝ)^6259
        have hw : |(2758108981/5000000000 : ℝ)|=(2758108981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030881259/2000000000 : ℝ)|^8307 ≤ (8299099278307/20000000000000 : ℝ)^6259
        have hw : |(1030881259/2000000000 : ℝ)|=(1030881259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s2_1 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5375075731/10000000000 : ℝ)*x 0 + (-2350459147/10000000000 : ℝ)*x 1 + (515440763/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375075731/10000000000 : ℝ)^8307 ≤ (21934818798463/50000000000000 : ℝ)^6259 := by
    have hnat : (5375075731 : ℕ)^8307*50000000000000^6259 ≤ 21934818798463^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375075731 10000000000 21934818798463 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2350459147/10000000000 : ℝ)^8307 ≤ (7317425867489/50000000000000 : ℝ)^6259 := by
    have hnat : (2350459147 : ℕ)^8307*50000000000000^6259 ≤ 7317425867489^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2350459147 10000000000 7317425867489 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515440763/1000000000 : ℝ)^8307 ≤ (8299102131117/20000000000000 : ℝ)^6259 := by
    have hnat : (515440763 : ℕ)^8307*20000000000000^6259 ≤ 8299102131117^6259*1000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515440763 1000000000 8299102131117 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375075731/10000000000 : ℝ), (-2350459147/10000000000 : ℝ), (515440763/1000000000 : ℝ)] ![(21934818798463/50000000000000 : ℝ), (7317425867489/50000000000000 : ℝ), (8299102131117/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375075731/10000000000 : ℝ)|^8307 ≤ (21934818798463/50000000000000 : ℝ)^6259
        have hw : |(5375075731/10000000000 : ℝ)|=(5375075731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2350459147/10000000000 : ℝ)|^8307 ≤ (7317425867489/50000000000000 : ℝ)^6259
        have hw : |(-2350459147/10000000000 : ℝ)|=(2350459147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(515440763/1000000000 : ℝ)|^8307 ≤ (8299102131117/20000000000000 : ℝ)^6259
        have hw : |(515440763/1000000000 : ℝ)|=(515440763/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s2_2 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5375075667/10000000000 : ℝ)*x 0 + (515440769/1000000000 : ℝ)*x 1 + (-1175229577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375075667/10000000000 : ℝ)^8307 ≤ (21934818451831/50000000000000 : ℝ)^6259 := by
    have hnat : (5375075667 : ℕ)^8307*50000000000000^6259 ≤ 21934818451831^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375075667 10000000000 21934818451831 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515440769/1000000000 : ℝ)^8307 ≤ (20747755648333/50000000000000 : ℝ)^6259 := by
    have hnat : (515440769 : ℕ)^8307*50000000000000^6259 ≤ 20747755648333^6259*1000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515440769 1000000000 20747755648333 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1175229577/5000000000 : ℝ)^8307 ≤ (1829356474103/12500000000000 : ℝ)^6259 := by
    have hnat : (1175229577 : ℕ)^8307*12500000000000^6259 ≤ 1829356474103^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175229577 5000000000 1829356474103 12500000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375075667/10000000000 : ℝ), (515440769/1000000000 : ℝ), (-1175229577/5000000000 : ℝ)] ![(21934818451831/50000000000000 : ℝ), (20747755648333/50000000000000 : ℝ), (1829356474103/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375075667/10000000000 : ℝ)|^8307 ≤ (21934818451831/50000000000000 : ℝ)^6259
        have hw : |(5375075667/10000000000 : ℝ)|=(5375075667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(515440769/1000000000 : ℝ)|^8307 ≤ (20747755648333/50000000000000 : ℝ)^6259
        have hw : |(515440769/1000000000 : ℝ)|=(515440769/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1175229577/5000000000 : ℝ)|^8307 ≤ (1829356474103/12500000000000 : ℝ)^6259
        have hw : |(-1175229577/5000000000 : ℝ)|=(1175229577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s2_3 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871457789/2000000000 : ℝ)*x 0 + (2007010789/5000000000 : ℝ)*x 1 + (4729882303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871457789/2000000000 : ℝ)^8307 ≤ (6640408046527/20000000000000 : ℝ)^6259 := by
    have hnat : (871457789 : ℕ)^8307*20000000000000^6259 ≤ 6640408046527^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871457789 2000000000 6640408046527 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2007010789/5000000000 : ℝ)^8307 ≤ (29776077446619/100000000000000 : ℝ)^6259 := by
    have hnat : (2007010789 : ℕ)^8307*100000000000000^6259 ≤ 29776077446619^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007010789 5000000000 29776077446619 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4729882303/10000000000 : ℝ)^8307 ≤ (9255470573783/25000000000000 : ℝ)^6259 := by
    have hnat : (4729882303 : ℕ)^8307*25000000000000^6259 ≤ 9255470573783^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4729882303 10000000000 9255470573783 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871457789/2000000000 : ℝ), (2007010789/5000000000 : ℝ), (4729882303/10000000000 : ℝ)] ![(6640408046527/20000000000000 : ℝ), (29776077446619/100000000000000 : ℝ), (9255470573783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871457789/2000000000 : ℝ)|^8307 ≤ (6640408046527/20000000000000 : ℝ)^6259
        have hw : |(871457789/2000000000 : ℝ)|=(871457789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2007010789/5000000000 : ℝ)|^8307 ≤ (29776077446619/100000000000000 : ℝ)^6259
        have hw : |(2007010789/5000000000 : ℝ)|=(2007010789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4729882303/10000000000 : ℝ)|^8307 ≤ (9255470573783/25000000000000 : ℝ)^6259
        have hw : |(4729882303/10000000000 : ℝ)|=(4729882303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s2_4 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1081127173/5000000000 : ℝ)*x 0 + (515695099/1000000000 : ℝ)*x 1 + (5513647517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081127173/5000000000 : ℝ)^8307 ≤ (2620067057301/20000000000000 : ℝ)^6259 := by
    have hnat : (1081127173 : ℕ)^8307*20000000000000^6259 ≤ 2620067057301^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081127173 5000000000 2620067057301 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515695099/1000000000 : ℝ)^8307 ≤ (41522687842567/100000000000000 : ℝ)^6259 := by
    have hnat : (515695099 : ℕ)^8307*100000000000000^6259 ≤ 41522687842567^6259*1000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515695099 1000000000 41522687842567 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5513647517/10000000000 : ℝ)^8307 ≤ (22688488427761/50000000000000 : ℝ)^6259 := by
    have hnat : (5513647517 : ℕ)^8307*50000000000000^6259 ≤ 22688488427761^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513647517 10000000000 22688488427761 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1081127173/5000000000 : ℝ), (515695099/1000000000 : ℝ), (5513647517/10000000000 : ℝ)] ![(2620067057301/20000000000000 : ℝ), (41522687842567/100000000000000 : ℝ), (22688488427761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1081127173/5000000000 : ℝ)|^8307 ≤ (2620067057301/20000000000000 : ℝ)^6259
        have hw : |(-1081127173/5000000000 : ℝ)|=(1081127173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(515695099/1000000000 : ℝ)|^8307 ≤ (41522687842567/100000000000000 : ℝ)^6259
        have hw : |(515695099/1000000000 : ℝ)|=(515695099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5513647517/10000000000 : ℝ)|^8307 ≤ (22688488427761/50000000000000 : ℝ)^6259
        have hw : |(5513647517/10000000000 : ℝ)|=(5513647517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s2_5 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2641723717/5000000000 : ℝ)*x 0 + (-398243723/2000000000 : ℝ)*x 1 + (5513647599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641723717/5000000000 : ℝ)^8307 ≤ (4287987567809/10000000000000 : ℝ)^6259 := by
    have hnat : (2641723717 : ℕ)^8307*10000000000000^6259 ≤ 4287987567809^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641723717 5000000000 4287987567809 10000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (398243723/2000000000 : ℝ)^8307 ≤ (5871573274671/50000000000000 : ℝ)^6259 := by
    have hnat : (398243723 : ℕ)^8307*50000000000000^6259 ≤ 5871573274671^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398243723 2000000000 5871573274671 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5513647599/10000000000 : ℝ)^8307 ≤ (9075395550239/20000000000000 : ℝ)^6259 := by
    have hnat : (5513647599 : ℕ)^8307*20000000000000^6259 ≤ 9075395550239^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513647599 10000000000 9075395550239 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641723717/5000000000 : ℝ), (-398243723/2000000000 : ℝ), (5513647599/10000000000 : ℝ)] ![(4287987567809/10000000000000 : ℝ), (5871573274671/50000000000000 : ℝ), (9075395550239/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641723717/5000000000 : ℝ)|^8307 ≤ (4287987567809/10000000000000 : ℝ)^6259
        have hw : |(2641723717/5000000000 : ℝ)|=(2641723717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-398243723/2000000000 : ℝ)|^8307 ≤ (5871573274671/50000000000000 : ℝ)^6259
        have hw : |(-398243723/2000000000 : ℝ)|=(398243723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5513647599/10000000000 : ℝ)|^8307 ≤ (9075395550239/20000000000000 : ℝ)^6259
        have hw : |(5513647599/10000000000 : ℝ)|=(5513647599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s2_6 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132086189/250000000 : ℝ)*x 0 + (110272951/200000000 : ℝ)*x 1 + (-199121851/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132086189/250000000 : ℝ)^8307 ≤ (1339996157353/3125000000000 : ℝ)^6259 := by
    have hnat : (132086189 : ℕ)^8307*3125000000000^6259 ≤ 1339996157353^6259*250000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132086189 250000000 1339996157353 3125000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110272951/200000000 : ℝ)^8307 ≤ (5672122151997/12500000000000 : ℝ)^6259 := by
    have hnat : (110272951 : ℕ)^8307*12500000000000^6259 ≤ 5672122151997^6259*200000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110272951 200000000 5672122151997 12500000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199121851/1000000000 : ℝ)^8307 ≤ (11743145727489/100000000000000 : ℝ)^6259 := by
    have hnat : (199121851 : ℕ)^8307*100000000000000^6259 ≤ 11743145727489^6259*1000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199121851 1000000000 11743145727489 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132086189/250000000 : ℝ), (110272951/200000000 : ℝ), (-199121851/1000000000 : ℝ)] ![(1339996157353/3125000000000 : ℝ), (5672122151997/12500000000000 : ℝ), (11743145727489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132086189/250000000 : ℝ)|^8307 ≤ (1339996157353/3125000000000 : ℝ)^6259
        have hw : |(132086189/250000000 : ℝ)|=(132086189/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110272951/200000000 : ℝ)|^8307 ≤ (5672122151997/12500000000000 : ℝ)^6259
        have hw : |(110272951/200000000 : ℝ)|=(110272951/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199121851/1000000000 : ℝ)|^8307 ≤ (11743145727489/100000000000000 : ℝ)^6259
        have hw : |(-199121851/1000000000 : ℝ)|=(199121851/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s2_7 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178754327/5000000000 : ℝ)*x 0 + (4724848793/10000000000 : ℝ)*x 1 + (2009552547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178754327/5000000000 : ℝ)^8307 ≤ (33204262207287/100000000000000 : ℝ)^6259 := by
    have hnat : (2178754327 : ℕ)^8307*100000000000000^6259 ≤ 33204262207287^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178754327 5000000000 33204262207287 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4724848793/10000000000 : ℝ)^8307 ≤ (577650022433/1562500000000 : ℝ)^6259 := by
    have hnat : (4724848793 : ℕ)^8307*1562500000000^6259 ≤ 577650022433^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4724848793 10000000000 577650022433 1562500000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2009552547/5000000000 : ℝ)^8307 ≤ (14913068166567/50000000000000 : ℝ)^6259 := by
    have hnat : (2009552547 : ℕ)^8307*50000000000000^6259 ≤ 14913068166567^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009552547 5000000000 14913068166567 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178754327/5000000000 : ℝ), (4724848793/10000000000 : ℝ), (2009552547/5000000000 : ℝ)] ![(33204262207287/100000000000000 : ℝ), (577650022433/1562500000000 : ℝ), (14913068166567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178754327/5000000000 : ℝ)|^8307 ≤ (33204262207287/100000000000000 : ℝ)^6259
        have hw : |(2178754327/5000000000 : ℝ)|=(2178754327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4724848793/10000000000 : ℝ)|^8307 ≤ (577650022433/1562500000000 : ℝ)^6259
        have hw : |(4724848793/10000000000 : ℝ)|=(4724848793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2009552547/5000000000 : ℝ)|^8307 ≤ (14913068166567/50000000000000 : ℝ)^6259
        have hw : |(2009552547/5000000000 : ℝ)|=(2009552547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1114_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4113/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4471/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16587/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4113/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5491/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4113/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5491/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4113/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5491/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4113/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5491/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4113/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5491/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4113/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5491/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (5491/100000 : ℝ) ^ (4153/1024 : ℝ) ≤ (24171281472127/3125000000000000000 : ℝ) := by
    have hpowers : (5491/100000 : ℝ)^4153 ≤ (24171281472127/3125000000000000000 : ℝ)^1024 := by
      have hnat : (5491 : ℕ)^4153*3125000000000000000^1024 ≤ 24171281472127^1024*100000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5491 100000 24171281472127 3125000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5491/100000 : ℝ)) (X := (24171281472127/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4113/20000 : ℝ) ^ (4153/1024 : ℝ) ≤ (81893760399458029/50000000000000000000 : ℝ) := by
    have hpowers : (4113/20000 : ℝ)^4153 ≤ (81893760399458029/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4113 : ℕ)^4153*50000000000000000000^1024 ≤ 81893760399458029^1024*20000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4113 20000 81893760399458029 50000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4113/20000 : ℝ)) (X := (81893760399458029/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562524171281472127/1562500000000000000 : ℝ) ≤ (10000038143026033/10000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (1562524171281472127/1562500000000000000 : ℝ)^1024 ≤ (10000038143026033/10000000000000000 : ℝ)^4153 := by
      have hnat : (1562524171281472127 : ℕ)^1024*10000000000000000^4153 ≤ 10000038143026033^4153*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562524171281472127 1562500000000000000 10000038143026033 10000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000038143026033/10000000000000000 : ℝ)) (X := (1562524171281472127/1562500000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50082280500903012061/50000000000000000000 : ℝ) ≤ (2000811009400541/2000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (50082280500903012061/50000000000000000000 : ℝ)^1024 ≤ (2000811009400541/2000000000000000 : ℝ)^4153 := by
      have hnat : (50082280500903012061 : ℕ)^1024*2000000000000000^4153 ≤ 2000811009400541^4153*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50082280500903012061 50000000000000000000 2000811009400541 2000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000811009400541/2000000000000000 : ℝ)) (X := (50082280500903012061/50000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25081893760399458029/25000000000000000000 : ℝ) ≤ (10008071950979377/10000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (25081893760399458029/25000000000000000000 : ℝ)^1024 ≤ (10008071950979377/10000000000000000 : ℝ)^4153 := by
      have hnat : (25081893760399458029 : ℕ)^1024*10000000000000000^4153 ≤ 10008071950979377^4153*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25081893760399458029 25000000000000000000 10008071950979377 10000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008071950979377/10000000000000000 : ℝ)) (X := (25081893760399458029/25000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(24171281472127/3125000000000000000 : ℝ) ≤ ((75348230664251304769/75370000000000000000 : ℝ)+2*(125528249271/47106250000000 : ℝ)*(5491/100000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (75348230664251304769/75370000000000000000 : ℝ)+2*(125528249271/47106250000000 : ℝ)*(5491/100000 : ℝ)=(10000038143026033/10000000000000000 : ℝ) by norm_num, show 1+2*(24171281472127/3125000000000000000 : ℝ)=(1562524171281472127/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(81893760399458029/50000000000000000000 : ℝ)+(24171281472127/3125000000000000000 : ℝ) ≤ ((75348230664251304769/75370000000000000000 : ℝ)+(125528249271/47106250000000 : ℝ)*((4113/20000 : ℝ)+(5491/100000 : ℝ)))^(4153/1024 : ℝ) := by
    rw [show (75348230664251304769/75370000000000000000 : ℝ)+(125528249271/47106250000000 : ℝ)*((4113/20000 : ℝ)+(5491/100000 : ℝ))=(2000811009400541/2000000000000000 : ℝ) by norm_num, show 1+(81893760399458029/50000000000000000000 : ℝ)+(24171281472127/3125000000000000000 : ℝ)=(50082280500903012061/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(81893760399458029/50000000000000000000 : ℝ) ≤ ((75348230664251304769/75370000000000000000 : ℝ)+2*(125528249271/47106250000000 : ℝ)*(4113/20000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (75348230664251304769/75370000000000000000 : ℝ)+2*(125528249271/47106250000000 : ℝ)*(4113/20000 : ℝ)=(10008071950979377/10000000000000000 : ℝ) by norm_num, show 1+2*(81893760399458029/50000000000000000000 : ℝ)=(25081893760399458029/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (75348230664251304769/75370000000000000000 : ℝ)*(X 1 0+X 2 0)+(125528249271/47106250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (5491/100000 : ℝ)) (hi := (4113/20000 : ℝ)) (c := (75348230664251304769/75370000000000000000 : ℝ)) (alpha := (125528249271/47106250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (75348230664251304769/75370000000000000000 : ℝ)*(X 0 1+X 2 1)+(125528249271/47106250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (5491/100000 : ℝ)) (hi := (4113/20000 : ℝ)) (c := (75348230664251304769/75370000000000000000 : ℝ)) (alpha := (125528249271/47106250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (75348230664251304769/75370000000000000000 : ℝ)*(X 0 2+X 1 2)+(125528249271/47106250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (5491/100000 : ℝ)) (hi := (4113/20000 : ℝ)) (c := (75348230664251304769/75370000000000000000 : ℝ)) (alpha := (125528249271/47106250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-540536001/2500000000 : ℝ)*X 0 0+(2758108981/5000000000 : ℝ)*X 0 1+(1030881259/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5375075731/10000000000 : ℝ)*X 1 0+(-2350459147/10000000000 : ℝ)*X 1 1+(515440763/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5375075667/10000000000 : ℝ)*X 2 0+(515440769/1000000000 : ℝ)*X 2 1+(-1175229577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871457789/2000000000 : ℝ)*X 0 0+(2007010789/5000000000 : ℝ)*X 0 1+(4729882303/10000000000 : ℝ)*X 0 2+(871457789/2000000000 : ℝ)*X 1 0+(2007010789/5000000000 : ℝ)*X 1 1+(4729882303/10000000000 : ℝ)*X 1 2+(871457789/2000000000 : ℝ)*X 2 0+(2007010789/5000000000 : ℝ)*X 2 1+(4729882303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1081127173/5000000000 : ℝ)*X 0 0+(515695099/1000000000 : ℝ)*X 0 1+(5513647517/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2641723717/5000000000 : ℝ)*X 1 0+(-398243723/2000000000 : ℝ)*X 1 1+(5513647599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132086189/250000000 : ℝ)*X 2 0+(110272951/200000000 : ℝ)*X 2 1+(-199121851/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178754327/5000000000 : ℝ)*X 0 0+(4724848793/10000000000 : ℝ)*X 0 1+(2009552547/5000000000 : ℝ)*X 0 2+(2178754327/5000000000 : ℝ)*X 1 0+(4724848793/10000000000 : ℝ)*X 1 1+(2009552547/5000000000 : ℝ)*X 1 2+(2178754327/5000000000 : ℝ)*X 2 0+(4724848793/10000000000 : ℝ)*X 2 1+(2009552547/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (270037869739623031311277839/75370000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10473251/20000000000000 : ℝ)*(base29) + (93559409/100000000000000 : ℝ)*(upper2) + (18200237/100000000000000 : ℝ)*(upper3) + (1185477/1562500000000 : ℝ)*(upper4) + (6412347/20000000000000 : ℝ)*(upper5) + (416080970993519/20000000000000 : ℝ)*(major0) + (41608098146677/2000000000000 : ℝ)*(major1) + (41608098146677/2000000000000 : ℝ)*(major2) + (276387782580207/10000000000000 : ℝ)*(sp0) + (1381943395199663/50000000000000 : ℝ)*(sp1) + (690971697599831/25000000000000 : ℝ)*(sp2) + (1396921411863261/100000000000000 : ℝ)*(sp3) + (9016963511/100000000000000 : ℝ)*(sp4) + (144061119/10000000000000 : ℝ)*(sp7) + (27938457049489/2000000000000 : ℝ)*(f.failure) + (2763886842765581/100000000000000 : ℝ)*(f.sum) + (42096668588083/7537000000000000000000000000 : ℝ)*base66 + (99874453637882613/150740000000000000000000000000000 : ℝ)*base67 + (896382489598397387/150740000000000000000000000000000 : ℝ)*base70 + (59849547946403392111/1507400000000000000000000000000000 : ℝ)*base71 + (532173342087/753700000000000000000000000 : ℝ)*base74 + (1033261502213577387/150740000000000000000000000000000 : ℝ)*base76 + (7477405515931407889/1507400000000000000000000000000000 : ℝ)*base78 + (491609233669677387/150740000000000000000000000000000 : ℝ)*base80 + (41024920279687/7537000000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base88 + (206071/25000000000000000000 : ℝ)*base90 + (206071/25000000000000000000 : ℝ)*base92 + (206071/25000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39294424053204308483757/18842500000000000000000000000 : ℝ) := by norm_num
    linear_combination (433913157/100000000000000 : ℝ)*(base19) + (35093083/6250000000000 : ℝ)*(base23) + (78877947/100000000000000 : ℝ)*(upper3) + (7102853/50000000000000 : ℝ)*(lower4) + (25248817/100000000000000 : ℝ)*(upper5) + (2110224227069431/100000000000000 : ℝ)*(major0) + (2110224227069431/100000000000000 : ℝ)*(major1) + (2110224227069431/100000000000000 : ℝ)*(major2) + (3863142263/100000000000000 : ℝ)*(sp1) + (5813901463/100000000000000 : ℝ)*(sp2) + (1401751424283839/50000000000000 : ℝ)*(sp4) + (2803498551512257/100000000000000 : ℝ)*(sp5) + (1401748236588443/50000000000000 : ℝ)*(sp6) + (1416945536057359/100000000000000 : ℝ)*(sp7) + (1416945536057359/100000000000000 : ℝ)*(f.failure) + (1401751424283839/50000000000000 : ℝ)*(f.sum) + (15362500332407/18842500000000000000000000000 : ℝ)*base66 + (45928285515472983561/7537000000000000000000000000000000 : ℝ)*base68 + (32812574217477983561/7537000000000000000000000000000000 : ℝ)*base70 + (11350667536262983561/7537000000000000000000000000000000 : ℝ)*base72 + (54389966190319/37685000000000000000000000000 : ℝ)*base74 + (80252735592063016439/7537000000000000000000000000000000 : ℝ)*base75 + (37080728834707016439/7537000000000000000000000000000000 : ℝ)*base77 + (22990957853177016439/7537000000000000000000000000000000 : ℝ)*base79 + (26975109236403/4710625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1406999/1250000000000000000000 : ℝ)*base89 + (1406999/1250000000000000000000 : ℝ)*base91 + (1406999/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1114_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4113/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4471/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16587/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1114_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1114_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4471/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16587/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1114_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1114_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1114_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4471/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16587/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1114_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

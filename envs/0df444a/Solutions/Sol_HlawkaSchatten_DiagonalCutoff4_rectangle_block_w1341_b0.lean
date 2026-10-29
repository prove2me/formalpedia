-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1341_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:04:08.587177+00:00
-- url     : https://prove2.me/submissions/58a1bb73-f753-4198-aeee-dd351cc0a0a1

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
theorem support_rectangle_w1341_s0_0 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1809737549/10000000000 : ℝ)*x 0 + (1499337201/2500000000 : ℝ)*x 1 + (2405335169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1809737549/10000000000 : ℝ)^4301 ≤ (2652006836023/25000000000000 : ℝ)^3277 := by
    have hnat : (1809737549 : ℕ)^4301*25000000000000^3277 ≤ 2652006836023^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1809737549 10000000000 2652006836023 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1499337201/2500000000 : ℝ)^4301 ≤ (51118232223953/100000000000000 : ℝ)^3277 := by
    have hnat : (1499337201 : ℕ)^4301*100000000000000^3277 ≤ 51118232223953^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499337201 2500000000 51118232223953 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2405335169/5000000000 : ℝ)^4301 ≤ (9568435104037/25000000000000 : ℝ)^3277 := by
    have hnat : (2405335169 : ℕ)^4301*25000000000000^3277 ≤ 9568435104037^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405335169 5000000000 9568435104037 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1809737549/10000000000 : ℝ), (1499337201/2500000000 : ℝ), (2405335169/5000000000 : ℝ)] ![(2652006836023/25000000000000 : ℝ), (51118232223953/100000000000000 : ℝ), (9568435104037/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1809737549/10000000000 : ℝ)|^4301 ≤ (2652006836023/25000000000000 : ℝ)^3277
        have hw : |(-1809737549/10000000000 : ℝ)|=(1809737549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1499337201/2500000000 : ℝ)|^4301 ≤ (51118232223953/100000000000000 : ℝ)^3277
        have hw : |(1499337201/2500000000 : ℝ)|=(1499337201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2405335169/5000000000 : ℝ)|^4301 ≤ (9568435104037/25000000000000 : ℝ)^3277
        have hw : |(2405335169/5000000000 : ℝ)|=(2405335169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s0_1 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1100384921/2000000000 : ℝ)*x 0 + (-77634037/312500000 : ℝ)*x 1 + (4810670741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100384921/2000000000 : ℝ)^4301 ≤ (45648909494887/100000000000000 : ℝ)^3277 := by
    have hnat : (1100384921 : ℕ)^4301*100000000000000^3277 ≤ 45648909494887^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100384921 2000000000 45648909494887 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77634037/312500000 : ℝ)^4301 ≤ (16077345873157/100000000000000 : ℝ)^3277 := by
    have hnat : (77634037 : ℕ)^4301*100000000000000^3277 ≤ 16077345873157^3277*312500000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77634037 312500000 16077345873157 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4810670741/10000000000 : ℝ)^4301 ≤ (19136872312159/50000000000000 : ℝ)^3277 := by
    have hnat : (4810670741 : ℕ)^4301*50000000000000^3277 ≤ 19136872312159^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4810670741 10000000000 19136872312159 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1100384921/2000000000 : ℝ), (-77634037/312500000 : ℝ), (4810670741/10000000000 : ℝ)] ![(45648909494887/100000000000000 : ℝ), (16077345873157/100000000000000 : ℝ), (19136872312159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1100384921/2000000000 : ℝ)|^4301 ≤ (45648909494887/100000000000000 : ℝ)^3277
        have hw : |(1100384921/2000000000 : ℝ)|=(1100384921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-77634037/312500000 : ℝ)|^4301 ≤ (16077345873157/100000000000000 : ℝ)^3277
        have hw : |(-77634037/312500000 : ℝ)|=(77634037/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4810670741/10000000000 : ℝ)|^4301 ≤ (19136872312159/50000000000000 : ℝ)^3277
        have hw : |(4810670741/10000000000 : ℝ)|=(4810670741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s0_2 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2750962143/5000000000 : ℝ)*x 0 + (2405335283/5000000000 : ℝ)*x 1 + (-155268113/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2750962143/5000000000 : ℝ)^4301 ≤ (4564890602113/10000000000000 : ℝ)^3277 := by
    have hnat : (2750962143 : ℕ)^4301*10000000000000^3277 ≤ 4564890602113^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750962143 5000000000 4564890602113 10000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2405335283/5000000000 : ℝ)^4301 ≤ (38273742796949/100000000000000 : ℝ)^3277 := by
    have hnat : (2405335283 : ℕ)^4301*100000000000000^3277 ≤ 38273742796949^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405335283 5000000000 38273742796949 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (155268113/625000000 : ℝ)^4301 ≤ (1004834448333/6250000000000 : ℝ)^3277 := by
    have hnat : (155268113 : ℕ)^4301*6250000000000^3277 ≤ 1004834448333^3277*625000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155268113 625000000 1004834448333 6250000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2750962143/5000000000 : ℝ), (2405335283/5000000000 : ℝ), (-155268113/625000000 : ℝ)] ![(4564890602113/10000000000000 : ℝ), (38273742796949/100000000000000 : ℝ), (1004834448333/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2750962143/5000000000 : ℝ)|^4301 ≤ (4564890602113/10000000000000 : ℝ)^3277
        have hw : |(2750962143/5000000000 : ℝ)|=(2750962143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2405335283/5000000000 : ℝ)|^4301 ≤ (38273742796949/100000000000000 : ℝ)^3277
        have hw : |(2405335283/5000000000 : ℝ)|=(2405335283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-155268113/625000000 : ℝ)|^4301 ≤ (1004834448333/6250000000000 : ℝ)^3277
        have hw : |(-155268113/625000000 : ℝ)|=(155268113/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s0_3 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (835779277/2000000000 : ℝ)*x 0 + (621323013/2000000000 : ℝ)*x 1 + (5591262871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835779277/2000000000 : ℝ)^4301 ≤ (248565363543/781250000000 : ℝ)^3277 := by
    have hnat : (835779277 : ℕ)^4301*781250000000^3277 ≤ 248565363543^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835779277 2000000000 248565363543 781250000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (621323013/2000000000 : ℝ)^4301 ≤ (10779707029751/50000000000000 : ℝ)^3277 := by
    have hnat : (621323013 : ℕ)^4301*50000000000000^3277 ≤ 10779707029751^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621323013 2000000000 10779707029751 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5591262871/10000000000 : ℝ)^4301 ≤ (23312109694529/50000000000000 : ℝ)^3277 := by
    have hnat : (5591262871 : ℕ)^4301*50000000000000^3277 ≤ 23312109694529^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591262871 10000000000 23312109694529 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(835779277/2000000000 : ℝ), (621323013/2000000000 : ℝ), (5591262871/10000000000 : ℝ)] ![(248565363543/781250000000 : ℝ), (10779707029751/50000000000000 : ℝ), (23312109694529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(835779277/2000000000 : ℝ)|^4301 ≤ (248565363543/781250000000 : ℝ)^3277
        have hw : |(835779277/2000000000 : ℝ)|=(835779277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(621323013/2000000000 : ℝ)|^4301 ≤ (10779707029751/50000000000000 : ℝ)^3277
        have hw : |(621323013/2000000000 : ℝ)|=(621323013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5591262871/10000000000 : ℝ)|^4301 ≤ (23312109694529/50000000000000 : ℝ)^3277
        have hw : |(5591262871/10000000000 : ℝ)|=(5591262871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s0_4 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-907099691/5000000000 : ℝ)*x 0 + (2420607259/5000000000 : ℝ)*x 1 + (5965714191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (907099691/5000000000 : ℝ)^4301 ≤ (212847334579/2000000000000 : ℝ)^3277 := by
    have hnat : (907099691 : ℕ)^4301*2000000000000^3277 ≤ 212847334579^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907099691 5000000000 212847334579 2000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2420607259/5000000000 : ℝ)^4301 ≤ (9648250519207/25000000000000 : ℝ)^3277 := by
    have hnat : (2420607259 : ℕ)^4301*25000000000000^3277 ≤ 9648250519207^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2420607259 5000000000 9648250519207 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5965714191/10000000000 : ℝ)^4301 ≤ (1015292623443/2000000000000 : ℝ)^3277 := by
    have hnat : (5965714191 : ℕ)^4301*2000000000000^3277 ≤ 1015292623443^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5965714191 10000000000 1015292623443 2000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-907099691/5000000000 : ℝ), (2420607259/5000000000 : ℝ), (5965714191/10000000000 : ℝ)] ![(212847334579/2000000000000 : ℝ), (9648250519207/25000000000000 : ℝ), (1015292623443/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-907099691/5000000000 : ℝ)|^4301 ≤ (212847334579/2000000000000 : ℝ)^3277
        have hw : |(-907099691/5000000000 : ℝ)|=(907099691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2420607259/5000000000 : ℝ)|^4301 ≤ (9648250519207/25000000000000 : ℝ)^3277
        have hw : |(2420607259/5000000000 : ℝ)|=(2420607259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5965714191/10000000000 : ℝ)|^4301 ≤ (1015292623443/2000000000000 : ℝ)^3277
        have hw : |(5965714191/10000000000 : ℝ)|=(5965714191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s0_5 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5178522331/10000000000 : ℝ)*x 0 + (-332311671/2500000000 : ℝ)*x 1 + (238628559/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5178522331/10000000000 : ℝ)^4301 ≤ (21080001509387/50000000000000 : ℝ)^3277 := by
    have hnat : (5178522331 : ℕ)^4301*50000000000000^3277 ≤ 21080001509387^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178522331 10000000000 21080001509387 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (332311671/2500000000 : ℝ)^4301 ≤ (7075368209927/100000000000000 : ℝ)^3277 := by
    have hnat : (332311671 : ℕ)^4301*100000000000000^3277 ≤ 7075368209927^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332311671 2500000000 7075368209927 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238628559/400000000 : ℝ)^4301 ≤ (50764628759771/100000000000000 : ℝ)^3277 := by
    have hnat : (238628559 : ℕ)^4301*100000000000000^3277 ≤ 50764628759771^3277*400000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238628559 400000000 50764628759771 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5178522331/10000000000 : ℝ), (-332311671/2500000000 : ℝ), (238628559/400000000 : ℝ)] ![(21080001509387/50000000000000 : ℝ), (7075368209927/100000000000000 : ℝ), (50764628759771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5178522331/10000000000 : ℝ)|^4301 ≤ (21080001509387/50000000000000 : ℝ)^3277
        have hw : |(5178522331/10000000000 : ℝ)|=(5178522331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-332311671/2500000000 : ℝ)|^4301 ≤ (7075368209927/100000000000000 : ℝ)^3277
        have hw : |(-332311671/2500000000 : ℝ)|=(332311671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(238628559/400000000 : ℝ)|^4301 ≤ (50764628759771/100000000000000 : ℝ)^3277
        have hw : |(238628559/400000000 : ℝ)|=(238628559/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s0_6 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1294630581/2500000000 : ℝ)*x 0 + (5965714189/10000000000 : ℝ)*x 1 + (-1329246353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1294630581/2500000000 : ℝ)^4301 ≤ (42160002943977/100000000000000 : ℝ)^3277 := by
    have hnat : (1294630581 : ℕ)^4301*100000000000000^3277 ≤ 42160002943977^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294630581 2500000000 42160002943977 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5965714189/10000000000 : ℝ)^4301 ≤ (50764631149813/100000000000000 : ℝ)^3277 := by
    have hnat : (5965714189 : ℕ)^4301*100000000000000^3277 ≤ 50764631149813^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5965714189 10000000000 50764631149813 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1329246353/10000000000 : ℝ)^4301 ≤ (7075365897519/100000000000000 : ℝ)^3277 := by
    have hnat : (1329246353 : ℕ)^4301*100000000000000^3277 ≤ 7075365897519^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1329246353 10000000000 7075365897519 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1294630581/2500000000 : ℝ), (5965714189/10000000000 : ℝ), (-1329246353/10000000000 : ℝ)] ![(42160002943977/100000000000000 : ℝ), (50764631149813/100000000000000 : ℝ), (7075365897519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1294630581/2500000000 : ℝ)|^4301 ≤ (42160002943977/100000000000000 : ℝ)^3277
        have hw : |(1294630581/2500000000 : ℝ)|=(1294630581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5965714189/10000000000 : ℝ)|^4301 ≤ (50764631149813/100000000000000 : ℝ)^3277
        have hw : |(5965714189/10000000000 : ℝ)|=(5965714189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1329246353/10000000000 : ℝ)|^4301 ≤ (7075365897519/100000000000000 : ℝ)^3277
        have hw : |(-1329246353/10000000000 : ℝ)|=(1329246353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s0_7 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4188236721/10000000000 : ℝ)*x 0 + (5527310831/10000000000 : ℝ)*x 1 + (396606313/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4188236721/10000000000 : ℝ)^4301 ≤ (31909734099511/100000000000000 : ℝ)^3277 := by
    have hnat : (4188236721 : ℕ)^4301*100000000000000^3277 ≤ 31909734099511^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4188236721 10000000000 31909734099511 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5527310831/10000000000 : ℝ)^4301 ≤ (45925552412929/100000000000000 : ℝ)^3277 := by
    have hnat : (5527310831 : ℕ)^4301*100000000000000^3277 ≤ 45925552412929^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527310831 10000000000 45925552412929 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396606313/1250000000 : ℝ)^4301 ≤ (692647295917/3125000000000 : ℝ)^3277 := by
    have hnat : (396606313 : ℕ)^4301*3125000000000^3277 ≤ 692647295917^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396606313 1250000000 692647295917 3125000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4188236721/10000000000 : ℝ), (5527310831/10000000000 : ℝ), (396606313/1250000000 : ℝ)] ![(31909734099511/100000000000000 : ℝ), (45925552412929/100000000000000 : ℝ), (692647295917/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4188236721/10000000000 : ℝ)|^4301 ≤ (31909734099511/100000000000000 : ℝ)^3277
        have hw : |(4188236721/10000000000 : ℝ)|=(4188236721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5527310831/10000000000 : ℝ)|^4301 ≤ (45925552412929/100000000000000 : ℝ)^3277
        have hw : |(5527310831/10000000000 : ℝ)|=(5527310831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(396606313/1250000000 : ℝ)|^4301 ≤ (692647295917/3125000000000 : ℝ)^3277
        have hw : |(396606313/1250000000 : ℝ)|=(396606313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1341_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1407/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13439/50000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
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
  have hpowlo : (0 : ℝ) ^ (1075/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1075 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1075*1^256 ≤ 0^256*1^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1075/256 : ℝ) ≤ (266607809843764797/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1075 ≤ (266607809843764797/12500000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1075*12500000000000000000^256 ≤ 266607809843764797^256*5^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 266607809843764797 12500000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (266607809843764797/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1075 := by
      have hnat : (1 : ℕ)^256*1^1075 ≤ 1^1075*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12766607809843764797/12500000000000000000 : ℝ) ≤ (5025192156143867/5000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (12766607809843764797/12500000000000000000 : ℝ)^256 ≤ (5025192156143867/5000000000000000 : ℝ)^1075 := by
      have hnat : (12766607809843764797 : ℕ)^256*5000000000000000^1075 ≤ 5025192156143867^1075*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12766607809843764797 12500000000000000000 5025192156143867 5000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5025192156143867/5000000000000000 : ℝ)) (X := (12766607809843764797/12500000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6516607809843764797/6250000000000000000 : ℝ) ≤ (2525192156143867/2500000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (6516607809843764797/6250000000000000000 : ℝ)^256 ≤ (2525192156143867/2500000000000000 : ℝ)^1075 := by
      have hnat : (6516607809843764797 : ℕ)^256*2500000000000000^1075 ≤ 2525192156143867^1075*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6516607809843764797 6250000000000000000 2525192156143867 2500000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2525192156143867/2500000000000000 : ℝ)) (X := (6516607809843764797/6250000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(25192156143867/2000000000000000 : ℝ)*(0 : ℝ))^(1075/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(25192156143867/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(266607809843764797/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(25192156143867/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1075/256 : ℝ) := by
    rw [show (1 : ℝ)+(25192156143867/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5025192156143867/5000000000000000 : ℝ) by norm_num, show 1+(266607809843764797/12500000000000000000 : ℝ)+(0 : ℝ)=(12766607809843764797/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(266607809843764797/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(25192156143867/2000000000000000 : ℝ)*(2/5 : ℝ))^(1075/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(25192156143867/2000000000000000 : ℝ)*(2/5 : ℝ)=(2525192156143867/2500000000000000 : ℝ) by norm_num, show 1+2*(266607809843764797/12500000000000000000 : ℝ)=(6516607809843764797/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(25192156143867/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25192156143867/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(25192156143867/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25192156143867/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(25192156143867/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25192156143867/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1809737549/10000000000 : ℝ)*X 0 0+(1499337201/2500000000 : ℝ)*X 0 1+(2405335169/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1100384921/2000000000 : ℝ)*X 1 0+(-77634037/312500000 : ℝ)*X 1 1+(4810670741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2750962143/5000000000 : ℝ)*X 2 0+(2405335283/5000000000 : ℝ)*X 2 1+(-155268113/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((835779277/2000000000 : ℝ)*X 0 0+(621323013/2000000000 : ℝ)*X 0 1+(5591262871/10000000000 : ℝ)*X 0 2+(835779277/2000000000 : ℝ)*X 1 0+(621323013/2000000000 : ℝ)*X 1 1+(5591262871/10000000000 : ℝ)*X 1 2+(835779277/2000000000 : ℝ)*X 2 0+(621323013/2000000000 : ℝ)*X 2 1+(5591262871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-907099691/5000000000 : ℝ)*X 0 0+(2420607259/5000000000 : ℝ)*X 0 1+(5965714191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5178522331/10000000000 : ℝ)*X 1 0+(-332311671/2500000000 : ℝ)*X 1 1+(238628559/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1294630581/2500000000 : ℝ)*X 2 0+(5965714189/10000000000 : ℝ)*X 2 1+(-1329246353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4188236721/10000000000 : ℝ)*X 0 0+(5527310831/10000000000 : ℝ)*X 0 1+(396606313/1250000000 : ℝ)*X 0 2+(4188236721/10000000000 : ℝ)*X 1 0+(5527310831/10000000000 : ℝ)*X 1 1+(396606313/1250000000 : ℝ)*X 1 2+(4188236721/10000000000 : ℝ)*X 2 0+(5527310831/10000000000 : ℝ)*X 2 1+(396606313/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2266281997191935608143/781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (77719543/100000000000000 : ℝ)*(base1) + (14116437/100000000000000 : ℝ)*(base16) + (344260663/50000000000000 : ℝ)*(base19) + (653778719/100000000000000 : ℝ)*(base23) + (31912829/25000000000000 : ℝ)*(upper3) + (19455724632003/3125000000000 : ℝ)*(major0) + (19455724632003/3125000000000 : ℝ)*(major1) + (19455724632003/3125000000000 : ℝ)*(major2) + (84269090705697/10000000000000 : ℝ)*(sp0) + (421346013211277/50000000000000 : ℝ)*(sp1) + (842692075281597/100000000000000 : ℝ)*(sp2) + (80494463062193/20000000000000 : ℝ)*(sp3) + (237465361/12500000000000 : ℝ)*(sp4) + (1157662661/100000000000000 : ℝ)*(sp7) + (25154596918323/6250000000000 : ℝ)*(f.failure) + (210673182265079/25000000000000 : ℝ)*(f.sum) + (7496256999399/3125000000000000000000000000 : ℝ)*base66 + (32840844875601/6250000000000000000000000000 : ℝ)*base67 + (41380530831851/6250000000000000000000000000 : ℝ)*base69 + (4531117400601/6250000000000000000000000000 : ℝ)*base71 + (12334059500601/3125000000000000000000000000 : ℝ)*base73 + (2782175705649/6250000000000000000000000000 : ℝ)*base76 + (11758470075601/6250000000000000000000000000 : ℝ)*base77 + (981332138101/6250000000000000000000000000 : ℝ)*base79 + (1614275254387/1562500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (2629293/312500000000000000000 : ℝ)*base90 + (2629293/312500000000000000000 : ℝ)*base92 + (2629293/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (157060794421560075562263/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (521664297/100000000000000 : ℝ)*(base19) + (163683793/25000000000000 : ℝ)*(base23) + (135082969/100000000000000 : ℝ)*(base39) + (25989863/50000000000000 : ℝ)*(upper3) + (56429051/50000000000000 : ℝ)*(upper5) + (657004738868537/100000000000000 : ℝ)*(major0) + (657004738868537/100000000000000 : ℝ)*(major1) + (20531393868299/3125000000000 : ℝ)*(major2) + (1205721499/100000000000000 : ℝ)*(sp1) + (1245365169/100000000000000 : ℝ)*(sp2) + (88928361882293/10000000000000 : ℝ)*(sp4) + (444640945718567/50000000000000 : ℝ)*(sp5) + (444640926902779/50000000000000 : ℝ)*(sp6) + (53090702390497/12500000000000 : ℝ)*(sp7) + (53090702390497/12500000000000 : ℝ)*(f.failure) + (889283753905899/100000000000000 : ℝ)*(f.sum) + (68591737815193/40000000000000000000000000000 : ℝ)*base66 + (9005033347233/6250000000000000000000000000 : ℝ)*base67 + (846905865012579/200000000000000000000000000000 : ℝ)*base69 + (19642138665983/6250000000000000000000000000 : ℝ)*base71 + (191366143735193/40000000000000000000000000000 : ℝ)*base74 + (456004109212579/200000000000000000000000000000 : ℝ)*base75 + (577843807412579/200000000000000000000000000000 : ℝ)*base77 + (205530137412579/200000000000000000000000000000 : ℝ)*base79 + (192106934012579/100000000000000000000000000000 : ℝ)*base81 + (469327/625000000000000000000 : ℝ)*base90 + (469327/625000000000000000000 : ℝ)*base92 + (469327/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1341_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1407/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13439/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1341_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1341_s1_0 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-398939891/2000000000 : ℝ)*x 0 + (564257443/1000000000 : ℝ)*x 1 + (5046994451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398939891/2000000000 : ℝ)^4301 ≤ (12053204666071/100000000000000 : ℝ)^3277 := by
    have hnat : (398939891 : ℕ)^4301*100000000000000^3277 ≤ 12053204666071^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398939891 2000000000 12053204666071 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564257443/1000000000 : ℝ)^4301 ≤ (47186600637257/100000000000000 : ℝ)^3277 := by
    have hnat : (564257443 : ℕ)^4301*100000000000000^3277 ≤ 47186600637257^3277*1000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564257443 1000000000 47186600637257 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5046994451/10000000000 : ℝ)^4301 ≤ (40760194678079/100000000000000 : ℝ)^3277 := by
    have hnat : (5046994451 : ℕ)^4301*100000000000000^3277 ≤ 40760194678079^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5046994451 10000000000 40760194678079 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398939891/2000000000 : ℝ), (564257443/1000000000 : ℝ), (5046994451/10000000000 : ℝ)] ![(12053204666071/100000000000000 : ℝ), (47186600637257/100000000000000 : ℝ), (40760194678079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398939891/2000000000 : ℝ)|^4301 ≤ (12053204666071/100000000000000 : ℝ)^3277
        have hw : |(-398939891/2000000000 : ℝ)|=(398939891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564257443/1000000000 : ℝ)|^4301 ≤ (47186600637257/100000000000000 : ℝ)^3277
        have hw : |(564257443/1000000000 : ℝ)|=(564257443/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5046994451/10000000000 : ℝ)|^4301 ≤ (40760194678079/100000000000000 : ℝ)^3277
        have hw : |(5046994451/10000000000 : ℝ)|=(5046994451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s1_1 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5405820109/10000000000 : ℝ)*x 0 + (-2312541669/10000000000 : ℝ)*x 1 + (1261748603/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5405820109/10000000000 : ℝ)^4301 ≤ (44605245204443/100000000000000 : ℝ)^3277 := by
    have hnat : (5405820109 : ℕ)^4301*100000000000000^3277 ≤ 44605245204443^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405820109 10000000000 44605245204443 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2312541669/10000000000 : ℝ)^4301 ≤ (14634560515677/100000000000000 : ℝ)^3277 := by
    have hnat : (2312541669 : ℕ)^4301*100000000000000^3277 ≤ 14634560515677^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312541669 10000000000 14634560515677 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1261748603/2500000000 : ℝ)^4301 ≤ (2547512141543/6250000000000 : ℝ)^3277 := by
    have hnat : (1261748603 : ℕ)^4301*6250000000000^3277 ≤ 2547512141543^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1261748603 2500000000 2547512141543 6250000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5405820109/10000000000 : ℝ), (-2312541669/10000000000 : ℝ), (1261748603/2500000000 : ℝ)] ![(44605245204443/100000000000000 : ℝ), (14634560515677/100000000000000 : ℝ), (2547512141543/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5405820109/10000000000 : ℝ)|^4301 ≤ (44605245204443/100000000000000 : ℝ)^3277
        have hw : |(5405820109/10000000000 : ℝ)|=(5405820109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2312541669/10000000000 : ℝ)|^4301 ≤ (14634560515677/100000000000000 : ℝ)^3277
        have hw : |(-2312541669/10000000000 : ℝ)|=(2312541669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1261748603/2500000000 : ℝ)|^4301 ≤ (2547512141543/6250000000000 : ℝ)^3277
        have hw : |(1261748603/2500000000 : ℝ)|=(1261748603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s1_2 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (54058201/100000000 : ℝ)*x 0 + (5046994191/10000000000 : ℝ)*x 1 + (-2312541963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54058201/100000000 : ℝ)^4301 ≤ (1393913909593/3125000000000 : ℝ)^3277 := by
    have hnat : (54058201 : ℕ)^4301*3125000000000^3277 ≤ 1393913909593^3277*100000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54058201 100000000 1393913909593 3125000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5046994191/10000000000 : ℝ)^4301 ≤ (40760191922139/100000000000000 : ℝ)^3277 := by
    have hnat : (5046994191 : ℕ)^4301*100000000000000^3277 ≤ 40760191922139^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5046994191 10000000000 40760191922139 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2312541963/10000000000 : ℝ)^4301 ≤ (14634562957591/100000000000000 : ℝ)^3277 := by
    have hnat : (2312541963 : ℕ)^4301*100000000000000^3277 ≤ 14634562957591^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312541963 10000000000 14634562957591 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54058201/100000000 : ℝ), (5046994191/10000000000 : ℝ), (-2312541963/10000000000 : ℝ)] ![(1393913909593/3125000000000 : ℝ), (40760191922139/100000000000000 : ℝ), (14634562957591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54058201/100000000 : ℝ)|^4301 ≤ (1393913909593/3125000000000 : ℝ)^3277
        have hw : |(54058201/100000000 : ℝ)|=(54058201/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5046994191/10000000000 : ℝ)|^4301 ≤ (40760191922139/100000000000000 : ℝ)^3277
        have hw : |(5046994191/10000000000 : ℝ)|=(5046994191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2312541963/10000000000 : ℝ)|^4301 ≤ (14634562957591/100000000000000 : ℝ)^3277
        have hw : |(-2312541963/10000000000 : ℝ)|=(2312541963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s1_3 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2146243961/5000000000 : ℝ)*x 0 + (1855482237/5000000000 : ℝ)*x 1 + (4957980339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146243961/5000000000 : ℝ)^4301 ≤ (6591248274791/20000000000000 : ℝ)^3277 := by
    have hnat : (2146243961 : ℕ)^4301*20000000000000^3277 ≤ 6591248274791^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146243961 5000000000 6591248274791 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1855482237/5000000000 : ℝ)^4301 ≤ (27224482403861/100000000000000 : ℝ)^3277 := by
    have hnat : (1855482237 : ℕ)^4301*100000000000000^3277 ≤ 27224482403861^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855482237 5000000000 27224482403861 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4957980339/10000000000 : ℝ)^4301 ≤ (159277104803/400000000000 : ℝ)^3277 := by
    have hnat : (4957980339 : ℕ)^4301*400000000000^3277 ≤ 159277104803^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4957980339 10000000000 159277104803 400000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2146243961/5000000000 : ℝ), (1855482237/5000000000 : ℝ), (4957980339/10000000000 : ℝ)] ![(6591248274791/20000000000000 : ℝ), (27224482403861/100000000000000 : ℝ), (159277104803/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2146243961/5000000000 : ℝ)|^4301 ≤ (6591248274791/20000000000000 : ℝ)^3277
        have hw : |(2146243961/5000000000 : ℝ)|=(2146243961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1855482237/5000000000 : ℝ)|^4301 ≤ (27224482403861/100000000000000 : ℝ)^3277
        have hw : |(1855482237/5000000000 : ℝ)|=(1855482237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4957980339/10000000000 : ℝ)|^4301 ≤ (159277104803/400000000000 : ℝ)^3277
        have hw : |(4957980339/10000000000 : ℝ)|=(4957980339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s1_4 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1995237703/10000000000 : ℝ)*x 0 + (5054472211/10000000000 : ℝ)*x 1 + (5634960611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1995237703/10000000000 : ℝ)^4301 ≤ (6028736796869/50000000000000 : ℝ)^3277 := by
    have hnat : (1995237703 : ℕ)^4301*50000000000000^3277 ≤ 6028736796869^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995237703 10000000000 6028736796869 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5054472211/10000000000 : ℝ)^4301 ≤ (40839475553119/100000000000000 : ℝ)^3277 := by
    have hnat : (5054472211 : ℕ)^4301*100000000000000^3277 ≤ 40839475553119^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5054472211 10000000000 40839475553119 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5634960611/10000000000 : ℝ)^4301 ≤ (9420610170049/20000000000000 : ℝ)^3277 := by
    have hnat : (5634960611 : ℕ)^4301*20000000000000^3277 ≤ 9420610170049^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5634960611 10000000000 9420610170049 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1995237703/10000000000 : ℝ), (5054472211/10000000000 : ℝ), (5634960611/10000000000 : ℝ)] ![(6028736796869/50000000000000 : ℝ), (40839475553119/100000000000000 : ℝ), (9420610170049/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1995237703/10000000000 : ℝ)|^4301 ≤ (6028736796869/50000000000000 : ℝ)^3277
        have hw : |(-1995237703/10000000000 : ℝ)|=(1995237703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5054472211/10000000000 : ℝ)|^4301 ≤ (40839475553119/100000000000000 : ℝ)^3277
        have hw : |(5054472211/10000000000 : ℝ)|=(5054472211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5634960611/10000000000 : ℝ)|^4301 ≤ (9420610170049/20000000000000 : ℝ)^3277
        have hw : |(5634960611/10000000000 : ℝ)|=(5634960611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s1_5 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625644133/5000000000 : ℝ)*x 0 + (-1724576063/10000000000 : ℝ)*x 1 + (5634959827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625644133/5000000000 : ℝ)^4301 ≤ (21469616146059/50000000000000 : ℝ)^3277 := by
    have hnat : (2625644133 : ℕ)^4301*50000000000000^3277 ≤ 21469616146059^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625644133 5000000000 21469616146059 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1724576063/10000000000 : ℝ)^4301 ≤ (62235784021/625000000000 : ℝ)^3277 := by
    have hnat : (1724576063 : ℕ)^4301*625000000000^3277 ≤ 62235784021^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724576063 10000000000 62235784021 625000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5634959827/10000000000 : ℝ)^4301 ≤ (47103042248883/100000000000000 : ℝ)^3277 := by
    have hnat : (5634959827 : ℕ)^4301*100000000000000^3277 ≤ 47103042248883^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5634959827 10000000000 47103042248883 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625644133/5000000000 : ℝ), (-1724576063/10000000000 : ℝ), (5634959827/10000000000 : ℝ)] ![(21469616146059/50000000000000 : ℝ), (62235784021/625000000000 : ℝ), (47103042248883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625644133/5000000000 : ℝ)|^4301 ≤ (21469616146059/50000000000000 : ℝ)^3277
        have hw : |(2625644133/5000000000 : ℝ)|=(2625644133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1724576063/10000000000 : ℝ)|^4301 ≤ (62235784021/625000000000 : ℝ)^3277
        have hw : |(-1724576063/10000000000 : ℝ)|=(1724576063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5634959827/10000000000 : ℝ)|^4301 ≤ (47103042248883/100000000000000 : ℝ)^3277
        have hw : |(5634959827/10000000000 : ℝ)|=(5634959827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s1_6 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625643773/5000000000 : ℝ)*x 0 + (45079677/80000000 : ℝ)*x 1 + (-13796619/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625643773/5000000000 : ℝ)^4301 ≤ (8587844913013/20000000000000 : ℝ)^3277 := by
    have hnat : (2625643773 : ℕ)^4301*20000000000000^3277 ≤ 8587844913013^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625643773 5000000000 8587844913013 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45079677/80000000 : ℝ)^4301 ≤ (11775760008179/25000000000000 : ℝ)^3277 := by
    have hnat : (45079677 : ℕ)^4301*25000000000000^3277 ≤ 11775760008179^3277*80000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45079677 80000000 11775760008179 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13796619/80000000 : ℝ)^4301 ≤ (2489433846517/25000000000000 : ℝ)^3277 := by
    have hnat : (13796619 : ℕ)^4301*25000000000000^3277 ≤ 2489433846517^3277*80000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13796619 80000000 2489433846517 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625643773/5000000000 : ℝ), (45079677/80000000 : ℝ), (-13796619/80000000 : ℝ)] ![(8587844913013/20000000000000 : ℝ), (11775760008179/25000000000000 : ℝ), (2489433846517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625643773/5000000000 : ℝ)|^4301 ≤ (8587844913013/20000000000000 : ℝ)^3277
        have hw : |(2625643773/5000000000 : ℝ)|=(2625643773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45079677/80000000 : ℝ)|^4301 ≤ (11775760008179/25000000000000 : ℝ)^3277
        have hw : |(45079677/80000000 : ℝ)|=(45079677/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13796619/80000000 : ℝ)|^4301 ≤ (2489433846517/25000000000000 : ℝ)^3277
        have hw : |(-13796619/80000000 : ℝ)|=(13796619/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s1_7 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2146807059/5000000000 : ℝ)*x 0 + (4942322589/10000000000 : ℝ)*x 1 + (1863454007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146807059/5000000000 : ℝ)^4301 ≤ (32967590263677/100000000000000 : ℝ)^3277 := by
    have hnat : (2146807059 : ℕ)^4301*100000000000000^3277 ≤ 32967590263677^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146807059 5000000000 32967590263677 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4942322589/10000000000 : ℝ)^4301 ≤ (2478394340669/6250000000000 : ℝ)^3277 := by
    have hnat : (4942322589 : ℕ)^4301*6250000000000^3277 ≤ 2478394340669^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4942322589 10000000000 2478394340669 6250000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1863454007/5000000000 : ℝ)^4301 ≤ (27378100271571/100000000000000 : ℝ)^3277 := by
    have hnat : (1863454007 : ℕ)^4301*100000000000000^3277 ≤ 27378100271571^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863454007 5000000000 27378100271571 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2146807059/5000000000 : ℝ), (4942322589/10000000000 : ℝ), (1863454007/5000000000 : ℝ)] ![(32967590263677/100000000000000 : ℝ), (2478394340669/6250000000000 : ℝ), (27378100271571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2146807059/5000000000 : ℝ)|^4301 ≤ (32967590263677/100000000000000 : ℝ)^3277
        have hw : |(2146807059/5000000000 : ℝ)|=(2146807059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4942322589/10000000000 : ℝ)|^4301 ≤ (2478394340669/6250000000000 : ℝ)^3277
        have hw : |(4942322589/10000000000 : ℝ)|=(4942322589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1863454007/5000000000 : ℝ)|^4301 ≤ (27378100271571/100000000000000 : ℝ)^3277
        have hw : |(1863454007/5000000000 : ℝ)|=(1863454007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1341_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13439/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1407/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6881/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19469/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13439/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1407/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13439/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1407/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13439/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1407/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13439/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1407/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13439/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1407/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13439/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1407/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1407/100000 : ℝ) ^ (1075/256 : ℝ) ≤ (838015128261/50000000000000000000 : ℝ) := by
    have hpowers : (1407/100000 : ℝ)^1075 ≤ (838015128261/50000000000000000000 : ℝ)^256 := by
      have hnat : (1407 : ℕ)^1075*50000000000000000000^256 ≤ 838015128261^256*100000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1407 100000 838015128261 50000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1407/100000 : ℝ)) (X := (838015128261/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hpowhi : (13439/50000 : ℝ) ^ (1075/256 : ℝ) ≤ (100427576067634251/25000000000000000000 : ℝ) := by
    have hpowers : (13439/50000 : ℝ)^1075 ≤ (100427576067634251/25000000000000000000 : ℝ)^256 := by
      have hnat : (13439 : ℕ)^1075*25000000000000000000^256 ≤ 100427576067634251^256*50000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13439 50000 100427576067634251 25000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13439/50000 : ℝ)) (X := (100427576067634251/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000838015128261/25000000000000000000 : ℝ) ≤ (10000000079825813/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (25000000838015128261/25000000000000000000 : ℝ)^256 ≤ (10000000079825813/10000000000000000 : ℝ)^1075 := by
      have hnat : (25000000838015128261 : ℕ)^256*10000000000000000^1075 ≤ 10000000079825813^1075*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000838015128261 25000000000000000000 10000000079825813 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000079825813/10000000000000000 : ℝ)) (X := (25000000838015128261/25000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50200855990150396763/50000000000000000000 : ℝ) ≤ (1000955174602023/1000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (50200855990150396763/50000000000000000000 : ℝ)^256 ≤ (1000955174602023/1000000000000000 : ℝ)^1075 := by
      have hnat : (50200855990150396763 : ℕ)^256*1000000000000000^1075 ≤ 1000955174602023^1075*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50200855990150396763 50000000000000000000 1000955174602023 1000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000955174602023/1000000000000000 : ℝ)) (X := (50200855990150396763/50000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12600427576067634251/12500000000000000000 : ℝ) ≤ (10019103412214647/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (12600427576067634251/12500000000000000000 : ℝ)^256 ≤ (10019103412214647/10000000000000000 : ℝ)^1075 := by
      have hnat : (12600427576067634251 : ℕ)^256*10000000000000000^1075 ≤ 10019103412214647^1075*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12600427576067634251 12500000000000000000 10019103412214647 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10019103412214647/10000000000000000 : ℝ)) (X := (12600427576067634251/12500000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(838015128261/50000000000000000000 : ℝ) ≤ ((50936624728914438697/50942000000000000000 : ℝ)+2*(9551666194417/2547100000000000 : ℝ)*(1407/100000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (50936624728914438697/50942000000000000000 : ℝ)+2*(9551666194417/2547100000000000 : ℝ)*(1407/100000 : ℝ)=(10000000079825813/10000000000000000 : ℝ) by norm_num, show 1+2*(838015128261/50000000000000000000 : ℝ)=(25000000838015128261/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(100427576067634251/25000000000000000000 : ℝ)+(838015128261/50000000000000000000 : ℝ) ≤ ((50936624728914438697/50942000000000000000 : ℝ)+(9551666194417/2547100000000000 : ℝ)*((13439/50000 : ℝ)+(1407/100000 : ℝ)))^(1075/256 : ℝ) := by
    rw [show (50936624728914438697/50942000000000000000 : ℝ)+(9551666194417/2547100000000000 : ℝ)*((13439/50000 : ℝ)+(1407/100000 : ℝ))=(1000955174602023/1000000000000000 : ℝ) by norm_num, show 1+(100427576067634251/25000000000000000000 : ℝ)+(838015128261/50000000000000000000 : ℝ)=(50200855990150396763/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(100427576067634251/25000000000000000000 : ℝ) ≤ ((50936624728914438697/50942000000000000000 : ℝ)+2*(9551666194417/2547100000000000 : ℝ)*(13439/50000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (50936624728914438697/50942000000000000000 : ℝ)+2*(9551666194417/2547100000000000 : ℝ)*(13439/50000 : ℝ)=(10019103412214647/10000000000000000 : ℝ) by norm_num, show 1+2*(100427576067634251/25000000000000000000 : ℝ)=(12600427576067634251/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (50936624728914438697/50942000000000000000 : ℝ)*(X 1 0+X 2 0)+(9551666194417/2547100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (1407/100000 : ℝ)) (hi := (13439/50000 : ℝ)) (c := (50936624728914438697/50942000000000000000 : ℝ)) (alpha := (9551666194417/2547100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (50936624728914438697/50942000000000000000 : ℝ)*(X 0 1+X 2 1)+(9551666194417/2547100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (1407/100000 : ℝ)) (hi := (13439/50000 : ℝ)) (c := (50936624728914438697/50942000000000000000 : ℝ)) (alpha := (9551666194417/2547100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (50936624728914438697/50942000000000000000 : ℝ)*(X 0 2+X 1 2)+(9551666194417/2547100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (1407/100000 : ℝ)) (hi := (13439/50000 : ℝ)) (c := (50936624728914438697/50942000000000000000 : ℝ)) (alpha := (9551666194417/2547100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-398939891/2000000000 : ℝ)*X 0 0+(564257443/1000000000 : ℝ)*X 0 1+(5046994451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5405820109/10000000000 : ℝ)*X 1 0+(-2312541669/10000000000 : ℝ)*X 1 1+(1261748603/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((54058201/100000000 : ℝ)*X 2 0+(5046994191/10000000000 : ℝ)*X 2 1+(-2312541963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2146243961/5000000000 : ℝ)*X 0 0+(1855482237/5000000000 : ℝ)*X 0 1+(4957980339/10000000000 : ℝ)*X 0 2+(2146243961/5000000000 : ℝ)*X 1 0+(1855482237/5000000000 : ℝ)*X 1 1+(4957980339/10000000000 : ℝ)*X 1 2+(2146243961/5000000000 : ℝ)*X 2 0+(1855482237/5000000000 : ℝ)*X 2 1+(4957980339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1995237703/10000000000 : ℝ)*X 0 0+(5054472211/10000000000 : ℝ)*X 0 1+(5634960611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2625644133/5000000000 : ℝ)*X 1 0+(-1724576063/10000000000 : ℝ)*X 1 1+(5634959827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2625643773/5000000000 : ℝ)*X 2 0+(45079677/80000000 : ℝ)*X 2 1+(-13796619/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2146807059/5000000000 : ℝ)*X 0 0+(4942322589/10000000000 : ℝ)*X 0 1+(1863454007/5000000000 : ℝ)*X 0 2+(2146807059/5000000000 : ℝ)*X 1 0+(4942322589/10000000000 : ℝ)*X 1 1+(1863454007/5000000000 : ℝ)*X 1 2+(2146807059/5000000000 : ℝ)*X 2 0+(4942322589/10000000000 : ℝ)*X 2 1+(1863454007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (254792770649609151450951/63677500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1627097/4000000000000 : ℝ)*(base1) + (94098379/20000000000000 : ℝ)*(base19) + (467696509/100000000000000 : ℝ)*(base23) + (64662003/50000000000000 : ℝ)*(upper3) + (829133/10000000000000 : ℝ)*(upper5) + (310119488710863/25000000000000 : ℝ)*(major0) + (310119488710863/25000000000000 : ℝ)*(major1) + (310119488710863/25000000000000 : ℝ)*(major2) + (839519138700801/50000000000000 : ℝ)*(sp0) + (209879883698201/12500000000000 : ℝ)*(sp1) + (839519536190497/50000000000000 : ℝ)*(sp2) + (16038300125803/2000000000000 : ℝ)*(sp3) + (651676663/50000000000000 : ℝ)*(sp4) + (594632581/50000000000000 : ℝ)*(sp7) + (25059882382273/3125000000000 : ℝ)*(f.failure) + (1679039540077503/100000000000000 : ℝ)*(f.sum) + (14491789726239/31838750000000000000000000000 : ℝ)*base66 + (6538287867146685511/1273550000000000000000000000000000 : ℝ)*base67 + (8123056157222414489/1273550000000000000000000000000000 : ℝ)*base70 + (750792050806485511/1273550000000000000000000000000000 : ℝ)*base71 + (176909501864277/63677500000000000000000000000 : ℝ)*base73 + (1135430921200814489/1273550000000000000000000000000000 : ℝ)*base76 + (2050748119607914489/1273550000000000000000000000000000 : ℝ)*base78 + (4514431987498285511/1273550000000000000000000000000000 : ℝ)*base79 + (119221205059399/31838750000000000000000000000 : ℝ)*base82 + (33743/156250000000000000000 : ℝ)*base90 + (33743/156250000000000000000 : ℝ)*base92 + (33743/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (520650061996412952544146363/50942000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1088647/25000000000000 : ℝ)*(base1) + (381745937/25000000000000 : ℝ)*(base19) + (141642449/12500000000000 : ℝ)*(base23) + (85039713/100000000000000 : ℝ)*(upper3) + (65472861/25000000000000 : ℝ)*(upper5) + (25454520784331/2000000000000 : ℝ)*(major0) + (25454520784331/2000000000000 : ℝ)*(major1) + (25454520784331/2000000000000 : ℝ)*(major2) + (7551162797/100000000000000 : ℝ)*(sp1) + (219397659/10000000000000 : ℝ)*(sp2) + (861344245471177/50000000000000 : ℝ)*(sp4) + (1722679408441221/100000000000000 : ℝ)*(sp5) + (53833911233487/3125000000000 : ℝ)*(sp6) + (411381623404571/50000000000000 : ℝ)*(sp7) + (82276325116373/10000000000000 : ℝ)*(f.failure) + (861344243293883/50000000000000 : ℝ)*(f.sum) + (246833743451/6367750000000000000000000000 : ℝ)*base66 + (883539334539291293/101884000000000000000000000000000 : ℝ)*base68 + (430547680961091293/101884000000000000000000000000000 : ℝ)*base70 + (120747181799663293/101884000000000000000000000000000 : ℝ)*base72 + (8804364332037/1591937500000000000000000000 : ℝ)*base74 + (484087808237999293/101884000000000000000000000000000 : ℝ)*base76 + (386486553221883293/101884000000000000000000000000000 : ℝ)*base78 + (231365586371755293/101884000000000000000000000000000 : ℝ)*base80 + (4749465851249/3183875000000000000000000000 : ℝ)*base81 + (816843/500000000000000000000 : ℝ)*base90 + (816843/500000000000000000000 : ℝ)*base92 + (816843/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1341_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13439/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1407/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6881/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19469/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1341_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1341_s2_0 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-81397511/400000000 : ℝ)*x 0 + (5480021043/10000000000 : ℝ)*x 1 + (5183774457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81397511/400000000 : ℝ)^4301 ≤ (6186664355701/50000000000000 : ℝ)^3277 := by
    have hnat : (81397511 : ℕ)^4301*50000000000000^3277 ≤ 6186664355701^3277*400000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81397511 400000000 6186664355701 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5480021043/10000000000 : ℝ)^4301 ≤ (22705269346991/50000000000000 : ℝ)^3277 := by
    have hnat : (5480021043 : ℕ)^4301*50000000000000^3277 ≤ 22705269346991^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480021043 10000000000 22705269346991 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183774457/10000000000 : ℝ)^4301 ≤ (21108066294367/50000000000000 : ℝ)^3277 := by
    have hnat : (5183774457 : ℕ)^4301*50000000000000^3277 ≤ 21108066294367^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183774457 10000000000 21108066294367 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81397511/400000000 : ℝ), (5480021043/10000000000 : ℝ), (5183774457/10000000000 : ℝ)] ![(6186664355701/50000000000000 : ℝ), (22705269346991/50000000000000 : ℝ), (21108066294367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81397511/400000000 : ℝ)|^4301 ≤ (6186664355701/50000000000000 : ℝ)^3277
        have hw : |(-81397511/400000000 : ℝ)|=(81397511/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5480021043/10000000000 : ℝ)|^4301 ≤ (22705269346991/50000000000000 : ℝ)^3277
        have hw : |(5480021043/10000000000 : ℝ)|=(5480021043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183774457/10000000000 : ℝ)|^4301 ≤ (21108066294367/50000000000000 : ℝ)^3277
        have hw : |(5183774457/10000000000 : ℝ)|=(5183774457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s2_1 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2683011867/5000000000 : ℝ)*x 0 + (-2188018731/10000000000 : ℝ)*x 1 + (2591887423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683011867/5000000000 : ℝ)^4301 ≤ (22087379025597/50000000000000 : ℝ)^3277 := by
    have hnat : (2683011867 : ℕ)^4301*50000000000000^3277 ≤ 22087379025597^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683011867 5000000000 22087379025597 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2188018731/10000000000 : ℝ)^4301 ≤ (13609105189919/100000000000000 : ℝ)^3277 := by
    have hnat : (2188018731 : ℕ)^4301*100000000000000^3277 ≤ 13609105189919^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188018731 10000000000 13609105189919 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591887423/5000000000 : ℝ)^4301 ≤ (42216136746643/100000000000000 : ℝ)^3277 := by
    have hnat : (2591887423 : ℕ)^4301*100000000000000^3277 ≤ 42216136746643^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591887423 5000000000 42216136746643 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683011867/5000000000 : ℝ), (-2188018731/10000000000 : ℝ), (2591887423/5000000000 : ℝ)] ![(22087379025597/50000000000000 : ℝ), (13609105189919/100000000000000 : ℝ), (42216136746643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683011867/5000000000 : ℝ)|^4301 ≤ (22087379025597/50000000000000 : ℝ)^3277
        have hw : |(2683011867/5000000000 : ℝ)|=(2683011867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2188018731/10000000000 : ℝ)|^4301 ≤ (13609105189919/100000000000000 : ℝ)^3277
        have hw : |(-2188018731/10000000000 : ℝ)|=(2188018731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591887423/5000000000 : ℝ)|^4301 ≤ (42216136746643/100000000000000 : ℝ)^3277
        have hw : |(2591887423/5000000000 : ℝ)|=(2591887423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s2_2 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268301191/500000000 : ℝ)*x 0 + (5183774747/10000000000 : ℝ)*x 1 + (-2188018747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268301191/500000000 : ℝ)^4301 ≤ (22087379490201/50000000000000 : ℝ)^3277 := by
    have hnat : (268301191 : ℕ)^4301*50000000000000^3277 ≤ 22087379490201^3277*500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268301191 500000000 22087379490201 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183774747/10000000000 : ℝ)^4301 ≤ (42216135688461/100000000000000 : ℝ)^3277 := by
    have hnat : (5183774747 : ℕ)^4301*100000000000000^3277 ≤ 42216135688461^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183774747 10000000000 42216135688461 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188018747/10000000000 : ℝ)^4301 ≤ (6804552660267/50000000000000 : ℝ)^3277 := by
    have hnat : (2188018747 : ℕ)^4301*50000000000000^3277 ≤ 6804552660267^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188018747 10000000000 6804552660267 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268301191/500000000 : ℝ), (5183774747/10000000000 : ℝ), (-2188018747/10000000000 : ℝ)] ![(22087379490201/50000000000000 : ℝ), (42216135688461/100000000000000 : ℝ), (6804552660267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268301191/500000000 : ℝ)|^4301 ≤ (22087379490201/50000000000000 : ℝ)^3277
        have hw : |(268301191/500000000 : ℝ)|=(268301191/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183774747/10000000000 : ℝ)|^4301 ≤ (42216135688461/100000000000000 : ℝ)^3277
        have hw : |(5183774747/10000000000 : ℝ)|=(5183774747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2188018747/10000000000 : ℝ)|^4301 ≤ (6804552660267/50000000000000 : ℝ)^3277
        have hw : |(-2188018747/10000000000 : ℝ)|=(2188018747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s2_3 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4320622727/10000000000 : ℝ)*x 0 + (1005216477/2500000000 : ℝ)*x 1 + (2320570817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320622727/10000000000 : ℝ)^4301 ≤ (33240039391439/100000000000000 : ℝ)^3277 := by
    have hnat : (4320622727 : ℕ)^4301*100000000000000^3277 ≤ 33240039391439^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320622727 10000000000 33240039391439 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005216477/2500000000 : ℝ)^4301 ≤ (30246631026599/100000000000000 : ℝ)^3277 := by
    have hnat : (1005216477 : ℕ)^4301*100000000000000^3277 ≤ 30246631026599^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005216477 2500000000 30246631026599 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2320570817/5000000000 : ℝ)^4301 ≤ (7302665914309/20000000000000 : ℝ)^3277 := by
    have hnat : (2320570817 : ℕ)^4301*20000000000000^3277 ≤ 7302665914309^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320570817 5000000000 7302665914309 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320622727/10000000000 : ℝ), (1005216477/2500000000 : ℝ), (2320570817/5000000000 : ℝ)] ![(33240039391439/100000000000000 : ℝ), (30246631026599/100000000000000 : ℝ), (7302665914309/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320622727/10000000000 : ℝ)|^4301 ≤ (33240039391439/100000000000000 : ℝ)^3277
        have hw : |(4320622727/10000000000 : ℝ)|=(4320622727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005216477/2500000000 : ℝ)|^4301 ≤ (30246631026599/100000000000000 : ℝ)^3277
        have hw : |(1005216477/2500000000 : ℝ)|=(1005216477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2320570817/5000000000 : ℝ)|^4301 ≤ (7302665914309/20000000000000 : ℝ)^3277
        have hw : |(2320570817/5000000000 : ℝ)|=(2320570817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s2_4 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2035004031/10000000000 : ℝ)*x 0 + (5185634983/10000000000 : ℝ)*x 1 + (342383983/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2035004031/10000000000 : ℝ)^4301 ≤ (247477149361/2000000000000 : ℝ)^3277 := by
    have hnat : (2035004031 : ℕ)^4301*2000000000000^3277 ≤ 247477149361^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035004031 10000000000 247477149361 2000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185634983/10000000000 : ℝ)^4301 ≤ (4223602032919/10000000000000 : ℝ)^3277 := by
    have hnat : (5185634983 : ℕ)^4301*10000000000000^3277 ≤ 4223602032919^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185634983 10000000000 4223602032919 10000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342383983/625000000 : ℝ)^4301 ≤ (22695061096087/50000000000000 : ℝ)^3277 := by
    have hnat : (342383983 : ℕ)^4301*50000000000000^3277 ≤ 22695061096087^3277*625000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342383983 625000000 22695061096087 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2035004031/10000000000 : ℝ), (5185634983/10000000000 : ℝ), (342383983/625000000 : ℝ)] ![(247477149361/2000000000000 : ℝ), (4223602032919/10000000000000 : ℝ), (22695061096087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2035004031/10000000000 : ℝ)|^4301 ≤ (247477149361/2000000000000 : ℝ)^3277
        have hw : |(-2035004031/10000000000 : ℝ)|=(2035004031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185634983/10000000000 : ℝ)|^4301 ≤ (4223602032919/10000000000000 : ℝ)^3277
        have hw : |(5185634983/10000000000 : ℝ)|=(5185634983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(342383983/625000000 : ℝ)|^4301 ≤ (22695061096087/50000000000000 : ℝ)^3277
        have hw : |(342383983/625000000 : ℝ)|=(342383983/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s2_5 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289674449/10000000000 : ℝ)*x 0 + (-1893649549/10000000000 : ℝ)*x 1 + (5478143731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289674449/10000000000 : ℝ)^4301 ≤ (2167583161809/5000000000000 : ℝ)^3277 := by
    have hnat : (5289674449 : ℕ)^4301*5000000000000^3277 ≤ 2167583161809^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289674449 10000000000 2167583161809 5000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1893649549/10000000000 : ℝ)^4301 ≤ (11258214530333/100000000000000 : ℝ)^3277 := by
    have hnat : (1893649549 : ℕ)^4301*100000000000000^3277 ≤ 11258214530333^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893649549 10000000000 11258214530333 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5478143731/10000000000 : ℝ)^4301 ≤ (45390122224799/100000000000000 : ℝ)^3277 := by
    have hnat : (5478143731 : ℕ)^4301*100000000000000^3277 ≤ 45390122224799^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478143731 10000000000 45390122224799 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289674449/10000000000 : ℝ), (-1893649549/10000000000 : ℝ), (5478143731/10000000000 : ℝ)] ![(2167583161809/5000000000000 : ℝ), (11258214530333/100000000000000 : ℝ), (45390122224799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289674449/10000000000 : ℝ)|^4301 ≤ (2167583161809/5000000000000 : ℝ)^3277
        have hw : |(5289674449/10000000000 : ℝ)|=(5289674449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1893649549/10000000000 : ℝ)|^4301 ≤ (11258214530333/100000000000000 : ℝ)^3277
        have hw : |(-1893649549/10000000000 : ℝ)|=(1893649549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5478143731/10000000000 : ℝ)|^4301 ≤ (45390122224799/100000000000000 : ℝ)^3277
        have hw : |(5478143731/10000000000 : ℝ)|=(5478143731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s2_6 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322418617/2500000000 : ℝ)*x 0 + (684767967/1250000000 : ℝ)*x 1 + (-473412379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322418617/2500000000 : ℝ)^4301 ≤ (43351663440553/100000000000000 : ℝ)^3277 := by
    have hnat : (1322418617 : ℕ)^4301*100000000000000^3277 ≤ 43351663440553^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322418617 2500000000 43351663440553 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684767967/1250000000 : ℝ)^4301 ≤ (45390122279173/100000000000000 : ℝ)^3277 := by
    have hnat : (684767967 : ℕ)^4301*100000000000000^3277 ≤ 45390122279173^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684767967 1250000000 45390122279173 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (473412379/2500000000 : ℝ)^4301 ≤ (11258214272833/100000000000000 : ℝ)^3277 := by
    have hnat : (473412379 : ℕ)^4301*100000000000000^3277 ≤ 11258214272833^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473412379 2500000000 11258214272833 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322418617/2500000000 : ℝ), (684767967/1250000000 : ℝ), (-473412379/2500000000 : ℝ)] ![(43351663440553/100000000000000 : ℝ), (45390122279173/100000000000000 : ℝ), (11258214272833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322418617/2500000000 : ℝ)|^4301 ≤ (43351663440553/100000000000000 : ℝ)^3277
        have hw : |(1322418617/2500000000 : ℝ)|=(1322418617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(684767967/1250000000 : ℝ)|^4301 ≤ (45390122279173/100000000000000 : ℝ)^3277
        have hw : |(684767967/1250000000 : ℝ)|=(684767967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-473412379/2500000000 : ℝ)|^4301 ≤ (11258214272833/100000000000000 : ℝ)^3277
        have hw : |(-473412379/2500000000 : ℝ)|=(473412379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s2_7 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080190453/2500000000 : ℝ)*x 0 + (4637246753/10000000000 : ℝ)*x 1 + (4024795987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080190453/2500000000 : ℝ)^4301 ≤ (33241443790933/100000000000000 : ℝ)^3277 := by
    have hnat : (1080190453 : ℕ)^4301*100000000000000^3277 ≤ 33241443790933^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080190453 2500000000 33241443790933 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4637246753/10000000000 : ℝ)^4301 ≤ (36473117462559/100000000000000 : ℝ)^3277 := by
    have hnat : (4637246753 : ℕ)^4301*100000000000000^3277 ≤ 36473117462559^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4637246753 10000000000 36473117462559 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4024795987/10000000000 : ℝ)^4301 ≤ (15142719367679/50000000000000 : ℝ)^3277 := by
    have hnat : (4024795987 : ℕ)^4301*50000000000000^3277 ≤ 15142719367679^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024795987 10000000000 15142719367679 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080190453/2500000000 : ℝ), (4637246753/10000000000 : ℝ), (4024795987/10000000000 : ℝ)] ![(33241443790933/100000000000000 : ℝ), (36473117462559/100000000000000 : ℝ), (15142719367679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080190453/2500000000 : ℝ)|^4301 ≤ (33241443790933/100000000000000 : ℝ)^3277
        have hw : |(1080190453/2500000000 : ℝ)|=(1080190453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4637246753/10000000000 : ℝ)|^4301 ≤ (36473117462559/100000000000000 : ℝ)^3277
        have hw : |(4637246753/10000000000 : ℝ)|=(4637246753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4024795987/10000000000 : ℝ)|^4301 ≤ (15142719367679/50000000000000 : ℝ)^3277
        have hw : |(4024795987/10000000000 : ℝ)|=(4024795987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1341_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19469/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6881/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1969/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4027/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19469/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6881/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19469/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6881/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19469/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6881/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19469/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6881/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19469/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6881/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19469/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6881/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6881/100000 : ℝ) ^ (1075/256 : ℝ) ≤ (1315359990351101/100000000000000000000 : ℝ) := by
    have hpowers : (6881/100000 : ℝ)^1075 ≤ (1315359990351101/100000000000000000000 : ℝ)^256 := by
      have hnat : (6881 : ℕ)^1075*100000000000000000000^256 ≤ 1315359990351101^256*100000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6881 100000 1315359990351101 100000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6881/100000 : ℝ)) (X := (1315359990351101/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hpowhi : (19469/100000 : ℝ) ^ (1075/256 : ℝ) ≤ (103704716782848407/100000000000000000000 : ℝ) := by
    have hpowers : (19469/100000 : ℝ)^1075 ≤ (103704716782848407/100000000000000000000 : ℝ)^256 := by
      have hnat : (19469 : ℕ)^1075*100000000000000000000^256 ≤ 103704716782848407^256*100000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19469 100000 103704716782848407 100000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19469/100000 : ℝ)) (X := (103704716782848407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001315359990351101/50000000000000000000 : ℝ) ≤ (2000012529443093/2000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (50001315359990351101/50000000000000000000 : ℝ)^256 ≤ (2000012529443093/2000000000000000 : ℝ)^1075 := by
      have hnat : (50001315359990351101 : ℕ)^256*2000000000000000^1075 ≤ 2000012529443093^1075*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001315359990351101 50000000000000000000 2000012529443093 2000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000012529443093/2000000000000000 : ℝ)) (X := (50001315359990351101/50000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25026255019193299877/25000000000000000000 : ℝ) ≤ (10002499943329863/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (25026255019193299877/25000000000000000000 : ℝ)^256 ≤ (10002499943329863/10000000000000000 : ℝ)^1075 := by
      have hnat : (25026255019193299877 : ℕ)^256*10000000000000000^1075 ≤ 10002499943329863^1075*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25026255019193299877 25000000000000000000 10002499943329863 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002499943329863/10000000000000000 : ℝ)) (X := (25026255019193299877/25000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50103704716782848407/50000000000000000000 : ℝ) ≤ (10004937239444261/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (50103704716782848407/50000000000000000000 : ℝ)^256 ≤ (10004937239444261/10000000000000000 : ℝ)^1075 := by
      have hnat : (50103704716782848407 : ℕ)^256*10000000000000000^1075 ≤ 10004937239444261^1075*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50103704716782848407 50000000000000000000 10004937239444261 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004937239444261/10000000000000000 : ℝ)) (X := (50103704716782848407/50000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1315359990351101/100000000000000000000 : ℝ) ≤ ((7865452908376370509/7867500000000000000 : ℝ)+2*(1218648057199/629400000000000 : ℝ)*(6881/100000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (7865452908376370509/7867500000000000000 : ℝ)+2*(1218648057199/629400000000000 : ℝ)*(6881/100000 : ℝ)=(2000012529443093/2000000000000000 : ℝ) by norm_num, show 1+2*(1315359990351101/100000000000000000000 : ℝ)=(50001315359990351101/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(103704716782848407/100000000000000000000 : ℝ)+(1315359990351101/100000000000000000000 : ℝ) ≤ ((7865452908376370509/7867500000000000000 : ℝ)+(1218648057199/629400000000000 : ℝ)*((19469/100000 : ℝ)+(6881/100000 : ℝ)))^(1075/256 : ℝ) := by
    rw [show (7865452908376370509/7867500000000000000 : ℝ)+(1218648057199/629400000000000 : ℝ)*((19469/100000 : ℝ)+(6881/100000 : ℝ))=(10002499943329863/10000000000000000 : ℝ) by norm_num, show 1+(103704716782848407/100000000000000000000 : ℝ)+(1315359990351101/100000000000000000000 : ℝ)=(25026255019193299877/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(103704716782848407/100000000000000000000 : ℝ) ≤ ((7865452908376370509/7867500000000000000 : ℝ)+2*(1218648057199/629400000000000 : ℝ)*(19469/100000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (7865452908376370509/7867500000000000000 : ℝ)+2*(1218648057199/629400000000000 : ℝ)*(19469/100000 : ℝ)=(10004937239444261/10000000000000000 : ℝ) by norm_num, show 1+2*(103704716782848407/100000000000000000000 : ℝ)=(50103704716782848407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7865452908376370509/7867500000000000000 : ℝ)*(X 1 0+X 2 0)+(1218648057199/629400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (6881/100000 : ℝ)) (hi := (19469/100000 : ℝ)) (c := (7865452908376370509/7867500000000000000 : ℝ)) (alpha := (1218648057199/629400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7865452908376370509/7867500000000000000 : ℝ)*(X 0 1+X 2 1)+(1218648057199/629400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (6881/100000 : ℝ)) (hi := (19469/100000 : ℝ)) (c := (7865452908376370509/7867500000000000000 : ℝ)) (alpha := (1218648057199/629400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7865452908376370509/7867500000000000000 : ℝ)*(X 0 2+X 1 2)+(1218648057199/629400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (6881/100000 : ℝ)) (hi := (19469/100000 : ℝ)) (c := (7865452908376370509/7867500000000000000 : ℝ)) (alpha := (1218648057199/629400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-81397511/400000000 : ℝ)*X 0 0+(5480021043/10000000000 : ℝ)*X 0 1+(5183774457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2683011867/5000000000 : ℝ)*X 1 0+(-2188018731/10000000000 : ℝ)*X 1 1+(2591887423/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((268301191/500000000 : ℝ)*X 2 0+(5183774747/10000000000 : ℝ)*X 2 1+(-2188018747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320622727/10000000000 : ℝ)*X 0 0+(1005216477/2500000000 : ℝ)*X 0 1+(2320570817/5000000000 : ℝ)*X 0 2+(4320622727/10000000000 : ℝ)*X 1 0+(1005216477/2500000000 : ℝ)*X 1 1+(2320570817/5000000000 : ℝ)*X 1 2+(4320622727/10000000000 : ℝ)*X 2 0+(1005216477/2500000000 : ℝ)*X 2 1+(2320570817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2035004031/10000000000 : ℝ)*X 0 0+(5185634983/10000000000 : ℝ)*X 0 1+(342383983/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289674449/10000000000 : ℝ)*X 1 0+(-1893649549/10000000000 : ℝ)*X 1 1+(5478143731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322418617/2500000000 : ℝ)*X 2 0+(684767967/1250000000 : ℝ)*X 2 1+(-473412379/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080190453/2500000000 : ℝ)*X 0 0+(4637246753/10000000000 : ℝ)*X 0 1+(4024795987/10000000000 : ℝ)*X 0 2+(1080190453/2500000000 : ℝ)*X 1 0+(4637246753/10000000000 : ℝ)*X 1 1+(4024795987/10000000000 : ℝ)*X 1 2+(1080190453/2500000000 : ℝ)*X 2 0+(4637246753/10000000000 : ℝ)*X 2 1+(4024795987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (281649957825637033532511291/32781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (762549903/50000000000000 : ℝ)*(base19) + (765093557/50000000000000 : ℝ)*(base23) + (26300381/100000000000000 : ℝ)*(lower2) + (205133651/100000000000000 : ℝ)*(upper3) + (163601189/100000000000000 : ℝ)*(upper5) + (623477189006733/25000000000000 : ℝ)*(major0) + (623477189006733/25000000000000 : ℝ)*(major1) + (623477189006733/25000000000000 : ℝ)*(major2) + (3375588844363759/100000000000000 : ℝ)*(sp0) + (843902440965801/25000000000000 : ℝ)*(sp1) + (675121951755179/20000000000000 : ℝ)*(sp2) + (1612195731438969/100000000000000 : ℝ)*(sp3) + (22444599251/100000000000000 : ℝ)*(sp4) + (318914329/3125000000000 : ℝ)*(sp7) + (201525742087187/12500000000000 : ℝ)*(f.failure) + (337561128896301/10000000000000 : ℝ)*(f.sum) + (11093427411707/5245000000000000000000000000 : ℝ)*base66 + (1017739267030216801/65562500000000000000000000000000 : ℝ)*base68 + (553117974722904301/65562500000000000000000000000000 : ℝ)*base70 + (34797296862779301/65562500000000000000000000000000 : ℝ)*base72 + (8706170892931/2622500000000000000000000000 : ℝ)*base74 + (1210074876451466801/65562500000000000000000000000000 : ℝ)*base76 + (586737508552529301/65562500000000000000000000000000 : ℝ)*base78 + (327074073877404301/65562500000000000000000000000000 : ℝ)*base80 + (3245066560913/5245000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2575117/625000000000000000000 : ℝ)*base90 + (2575117/625000000000000000000 : ℝ)*base92 + (2575117/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57588313430036513007064779/8195312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1436786147/100000000000000 : ℝ)*(base19) + (1636860733/100000000000000 : ℝ)*(base23) + (45032169/25000000000000 : ℝ)*(upper3) + (36969847/50000000000000 : ℝ)*(lower4) + (106141233/100000000000000 : ℝ)*(upper5) + (78929434832849/3125000000000 : ℝ)*(major0) + (78929434832849/3125000000000 : ℝ)*(major1) + (78929434832849/3125000000000 : ℝ)*(major2) + (7993218751/50000000000000 : ℝ)*(sp1) + (19312938193/100000000000000 : ℝ)*(sp2) + (341869887528959/10000000000000 : ℝ)*(sp4) + (170934072603297/5000000000000 : ℝ)*(sp5) + (3418677925490663/100000000000000 : ℝ)*(sp6) + (408196179944999/25000000000000 : ℝ)*(sp7) + (408196179944999/25000000000000 : ℝ)*(f.failure) + (341869887528959/10000000000000 : ℝ)*(f.sum) + (19582062092323/7867500000000000000000000000 : ℝ)*base65 + (15666053299064459/1024414062500000000000000000000 : ℝ)*base67 + (110585980243406297/8195312500000000000000000000000 : ℝ)*base69 + (104852664941125047/8195312500000000000000000000000 : ℝ)*base71 + (44968387872103/7867500000000000000000000000 : ℝ)*base73 + (154954539053656297/8195312500000000000000000000000 : ℝ)*base75 + (61020773481875047/8195312500000000000000000000000 : ℝ)*base77 + (360057355046265719/16390625000000000000000000000000 : ℝ)*base79 + (76630302946061/15735000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (10839609/1250000000000000000000 : ℝ)*base90 + (10839609/1250000000000000000000 : ℝ)*base92 + (10839609/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1341_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19469/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6881/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1969/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4027/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1341_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1341_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1969/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4027/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1341_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1341_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1341_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1969/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4027/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1341_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

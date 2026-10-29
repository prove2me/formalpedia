-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1397_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:38.98301+00:00
-- url     : https://prove2.me/submissions/33181d65-fcb1-48fe-8729-a7270153075b

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
theorem support_rectangle_w1397_s6_0 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-499347713/2500000000 : ℝ)*x 0 + (5409875899/10000000000 : ℝ)*x 1 + (5246140109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (499347713/2500000000 : ℝ)^4357 ≤ (3044274600299/25000000000000 : ℝ)^3333 := by
    have hnat : (499347713 : ℕ)^4357*25000000000000^3333 ≤ 3044274600299^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499347713 2500000000 3044274600299 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409875899/10000000000 : ℝ)^4357 ≤ (4479342230839/10000000000000 : ℝ)^3333 := by
    have hnat : (5409875899 : ℕ)^4357*10000000000000^3333 ≤ 4479342230839^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409875899 10000000000 4479342230839 10000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246140109/10000000000 : ℝ)^4357 ≤ (2689342454771/6250000000000 : ℝ)^3333 := by
    have hnat : (5246140109 : ℕ)^4357*6250000000000^3333 ≤ 2689342454771^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246140109 10000000000 2689342454771 6250000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-499347713/2500000000 : ℝ), (5409875899/10000000000 : ℝ), (5246140109/10000000000 : ℝ)] ![(3044274600299/25000000000000 : ℝ), (4479342230839/10000000000000 : ℝ), (2689342454771/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-499347713/2500000000 : ℝ)|^4357 ≤ (3044274600299/25000000000000 : ℝ)^3333
        have hw : |(-499347713/2500000000 : ℝ)|=(499347713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409875899/10000000000 : ℝ)|^4357 ≤ (4479342230839/10000000000000 : ℝ)^3333
        have hw : |(5409875899/10000000000 : ℝ)|=(5409875899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246140109/10000000000 : ℝ)|^4357 ≤ (2689342454771/6250000000000 : ℝ)^3333
        have hw : |(5246140109/10000000000 : ℝ)|=(5246140109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s6_1 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347981777/10000000000 : ℝ)*x 0 + (-2080774229/10000000000 : ℝ)*x 1 + (2623070067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347981777/10000000000 : ℝ)^4357 ≤ (11031168530037/25000000000000 : ℝ)^3333 := by
    have hnat : (5347981777 : ℕ)^4357*25000000000000^3333 ≤ 11031168530037^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347981777 10000000000 11031168530037 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080774229/10000000000 : ℝ)^4357 ≤ (12845846316557/100000000000000 : ℝ)^3333 := by
    have hnat : (2080774229 : ℕ)^4357*100000000000000^3333 ≤ 12845846316557^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080774229 10000000000 12845846316557 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623070067/5000000000 : ℝ)^4357 ≤ (43029479544387/100000000000000 : ℝ)^3333 := by
    have hnat : (2623070067 : ℕ)^4357*100000000000000^3333 ≤ 43029479544387^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623070067 5000000000 43029479544387 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347981777/10000000000 : ℝ), (-2080774229/10000000000 : ℝ), (2623070067/5000000000 : ℝ)] ![(11031168530037/25000000000000 : ℝ), (12845846316557/100000000000000 : ℝ), (43029479544387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347981777/10000000000 : ℝ)|^4357 ≤ (11031168530037/25000000000000 : ℝ)^3333
        have hw : |(5347981777/10000000000 : ℝ)|=(5347981777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080774229/10000000000 : ℝ)|^4357 ≤ (12845846316557/100000000000000 : ℝ)^3333
        have hw : |(-2080774229/10000000000 : ℝ)|=(2080774229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623070067/5000000000 : ℝ)|^4357 ≤ (43029479544387/100000000000000 : ℝ)^3333
        have hw : |(2623070067/5000000000 : ℝ)|=(2623070067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s6_2 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069596373/2000000000 : ℝ)*x 0 + (5246140047/10000000000 : ℝ)*x 1 + (-520193557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069596373/2000000000 : ℝ)^4357 ≤ (275779219183/625000000000 : ℝ)^3333 := by
    have hnat : (1069596373 : ℕ)^4357*625000000000^3333 ≤ 275779219183^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069596373 2000000000 275779219183 625000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246140047/10000000000 : ℝ)^4357 ≤ (2689342413223/6250000000000 : ℝ)^3333 := by
    have hnat : (5246140047 : ℕ)^4357*6250000000000^3333 ≤ 2689342413223^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246140047 10000000000 2689342413223 6250000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520193557/2500000000 : ℝ)^4357 ≤ (6422923154243/50000000000000 : ℝ)^3333 := by
    have hnat : (520193557 : ℕ)^4357*50000000000000^3333 ≤ 6422923154243^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520193557 2500000000 6422923154243 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069596373/2000000000 : ℝ), (5246140047/10000000000 : ℝ), (-520193557/2500000000 : ℝ)] ![(275779219183/625000000000 : ℝ), (2689342413223/6250000000000 : ℝ), (6422923154243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069596373/2000000000 : ℝ)|^4357 ≤ (275779219183/625000000000 : ℝ)^3333
        have hw : |(1069596373/2000000000 : ℝ)|=(1069596373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246140047/10000000000 : ℝ)|^4357 ≤ (2689342413223/6250000000000 : ℝ)^3333
        have hw : |(5246140047/10000000000 : ℝ)|=(5246140047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-520193557/2500000000 : ℝ)|^4357 ≤ (6422923154243/50000000000000 : ℝ)^3333
        have hw : |(-520193557/2500000000 : ℝ)|=(520193557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s6_3 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4312440061/10000000000 : ℝ)*x 0 + (2070323331/5000000000 : ℝ)*x 1 + (2245356693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312440061/10000000000 : ℝ)^4357 ≤ (1040755701521/3125000000000 : ℝ)^3333 := by
    have hnat : (4312440061 : ℕ)^4357*3125000000000^3333 ≤ 1040755701521^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312440061 10000000000 1040755701521 3125000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070323331/5000000000 : ℝ)^4357 ≤ (7895138595651/25000000000000 : ℝ)^3333 := by
    have hnat : (2070323331 : ℕ)^4357*25000000000000^3333 ≤ 7895138595651^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070323331 5000000000 7895138595651 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245356693/5000000000 : ℝ)^4357 ≤ (8778815790107/25000000000000 : ℝ)^3333 := by
    have hnat : (2245356693 : ℕ)^4357*25000000000000^3333 ≤ 8778815790107^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245356693 5000000000 8778815790107 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312440061/10000000000 : ℝ), (2070323331/5000000000 : ℝ), (2245356693/5000000000 : ℝ)] ![(1040755701521/3125000000000 : ℝ), (7895138595651/25000000000000 : ℝ), (8778815790107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312440061/10000000000 : ℝ)|^4357 ≤ (1040755701521/3125000000000 : ℝ)^3333
        have hw : |(4312440061/10000000000 : ℝ)|=(4312440061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2070323331/5000000000 : ℝ)|^4357 ≤ (7895138595651/25000000000000 : ℝ)^3333
        have hw : |(2070323331/5000000000 : ℝ)|=(2070323331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245356693/5000000000 : ℝ)|^4357 ≤ (8778815790107/25000000000000 : ℝ)^3333
        have hw : |(2245356693/5000000000 : ℝ)|=(2245356693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s6_4 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1997402419/10000000000 : ℝ)*x 0 + (5246729013/10000000000 : ℝ)*x 1 + (5409283993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1997402419/10000000000 : ℝ)^4357 ≤ (6088595292447/50000000000000 : ℝ)^3333 := by
    have hnat : (1997402419 : ℕ)^4357*50000000000000^3333 ≤ 6088595292447^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997402419 10000000000 6088595292447 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246729013/10000000000 : ℝ)^4357 ≤ (8607158730483/20000000000000 : ℝ)^3333 := by
    have hnat : (5246729013 : ℕ)^4357*20000000000000^3333 ≤ 8607158730483^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246729013 10000000000 8607158730483 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409283993/10000000000 : ℝ)^4357 ≤ (1791480630093/4000000000000 : ℝ)^3333 := by
    have hnat : (5409283993 : ℕ)^4357*4000000000000^3333 ≤ 1791480630093^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409283993 10000000000 1791480630093 4000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1997402419/10000000000 : ℝ), (5246729013/10000000000 : ℝ), (5409283993/10000000000 : ℝ)] ![(6088595292447/50000000000000 : ℝ), (8607158730483/20000000000000 : ℝ), (1791480630093/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1997402419/10000000000 : ℝ)|^4357 ≤ (6088595292447/50000000000000 : ℝ)^3333
        have hw : |(-1997402419/10000000000 : ℝ)|=(1997402419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246729013/10000000000 : ℝ)|^4357 ≤ (8607158730483/20000000000000 : ℝ)^3333
        have hw : |(5246729013/10000000000 : ℝ)|=(5246729013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409283993/10000000000 : ℝ)|^4357 ≤ (1791480630093/4000000000000 : ℝ)^3333
        have hw : |(5409283993/10000000000 : ℝ)|=(5409283993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s6_5 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305552107/10000000000 : ℝ)*x 0 + (-1917630367/10000000000 : ℝ)*x 1 + (2704642001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305552107/10000000000 : ℝ)^4357 ≤ (1746704157131/4000000000000 : ℝ)^3333 := by
    have hnat : (5305552107 : ℕ)^4357*4000000000000^3333 ≤ 1746704157131^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305552107 10000000000 1746704157131 4000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1917630367/10000000000 : ℝ)^4357 ≤ (5772690104781/50000000000000 : ℝ)^3333 := by
    have hnat : (1917630367 : ℕ)^4357*50000000000000^3333 ≤ 5772690104781^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917630367 10000000000 5772690104781 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704642001/5000000000 : ℝ)^4357 ≤ (5598376981217/12500000000000 : ℝ)^3333 := by
    have hnat : (2704642001 : ℕ)^4357*12500000000000^3333 ≤ 5598376981217^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704642001 5000000000 5598376981217 12500000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305552107/10000000000 : ℝ), (-1917630367/10000000000 : ℝ), (2704642001/5000000000 : ℝ)] ![(1746704157131/4000000000000 : ℝ), (5772690104781/50000000000000 : ℝ), (5598376981217/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305552107/10000000000 : ℝ)|^4357 ≤ (1746704157131/4000000000000 : ℝ)^3333
        have hw : |(5305552107/10000000000 : ℝ)|=(5305552107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1917630367/10000000000 : ℝ)|^4357 ≤ (5772690104781/50000000000000 : ℝ)^3333
        have hw : |(-1917630367/10000000000 : ℝ)|=(1917630367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704642001/5000000000 : ℝ)|^4357 ≤ (5598376981217/12500000000000 : ℝ)^3333
        have hw : |(2704642001/5000000000 : ℝ)|=(2704642001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s6_6 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305552117/10000000000 : ℝ)*x 0 + (5409283951/10000000000 : ℝ)*x 1 + (-1917630423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305552117/10000000000 : ℝ)^4357 ≤ (10916901008967/25000000000000 : ℝ)^3333 := by
    have hnat : (5305552117 : ℕ)^4357*25000000000000^3333 ≤ 10916901008967^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305552117 10000000000 10916901008967 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409283951/10000000000 : ℝ)^4357 ≤ (44787015297741/100000000000000 : ℝ)^3333 := by
    have hnat : (5409283951 : ℕ)^4357*100000000000000^3333 ≤ 44787015297741^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409283951 10000000000 44787015297741 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1917630423/10000000000 : ℝ)^4357 ≤ (11545380650303/100000000000000 : ℝ)^3333 := by
    have hnat : (1917630423 : ℕ)^4357*100000000000000^3333 ≤ 11545380650303^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917630423 10000000000 11545380650303 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305552117/10000000000 : ℝ), (5409283951/10000000000 : ℝ), (-1917630423/10000000000 : ℝ)] ![(10916901008967/25000000000000 : ℝ), (44787015297741/100000000000000 : ℝ), (11545380650303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305552117/10000000000 : ℝ)|^4357 ≤ (10916901008967/25000000000000 : ℝ)^3333
        have hw : |(5305552117/10000000000 : ℝ)|=(5305552117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409283951/10000000000 : ℝ)|^4357 ≤ (44787015297741/100000000000000 : ℝ)^3333
        have hw : |(5409283951/10000000000 : ℝ)|=(5409283951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1917630423/10000000000 : ℝ)|^4357 ≤ (11545380650303/100000000000000 : ℝ)^3333
        have hw : |(-1917630423/10000000000 : ℝ)|=(1917630423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s6_7 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2156232431/5000000000 : ℝ)*x 0 + (1122363559/2500000000 : ℝ)*x 1 + (2070956187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156232431/5000000000 : ℝ)^4357 ≤ (33304432827457/100000000000000 : ℝ)^3333 := by
    have hnat : (2156232431 : ℕ)^4357*100000000000000^3333 ≤ 33304432827457^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156232431 5000000000 33304432827457 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122363559/2500000000 : ℝ)^4357 ≤ (7020478554731/20000000000000 : ℝ)^3333 := by
    have hnat : (1122363559 : ℕ)^4357*20000000000000^3333 ≤ 7020478554731^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122363559 2500000000 7020478554731 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070956187/5000000000 : ℝ)^4357 ≤ (1974573398473/6250000000000 : ℝ)^3333 := by
    have hnat : (2070956187 : ℕ)^4357*6250000000000^3333 ≤ 1974573398473^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070956187 5000000000 1974573398473 6250000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2156232431/5000000000 : ℝ), (1122363559/2500000000 : ℝ), (2070956187/5000000000 : ℝ)] ![(33304432827457/100000000000000 : ℝ), (7020478554731/20000000000000 : ℝ), (1974573398473/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2156232431/5000000000 : ℝ)|^4357 ≤ (33304432827457/100000000000000 : ℝ)^3333
        have hw : |(2156232431/5000000000 : ℝ)|=(2156232431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122363559/2500000000 : ℝ)|^4357 ≤ (7020478554731/20000000000000 : ℝ)^3333
        have hw : |(1122363559/2500000000 : ℝ)|=(1122363559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2070956187/5000000000 : ℝ)|^4357 ≤ (1974573398473/6250000000000 : ℝ)^3333
        have hw : |(2070956187/5000000000 : ℝ)|=(2070956187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1397_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11273/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (737/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2949/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2817/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2949/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2817/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2949/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2817/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2949/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2817/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2949/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2817/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2949/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2817/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2817/25000 : ℝ) ^ (1089/256 : ℝ) ≤ (2315183124649167/25000000000000000000 : ℝ) := by
    have hpowers : (2817/25000 : ℝ)^1089 ≤ (2315183124649167/25000000000000000000 : ℝ)^256 := by
      have hnat : (2817 : ℕ)^1089*25000000000000000000^256 ≤ 2315183124649167^256*25000^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2817 25000 2315183124649167 25000000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2817/25000 : ℝ)) (X := (2315183124649167/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2949/20000 : ℝ) ^ (1089/256 : ℝ) ≤ (7268299741254403/25000000000000000000 : ℝ) := by
    have hpowers : (2949/20000 : ℝ)^1089 ≤ (7268299741254403/25000000000000000000 : ℝ)^256 := by
      have hnat : (2949 : ℕ)^1089*25000000000000000000^256 ≤ 7268299741254403^256*20000^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2949 20000 7268299741254403 25000000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2949/20000 : ℝ)) (X := (7268299741254403/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502315183124649167/12500000000000000000 : ℝ) ≤ (2000087073630869/2000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (12502315183124649167/12500000000000000000 : ℝ)^256 ≤ (2000087073630869/2000000000000000 : ℝ)^1089 := by
      have hnat : (12502315183124649167 : ℕ)^256*2000000000000000^1089 ≤ 2000087073630869^1089*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502315183124649167 12500000000000000000 2000087073630869 2000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000087073630869/2000000000000000 : ℝ)) (X := (12502315183124649167/12500000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500958348286590357/2500000000000000000 : ℝ) ≤ (2000180202901763/2000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (2500958348286590357/2500000000000000000 : ℝ)^256 ≤ (2000180202901763/2000000000000000 : ℝ)^1089 := by
      have hnat : (2500958348286590357 : ℕ)^256*2000000000000000^1089 ≤ 2000180202901763^1089*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500958348286590357 2500000000000000000 2000180202901763 2000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000180202901763/2000000000000000 : ℝ)) (X := (2500958348286590357/2500000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507268299741254403/12500000000000000000 : ℝ) ≤ (2000273332172657/2000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (12507268299741254403/12500000000000000000 : ℝ)^256 ≤ (2000273332172657/2000000000000000 : ℝ)^1089 := by
      have hnat : (12507268299741254403 : ℕ)^256*2000000000000000^1089 ≤ 2000273332172657^1089*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507268299741254403 12500000000000000000 2000273332172657 2000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000273332172657/2000000000000000 : ℝ)) (X := (12507268299741254403/12500000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2315183124649167/25000000000000000000 : ℝ) ≤ ((2317401331255221443/2318000000000000000 : ℝ)+2*(15521545149/11590000000000 : ℝ)*(2817/25000 : ℝ))^(1089/256 : ℝ) := by
    rw [show (2317401331255221443/2318000000000000000 : ℝ)+2*(15521545149/11590000000000 : ℝ)*(2817/25000 : ℝ)=(2000087073630869/2000000000000000 : ℝ) by norm_num, show 1+2*(2315183124649167/25000000000000000000 : ℝ)=(12502315183124649167/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7268299741254403/25000000000000000000 : ℝ)+(2315183124649167/25000000000000000000 : ℝ) ≤ ((2317401331255221443/2318000000000000000 : ℝ)+(15521545149/11590000000000 : ℝ)*((2949/20000 : ℝ)+(2817/25000 : ℝ)))^(1089/256 : ℝ) := by
    rw [show (2317401331255221443/2318000000000000000 : ℝ)+(15521545149/11590000000000 : ℝ)*((2949/20000 : ℝ)+(2817/25000 : ℝ))=(2000180202901763/2000000000000000 : ℝ) by norm_num, show 1+(7268299741254403/25000000000000000000 : ℝ)+(2315183124649167/25000000000000000000 : ℝ)=(2500958348286590357/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7268299741254403/25000000000000000000 : ℝ) ≤ ((2317401331255221443/2318000000000000000 : ℝ)+2*(15521545149/11590000000000 : ℝ)*(2949/20000 : ℝ))^(1089/256 : ℝ) := by
    rw [show (2317401331255221443/2318000000000000000 : ℝ)+2*(15521545149/11590000000000 : ℝ)*(2949/20000 : ℝ)=(2000273332172657/2000000000000000 : ℝ) by norm_num, show 1+2*(7268299741254403/25000000000000000000 : ℝ)=(12507268299741254403/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2317401331255221443/2318000000000000000 : ℝ)*(X 1 0+X 2 0)+(15521545149/11590000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (2817/25000 : ℝ)) (hi := (2949/20000 : ℝ)) (c := (2317401331255221443/2318000000000000000 : ℝ)) (alpha := (15521545149/11590000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2317401331255221443/2318000000000000000 : ℝ)*(X 0 1+X 2 1)+(15521545149/11590000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (2817/25000 : ℝ)) (hi := (2949/20000 : ℝ)) (c := (2317401331255221443/2318000000000000000 : ℝ)) (alpha := (15521545149/11590000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2317401331255221443/2318000000000000000 : ℝ)*(X 0 2+X 1 2)+(15521545149/11590000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (2817/25000 : ℝ)) (hi := (2949/20000 : ℝ)) (c := (2317401331255221443/2318000000000000000 : ℝ)) (alpha := (15521545149/11590000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-499347713/2500000000 : ℝ)*X 0 0+(5409875899/10000000000 : ℝ)*X 0 1+(5246140109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347981777/10000000000 : ℝ)*X 1 0+(-2080774229/10000000000 : ℝ)*X 1 1+(2623070067/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069596373/2000000000 : ℝ)*X 2 0+(5246140047/10000000000 : ℝ)*X 2 1+(-520193557/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4312440061/10000000000 : ℝ)*X 0 0+(2070323331/5000000000 : ℝ)*X 0 1+(2245356693/5000000000 : ℝ)*X 0 2+(4312440061/10000000000 : ℝ)*X 1 0+(2070323331/5000000000 : ℝ)*X 1 1+(2245356693/5000000000 : ℝ)*X 1 2+(4312440061/10000000000 : ℝ)*X 2 0+(2070323331/5000000000 : ℝ)*X 2 1+(2245356693/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1997402419/10000000000 : ℝ)*X 0 0+(5246729013/10000000000 : ℝ)*X 0 1+(5409283993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305552107/10000000000 : ℝ)*X 1 0+(-1917630367/10000000000 : ℝ)*X 1 1+(2704642001/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305552117/10000000000 : ℝ)*X 2 0+(5409283951/10000000000 : ℝ)*X 2 1+(-1917630423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2156232431/5000000000 : ℝ)*X 0 0+(1122363559/2500000000 : ℝ)*X 0 1+(2070956187/5000000000 : ℝ)*X 0 2+(2156232431/5000000000 : ℝ)*X 1 0+(1122363559/2500000000 : ℝ)*X 1 1+(2070956187/5000000000 : ℝ)*X 1 2+(2156232431/5000000000 : ℝ)*X 2 0+(1122363559/2500000000 : ℝ)*X 2 1+(2070956187/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (877691201997771356757/289750000000000000000000000 : ℝ) := by norm_num
    linear_combination (454880499/100000000000000 : ℝ)*(base19) + (469818773/100000000000000 : ℝ)*(base23) + (11439081/25000000000000 : ℝ)*(lower2) + (14771653/20000000000000 : ℝ)*(upper3) + (30273471/100000000000000 : ℝ)*(upper5) + (4482013843976769/100000000000000 : ℝ)*(major0) + (4482013843976769/100000000000000 : ℝ)*(major1) + (4482013843976769/100000000000000 : ℝ)*(major2) + (610740966508957/10000000000000 : ℝ)*(sp0) + (1526854718427363/25000000000000 : ℝ)*(sp1) + (6107418858771177/100000000000000 : ℝ)*(sp2) + (2856602570668147/100000000000000 : ℝ)*(sp3) + (9663500381/100000000000000 : ℝ)*(sp4) + (5687724343/100000000000000 : ℝ)*(sp7) + (285660825839249/10000000000000 : ℝ)*(f.failure) + (122148386571799/2000000000000 : ℝ)*(f.sum) + (1216417873469/289750000000000000000000000 : ℝ)*base65 + (1499486728152142333/231800000000000000000000000000000 : ℝ)*base68 + (542391677327742333/231800000000000000000000000000000 : ℝ)*base70 + (275920968857742333/231800000000000000000000000000000 : ℝ)*base72 + (2138375600569/289750000000000000000000000 : ℝ)*base73 + (374358290733257667/231800000000000000000000000000000 : ℝ)*base75 + (398142095890457667/231800000000000000000000000000000 : ℝ)*base77 + (1671421850283057667/231800000000000000000000000000000 : ℝ)*base79 + (66598253639/23180000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2250671/500000000000000000000 : ℝ)*base90 + (2250671/500000000000000000000 : ℝ)*base92 + (2250671/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (194511405432701265682684197/28975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (197271689/25000000000000 : ℝ)*(base19) + (972280651/100000000000000 : ℝ)*(base23) + (4820671/6250000000000 : ℝ)*(upper3) + (18167187/20000000000000 : ℝ)*(lower4) + (125902821/100000000000000 : ℝ)*(upper5) + (1128639327030493/25000000000000 : ℝ)*(major0) + (1128639327030493/25000000000000 : ℝ)*(major1) + (1128639327030493/25000000000000 : ℝ)*(major2) + (8907879117/50000000000000 : ℝ)*(sp1) + (1786445963/10000000000000 : ℝ)*(sp2) + (1537941145229149/25000000000000 : ℝ)*(sp4) + (3075872988035803/50000000000000 : ℝ)*(sp5) + (1537936436044079/25000000000000 : ℝ)*(sp6) + (287734981155811/10000000000000 : ℝ)*(sp7) + (287734981155811/10000000000000 : ℝ)*(f.failure) + (1537941145229149/25000000000000 : ℝ)*(f.sum) + (181031850087/72437500000000000000000000 : ℝ)*base65 + (424836112358738601/57950000000000000000000000000000 : ℝ)*base68 + (30738286075738601/57950000000000000000000000000000 : ℝ)*base70 + (57426524503861399/57950000000000000000000000000000 : ℝ)*base71 + (1451129544223/289750000000000000000000000 : ℝ)*base74 + (387696536858738601/57950000000000000000000000000000 : ℝ)*base76 + (717584910929038601/57950000000000000000000000000000 : ℝ)*base78 + (128904685086161399/57950000000000000000000000000000 : ℝ)*base79 + (112881338699/36218750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1640931/500000000000000000000 : ℝ)*base89 + (1640931/500000000000000000000 : ℝ)*base91 + (1640931/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1397_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (737/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1397_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1397_s7_0 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336993071/2500000000 : ℝ)*x 0 + (-2080739727/10000000000 : ℝ)*x 1 + (1311543913/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336993071/2500000000 : ℝ)^4357 ≤ (22062285866293/50000000000000 : ℝ)^3333 := by
    have hnat : (1336993071 : ℕ)^4357*50000000000000^3333 ≤ 22062285866293^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336993071 2500000000 22062285866293 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080739727/10000000000 : ℝ)^4357 ≤ (2569113575113/20000000000000 : ℝ)^3333 := by
    have hnat : (2080739727 : ℕ)^4357*20000000000000^3333 ≤ 2569113575113^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080739727 10000000000 2569113575113 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311543913/2500000000 : ℝ)^4357 ≤ (43029860371103/100000000000000 : ℝ)^3333 := by
    have hnat : (1311543913 : ℕ)^4357*100000000000000^3333 ≤ 43029860371103^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311543913 2500000000 43029860371103 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336993071/2500000000 : ℝ), (-2080739727/10000000000 : ℝ), (1311543913/2500000000 : ℝ)] ![(22062285866293/50000000000000 : ℝ), (2569113575113/20000000000000 : ℝ), (43029860371103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336993071/2500000000 : ℝ)|^4357 ≤ (22062285866293/50000000000000 : ℝ)^3333
        have hw : |(1336993071/2500000000 : ℝ)|=(1336993071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080739727/10000000000 : ℝ)|^4357 ≤ (2569113575113/20000000000000 : ℝ)^3333
        have hw : |(-2080739727/10000000000 : ℝ)|=(2080739727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311543913/2500000000 : ℝ)|^4357 ≤ (43029860371103/100000000000000 : ℝ)^3333
        have hw : |(1311543913/2500000000 : ℝ)|=(1311543913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s7_1 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1997406067/10000000000 : ℝ)*x 0 + (5246764057/10000000000 : ℝ)*x 1 + (540924659/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1997406067/10000000000 : ℝ)^4357 ≤ (12177219657819/100000000000000 : ℝ)^3333 := by
    have hnat : (1997406067 : ℕ)^4357*100000000000000^3333 ≤ 12177219657819^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997406067 10000000000 12177219657819 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246764057/10000000000 : ℝ)^4357 ≤ (21518084704909/50000000000000 : ℝ)^3333 := by
    have hnat : (5246764057 : ℕ)^4357*50000000000000^3333 ≤ 21518084704909^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246764057 10000000000 21518084704909 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540924659/1000000000 : ℝ)^4357 ≤ (8957322184861/20000000000000 : ℝ)^3333 := by
    have hnat : (540924659 : ℕ)^4357*20000000000000^3333 ≤ 8957322184861^3333*1000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540924659 1000000000 8957322184861 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1997406067/10000000000 : ℝ), (5246764057/10000000000 : ℝ), (540924659/1000000000 : ℝ)] ![(12177219657819/100000000000000 : ℝ), (21518084704909/50000000000000 : ℝ), (8957322184861/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1997406067/10000000000 : ℝ)|^4357 ≤ (12177219657819/100000000000000 : ℝ)^3333
        have hw : |(-1997406067/10000000000 : ℝ)|=(1997406067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246764057/10000000000 : ℝ)|^4357 ≤ (21518084704909/50000000000000 : ℝ)^3333
        have hw : |(5246764057/10000000000 : ℝ)|=(5246764057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540924659/1000000000 : ℝ)|^4357 ≤ (8957322184861/20000000000000 : ℝ)^3333
        have hw : |(540924659/1000000000 : ℝ)|=(540924659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s7_2 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326390373/2500000000 : ℝ)*x 0 + (-958834361/5000000000 : ℝ)*x 1 + (5409246783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326390373/2500000000 : ℝ)^4357 ≤ (43667704903637/100000000000000 : ℝ)^3333 := by
    have hnat : (1326390373 : ℕ)^4357*100000000000000^3333 ≤ 43667704903637^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326390373 2500000000 43667704903637 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (958834361/5000000000 : ℝ)^4357 ≤ (2309136415767/20000000000000 : ℝ)^3333 := by
    have hnat : (958834361 : ℕ)^4357*20000000000000^3333 ≤ 2309136415767^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958834361 5000000000 2309136415767 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409246783/10000000000 : ℝ)^4357 ≤ (44786613013221/100000000000000 : ℝ)^3333 := by
    have hnat : (5409246783 : ℕ)^4357*100000000000000^3333 ≤ 44786613013221^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409246783 10000000000 44786613013221 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326390373/2500000000 : ℝ), (-958834361/5000000000 : ℝ), (5409246783/10000000000 : ℝ)] ![(43667704903637/100000000000000 : ℝ), (2309136415767/20000000000000 : ℝ), (44786613013221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326390373/2500000000 : ℝ)|^4357 ≤ (43667704903637/100000000000000 : ℝ)^3333
        have hw : |(1326390373/2500000000 : ℝ)|=(1326390373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-958834361/5000000000 : ℝ)|^4357 ≤ (2309136415767/20000000000000 : ℝ)^3333
        have hw : |(-958834361/5000000000 : ℝ)|=(958834361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409246783/10000000000 : ℝ)|^4357 ≤ (44786613013221/100000000000000 : ℝ)^3333
        have hw : |(5409246783/10000000000 : ℝ)|=(5409246783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s7_3 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305561409/10000000000 : ℝ)*x 0 + (84519481/156250000 : ℝ)*x 1 + (-59927151/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305561409/10000000000 : ℝ)^4357 ≤ (43667704010621/100000000000000 : ℝ)^3333 := by
    have hnat : (5305561409 : ℕ)^4357*100000000000000^3333 ≤ 43667704010621^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305561409 10000000000 43667704010621 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84519481/156250000 : ℝ)^4357 ≤ (11196653256011/25000000000000 : ℝ)^3333 := by
    have hnat : (84519481 : ℕ)^4357*25000000000000^3333 ≤ 11196653256011^3333*156250000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84519481 156250000 11196653256011 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59927151/312500000 : ℝ)^4357 ≤ (5772841472291/50000000000000 : ℝ)^3333 := by
    have hnat : (59927151 : ℕ)^4357*50000000000000^3333 ≤ 5772841472291^3333*312500000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59927151 312500000 5772841472291 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305561409/10000000000 : ℝ), (84519481/156250000 : ℝ), (-59927151/312500000 : ℝ)] ![(43667704010621/100000000000000 : ℝ), (11196653256011/25000000000000 : ℝ), (5772841472291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305561409/10000000000 : ℝ)|^4357 ≤ (43667704010621/100000000000000 : ℝ)^3333
        have hw : |(5305561409/10000000000 : ℝ)|=(5305561409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84519481/156250000 : ℝ)|^4357 ≤ (11196653256011/25000000000000 : ℝ)^3333
        have hw : |(84519481/156250000 : ℝ)|=(84519481/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-59927151/312500000 : ℝ)|^4357 ≤ (5772841472291/50000000000000 : ℝ)^3333
        have hw : |(-59927151/312500000 : ℝ)|=(59927151/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s7_4 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (862493493/2000000000 : ℝ)*x 0 + (4489376479/10000000000 : ℝ)*x 1 + (828397889/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862493493/2000000000 : ℝ)^4357 ≤ (333044591061/1000000000000 : ℝ)^3333 := by
    have hnat : (862493493 : ℕ)^4357*1000000000000^3333 ≤ 333044591061^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862493493 2000000000 333044591061 1000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489376479/10000000000 : ℝ)^4357 ≤ (8775399504439/25000000000000 : ℝ)^3333 := by
    have hnat : (4489376479 : ℕ)^4357*25000000000000^3333 ≤ 8775399504439^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489376479 10000000000 8775399504439 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828397889/2000000000 : ℝ)^4357 ≤ (7898485715781/25000000000000 : ℝ)^3333 := by
    have hnat : (828397889 : ℕ)^4357*25000000000000^3333 ≤ 7898485715781^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828397889 2000000000 7898485715781 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862493493/2000000000 : ℝ), (4489376479/10000000000 : ℝ), (828397889/2000000000 : ℝ)] ![(333044591061/1000000000000 : ℝ), (8775399504439/25000000000000 : ℝ), (7898485715781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862493493/2000000000 : ℝ)|^4357 ≤ (333044591061/1000000000000 : ℝ)^3333
        have hw : |(862493493/2000000000 : ℝ)|=(862493493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489376479/10000000000 : ℝ)|^4357 ≤ (8775399504439/25000000000000 : ℝ)^3333
        have hw : |(4489376479/10000000000 : ℝ)|=(4489376479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(828397889/2000000000 : ℝ)|^4357 ≤ (7898485715781/25000000000000 : ℝ)^3333
        have hw : |(828397889/2000000000 : ℝ)|=(828397889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1397_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (737/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11273/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14739/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (737/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (737/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (737/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (737/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (737/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (737/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11273/100000 : ℝ) ^ (1089/256 : ℝ) ≤ (463911286304087/5000000000000000000 : ℝ) := by
    have hpowers : (11273/100000 : ℝ)^1089 ≤ (463911286304087/5000000000000000000 : ℝ)^256 := by
      have hnat : (11273 : ℕ)^1089*5000000000000000000^256 ≤ 463911286304087^256*100000^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11273 100000 463911286304087 5000000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11273/100000 : ℝ)) (X := (463911286304087/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hpowhi : (737/5000 : ℝ) ^ (1089/256 : ℝ) ≤ (1451564213268157/5000000000000000000 : ℝ) := by
    have hpowers : (737/5000 : ℝ)^1089 ≤ (1451564213268157/5000000000000000000 : ℝ)^256 := by
      have hnat : (737 : ℕ)^1089*5000000000000000000^256 ≤ 1451564213268157^256*5000^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        737 5000 1451564213268157 5000000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (737/5000 : ℝ)) (X := (1451564213268157/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500463911286304087/2500000000000000000 : ℝ) ≤ (2000087238098501/2000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (2500463911286304087/2500000000000000000 : ℝ)^256 ≤ (2000087238098501/2000000000000000 : ℝ)^1089 := by
      have hnat : (2500463911286304087 : ℕ)^256*2000000000000000^1089 ≤ 2000087238098501^1089*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500463911286304087 2500000000000000000 2000087238098501 2000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000087238098501/2000000000000000 : ℝ)) (X := (2500463911286304087/2500000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250478868874893061/1250000000000000000 : ℝ) ≤ (10000900440581829/10000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (1250478868874893061/1250000000000000000 : ℝ)^256 ≤ (10000900440581829/10000000000000000 : ℝ)^1089 := by
      have hnat : (1250478868874893061 : ℕ)^256*10000000000000000^1089 ≤ 10000900440581829^1089*1250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250478868874893061 1250000000000000000 10000900440581829 10000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000900440581829/10000000000000000 : ℝ)) (X := (1250478868874893061/1250000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501451564213268157/2500000000000000000 : ℝ) ≤ (10001364690671153/10000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (2501451564213268157/2500000000000000000 : ℝ)^256 ≤ (10001364690671153/10000000000000000 : ℝ)^1089 := by
      have hnat : (2501451564213268157 : ℕ)^256*10000000000000000^1089 ≤ 10001364690671153^1089*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501451564213268157 2500000000000000000 10001364690671153 10000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001364690671153/10000000000000000 : ℝ)) (X := (2501451564213268157/2500000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(463911286304087/5000000000000000000 : ℝ) ≤ ((34661045289923615931/34670000000000000000 : ℝ)+2*(116062522331/86675000000000 : ℝ)*(11273/100000 : ℝ))^(1089/256 : ℝ) := by
    rw [show (34661045289923615931/34670000000000000000 : ℝ)+2*(116062522331/86675000000000 : ℝ)*(11273/100000 : ℝ)=(2000087238098501/2000000000000000 : ℝ) by norm_num, show 1+2*(463911286304087/5000000000000000000 : ℝ)=(2500463911286304087/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1451564213268157/5000000000000000000 : ℝ)+(463911286304087/5000000000000000000 : ℝ) ≤ ((34661045289923615931/34670000000000000000 : ℝ)+(116062522331/86675000000000 : ℝ)*((737/5000 : ℝ)+(11273/100000 : ℝ)))^(1089/256 : ℝ) := by
    rw [show (34661045289923615931/34670000000000000000 : ℝ)+(116062522331/86675000000000 : ℝ)*((737/5000 : ℝ)+(11273/100000 : ℝ))=(10000900440581829/10000000000000000 : ℝ) by norm_num, show 1+(1451564213268157/5000000000000000000 : ℝ)+(463911286304087/5000000000000000000 : ℝ)=(1250478868874893061/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1451564213268157/5000000000000000000 : ℝ) ≤ ((34661045289923615931/34670000000000000000 : ℝ)+2*(116062522331/86675000000000 : ℝ)*(737/5000 : ℝ))^(1089/256 : ℝ) := by
    rw [show (34661045289923615931/34670000000000000000 : ℝ)+2*(116062522331/86675000000000 : ℝ)*(737/5000 : ℝ)=(10001364690671153/10000000000000000 : ℝ) by norm_num, show 1+2*(1451564213268157/5000000000000000000 : ℝ)=(2501451564213268157/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34661045289923615931/34670000000000000000 : ℝ)*(X 1 0+X 2 0)+(116062522331/86675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (11273/100000 : ℝ)) (hi := (737/5000 : ℝ)) (c := (34661045289923615931/34670000000000000000 : ℝ)) (alpha := (116062522331/86675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34661045289923615931/34670000000000000000 : ℝ)*(X 0 1+X 2 1)+(116062522331/86675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (11273/100000 : ℝ)) (hi := (737/5000 : ℝ)) (c := (34661045289923615931/34670000000000000000 : ℝ)) (alpha := (116062522331/86675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34661045289923615931/34670000000000000000 : ℝ)*(X 0 2+X 1 2)+(116062522331/86675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (11273/100000 : ℝ)) (hi := (737/5000 : ℝ)) (c := (34661045289923615931/34670000000000000000 : ℝ)) (alpha := (116062522331/86675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1336993071/2500000000 : ℝ)*X 1 0+(-2080739727/10000000000 : ℝ)*X 1 1+(1311543913/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s7_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1997406067/10000000000 : ℝ)*X 0 0+(5246764057/10000000000 : ℝ)*X 0 1+(540924659/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1326390373/2500000000 : ℝ)*X 1 0+(-958834361/5000000000 : ℝ)*X 1 1+(5409246783/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5305561409/10000000000 : ℝ)*X 2 0+(84519481/156250000 : ℝ)*X 2 1+(-59927151/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((862493493/2000000000 : ℝ)*X 0 0+(4489376479/10000000000 : ℝ)*X 0 1+(828397889/2000000000 : ℝ)*X 0 2+(862493493/2000000000 : ℝ)*X 1 0+(4489376479/10000000000 : ℝ)*X 1 1+(828397889/2000000000 : ℝ)*X 1 2+(862493493/2000000000 : ℝ)*X 2 0+(4489376479/10000000000 : ℝ)*X 2 1+(828397889/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2112368315215011066978424143/433375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42811377/10000000000000 : ℝ)*(base19) + (219391173/50000000000000 : ℝ)*(base23) + (200758663/100000000000000 : ℝ)*(lower1) + (8390089/12500000000000 : ℝ)*(upper3) + (8635031/12500000000000 : ℝ)*(lower4) + (6170603/6250000000000 : ℝ)*(upper5) + (2258280152688049/50000000000000 : ℝ)*(major0) + (2258280152688049/50000000000000 : ℝ)*(major1) + (2258280152688049/50000000000000 : ℝ)*(major2) + (116363517/4000000000000 : ℝ)*(sp0) + (1230898805575813/20000000000000 : ℝ)*(sp1) + (615449069067737/10000000000000 : ℝ)*(sp2) + (6154493589096719/100000000000000 : ℝ)*(sp3) + (17991415127493/625000000000 : ℝ)*(sp4) + (17991415127493/625000000000 : ℝ)*(f.failure) + (1230898805575813/20000000000000 : ℝ)*(f.sum) + (19577367344677/17335000000000000000000000000 : ℝ)*base65 + (4168261490620191381/1733500000000000000000000000000000 : ℝ)*base68 + (11458981461092308619/1733500000000000000000000000000000 : ℝ)*base69 + (7892502847427308619/1733500000000000000000000000000000 : ℝ)*base71 + (25408241485423/17335000000000000000000000000 : ℝ)*base74 + (811886069682308619/1733500000000000000000000000000000 : ℝ)*base75 + (2331416938638808619/1733500000000000000000000000000000 : ℝ)*base77 + (12246362702481308619/1733500000000000000000000000000000 : ℝ)*base79 + (2791904377179/2166875000000000000000000000 : ℝ)*base81 + (153053/31250000000000000000 : ℝ)*base89 + (153053/31250000000000000000 : ℝ)*base91 + (153053/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1397_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (737/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14739/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1397_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1397_box_0 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-917191243/5000000000 : ℝ)*x 0 + (1346905403/2500000000 : ℝ)*x 1 + (5387621619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (917191243/5000000000 : ℝ)^4357 ≤ (5447300923999/50000000000000 : ℝ)^3333 := by
    have hnat : (917191243 : ℕ)^4357*50000000000000^3333 ≤ 5447300923999^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917191243 5000000000 5447300923999 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346905403/2500000000 : ℝ)^4357 ≤ (2784543689487/6250000000000 : ℝ)^3333 := by
    have hnat : (1346905403 : ℕ)^4357*6250000000000^3333 ≤ 2784543689487^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346905403 2500000000 2784543689487 6250000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387621619/10000000000 : ℝ)^4357 ≤ (44552699107463/100000000000000 : ℝ)^3333 := by
    have hnat : (5387621619 : ℕ)^4357*100000000000000^3333 ≤ 44552699107463^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387621619 10000000000 44552699107463 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-917191243/5000000000 : ℝ), (1346905403/2500000000 : ℝ), (5387621619/10000000000 : ℝ)] ![(5447300923999/50000000000000 : ℝ), (2784543689487/6250000000000 : ℝ), (44552699107463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-917191243/5000000000 : ℝ)|^4357 ≤ (5447300923999/50000000000000 : ℝ)^3333
        have hw : |(-917191243/5000000000 : ℝ)|=(917191243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346905403/2500000000 : ℝ)|^4357 ≤ (2784543689487/6250000000000 : ℝ)^3333
        have hw : |(1346905403/2500000000 : ℝ)|=(1346905403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387621619/10000000000 : ℝ)|^4357 ≤ (44552699107463/100000000000000 : ℝ)^3333
        have hw : |(5387621619/10000000000 : ℝ)|=(5387621619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_box_1 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642899581/5000000000 : ℝ)*x 0 + (-987067981/5000000000 : ℝ)*x 1 + (5387621767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642899581/5000000000 : ℝ)^4357 ≤ (2172759959223/5000000000000 : ℝ)^3333 := by
    have hnat : (2642899581 : ℕ)^4357*5000000000000^3333 ≤ 2172759959223^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642899581 5000000000 2172759959223 5000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (987067981/5000000000 : ℝ)^4357 ≤ (479684003549/4000000000000 : ℝ)^3333 := by
    have hnat : (987067981 : ℕ)^4357*4000000000000^3333 ≤ 479684003549^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987067981 5000000000 479684003549 4000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387621767/10000000000 : ℝ)^4357 ≤ (8910540141471/20000000000000 : ℝ)^3333 := by
    have hnat : (5387621767 : ℕ)^4357*20000000000000^3333 ≤ 8910540141471^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387621767 10000000000 8910540141471 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642899581/5000000000 : ℝ), (-987067981/5000000000 : ℝ), (5387621767/10000000000 : ℝ)] ![(2172759959223/5000000000000 : ℝ), (479684003549/4000000000000 : ℝ), (8910540141471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642899581/5000000000 : ℝ)|^4357 ≤ (2172759959223/5000000000000 : ℝ)^3333
        have hw : |(2642899581/5000000000 : ℝ)|=(2642899581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-987067981/5000000000 : ℝ)|^4357 ≤ (479684003549/4000000000000 : ℝ)^3333
        have hw : |(-987067981/5000000000 : ℝ)|=(987067981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387621767/10000000000 : ℝ)|^4357 ≤ (8910540141471/20000000000000 : ℝ)^3333
        have hw : |(5387621767/10000000000 : ℝ)|=(5387621767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_box_2 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642899319/5000000000 : ℝ)*x 0 + (1346905567/2500000000 : ℝ)*x 1 + (-197413599/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642899319/5000000000 : ℝ)^4357 ≤ (43455193553083/100000000000000 : ℝ)^3333 := by
    have hnat : (2642899319 : ℕ)^4357*100000000000000^3333 ≤ 43455193553083^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642899319 5000000000 43455193553083 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346905567/2500000000 : ℝ)^4357 ≤ (44552706123209/100000000000000 : ℝ)^3333 := by
    have hnat : (1346905567 : ℕ)^4357*100000000000000^3333 ≤ 44552706123209^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346905567 2500000000 44552706123209 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197413599/1000000000 : ℝ)^4357 ≤ (11992100311071/100000000000000 : ℝ)^3333 := by
    have hnat : (197413599 : ℕ)^4357*100000000000000^3333 ≤ 11992100311071^3333*1000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197413599 1000000000 11992100311071 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642899319/5000000000 : ℝ), (1346905567/2500000000 : ℝ), (-197413599/1000000000 : ℝ)] ![(43455193553083/100000000000000 : ℝ), (44552706123209/100000000000000 : ℝ), (11992100311071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642899319/5000000000 : ℝ)|^4357 ≤ (43455193553083/100000000000000 : ℝ)^3333
        have hw : |(2642899319/5000000000 : ℝ)|=(2642899319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346905567/2500000000 : ℝ)|^4357 ≤ (44552706123209/100000000000000 : ℝ)^3333
        have hw : |(1346905567/2500000000 : ℝ)|=(1346905567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-197413599/1000000000 : ℝ)|^4357 ≤ (11992100311071/100000000000000 : ℝ)^3333
        have hw : |(-197413599/1000000000 : ℝ)|=(197413599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_box_3 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (278712597/625000000 : ℝ)*x 0 + (4242734897/10000000000 : ℝ)*x 1 + (4242735443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (278712597/625000000 : ℝ)^4357 ≤ (869888480253/2500000000000 : ℝ)^3333 := by
    have hnat : (278712597 : ℕ)^4357*2500000000000^3333 ≤ 869888480253^3333*625000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278712597 625000000 869888480253 2500000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242734897/10000000000 : ℝ)^4357 ≤ (16301113824263/50000000000000 : ℝ)^3333 := by
    have hnat : (4242734897 : ℕ)^4357*50000000000000^3333 ≤ 16301113824263^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242734897 10000000000 16301113824263 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242735443/10000000000 : ℝ)^4357 ≤ (32602233133143/100000000000000 : ℝ)^3333 := by
    have hnat : (4242735443 : ℕ)^4357*100000000000000^3333 ≤ 32602233133143^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242735443 10000000000 32602233133143 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(278712597/625000000 : ℝ), (4242734897/10000000000 : ℝ), (4242735443/10000000000 : ℝ)] ![(869888480253/2500000000000 : ℝ), (16301113824263/50000000000000 : ℝ), (32602233133143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(278712597/625000000 : ℝ)|^4357 ≤ (869888480253/2500000000000 : ℝ)^3333
        have hw : |(278712597/625000000 : ℝ)|=(278712597/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242734897/10000000000 : ℝ)|^4357 ≤ (16301113824263/50000000000000 : ℝ)^3333
        have hw : |(4242734897/10000000000 : ℝ)|=(4242734897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4242735443/10000000000 : ℝ)|^4357 ≤ (32602233133143/100000000000000 : ℝ)^3333
        have hw : |(4242735443/10000000000 : ℝ)|=(4242735443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_box_4 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2163152161/10000000000 : ℝ)*x 0 + (5266011519/10000000000 : ℝ)*x 1 + (105320231/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163152161/10000000000 : ℝ)^4357 ≤ (3378667063019/25000000000000 : ℝ)^3333 := by
    have hnat : (2163152161 : ℕ)^4357*25000000000000^3333 ≤ 3378667063019^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163152161 10000000000 3378667063019 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266011519/10000000000 : ℝ)^4357 ≤ (21621332849763/50000000000000 : ℝ)^3333 := by
    have hnat : (5266011519 : ℕ)^4357*50000000000000^3333 ≤ 21621332849763^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266011519 10000000000 21621332849763 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105320231/200000000 : ℝ)^4357 ≤ (5405333254037/12500000000000 : ℝ)^3333 := by
    have hnat : (105320231 : ℕ)^4357*12500000000000^3333 ≤ 5405333254037^3333*200000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105320231 200000000 5405333254037 12500000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2163152161/10000000000 : ℝ), (5266011519/10000000000 : ℝ), (105320231/200000000 : ℝ)] ![(3378667063019/25000000000000 : ℝ), (21621332849763/50000000000000 : ℝ), (5405333254037/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2163152161/10000000000 : ℝ)|^4357 ≤ (3378667063019/25000000000000 : ℝ)^3333
        have hw : |(-2163152161/10000000000 : ℝ)|=(2163152161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266011519/10000000000 : ℝ)|^4357 ≤ (21621332849763/50000000000000 : ℝ)^3333
        have hw : |(5266011519/10000000000 : ℝ)|=(5266011519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105320231/200000000 : ℝ)|^4357 ≤ (5405333254037/12500000000000 : ℝ)^3333
        have hw : |(105320231/200000000 : ℝ)|=(105320231/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_box_5 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371019823/10000000000 : ℝ)*x 0 + (-2023303193/10000000000 : ℝ)*x 1 + (164562857/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371019823/10000000000 : ℝ)^4357 ≤ (22186658632847/50000000000000 : ℝ)^3333 := by
    have hnat : (5371019823 : ℕ)^4357*50000000000000^3333 ≤ 22186658632847^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371019823 10000000000 22186658632847 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2023303193/10000000000 : ℝ)^4357 ≤ (3096004510009/25000000000000 : ℝ)^3333 := by
    have hnat : (2023303193 : ℕ)^4357*25000000000000^3333 ≤ 3096004510009^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023303193 10000000000 3096004510009 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164562857/312500000 : ℝ)^4357 ≤ (21621332339873/50000000000000 : ℝ)^3333 := by
    have hnat : (164562857 : ℕ)^4357*50000000000000^3333 ≤ 21621332339873^3333*312500000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164562857 312500000 21621332339873 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371019823/10000000000 : ℝ), (-2023303193/10000000000 : ℝ), (164562857/312500000 : ℝ)] ![(22186658632847/50000000000000 : ℝ), (3096004510009/25000000000000 : ℝ), (21621332339873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371019823/10000000000 : ℝ)|^4357 ≤ (22186658632847/50000000000000 : ℝ)^3333
        have hw : |(5371019823/10000000000 : ℝ)|=(5371019823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2023303193/10000000000 : ℝ)|^4357 ≤ (3096004510009/25000000000000 : ℝ)^3333
        have hw : |(-2023303193/10000000000 : ℝ)|=(2023303193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164562857/312500000 : ℝ)|^4357 ≤ (21621332339873/50000000000000 : ℝ)^3333
        have hw : |(164562857/312500000 : ℝ)|=(164562857/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_box_6 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342754941/2500000000 : ℝ)*x 0 + (5266011543/10000000000 : ℝ)*x 1 + (-2023303113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342754941/2500000000 : ℝ)^4357 ≤ (44373316628503/100000000000000 : ℝ)^3333 := by
    have hnat : (1342754941 : ℕ)^4357*100000000000000^3333 ≤ 44373316628503^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342754941 2500000000 44373316628503 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266011543/10000000000 : ℝ)^4357 ≤ (21621332978577/50000000000000 : ℝ)^3333 := by
    have hnat : (5266011543 : ℕ)^4357*50000000000000^3333 ≤ 21621332978577^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266011543 10000000000 21621332978577 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2023303113/10000000000 : ℝ)^4357 ≤ (12384017399943/100000000000000 : ℝ)^3333 := by
    have hnat : (2023303113 : ℕ)^4357*100000000000000^3333 ≤ 12384017399943^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023303113 10000000000 12384017399943 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342754941/2500000000 : ℝ), (5266011543/10000000000 : ℝ), (-2023303113/10000000000 : ℝ)] ![(44373316628503/100000000000000 : ℝ), (21621332978577/50000000000000 : ℝ), (12384017399943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342754941/2500000000 : ℝ)|^4357 ≤ (44373316628503/100000000000000 : ℝ)^3333
        have hw : |(1342754941/2500000000 : ℝ)|=(1342754941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266011543/10000000000 : ℝ)|^4357 ≤ (21621332978577/50000000000000 : ℝ)^3333
        have hw : |(5266011543/10000000000 : ℝ)|=(5266011543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2023303113/10000000000 : ℝ)|^4357 ≤ (12384017399943/100000000000000 : ℝ)^3333
        have hw : |(-2023303113/10000000000 : ℝ)|=(2023303113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_box_7 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4164479147/10000000000 : ℝ)*x 0 + (2195072263/5000000000 : ℝ)*x 1 + (2195072273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4164479147/10000000000 : ℝ)^4357 ≤ (31818378812343/100000000000000 : ℝ)^3333 := by
    have hnat : (4164479147 : ℕ)^4357*100000000000000^3333 ≤ 31818378812343^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164479147 10000000000 31818378812343 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195072263/5000000000 : ℝ)^4357 ≤ (6818162096101/20000000000000 : ℝ)^3333 := by
    have hnat : (2195072263 : ℕ)^4357*20000000000000^3333 ≤ 6818162096101^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195072263 5000000000 6818162096101 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2195072273/5000000000 : ℝ)^4357 ≤ (17045405341763/50000000000000 : ℝ)^3333 := by
    have hnat : (2195072273 : ℕ)^4357*50000000000000^3333 ≤ 17045405341763^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195072273 5000000000 17045405341763 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4164479147/10000000000 : ℝ), (2195072263/5000000000 : ℝ), (2195072273/5000000000 : ℝ)] ![(31818378812343/100000000000000 : ℝ), (6818162096101/20000000000000 : ℝ), (17045405341763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4164479147/10000000000 : ℝ)|^4357 ≤ (31818378812343/100000000000000 : ℝ)^3333
        have hw : |(4164479147/10000000000 : ℝ)|=(4164479147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2195072263/5000000000 : ℝ)|^4357 ≤ (6818162096101/20000000000000 : ℝ)^3333
        have hw : |(2195072263/5000000000 : ℝ)|=(2195072263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2195072273/5000000000 : ℝ)|^4357 ≤ (17045405341763/50000000000000 : ℝ)^3333
        have hw : |(2195072273/5000000000 : ℝ)|=(2195072273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_box_8 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2093975701/10000000000 : ℝ)*x 0 + (5182038807/10000000000 : ℝ)*x 1 + (2700807793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093975701/10000000000 : ℝ)^4357 ≤ (12952489920101/100000000000000 : ℝ)^3333 := by
    have hnat : (2093975701 : ℕ)^4357*100000000000000^3333 ≤ 12952489920101^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093975701 10000000000 12952489920101 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182038807/10000000000 : ℝ)^4357 ≤ (10585868658647/25000000000000 : ℝ)^3333 := by
    have hnat : (5182038807 : ℕ)^4357*25000000000000^3333 ≤ 10585868658647^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182038807 10000000000 10585868658647 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700807793/5000000000 : ℝ)^4357 ≤ (44704035428411/100000000000000 : ℝ)^3333 := by
    have hnat : (2700807793 : ℕ)^4357*100000000000000^3333 ≤ 44704035428411^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700807793 5000000000 44704035428411 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2093975701/10000000000 : ℝ), (5182038807/10000000000 : ℝ), (2700807793/5000000000 : ℝ)] ![(12952489920101/100000000000000 : ℝ), (10585868658647/25000000000000 : ℝ), (44704035428411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2093975701/10000000000 : ℝ)|^4357 ≤ (12952489920101/100000000000000 : ℝ)^3333
        have hw : |(-2093975701/10000000000 : ℝ)|=(2093975701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182038807/10000000000 : ℝ)|^4357 ≤ (10585868658647/25000000000000 : ℝ)^3333
        have hw : |(5182038807/10000000000 : ℝ)|=(5182038807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700807793/5000000000 : ℝ)|^4357 ≤ (44704035428411/100000000000000 : ℝ)^3333
        have hw : |(2700807793/5000000000 : ℝ)|=(2700807793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_box_9 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1318997211/2500000000 : ℝ)*x 0 + (-984175209/5000000000 : ℝ)*x 1 + (1350403609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318997211/2500000000 : ℝ)^4357 ≤ (2167489935963/5000000000000 : ℝ)^3333 := by
    have hnat : (1318997211 : ℕ)^4357*5000000000000^3333 ≤ 2167489935963^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318997211 2500000000 2167489935963 5000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984175209/5000000000 : ℝ)^4357 ≤ (11946178285061/100000000000000 : ℝ)^3333 := by
    have hnat : (984175209 : ℕ)^4357*100000000000000^3333 ≤ 11946178285061^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984175209 5000000000 11946178285061 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350403609/2500000000 : ℝ)^4357 ≤ (447040229869/1000000000000 : ℝ)^3333 := by
    have hnat : (1350403609 : ℕ)^4357*1000000000000^3333 ≤ 447040229869^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350403609 2500000000 447040229869 1000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318997211/2500000000 : ℝ), (-984175209/5000000000 : ℝ), (1350403609/2500000000 : ℝ)] ![(2167489935963/5000000000000 : ℝ), (11946178285061/100000000000000 : ℝ), (447040229869/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318997211/2500000000 : ℝ)|^4357 ≤ (2167489935963/5000000000000 : ℝ)^3333
        have hw : |(1318997211/2500000000 : ℝ)|=(1318997211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-984175209/5000000000 : ℝ)|^4357 ≤ (11946178285061/100000000000000 : ℝ)^3333
        have hw : |(-984175209/5000000000 : ℝ)|=(984175209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350403609/2500000000 : ℝ)|^4357 ≤ (447040229869/1000000000000 : ℝ)^3333
        have hw : |(1350403609/2500000000 : ℝ)|=(1350403609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_box_10 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637994621/5000000000 : ℝ)*x 0 + (5401613903/10000000000 : ℝ)*x 1 + (-393670121/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637994621/5000000000 : ℝ)^4357 ≤ (43349802994087/100000000000000 : ℝ)^3333 := by
    have hnat : (2637994621 : ℕ)^4357*100000000000000^3333 ≤ 43349802994087^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637994621 5000000000 43349802994087 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401613903/10000000000 : ℝ)^4357 ≤ (44704017220531/100000000000000 : ℝ)^3333 := by
    have hnat : (5401613903 : ℕ)^4357*100000000000000^3333 ≤ 44704017220531^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401613903 10000000000 44704017220531 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (393670121/2000000000 : ℝ)^4357 ≤ (11946179768673/100000000000000 : ℝ)^3333 := by
    have hnat : (393670121 : ℕ)^4357*100000000000000^3333 ≤ 11946179768673^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393670121 2000000000 11946179768673 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637994621/5000000000 : ℝ), (5401613903/10000000000 : ℝ), (-393670121/2000000000 : ℝ)] ![(43349802994087/100000000000000 : ℝ), (44704017220531/100000000000000 : ℝ), (11946179768673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637994621/5000000000 : ℝ)|^4357 ≤ (43349802994087/100000000000000 : ℝ)^3333
        have hw : |(2637994621/5000000000 : ℝ)|=(2637994621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401613903/10000000000 : ℝ)|^4357 ≤ (44704017220531/100000000000000 : ℝ)^3333
        have hw : |(5401613903/10000000000 : ℝ)|=(5401613903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-393670121/2000000000 : ℝ)|^4357 ≤ (11946179768673/100000000000000 : ℝ)^3333
        have hw : |(-393670121/2000000000 : ℝ)|=(393670121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_box_11 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1123194483/2500000000 : ℝ)*x 0 + (4225759351/10000000000 : ℝ)*x 1 + (528220021/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1123194483/2500000000 : ℝ)^4357 ≤ (17568184146063/50000000000000 : ℝ)^3333 := by
    have hnat : (1123194483 : ℕ)^4357*50000000000000^3333 ≤ 17568184146063^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123194483 2500000000 17568184146063 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4225759351/10000000000 : ℝ)^4357 ≤ (6486362349227/20000000000000 : ℝ)^3333 := by
    have hnat : (4225759351 : ℕ)^4357*20000000000000^3333 ≤ 6486362349227^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225759351 10000000000 6486362349227 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528220021/1250000000 : ℝ)^4357 ≤ (8107954985717/25000000000000 : ℝ)^3333 := by
    have hnat : (528220021 : ℕ)^4357*25000000000000^3333 ≤ 8107954985717^3333*1250000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528220021 1250000000 8107954985717 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1123194483/2500000000 : ℝ), (4225759351/10000000000 : ℝ), (528220021/1250000000 : ℝ)] ![(17568184146063/50000000000000 : ℝ), (6486362349227/20000000000000 : ℝ), (8107954985717/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1123194483/2500000000 : ℝ)|^4357 ≤ (17568184146063/50000000000000 : ℝ)^3333
        have hw : |(1123194483/2500000000 : ℝ)|=(1123194483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4225759351/10000000000 : ℝ)|^4357 ≤ (6486362349227/20000000000000 : ℝ)^3333
        have hw : |(4225759351/10000000000 : ℝ)|=(4225759351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528220021/1250000000 : ℝ)|^4357 ≤ (8107954985717/25000000000000 : ℝ)^3333
        have hw : |(528220021/1250000000 : ℝ)|=(528220021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_box_12 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-19037939/100000000 : ℝ)*x 0 + (5469505909/10000000000 : ℝ)*x 1 + (2627451621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19037939/100000000 : ℝ)^4357 ≤ (5718301444569/50000000000000 : ℝ)^3333 := by
    have hnat : (19037939 : ℕ)^4357*50000000000000^3333 ≤ 5718301444569^3333*100000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19037939 100000000 5718301444569 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469505909/10000000000 : ℝ)^4357 ≤ (45439934833293/100000000000000 : ℝ)^3333 := by
    have hnat : (5469505909 : ℕ)^4357*100000000000000^3333 ≤ 45439934833293^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469505909 10000000000 45439934833293 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627451621/5000000000 : ℝ)^4357 ≤ (1724938490473/4000000000000 : ℝ)^3333 := by
    have hnat : (2627451621 : ℕ)^4357*4000000000000^3333 ≤ 1724938490473^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627451621 5000000000 1724938490473 4000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19037939/100000000 : ℝ), (5469505909/10000000000 : ℝ), (2627451621/5000000000 : ℝ)] ![(5718301444569/50000000000000 : ℝ), (45439934833293/100000000000000 : ℝ), (1724938490473/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19037939/100000000 : ℝ)|^4357 ≤ (5718301444569/50000000000000 : ℝ)^3333
        have hw : |(-19037939/100000000 : ℝ)|=(19037939/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469505909/10000000000 : ℝ)|^4357 ≤ (45439934833293/100000000000000 : ℝ)^3333
        have hw : |(5469505909/10000000000 : ℝ)|=(5469505909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627451621/5000000000 : ℝ)|^4357 ≤ (1724938490473/4000000000000 : ℝ)^3333
        have hw : |(2627451621/5000000000 : ℝ)|=(2627451621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_box_13 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537880277/1000000000 : ℝ)*x 0 + (-2027692957/10000000000 : ℝ)*x 1 + (5254902703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537880277/1000000000 : ℝ)^4357 ≤ (44457390565061/100000000000000 : ℝ)^3333 := by
    have hnat : (537880277 : ℕ)^4357*100000000000000^3333 ≤ 44457390565061^3333*1000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537880277 1000000000 44457390565061 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2027692957/10000000000 : ℝ)^4357 ≤ (3104788234061/25000000000000 : ℝ)^3333 := by
    have hnat : (2027692957 : ℕ)^4357*25000000000000^3333 ≤ 3104788234061^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027692957 10000000000 3104788234061 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254902703/10000000000 : ℝ)^4357 ≤ (10780864119917/25000000000000 : ℝ)^3333 := by
    have hnat : (5254902703 : ℕ)^4357*25000000000000^3333 ≤ 10780864119917^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254902703 10000000000 10780864119917 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537880277/1000000000 : ℝ), (-2027692957/10000000000 : ℝ), (5254902703/10000000000 : ℝ)] ![(44457390565061/100000000000000 : ℝ), (3104788234061/25000000000000 : ℝ), (10780864119917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537880277/1000000000 : ℝ)|^4357 ≤ (44457390565061/100000000000000 : ℝ)^3333
        have hw : |(537880277/1000000000 : ℝ)|=(537880277/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2027692957/10000000000 : ℝ)|^4357 ≤ (3104788234061/25000000000000 : ℝ)^3333
        have hw : |(-2027692957/10000000000 : ℝ)|=(2027692957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254902703/10000000000 : ℝ)|^4357 ≤ (10780864119917/25000000000000 : ℝ)^3333
        have hw : |(5254902703/10000000000 : ℝ)|=(5254902703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_box_14 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689401487/5000000000 : ℝ)*x 0 + (2627451317/5000000000 : ℝ)*x 1 + (-81107711/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689401487/5000000000 : ℝ)^4357 ≤ (44457392769209/100000000000000 : ℝ)^3333 := by
    have hnat : (2689401487 : ℕ)^4357*100000000000000^3333 ≤ 44457392769209^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689401487 5000000000 44457392769209 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627451317/5000000000 : ℝ)^4357 ≤ (21561727869733/50000000000000 : ℝ)^3333 := by
    have hnat : (2627451317 : ℕ)^4357*50000000000000^3333 ≤ 21561727869733^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627451317 5000000000 21561727869733 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81107711/400000000 : ℝ)^4357 ≤ (12419151479063/100000000000000 : ℝ)^3333 := by
    have hnat : (81107711 : ℕ)^4357*100000000000000^3333 ≤ 12419151479063^3333*400000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81107711 400000000 12419151479063 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689401487/5000000000 : ℝ), (2627451317/5000000000 : ℝ), (-81107711/400000000 : ℝ)] ![(44457392769209/100000000000000 : ℝ), (21561727869733/50000000000000 : ℝ), (12419151479063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689401487/5000000000 : ℝ)|^4357 ≤ (44457392769209/100000000000000 : ℝ)^3333
        have hw : |(2689401487/5000000000 : ℝ)|=(2689401487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627451317/5000000000 : ℝ)|^4357 ≤ (21561727869733/50000000000000 : ℝ)^3333
        have hw : |(2627451317/5000000000 : ℝ)|=(2627451317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-81107711/400000000 : ℝ)|^4357 ≤ (12419151479063/100000000000000 : ℝ)^3333
        have hw : |(-81107711/400000000 : ℝ)|=(81107711/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_box_15 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4137090213/10000000000 : ℝ)*x 0 + (137612481/312500000 : ℝ)*x 1 + (550449777/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4137090213/10000000000 : ℝ)^4357 ≤ (15772550278983/50000000000000 : ℝ)^3333 := by
    have hnat : (4137090213 : ℕ)^4357*50000000000000^3333 ≤ 15772550278983^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137090213 10000000000 15772550278983 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137612481/312500000 : ℝ)^4357 ≤ (17113727844007/50000000000000 : ℝ)^3333 := by
    have hnat : (137612481 : ℕ)^4357*50000000000000^3333 ≤ 17113727844007^3333*312500000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137612481 312500000 17113727844007 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550449777/1250000000 : ℝ)^4357 ≤ (34227443739157/100000000000000 : ℝ)^3333 := by
    have hnat : (550449777 : ℕ)^4357*100000000000000^3333 ≤ 34227443739157^3333*1250000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550449777 1250000000 34227443739157 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4137090213/10000000000 : ℝ), (137612481/312500000 : ℝ), (550449777/1250000000 : ℝ)] ![(15772550278983/50000000000000 : ℝ), (17113727844007/50000000000000 : ℝ), (34227443739157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4137090213/10000000000 : ℝ)|^4357 ≤ (15772550278983/50000000000000 : ℝ)^3333
        have hw : |(4137090213/10000000000 : ℝ)|=(4137090213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137612481/312500000 : ℝ)|^4357 ≤ (17113727844007/50000000000000 : ℝ)^3333
        have hw : |(137612481/312500000 : ℝ)|=(137612481/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550449777/1250000000 : ℝ)|^4357 ≤ (34227443739157/100000000000000 : ℝ)^3333
        have hw : |(550449777/1250000000 : ℝ)|=(550449777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1397_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14739/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62881/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59049/100000 : ℝ) ∧ (8027/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21141/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14739/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14739/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14739/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14739/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14739/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14739/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11273/100000 : ℝ) ^ (1089/256 : ℝ) ≤ (463911286304087/5000000000000000000 : ℝ) := by
    have hpowers : (11273/100000 : ℝ)^1089 ≤ (463911286304087/5000000000000000000 : ℝ)^256 := by
      have hnat : (11273 : ℕ)^1089*5000000000000000000^256 ≤ 463911286304087^256*100000^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11273 100000 463911286304087 5000000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11273/100000 : ℝ)) (X := (463911286304087/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14739/100000 : ℝ) ^ (1089/256 : ℝ) ≤ (14511453437595033/50000000000000000000 : ℝ) := by
    have hpowers : (14739/100000 : ℝ)^1089 ≤ (14511453437595033/50000000000000000000 : ℝ)^256 := by
      have hnat : (14739 : ℕ)^1089*50000000000000000000^256 ≤ 14511453437595033^256*100000^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14739 100000 14511453437595033 50000000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14739/100000 : ℝ)) (X := (14511453437595033/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500463911286304087/2500000000000000000 : ℝ) ≤ (2000087238098501/2000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (2500463911286304087/2500000000000000000 : ℝ)^256 ≤ (2000087238098501/2000000000000000 : ℝ)^1089 := by
      have hnat : (2500463911286304087 : ℕ)^256*2000000000000000^1089 ≤ 2000087238098501^1089*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500463911286304087 2500000000000000000 2000087238098501 2000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000087238098501/2000000000000000 : ℝ)) (X := (2500463911286304087/2500000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019150566300635903/50000000000000000000 : ℝ) ≤ (2000180048741091/2000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (50019150566300635903/50000000000000000000 : ℝ)^256 ≤ (2000180048741091/2000000000000000 : ℝ)^1089 := by
      have hnat : (50019150566300635903 : ℕ)^256*2000000000000000^1089 ≤ 2000180048741091^1089*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019150566300635903 50000000000000000000 2000180048741091 2000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000180048741091/2000000000000000 : ℝ)) (X := (50019150566300635903/50000000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014511453437595033/25000000000000000000 : ℝ) ≤ (2000272859383681/2000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (25014511453437595033/25000000000000000000 : ℝ)^256 ≤ (2000272859383681/2000000000000000 : ℝ)^1089 := by
      have hnat : (25014511453437595033 : ℕ)^256*2000000000000000^1089 ≤ 2000272859383681^1089*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014511453437595033 25000000000000000000 2000272859383681 2000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000272859383681/2000000000000000 : ℝ)) (X := (25014511453437595033/25000000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(463911286304087/5000000000000000000 : ℝ) ≤ ((3465104929250785163/3466000000000000000 : ℝ)+2*(9281064259/6932000000000 : ℝ)*(11273/100000 : ℝ))^(1089/256 : ℝ) := by
    rw [show (3465104929250785163/3466000000000000000 : ℝ)+2*(9281064259/6932000000000 : ℝ)*(11273/100000 : ℝ)=(2000087238098501/2000000000000000 : ℝ) by norm_num, show 1+2*(463911286304087/5000000000000000000 : ℝ)=(2500463911286304087/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14511453437595033/50000000000000000000 : ℝ)+(463911286304087/5000000000000000000 : ℝ) ≤ ((3465104929250785163/3466000000000000000 : ℝ)+(9281064259/6932000000000 : ℝ)*((14739/100000 : ℝ)+(11273/100000 : ℝ)))^(1089/256 : ℝ) := by
    rw [show (3465104929250785163/3466000000000000000 : ℝ)+(9281064259/6932000000000 : ℝ)*((14739/100000 : ℝ)+(11273/100000 : ℝ))=(2000180048741091/2000000000000000 : ℝ) by norm_num, show 1+(14511453437595033/50000000000000000000 : ℝ)+(463911286304087/5000000000000000000 : ℝ)=(50019150566300635903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14511453437595033/50000000000000000000 : ℝ) ≤ ((3465104929250785163/3466000000000000000 : ℝ)+2*(9281064259/6932000000000 : ℝ)*(14739/100000 : ℝ))^(1089/256 : ℝ) := by
    rw [show (3465104929250785163/3466000000000000000 : ℝ)+2*(9281064259/6932000000000 : ℝ)*(14739/100000 : ℝ)=(2000272859383681/2000000000000000 : ℝ) by norm_num, show 1+2*(14511453437595033/50000000000000000000 : ℝ)=(25014511453437595033/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3465104929250785163/3466000000000000000 : ℝ)*(X 1 0+X 2 0)+(9281064259/6932000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (11273/100000 : ℝ)) (hi := (14739/100000 : ℝ)) (c := (3465104929250785163/3466000000000000000 : ℝ)) (alpha := (9281064259/6932000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3465104929250785163/3466000000000000000 : ℝ)*(X 0 1+X 2 1)+(9281064259/6932000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (11273/100000 : ℝ)) (hi := (14739/100000 : ℝ)) (c := (3465104929250785163/3466000000000000000 : ℝ)) (alpha := (9281064259/6932000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3465104929250785163/3466000000000000000 : ℝ)*(X 0 2+X 1 2)+(9281064259/6932000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (11273/100000 : ℝ)) (hi := (14739/100000 : ℝ)) (c := (3465104929250785163/3466000000000000000 : ℝ)) (alpha := (9281064259/6932000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-917191243/5000000000 : ℝ)*X 0 0+(1346905403/2500000000 : ℝ)*X 0 1+(5387621619/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642899581/5000000000 : ℝ)*X 1 0+(-987067981/5000000000 : ℝ)*X 1 1+(5387621767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642899319/5000000000 : ℝ)*X 2 0+(1346905567/2500000000 : ℝ)*X 2 1+(-197413599/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((278712597/625000000 : ℝ)*X 0 0+(4242734897/10000000000 : ℝ)*X 0 1+(4242735443/10000000000 : ℝ)*X 0 2+(278712597/625000000 : ℝ)*X 1 0+(4242734897/10000000000 : ℝ)*X 1 1+(4242735443/10000000000 : ℝ)*X 1 2+(278712597/625000000 : ℝ)*X 2 0+(4242734897/10000000000 : ℝ)*X 2 1+(4242735443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2163152161/10000000000 : ℝ)*X 0 0+(5266011519/10000000000 : ℝ)*X 0 1+(105320231/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5371019823/10000000000 : ℝ)*X 1 0+(-2023303193/10000000000 : ℝ)*X 1 1+(164562857/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1342754941/2500000000 : ℝ)*X 2 0+(5266011543/10000000000 : ℝ)*X 2 1+(-2023303113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4164479147/10000000000 : ℝ)*X 0 0+(2195072263/5000000000 : ℝ)*X 0 1+(2195072273/5000000000 : ℝ)*X 0 2+(4164479147/10000000000 : ℝ)*X 1 0+(2195072263/5000000000 : ℝ)*X 1 1+(2195072273/5000000000 : ℝ)*X 1 2+(4164479147/10000000000 : ℝ)*X 2 0+(2195072263/5000000000 : ℝ)*X 2 1+(2195072273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2093975701/10000000000 : ℝ)*X 0 0+(5182038807/10000000000 : ℝ)*X 0 1+(2700807793/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1318997211/2500000000 : ℝ)*X 1 0+(-984175209/5000000000 : ℝ)*X 1 1+(1350403609/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637994621/5000000000 : ℝ)*X 2 0+(5401613903/10000000000 : ℝ)*X 2 1+(-393670121/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1123194483/2500000000 : ℝ)*X 0 0+(4225759351/10000000000 : ℝ)*X 0 1+(528220021/1250000000 : ℝ)*X 0 2+(1123194483/2500000000 : ℝ)*X 1 0+(4225759351/10000000000 : ℝ)*X 1 1+(528220021/1250000000 : ℝ)*X 1 2+(1123194483/2500000000 : ℝ)*X 2 0+(4225759351/10000000000 : ℝ)*X 2 1+(528220021/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-19037939/100000000 : ℝ)*X 0 0+(5469505909/10000000000 : ℝ)*X 0 1+(2627451621/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((537880277/1000000000 : ℝ)*X 1 0+(-2027692957/10000000000 : ℝ)*X 1 1+(5254902703/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2689401487/5000000000 : ℝ)*X 2 0+(2627451317/5000000000 : ℝ)*X 2 1+(-81107711/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4137090213/10000000000 : ℝ)*X 0 0+(137612481/312500000 : ℝ)*X 0 1+(550449777/1250000000 : ℝ)*X 0 2+(4137090213/10000000000 : ℝ)*X 1 0+(137612481/312500000 : ℝ)*X 1 1+(550449777/1250000000 : ℝ)*X 1 2+(4137090213/10000000000 : ℝ)*X 2 0+(137612481/312500000 : ℝ)*X 2 1+(550449777/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62881/100000 : ℝ) ≤ (-54484198448630083831269863666103/86650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2407463/12500000000000 : ℝ)*(lower2) + (5001589/25000000000000 : ℝ)*(lower3) + (616019/6250000000000 : ℝ)*(lower4) + (2733447/100000000000000 : ℝ)*(lower5) + (2981726765978873/100000000000000 : ℝ)*(major0) + (2981726765978873/100000000000000 : ℝ)*(major1) + (2981726765978873/100000000000000 : ℝ)*(major2) + (173765151/6250000000000 : ℝ)*(sp1) + (510501433435987/12500000000000 : ℝ)*(sp4) + (408400886116601/10000000000000 : ℝ)*(sp5) + (2041999521466141/50000000000000 : ℝ)*(sp6) + (2969377159629/156250000000 : ℝ)*(sp7) + (17392053/10000000000000 : ℝ)*(sp8) + (787404759/6250000000000 : ℝ)*(sp14) + (2969377159629/156250000000 : ℝ)*(f.failure) + (2042005820704213/50000000000000 : ℝ)*(f.sum) + (30386032792113/1733000000000000000000000000 : ℝ)*base65 + (734946135127038701/346600000000000000000000000000000 : ℝ)*base68 + (658364465150638701/346600000000000000000000000000000 : ℝ)*base70 + (648427721123838701/346600000000000000000000000000000 : ℝ)*base72 + (1095974345481/1733000000000000000000000000 : ℝ)*base73 + (1075736002381838701/346600000000000000000000000000000 : ℝ)*base76 + (1050812717254961299/346600000000000000000000000000000 : ℝ)*base77 + (1756727332787838701/346600000000000000000000000000000 : ℝ)*base80 + (8261527539033/1733000000000000000000000000 : ℝ)*base81 + (1727/976562500000000000 : ℝ)*base90 + (1727/976562500000000000 : ℝ)*base92 + (1727/976562500000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59049/100000 : ℝ) ≤ (102336648109016716684731647187489/173300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1685509/5000000000000 : ℝ)*(lower1) + (67458309/50000000000000 : ℝ)*(upper2) + (6805767/50000000000000 : ℝ)*(upper5) + (3052260911237333/100000000000000 : ℝ)*(major0) + (3052260911237333/100000000000000 : ℝ)*(major1) + (3052260911237333/100000000000000 : ℝ)*(major2) + (517434545111281/12500000000000 : ℝ)*(sp0) + (1034868403133029/25000000000000 : ℝ)*(sp1) + (258716499466347/6250000000000 : ℝ)*(sp2) + (1945351689646803/100000000000000 : ℝ)*(sp3) + (4015839349/50000000000000 : ℝ)*(sp5) + (8826374631/50000000000000 : ℝ)*(sp6) + (2289306693/50000000000000 : ℝ)*(sp7) + (2641660283/50000000000000 : ℝ)*(sp12) + (1945356268260189/100000000000000 : ℝ)*(f.failure) + (2069740822105407/50000000000000 : ℝ)*(f.sum) + (4859366523/69320000000000000000000000 : ℝ)*base66 + (331450661991390279/346600000000000000000000000000000 : ℝ)*base67 + (4534424726656190279/346600000000000000000000000000000 : ℝ)*base69 + (716820073941190279/346600000000000000000000000000000 : ℝ)*base71 + (5965432636579/866500000000000000000000000 : ℝ)*base74 + (131263925352190279/346600000000000000000000000000000 : ℝ)*base75 + (732880444174390279/346600000000000000000000000000000 : ℝ)*base77 + (3022901239360190279/346600000000000000000000000000000 : ℝ)*base79 + (139477625351/54156250000000000000000000 : ℝ)*base82 + (15504931/5000000000000000000000 : ℝ)*base90 + (15504931/5000000000000000000000 : ℝ)*base92 + (15504931/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (8027/10000 : ℝ) ≤ (69556261982632035380226768778791/86650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (91461859/50000000000000 : ℝ)*(upper0) + (140341/5000000000000 : ℝ)*(lower3) + (18747857/100000000000000 : ℝ)*(upper4) + (1680929180959827/50000000000000 : ℝ)*(major0) + (1680929180959827/50000000000000 : ℝ)*(major1) + (1680929180959827/50000000000000 : ℝ)*(major2) + (165654706041/100000000000000 : ℝ)*(sp1) + (53630004339/100000000000000 : ℝ)*(sp3) + (8515180291/25000000000000 : ℝ)*(sp4) + (2277113653157191/50000000000000 : ℝ)*(sp8) + (2277057768539247/50000000000000 : ℝ)*(sp9) + (910856238356907/20000000000000 : ℝ)*(sp10) + (1071312173956039/50000000000000 : ℝ)*(sp11) + (19824748989/100000000000000 : ℝ)*(sp12) + (2142677977916417/100000000000000 : ℝ)*(f.failure) + (910856238356907/20000000000000 : ℝ)*(f.sum) + (369299969197/216625000000000000000000000 : ℝ)*base65 + (227181785155546801/173300000000000000000000000000000 : ℝ)*base67 + (2270982369022846801/173300000000000000000000000000000 : ℝ)*base69 + (1603771350140546801/173300000000000000000000000000000 : ℝ)*base71 + (10229811052639/1733000000000000000000000000 : ℝ)*base73 + (222470752897546801/173300000000000000000000000000000 : ℝ)*base75 + (1626037992656946801/173300000000000000000000000000000 : ℝ)*base77 + (1072573201519346801/173300000000000000000000000000000 : ℝ)*base79 + (1703906903933/433250000000000000000000000 : ℝ)*base81 + (41746943/5000000000000000000000 : ℝ)*base90 + (41746943/5000000000000000000000 : ℝ)*base92 + (41746943/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-21141/25000 : ℝ) ≤ (-183181197022632439107496311/216625000000000000000000000 : ℝ) := by norm_num
    linear_combination (374380991/100000000000000 : ℝ)*(lower0) + (185403971/100000000000000 : ℝ)*(lower1) + (128782469/100000000000000 : ℝ)*(lower2) + (424868702113839/12500000000000 : ℝ)*(major0) + (424868702113839/12500000000000 : ℝ)*(major1) + (424868702113839/12500000000000 : ℝ)*(major2) + (6526780683/100000000000000 : ℝ)*(sp0) + (29435648901/6250000000000 : ℝ)*(sp5) + (427626336439/100000000000000 : ℝ)*(sp6) + (46680717651/100000000000000 : ℝ)*(sp7) + (4659761787999399/100000000000000 : ℝ)*(sp12) + (2329648672198833/50000000000000 : ℝ)*(sp13) + (4659340688443643/100000000000000 : ℝ)*(sp14) + (1057749698021/48828125000 : ℝ)*(sp15) + (2166318062264659/100000000000000 : ℝ)*(f.failure) + (2329884157390041/50000000000000 : ℝ)*(f.sum) + (3873675906961/1733000000000000000000000000 : ℝ)*base65 + (126001616395745757/43325000000000000000000000000000 : ℝ)*base67 + (226557240456245757/43325000000000000000000000000000 : ℝ)*base69 + (318387515784754243/43325000000000000000000000000000 : ℝ)*base72 + (15224288093693/216625000000000000000000000 : ℝ)*base73 + (58238531295029243/43325000000000000000000000000000 : ℝ)*base76 + (19150730289004243/43325000000000000000000000000000 : ℝ)*base78 + (1906533415320345757/43325000000000000000000000000000 : ℝ)*base79 + (1208845486173/866500000000000000000000000 : ℝ)*base82 + (20358061/5000000000000000000000 : ℝ)*base90 + (20358061/5000000000000000000000 : ℝ)*base92 + (20358061/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1397_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14739/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62881/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59049/100000 : ℝ) else (8027/10000 : ℝ) ≤ X j i ∧ X j i ≤ (21141/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1397_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1397_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62881/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59049/100000 : ℝ) else (8027/10000 : ℝ) ≤ X j i ∧ X j i ≤ (21141/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1397_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1397_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1397_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62881/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59049/100000 : ℝ) else (8027/10000 : ℝ) ≤ X j i ∧ X j i ≤ (21141/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1397_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

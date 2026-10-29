-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1764_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:29:16.3483+00:00
-- url     : https://prove2.me/submissions/6b03e087-cacf-42b1-a6e8-7dab0e3bce76

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
theorem support_rectangle_w1764_s3_0 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1148382773/10000000000 : ℝ)*x 0 + (13697007/25000000 : ℝ)*x 1 + (203384763/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1148382773/10000000000 : ℝ)^5999 ≤ (1838929668891/25000000000000 : ℝ)^4975 := by
    have hnat : (1148382773 : ℕ)^5999*25000000000000^4975 ≤ 1838929668891^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148382773 10000000000 1838929668891 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13697007/25000000 : ℝ)^5999 ≤ (48406040912691/100000000000000 : ℝ)^4975 := by
    have hnat : (13697007 : ℕ)^5999*100000000000000^4975 ≤ 48406040912691^4975*25000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13697007 25000000 48406040912691 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (203384763/400000000 : ℝ)^5999 ≤ (8847648081231/20000000000000 : ℝ)^4975 := by
    have hnat : (203384763 : ℕ)^5999*20000000000000^4975 ≤ 8847648081231^4975*400000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203384763 400000000 8847648081231 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1148382773/10000000000 : ℝ), (13697007/25000000 : ℝ), (203384763/400000000 : ℝ)] ![(1838929668891/25000000000000 : ℝ), (48406040912691/100000000000000 : ℝ), (8847648081231/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1148382773/10000000000 : ℝ)|^5999 ≤ (1838929668891/25000000000000 : ℝ)^4975
        have hw : |(-1148382773/10000000000 : ℝ)|=(1148382773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13697007/25000000 : ℝ)|^5999 ≤ (48406040912691/100000000000000 : ℝ)^4975
        have hw : |(13697007/25000000 : ℝ)|=(13697007/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(203384763/400000000 : ℝ)|^5999 ≤ (8847648081231/20000000000000 : ℝ)^4975
        have hw : |(203384763/400000000 : ℝ)|=(203384763/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s3_1 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (532659199/1000000000 : ℝ)*x 0 + (-42315733/312500000 : ℝ)*x 1 + (5084619839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532659199/1000000000 : ℝ)^5999 ≤ (23394553251717/50000000000000 : ℝ)^4975 := by
    have hnat : (532659199 : ℕ)^5999*50000000000000^4975 ≤ 23394553251717^4975*1000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532659199 1000000000 23394553251717 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42315733/312500000 : ℝ)^5999 ≤ (4486322526121/50000000000000 : ℝ)^4975 := by
    have hnat : (42315733 : ℕ)^5999*50000000000000^4975 ≤ 4486322526121^4975*312500000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42315733 312500000 4486322526121 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084619839/10000000000 : ℝ)^5999 ≤ (5529781052679/12500000000000 : ℝ)^4975 := by
    have hnat : (5084619839 : ℕ)^5999*12500000000000^4975 ≤ 5529781052679^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084619839 10000000000 5529781052679 12500000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532659199/1000000000 : ℝ), (-42315733/312500000 : ℝ), (5084619839/10000000000 : ℝ)] ![(23394553251717/50000000000000 : ℝ), (4486322526121/50000000000000 : ℝ), (5529781052679/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532659199/1000000000 : ℝ)|^5999 ≤ (23394553251717/50000000000000 : ℝ)^4975
        have hw : |(532659199/1000000000 : ℝ)|=(532659199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42315733/312500000 : ℝ)|^5999 ≤ (4486322526121/50000000000000 : ℝ)^4975
        have hw : |(-42315733/312500000 : ℝ)|=(42315733/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084619839/10000000000 : ℝ)|^5999 ≤ (5529781052679/12500000000000 : ℝ)^4975
        have hw : |(5084619839/10000000000 : ℝ)|=(5084619839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s3_2 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1331647953/2500000000 : ℝ)*x 0 + (5084618041/10000000000 : ℝ)*x 1 + (-677053027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1331647953/2500000000 : ℝ)^5999 ≤ (11697276154511/25000000000000 : ℝ)^4975 := by
    have hnat : (1331647953 : ℕ)^5999*25000000000000^4975 ≤ 11697276154511^4975*2500000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331647953 2500000000 11697276154511 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5084618041/10000000000 : ℝ)^5999 ≤ (22119114779127/50000000000000 : ℝ)^4975 := by
    have hnat : (5084618041 : ℕ)^5999*50000000000000^4975 ≤ 22119114779127^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084618041 10000000000 22119114779127 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677053027/5000000000 : ℝ)^5999 ≤ (8972665810631/100000000000000 : ℝ)^4975 := by
    have hnat : (677053027 : ℕ)^5999*100000000000000^4975 ≤ 8972665810631^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677053027 5000000000 8972665810631 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1331647953/2500000000 : ℝ), (5084618041/10000000000 : ℝ), (-677053027/5000000000 : ℝ)] ![(11697276154511/25000000000000 : ℝ), (22119114779127/50000000000000 : ℝ), (8972665810631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1331647953/2500000000 : ℝ)|^5999 ≤ (11697276154511/25000000000000 : ℝ)^4975
        have hw : |(1331647953/2500000000 : ℝ)|=(1331647953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5084618041/10000000000 : ℝ)|^5999 ≤ (22119114779127/50000000000000 : ℝ)^4975
        have hw : |(5084618041/10000000000 : ℝ)|=(5084618041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-677053027/5000000000 : ℝ)|^5999 ≤ (8972665810631/100000000000000 : ℝ)^4975
        have hw : |(-677053027/5000000000 : ℝ)|=(677053027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s3_3 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1996429167/5000000000 : ℝ)*x 0 + (417272147/1250000000 : ℝ)*x 1 + (2353755521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1996429167/5000000000 : ℝ)^5999 ≤ (8263357012549/25000000000000 : ℝ)^4975 := by
    have hnat : (1996429167 : ℕ)^5999*25000000000000^4975 ≤ 8263357012549^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996429167 5000000000 8263357012549 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417272147/1250000000 : ℝ)^5999 ≤ (13316918173433/50000000000000 : ℝ)^4975 := by
    have hnat : (417272147 : ℕ)^5999*50000000000000^4975 ≤ 13316918173433^4975*1250000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417272147 1250000000 13316918173433 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2353755521/5000000000 : ℝ)^5999 ≤ (40312735580999/100000000000000 : ℝ)^4975 := by
    have hnat : (2353755521 : ℕ)^5999*100000000000000^4975 ≤ 40312735580999^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2353755521 5000000000 40312735580999 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1996429167/5000000000 : ℝ), (417272147/1250000000 : ℝ), (2353755521/5000000000 : ℝ)] ![(8263357012549/25000000000000 : ℝ), (13316918173433/50000000000000 : ℝ), (40312735580999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1996429167/5000000000 : ℝ)|^5999 ≤ (8263357012549/25000000000000 : ℝ)^4975
        have hw : |(1996429167/5000000000 : ℝ)|=(1996429167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(417272147/1250000000 : ℝ)|^5999 ≤ (13316918173433/50000000000000 : ℝ)^4975
        have hw : |(417272147/1250000000 : ℝ)|=(417272147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2353755521/5000000000 : ℝ)|^5999 ≤ (40312735580999/100000000000000 : ℝ)^4975
        have hw : |(2353755521/5000000000 : ℝ)|=(2353755521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s3_4 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-4487139/39062500 : ℝ)*x 0 + (5091174743/10000000000 : ℝ)*x 1 + (2736054963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4487139/39062500 : ℝ)^5999 ≤ (7358227484501/100000000000000 : ℝ)^4975 := by
    have hnat : (4487139 : ℕ)^5999*100000000000000^4975 ≤ 7358227484501^4975*39062500^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487139 39062500 7358227484501 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5091174743/10000000000 : ℝ)^5999 ≤ (44307026358257/100000000000000 : ℝ)^4975 := by
    have hnat : (5091174743 : ℕ)^5999*100000000000000^4975 ≤ 44307026358257^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5091174743 10000000000 44307026358257 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736054963/5000000000 : ℝ)^5999 ≤ (24167373069083/50000000000000 : ℝ)^4975 := by
    have hnat : (2736054963 : ℕ)^5999*50000000000000^4975 ≤ 24167373069083^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736054963 5000000000 24167373069083 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4487139/39062500 : ℝ), (5091174743/10000000000 : ℝ), (2736054963/5000000000 : ℝ)] ![(7358227484501/100000000000000 : ℝ), (44307026358257/100000000000000 : ℝ), (24167373069083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4487139/39062500 : ℝ)|^5999 ≤ (7358227484501/100000000000000 : ℝ)^4975
        have hw : |(-4487139/39062500 : ℝ)|=(4487139/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5091174743/10000000000 : ℝ)|^5999 ≤ (44307026358257/100000000000000 : ℝ)^4975
        have hw : |(5091174743/10000000000 : ℝ)|=(5091174743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736054963/5000000000 : ℝ)|^5999 ≤ (24167373069083/50000000000000 : ℝ)^4975
        have hw : |(2736054963/5000000000 : ℝ)|=(2736054963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s3_5 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5222572771/10000000000 : ℝ)*x 0 + (5472109869/10000000000 : ℝ)*x 1 + (-966614577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5222572771/10000000000 : ℝ)^5999 ≤ (45689552852577/100000000000000 : ℝ)^4975 := by
    have hnat : (5222572771 : ℕ)^5999*100000000000000^4975 ≤ 45689552852577^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222572771 10000000000 45689552852577 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472109869/10000000000 : ℝ)^5999 ≤ (48334745531059/100000000000000 : ℝ)^4975 := by
    have hnat : (5472109869 : ℕ)^5999*100000000000000^4975 ≤ 48334745531059^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472109869 10000000000 48334745531059 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966614577/10000000000 : ℝ)^5999 ≤ (1195140318599/20000000000000 : ℝ)^4975 := by
    have hnat : (966614577 : ℕ)^5999*20000000000000^4975 ≤ 1195140318599^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966614577 10000000000 1195140318599 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5222572771/10000000000 : ℝ), (5472109869/10000000000 : ℝ), (-966614577/10000000000 : ℝ)] ![(45689552852577/100000000000000 : ℝ), (48334745531059/100000000000000 : ℝ), (1195140318599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5222572771/10000000000 : ℝ)|^5999 ≤ (45689552852577/100000000000000 : ℝ)^4975
        have hw : |(5222572771/10000000000 : ℝ)|=(5222572771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472109869/10000000000 : ℝ)|^5999 ≤ (48334745531059/100000000000000 : ℝ)^4975
        have hw : |(5472109869/10000000000 : ℝ)|=(5472109869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-966614577/10000000000 : ℝ)|^5999 ≤ (1195140318599/20000000000000 : ℝ)^4975
        have hw : |(-966614577/10000000000 : ℝ)|=(966614577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s3_6 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (798797499/2000000000 : ℝ)*x 0 + (585591597/1250000000 : ℝ)*x 1 + (1680712491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (798797499/2000000000 : ℝ)^5999 ≤ (16532349842263/50000000000000 : ℝ)^4975 := by
    have hnat : (798797499 : ℕ)^5999*50000000000000^4975 ≤ 16532349842263^4975*2000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798797499 2000000000 16532349842263 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (585591597/1250000000 : ℝ)^5999 ≤ (5009705250703/12500000000000 : ℝ)^4975 := by
    have hnat : (585591597 : ℕ)^5999*12500000000000^4975 ≤ 5009705250703^4975*1250000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585591597 1250000000 5009705250703 12500000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1680712491/5000000000 : ℝ)^5999 ≤ (3357207287261/12500000000000 : ℝ)^4975 := by
    have hnat : (1680712491 : ℕ)^5999*12500000000000^4975 ≤ 3357207287261^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680712491 5000000000 3357207287261 12500000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(798797499/2000000000 : ℝ), (585591597/1250000000 : ℝ), (1680712491/5000000000 : ℝ)] ![(16532349842263/50000000000000 : ℝ), (5009705250703/12500000000000 : ℝ), (3357207287261/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(798797499/2000000000 : ℝ)|^5999 ≤ (16532349842263/50000000000000 : ℝ)^4975
        have hw : |(798797499/2000000000 : ℝ)|=(798797499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(585591597/1250000000 : ℝ)|^5999 ≤ (5009705250703/12500000000000 : ℝ)^4975
        have hw : |(585591597/1250000000 : ℝ)|=(585591597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1680712491/5000000000 : ℝ)|^5999 ≤ (3357207287261/12500000000000 : ℝ)^4975
        have hw : |(1680712491/5000000000 : ℝ)|=(1680712491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1764_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44738407/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8853/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1839/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2299/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8853/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8853/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1839/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8853/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1839/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8853/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1839/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8853/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1839/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8853/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1839/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8853/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1839/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1839/20000 : ℝ) ^ (5983/1024 : ℝ) ≤ (87956431175131/100000000000000000000 : ℝ) := by
    have hpowers : (1839/20000 : ℝ)^5983 ≤ (87956431175131/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1839 : ℕ)^5983*100000000000000000000^1024 ≤ 87956431175131^1024*20000^5983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1839 20000 87956431175131 100000000000000000000 5983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1839/20000 : ℝ)) (X := (87956431175131/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8853/50000 : ℝ) ^ (5983/1024 : ℝ) ≤ (2022591599529/50000000000000000 : ℝ) := by
    have hpowers : (8853/50000 : ℝ)^5983 ≤ (2022591599529/50000000000000000 : ℝ)^1024 := by
      have hnat : (8853 : ℕ)^5983*50000000000000000^1024 ≤ 2022591599529^1024*50000^5983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8853 50000 2022591599529 50000000000000000 5983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8853/50000 : ℝ)) (X := (2022591599529/50000000000000000 : ℝ)) (by norm_num) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000087956431175131/50000000000000000000 : ℝ) ≤ (2500000752693631/2500000000000000 : ℝ) ^ (5983/1024 : ℝ) := by
    have hpowers : (50000087956431175131/50000000000000000000 : ℝ)^1024 ≤ (2500000752693631/2500000000000000 : ℝ)^5983 := by
      have hnat : (50000087956431175131 : ℕ)^1024*2500000000000000^5983 ≤ 2500000752693631^5983*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000087956431175131 50000000000000000000 2500000752693631 2500000000000000 1024 5983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000752693631/2500000000000000 : ℝ)) (X := (50000087956431175131/50000000000000000000 : ℝ)) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100004133139630233131/100000000000000000000 : ℝ) ≤ (2000014147626571/2000000000000000 : ℝ) ^ (5983/1024 : ℝ) := by
    have hpowers : (100004133139630233131/100000000000000000000 : ℝ)^1024 ≤ (2000014147626571/2000000000000000 : ℝ)^5983 := by
      have hnat : (100004133139630233131 : ℕ)^1024*2000000000000000^5983 ≤ 2000014147626571^5983*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100004133139630233131 100000000000000000000 2000014147626571 2000000000000000 1024 5983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000014147626571/2000000000000000 : ℝ)) (X := (100004133139630233131/100000000000000000000 : ℝ)) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25002022591599529/25000000000000000 : ℝ) ≤ (5000069232745593/5000000000000000 : ℝ) ^ (5983/1024 : ℝ) := by
    have hpowers : (25002022591599529/25000000000000000 : ℝ)^1024 ≤ (5000069232745593/5000000000000000 : ℝ)^5983 := by
      have hnat : (25002022591599529 : ℕ)^1024*5000000000000000^5983 ≤ 5000069232745593^5983*25000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002022591599529 25000000000000000 5000069232745593 5000000000000000 1024 5983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000069232745593/5000000000000000 : ℝ)) (X := (25002022591599529/25000000000000000 : ℝ)) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(87956431175131/100000000000000000000 : ℝ) ≤ ((14184796686430377779/14185000000000000000 : ℝ)+2*(67727358331/851100000000000 : ℝ)*(1839/20000 : ℝ))^(5983/1024 : ℝ) := by
    rw [show (14184796686430377779/14185000000000000000 : ℝ)+2*(67727358331/851100000000000 : ℝ)*(1839/20000 : ℝ)=(2500000752693631/2500000000000000 : ℝ) by norm_num, show 1+2*(87956431175131/100000000000000000000 : ℝ)=(50000087956431175131/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2022591599529/50000000000000000 : ℝ)+(87956431175131/100000000000000000000 : ℝ) ≤ ((14184796686430377779/14185000000000000000 : ℝ)+(67727358331/851100000000000 : ℝ)*((8853/50000 : ℝ)+(1839/20000 : ℝ)))^(5983/1024 : ℝ) := by
    rw [show (14184796686430377779/14185000000000000000 : ℝ)+(67727358331/851100000000000 : ℝ)*((8853/50000 : ℝ)+(1839/20000 : ℝ))=(2000014147626571/2000000000000000 : ℝ) by norm_num, show 1+(2022591599529/50000000000000000 : ℝ)+(87956431175131/100000000000000000000 : ℝ)=(100004133139630233131/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2022591599529/50000000000000000 : ℝ) ≤ ((14184796686430377779/14185000000000000000 : ℝ)+2*(67727358331/851100000000000 : ℝ)*(8853/50000 : ℝ))^(5983/1024 : ℝ) := by
    rw [show (14184796686430377779/14185000000000000000 : ℝ)+2*(67727358331/851100000000000 : ℝ)*(8853/50000 : ℝ)=(5000069232745593/5000000000000000 : ℝ) by norm_num, show 1+2*(2022591599529/50000000000000000 : ℝ)=(25002022591599529/25000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14184796686430377779/14185000000000000000 : ℝ)*(X 1 0+X 2 0)+(67727358331/851100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5983/1024 : ℝ)) (lo := (1839/20000 : ℝ)) (hi := (8853/50000 : ℝ)) (c := (14184796686430377779/14185000000000000000 : ℝ)) (alpha := (67727358331/851100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14184796686430377779/14185000000000000000 : ℝ)*(X 0 1+X 2 1)+(67727358331/851100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5983/1024 : ℝ)) (lo := (1839/20000 : ℝ)) (hi := (8853/50000 : ℝ)) (c := (14184796686430377779/14185000000000000000 : ℝ)) (alpha := (67727358331/851100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14184796686430377779/14185000000000000000 : ℝ)*(X 0 2+X 1 2)+(67727358331/851100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5983/1024 : ℝ)) (lo := (1839/20000 : ℝ)) (hi := (8853/50000 : ℝ)) (c := (14184796686430377779/14185000000000000000 : ℝ)) (alpha := (67727358331/851100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1148382773/10000000000 : ℝ)*X 0 0+(13697007/25000000 : ℝ)*X 0 1+(203384763/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((532659199/1000000000 : ℝ)*X 1 0+(-42315733/312500000 : ℝ)*X 1 1+(5084619839/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1331647953/2500000000 : ℝ)*X 2 0+(5084618041/10000000000 : ℝ)*X 2 1+(-677053027/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1996429167/5000000000 : ℝ)*X 0 0+(417272147/1250000000 : ℝ)*X 0 1+(2353755521/5000000000 : ℝ)*X 0 2+(1996429167/5000000000 : ℝ)*X 1 0+(417272147/1250000000 : ℝ)*X 1 1+(2353755521/5000000000 : ℝ)*X 1 2+(1996429167/5000000000 : ℝ)*X 2 0+(417272147/1250000000 : ℝ)*X 2 1+(2353755521/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-4487139/39062500 : ℝ)*X 0 0+(5091174743/10000000000 : ℝ)*X 0 1+(2736054963/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5222572771/10000000000 : ℝ)*X 2 0+(5472109869/10000000000 : ℝ)*X 2 1+(-966614577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s3_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((798797499/2000000000 : ℝ)*X 0 0+(585591597/1250000000 : ℝ)*X 0 1+(1680712491/5000000000 : ℝ)*X 0 2+(798797499/2000000000 : ℝ)*X 1 0+(585591597/1250000000 : ℝ)*X 1 1+(1680712491/5000000000 : ℝ)*X 1 2+(798797499/2000000000 : ℝ)*X 2 0+(585591597/1250000000 : ℝ)*X 2 1+(1680712491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4345184923138518661201972449/709250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (500426291/100000000000000 : ℝ)*(base19) + (200702611/100000000000000 : ℝ)*(base23) + (9968623/50000000000000 : ℝ)*(upper2) + (336002749/100000000000000 : ℝ)*(lower5) + (1633604048598423/100000000000000 : ℝ)*(major0) + (1633604048598423/100000000000000 : ℝ)*(major1) + (1633604048598423/100000000000000 : ℝ)*(major2) + (634226246145711/25000000000000 : ℝ)*(sp0) + (507383166814991/20000000000000 : ℝ)*(sp1) + (2536903210134483/100000000000000 : ℝ)*(sp2) + (365143117513369/50000000000000 : ℝ)*(sp3) + (5674959201/50000000000000 : ℝ)*(sp4) + (12923664153/100000000000000 : ℝ)*(sp5) + (5323453841/100000000000000 : ℝ)*(sp6) + (730291558480579/100000000000000 : ℝ)*(f.failure) + (1268458167250623/50000000000000 : ℝ)*(f.sum) + (3008825733461/886562500000000000000000000 : ℝ)*base65 + (9115369182672192517/1418500000000000000000000000000000 : ℝ)*base67 + (2137205928302192517/1418500000000000000000000000000000 : ℝ)*base69 + (6391203982202692517/1418500000000000000000000000000000 : ℝ)*base71 + (48591806530231/14185000000000000000000000000 : ℝ)*base73 + (716283698718307483/1418500000000000000000000000000000 : ℝ)*base76 + (13184938506486192517/1418500000000000000000000000000000 : ℝ)*base77 + (13096000113596807483/1418500000000000000000000000000000 : ℝ)*base80 + (2587482839887/1773125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (15102347/2000000000000000000000 : ℝ)*base90 + (15102347/2000000000000000000000 : ℝ)*base92 + (15102347/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1764_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44738407/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8853/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1839/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2299/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8853/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1764_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1764_box_0 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-783551211/10000000000 : ℝ)*x 0 + (1082121579/2000000000 : ℝ)*x 1 + (1082121559/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (783551211/10000000000 : ℝ)^5999 ≤ (4639105199883/100000000000000 : ℝ)^4975 := by
    have hnat : (783551211 : ℕ)^5999*100000000000000^4975 ≤ 4639105199883^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783551211 10000000000 4639105199883 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082121579/2000000000 : ℝ)^5999 ≤ (11920111982433/25000000000000 : ℝ)^4975 := by
    have hnat : (1082121579 : ℕ)^5999*25000000000000^4975 ≤ 11920111982433^4975*2000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082121579 2000000000 11920111982433 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082121559/2000000000 : ℝ)^5999 ≤ (47680446867107/100000000000000 : ℝ)^4975 := by
    have hnat : (1082121559 : ℕ)^5999*100000000000000^4975 ≤ 47680446867107^4975*2000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082121559 2000000000 47680446867107 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-783551211/10000000000 : ℝ), (1082121579/2000000000 : ℝ), (1082121559/2000000000 : ℝ)] ![(4639105199883/100000000000000 : ℝ), (11920111982433/25000000000000 : ℝ), (47680446867107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-783551211/10000000000 : ℝ)|^5999 ≤ (4639105199883/100000000000000 : ℝ)^4975
        have hw : |(-783551211/10000000000 : ℝ)|=(783551211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082121579/2000000000 : ℝ)|^5999 ≤ (11920111982433/25000000000000 : ℝ)^4975
        have hw : |(1082121579/2000000000 : ℝ)|=(1082121579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082121559/2000000000 : ℝ)|^5999 ≤ (47680446867107/100000000000000 : ℝ)^4975
        have hw : |(1082121559/2000000000 : ℝ)|=(1082121559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_box_1 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596363707/5000000000 : ℝ)*x 0 + (-1094902223/10000000000 : ℝ)*x 1 + (135265199/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596363707/5000000000 : ℝ)^5999 ≤ (45374894633167/100000000000000 : ℝ)^4975 := by
    have hnat : (2596363707 : ℕ)^5999*100000000000000^4975 ≤ 45374894633167^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596363707 5000000000 45374894633167 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094902223/10000000000 : ℝ)^5999 ≤ (1388931346577/20000000000000 : ℝ)^4975 := by
    have hnat : (1094902223 : ℕ)^5999*20000000000000^4975 ≤ 1388931346577^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094902223 10000000000 1388931346577 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135265199/250000000 : ℝ)^5999 ≤ (23840224310219/50000000000000 : ℝ)^4975 := by
    have hnat : (135265199 : ℕ)^5999*50000000000000^4975 ≤ 23840224310219^4975*250000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135265199 250000000 23840224310219 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596363707/5000000000 : ℝ), (-1094902223/10000000000 : ℝ), (135265199/250000000 : ℝ)] ![(45374894633167/100000000000000 : ℝ), (1388931346577/20000000000000 : ℝ), (23840224310219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596363707/5000000000 : ℝ)|^5999 ≤ (45374894633167/100000000000000 : ℝ)^4975
        have hw : |(2596363707/5000000000 : ℝ)|=(2596363707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1094902223/10000000000 : ℝ)|^5999 ≤ (1388931346577/20000000000000 : ℝ)^4975
        have hw : |(-1094902223/10000000000 : ℝ)|=(1094902223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135265199/250000000 : ℝ)|^5999 ≤ (23840224310219/50000000000000 : ℝ)^4975
        have hw : |(135265199/250000000 : ℝ)|=(135265199/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_box_2 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192727191/10000000000 : ℝ)*x 0 + (5410608087/10000000000 : ℝ)*x 1 + (-547451177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192727191/10000000000 : ℝ)^5999 ≤ (45374892283477/100000000000000 : ℝ)^4975 := by
    have hnat : (5192727191 : ℕ)^5999*100000000000000^4975 ≤ 45374892283477^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192727191 10000000000 45374892283477 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410608087/10000000000 : ℝ)^5999 ≤ (11920112492493/25000000000000 : ℝ)^4975 := by
    have hnat : (5410608087 : ℕ)^5999*25000000000000^4975 ≤ 11920112492493^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410608087 10000000000 11920112492493 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547451177/5000000000 : ℝ)^5999 ≤ (1736164433701/25000000000000 : ℝ)^4975 := by
    have hnat : (547451177 : ℕ)^5999*25000000000000^4975 ≤ 1736164433701^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547451177 5000000000 1736164433701 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192727191/10000000000 : ℝ), (5410608087/10000000000 : ℝ), (-547451177/5000000000 : ℝ)] ![(45374892283477/100000000000000 : ℝ), (11920112492493/25000000000000 : ℝ), (1736164433701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192727191/10000000000 : ℝ)|^5999 ≤ (45374892283477/100000000000000 : ℝ)^4975
        have hw : |(5192727191/10000000000 : ℝ)|=(5192727191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410608087/10000000000 : ℝ)|^5999 ≤ (11920112492493/25000000000000 : ℝ)^4975
        have hw : |(5410608087/10000000000 : ℝ)|=(5410608087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-547451177/5000000000 : ℝ)|^5999 ≤ (1736164433701/25000000000000 : ℝ)^4975
        have hw : |(-547451177/5000000000 : ℝ)|=(547451177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_box_3 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4517140481/10000000000 : ℝ)*x 0 + (3768030351/10000000000 : ℝ)*x 1 + (117750921/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4517140481/10000000000 : ℝ)^5999 ≤ (38355218942761/100000000000000 : ℝ)^4975 := by
    have hnat : (4517140481 : ℕ)^5999*100000000000000^4975 ≤ 38355218942761^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517140481 10000000000 38355218942761 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3768030351/10000000000 : ℝ)^5999 ≤ (30822394859719/100000000000000 : ℝ)^4975 := by
    have hnat : (3768030351 : ℕ)^5999*100000000000000^4975 ≤ 30822394859719^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3768030351 10000000000 30822394859719 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117750921/312500000 : ℝ)^5999 ≤ (120399946053/390625000000 : ℝ)^4975 := by
    have hnat : (117750921 : ℕ)^5999*390625000000^4975 ≤ 120399946053^4975*312500000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117750921 312500000 120399946053 390625000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4517140481/10000000000 : ℝ), (3768030351/10000000000 : ℝ), (117750921/312500000 : ℝ)] ![(38355218942761/100000000000000 : ℝ), (30822394859719/100000000000000 : ℝ), (120399946053/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4517140481/10000000000 : ℝ)|^5999 ≤ (38355218942761/100000000000000 : ℝ)^4975
        have hw : |(4517140481/10000000000 : ℝ)|=(4517140481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3768030351/10000000000 : ℝ)|^5999 ≤ (30822394859719/100000000000000 : ℝ)^4975
        have hw : |(3768030351/10000000000 : ℝ)|=(3768030351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(117750921/312500000 : ℝ)|^5999 ≤ (120399946053/390625000000 : ℝ)^4975
        have hw : |(117750921/312500000 : ℝ)|=(117750921/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_box_4 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-387997039/2500000000 : ℝ)*x 0 + (1282425909/2500000000 : ℝ)*x 1 + (5129702547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (387997039/2500000000 : ℝ)^5999 ≤ (5288343517397/50000000000000 : ℝ)^4975 := by
    have hnat : (387997039 : ℕ)^5999*50000000000000^4975 ≤ 5288343517397^4975*2500000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387997039 2500000000 5288343517397 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282425909/2500000000 : ℝ)^5999 ≤ (44711662196651/100000000000000 : ℝ)^4975 := by
    have hnat : (1282425909 : ℕ)^5999*100000000000000^4975 ≤ 44711662196651^4975*2500000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282425909 2500000000 44711662196651 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129702547/10000000000 : ℝ)^5999 ≤ (8942330150191/20000000000000 : ℝ)^4975 := by
    have hnat : (5129702547 : ℕ)^5999*20000000000000^4975 ≤ 8942330150191^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129702547 10000000000 8942330150191 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-387997039/2500000000 : ℝ), (1282425909/2500000000 : ℝ), (5129702547/10000000000 : ℝ)] ![(5288343517397/50000000000000 : ℝ), (44711662196651/100000000000000 : ℝ), (8942330150191/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-387997039/2500000000 : ℝ)|^5999 ≤ (5288343517397/50000000000000 : ℝ)^4975
        have hw : |(-387997039/2500000000 : ℝ)|=(387997039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1282425909/2500000000 : ℝ)|^5999 ≤ (44711662196651/100000000000000 : ℝ)^4975
        have hw : |(1282425909/2500000000 : ℝ)|=(1282425909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129702547/10000000000 : ℝ)|^5999 ≤ (8942330150191/20000000000000 : ℝ)^4975
        have hw : |(5129702547/10000000000 : ℝ)|=(5129702547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_box_5 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344921733/2500000000 : ℝ)*x 0 + (-1223057401/10000000000 : ℝ)*x 1 + (641212877/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344921733/2500000000 : ℝ)^5999 ≤ (47352067579161/100000000000000 : ℝ)^4975 := by
    have hnat : (1344921733 : ℕ)^5999*100000000000000^4975 ≤ 47352067579161^4975*2500000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344921733 2500000000 47352067579161 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1223057401/10000000000 : ℝ)^5999 ≤ (3968138363271/50000000000000 : ℝ)^4975 := by
    have hnat : (1223057401 : ℕ)^5999*50000000000000^4975 ≤ 3968138363271^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223057401 10000000000 3968138363271 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (641212877/1250000000 : ℝ)^5999 ≤ (44711655680277/100000000000000 : ℝ)^4975 := by
    have hnat : (641212877 : ℕ)^5999*100000000000000^4975 ≤ 44711655680277^4975*1250000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641212877 1250000000 44711655680277 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344921733/2500000000 : ℝ), (-1223057401/10000000000 : ℝ), (641212877/1250000000 : ℝ)] ![(47352067579161/100000000000000 : ℝ), (3968138363271/50000000000000 : ℝ), (44711655680277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344921733/2500000000 : ℝ)|^5999 ≤ (47352067579161/100000000000000 : ℝ)^4975
        have hw : |(1344921733/2500000000 : ℝ)|=(1344921733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1223057401/10000000000 : ℝ)|^5999 ≤ (3968138363271/50000000000000 : ℝ)^4975
        have hw : |(-1223057401/10000000000 : ℝ)|=(1223057401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(641212877/1250000000 : ℝ)|^5999 ≤ (44711655680277/100000000000000 : ℝ)^4975
        have hw : |(641212877/1250000000 : ℝ)|=(641212877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_box_6 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689843079/5000000000 : ℝ)*x 0 + (2564851939/5000000000 : ℝ)*x 1 + (-611528647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689843079/5000000000 : ℝ)^5999 ≤ (47352059364141/100000000000000 : ℝ)^4975 := by
    have hnat : (2689843079 : ℕ)^5999*100000000000000^4975 ≤ 47352059364141^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689843079 5000000000 47352059364141 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564851939/5000000000 : ℝ)^5999 ≤ (44711664740139/100000000000000 : ℝ)^4975 := by
    have hnat : (2564851939 : ℕ)^5999*100000000000000^4975 ≤ 44711664740139^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564851939 5000000000 44711664740139 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (611528647/5000000000 : ℝ)^5999 ≤ (3968137944661/50000000000000 : ℝ)^4975 := by
    have hnat : (611528647 : ℕ)^5999*50000000000000^4975 ≤ 3968137944661^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611528647 5000000000 3968137944661 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689843079/5000000000 : ℝ), (2564851939/5000000000 : ℝ), (-611528647/5000000000 : ℝ)] ![(47352059364141/100000000000000 : ℝ), (44711664740139/100000000000000 : ℝ), (3968137944661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689843079/5000000000 : ℝ)|^5999 ≤ (47352059364141/100000000000000 : ℝ)^4975
        have hw : |(2689843079/5000000000 : ℝ)|=(2689843079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564851939/5000000000 : ℝ)|^5999 ≤ (44711664740139/100000000000000 : ℝ)^4975
        have hw : |(2564851939/5000000000 : ℝ)|=(2564851939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-611528647/5000000000 : ℝ)|^5999 ≤ (3968137944661/50000000000000 : ℝ)^4975
        have hw : |(-611528647/5000000000 : ℝ)|=(611528647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_box_7 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (428700669/1250000000 : ℝ)*x 0 + (861951839/2000000000 : ℝ)*x 1 + (1077439503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428700669/1250000000 : ℝ)^5999 ≤ (3439488496699/12500000000000 : ℝ)^4975 := by
    have hnat : (428700669 : ℕ)^5999*12500000000000^4975 ≤ 3439488496699^4975*1250000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428700669 1250000000 3439488496699 12500000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (861951839/2000000000 : ℝ)^5999 ≤ (36242052003273/100000000000000 : ℝ)^4975 := by
    have hnat : (861951839 : ℕ)^5999*100000000000000^4975 ≤ 36242052003273^4975*2000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861951839 2000000000 36242052003273 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077439503/2500000000 : ℝ)^5999 ≤ (9060510001861/25000000000000 : ℝ)^4975 := by
    have hnat : (1077439503 : ℕ)^5999*25000000000000^4975 ≤ 9060510001861^4975*2500000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077439503 2500000000 9060510001861 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(428700669/1250000000 : ℝ), (861951839/2000000000 : ℝ), (1077439503/2500000000 : ℝ)] ![(3439488496699/12500000000000 : ℝ), (36242052003273/100000000000000 : ℝ), (9060510001861/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(428700669/1250000000 : ℝ)|^5999 ≤ (3439488496699/12500000000000 : ℝ)^4975
        have hw : |(428700669/1250000000 : ℝ)|=(428700669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(861951839/2000000000 : ℝ)|^5999 ≤ (36242052003273/100000000000000 : ℝ)^4975
        have hw : |(861951839/2000000000 : ℝ)|=(861951839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077439503/2500000000 : ℝ)|^5999 ≤ (9060510001861/25000000000000 : ℝ)^4975
        have hw : |(1077439503/2500000000 : ℝ)|=(1077439503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_box_8 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-43267607/312500000 : ℝ)*x 0 + (4914464873/10000000000 : ℝ)*x 1 + (5471109769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43267607/312500000 : ℝ)^5999 ≤ (4608292291787/50000000000000 : ℝ)^4975 := by
    have hnat : (43267607 : ℕ)^5999*50000000000000^4975 ≤ 4608292291787^4975*312500000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43267607 312500000 4608292291787 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4914464873/10000000000 : ℝ)^5999 ≤ (42459321736381/100000000000000 : ℝ)^4975 := by
    have hnat : (4914464873 : ℕ)^5999*100000000000000^4975 ≤ 42459321736381^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4914464873 10000000000 42459321736381 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471109769/10000000000 : ℝ)^5999 ≤ (4832409366583/10000000000000 : ℝ)^4975 := by
    have hnat : (5471109769 : ℕ)^5999*10000000000000^4975 ≤ 4832409366583^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471109769 10000000000 4832409366583 10000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43267607/312500000 : ℝ), (4914464873/10000000000 : ℝ), (5471109769/10000000000 : ℝ)] ![(4608292291787/50000000000000 : ℝ), (42459321736381/100000000000000 : ℝ), (4832409366583/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43267607/312500000 : ℝ)|^5999 ≤ (4608292291787/50000000000000 : ℝ)^4975
        have hw : |(-43267607/312500000 : ℝ)|=(43267607/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4914464873/10000000000 : ℝ)|^5999 ≤ (42459321736381/100000000000000 : ℝ)^4975
        have hw : |(4914464873/10000000000 : ℝ)|=(4914464873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471109769/10000000000 : ℝ)|^5999 ≤ (4832409366583/10000000000000 : ℝ)^4975
        have hw : |(5471109769/10000000000 : ℝ)|=(5471109769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_box_9 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152537641/10000000000 : ℝ)*x 0 + (-532995627/5000000000 : ℝ)*x 1 + (5471109631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152537641/10000000000 : ℝ)^5999 ≤ (899035276253/2000000000000 : ℝ)^4975 := by
    have hnat : (5152537641 : ℕ)^5999*2000000000000^4975 ≤ 899035276253^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152537641 10000000000 899035276253 2000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532995627/5000000000 : ℝ)^5999 ≤ (3362071989603/50000000000000 : ℝ)^4975 := by
    have hnat : (532995627 : ℕ)^5999*50000000000000^4975 ≤ 3362071989603^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532995627 5000000000 3362071989603 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471109631/10000000000 : ℝ)^5999 ≤ (3020255762253/6250000000000 : ℝ)^4975 := by
    have hnat : (5471109631 : ℕ)^5999*6250000000000^4975 ≤ 3020255762253^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471109631 10000000000 3020255762253 6250000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152537641/10000000000 : ℝ), (-532995627/5000000000 : ℝ), (5471109631/10000000000 : ℝ)] ![(899035276253/2000000000000 : ℝ), (3362071989603/50000000000000 : ℝ), (3020255762253/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152537641/10000000000 : ℝ)|^5999 ≤ (899035276253/2000000000000 : ℝ)^4975
        have hw : |(5152537641/10000000000 : ℝ)|=(5152537641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-532995627/5000000000 : ℝ)|^5999 ≤ (3362071989603/50000000000000 : ℝ)^4975
        have hw : |(-532995627/5000000000 : ℝ)|=(532995627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471109631/10000000000 : ℝ)|^5999 ≤ (3020255762253/6250000000000 : ℝ)^4975
        have hw : |(5471109631/10000000000 : ℝ)|=(5471109631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_box_10 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152537627/10000000000 : ℝ)*x 0 + (5471109403/10000000000 : ℝ)*x 1 + (-1065991593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152537627/10000000000 : ℝ)^5999 ≤ (11237940916343/25000000000000 : ℝ)^4975 := by
    have hnat : (5152537627 : ℕ)^5999*25000000000000^4975 ≤ 11237940916343^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152537627 10000000000 11237940916343 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471109403/10000000000 : ℝ)^5999 ≤ (48324089767711/100000000000000 : ℝ)^4975 := by
    have hnat : (5471109403 : ℕ)^5999*100000000000000^4975 ≤ 48324089767711^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471109403 10000000000 48324089767711 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065991593/10000000000 : ℝ)^5999 ≤ (6724146557717/100000000000000 : ℝ)^4975 := by
    have hnat : (1065991593 : ℕ)^5999*100000000000000^4975 ≤ 6724146557717^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065991593 10000000000 6724146557717 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152537627/10000000000 : ℝ), (5471109403/10000000000 : ℝ), (-1065991593/10000000000 : ℝ)] ![(11237940916343/25000000000000 : ℝ), (48324089767711/100000000000000 : ℝ), (6724146557717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152537627/10000000000 : ℝ)|^5999 ≤ (11237940916343/25000000000000 : ℝ)^4975
        have hw : |(5152537627/10000000000 : ℝ)|=(5152537627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471109403/10000000000 : ℝ)|^5999 ≤ (48324089767711/100000000000000 : ℝ)^4975
        have hw : |(5471109403/10000000000 : ℝ)|=(5471109403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1065991593/10000000000 : ℝ)|^5999 ≤ (6724146557717/100000000000000 : ℝ)^4975
        have hw : |(-1065991593/10000000000 : ℝ)|=(1065991593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_box_11 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2370465599/5000000000 : ℝ)*x 0 + (3650916681/10000000000 : ℝ)*x 1 + (3650917523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2370465599/5000000000 : ℝ)^5999 ≤ (40658087416323/100000000000000 : ℝ)^4975 := by
    have hnat : (2370465599 : ℕ)^5999*100000000000000^4975 ≤ 40658087416323^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2370465599 5000000000 40658087416323 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3650916681/10000000000 : ℝ)^5999 ≤ (5934190431061/20000000000000 : ℝ)^4975 := by
    have hnat : (3650916681 : ℕ)^5999*20000000000000^4975 ≤ 5934190431061^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3650916681 10000000000 5934190431061 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3650917523/10000000000 : ℝ)^5999 ≤ (29670960406701/100000000000000 : ℝ)^4975 := by
    have hnat : (3650917523 : ℕ)^5999*100000000000000^4975 ≤ 29670960406701^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3650917523 10000000000 29670960406701 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2370465599/5000000000 : ℝ), (3650916681/10000000000 : ℝ), (3650917523/10000000000 : ℝ)] ![(40658087416323/100000000000000 : ℝ), (5934190431061/20000000000000 : ℝ), (29670960406701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2370465599/5000000000 : ℝ)|^5999 ≤ (40658087416323/100000000000000 : ℝ)^4975
        have hw : |(2370465599/5000000000 : ℝ)|=(2370465599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3650916681/10000000000 : ℝ)|^5999 ≤ (5934190431061/20000000000000 : ℝ)^4975
        have hw : |(3650916681/10000000000 : ℝ)|=(3650916681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3650917523/10000000000 : ℝ)|^5999 ≤ (29670960406701/100000000000000 : ℝ)^4975
        have hw : |(3650917523/10000000000 : ℝ)|=(3650917523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_box_12 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-936545067/10000000000 : ℝ)*x 0 + (5613747233/10000000000 : ℝ)*x 1 + (5100072199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (936545067/10000000000 : ℝ)^5999 ≤ (2876135296999/50000000000000 : ℝ)^4975 := by
    have hnat : (936545067 : ℕ)^5999*50000000000000^4975 ≤ 2876135296999^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936545067 10000000000 2876135296999 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5613747233/10000000000 : ℝ)^5999 ≤ (49847316483651/100000000000000 : ℝ)^4975 := by
    have hnat : (5613747233 : ℕ)^5999*100000000000000^4975 ≤ 49847316483651^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5613747233 10000000000 49847316483651 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5100072199/10000000000 : ℝ)^5999 ≤ (44400412900043/100000000000000 : ℝ)^4975 := by
    have hnat : (5100072199 : ℕ)^5999*100000000000000^4975 ≤ 44400412900043^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5100072199 10000000000 44400412900043 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-936545067/10000000000 : ℝ), (5613747233/10000000000 : ℝ), (5100072199/10000000000 : ℝ)] ![(2876135296999/50000000000000 : ℝ), (49847316483651/100000000000000 : ℝ), (44400412900043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-936545067/10000000000 : ℝ)|^5999 ≤ (2876135296999/50000000000000 : ℝ)^4975
        have hw : |(-936545067/10000000000 : ℝ)|=(936545067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5613747233/10000000000 : ℝ)|^5999 ≤ (49847316483651/100000000000000 : ℝ)^4975
        have hw : |(5613747233/10000000000 : ℝ)|=(5613747233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5100072199/10000000000 : ℝ)|^5999 ≤ (44400412900043/100000000000000 : ℝ)^4975
        have hw : |(5100072199/10000000000 : ℝ)|=(5100072199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_box_13 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5399483941/10000000000 : ℝ)*x 0 + (-1235957691/10000000000 : ℝ)*x 1 + (1275017953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5399483941/10000000000 : ℝ)^5999 ≤ (9512453406933/20000000000000 : ℝ)^4975 := by
    have hnat : (5399483941 : ℕ)^5999*20000000000000^4975 ≤ 9512453406933^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399483941 10000000000 9512453406933 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1235957691/10000000000 : ℝ)^5999 ≤ (8037324110591/100000000000000 : ℝ)^4975 := by
    have hnat : (1235957691 : ℕ)^5999*100000000000000^4975 ≤ 8037324110591^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235957691 10000000000 8037324110591 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1275017953/2500000000 : ℝ)^5999 ≤ (11100102209353/25000000000000 : ℝ)^4975 := by
    have hnat : (1275017953 : ℕ)^5999*25000000000000^4975 ≤ 11100102209353^4975*2500000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275017953 2500000000 11100102209353 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5399483941/10000000000 : ℝ), (-1235957691/10000000000 : ℝ), (1275017953/2500000000 : ℝ)] ![(9512453406933/20000000000000 : ℝ), (8037324110591/100000000000000 : ℝ), (11100102209353/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5399483941/10000000000 : ℝ)|^5999 ≤ (9512453406933/20000000000000 : ℝ)^4975
        have hw : |(5399483941/10000000000 : ℝ)|=(5399483941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1235957691/10000000000 : ℝ)|^5999 ≤ (8037324110591/100000000000000 : ℝ)^4975
        have hw : |(-1235957691/10000000000 : ℝ)|=(1235957691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1275017953/2500000000 : ℝ)|^5999 ≤ (11100102209353/25000000000000 : ℝ)^4975
        have hw : |(1275017953/2500000000 : ℝ)|=(1275017953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_box_14 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079896721/2000000000 : ℝ)*x 0 + (1020014221/2000000000 : ℝ)*x 1 + (-308989773/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079896721/2000000000 : ℝ)^5999 ≤ (47562263465757/100000000000000 : ℝ)^4975 := by
    have hnat : (1079896721 : ℕ)^5999*100000000000000^4975 ≤ 47562263465757^4975*2000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079896721 2000000000 47562263465757 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1020014221/2000000000 : ℝ)^5999 ≤ (44400401415499/100000000000000 : ℝ)^4975 := by
    have hnat : (1020014221 : ℕ)^5999*100000000000000^4975 ≤ 44400401415499^4975*2000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020014221 2000000000 44400401415499 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (308989773/2500000000 : ℝ)^5999 ≤ (1607467019279/20000000000000 : ℝ)^4975 := by
    have hnat : (308989773 : ℕ)^5999*20000000000000^4975 ≤ 1607467019279^4975*2500000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308989773 2500000000 1607467019279 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079896721/2000000000 : ℝ), (1020014221/2000000000 : ℝ), (-308989773/2500000000 : ℝ)] ![(47562263465757/100000000000000 : ℝ), (44400401415499/100000000000000 : ℝ), (1607467019279/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079896721/2000000000 : ℝ)|^5999 ≤ (47562263465757/100000000000000 : ℝ)^4975
        have hw : |(1079896721/2000000000 : ℝ)|=(1079896721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1020014221/2000000000 : ℝ)|^5999 ≤ (44400401415499/100000000000000 : ℝ)^4975
        have hw : |(1020014221/2000000000 : ℝ)|=(1020014221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-308989773/2500000000 : ℝ)|^5999 ≤ (1607467019279/20000000000000 : ℝ)^4975
        have hw : |(-308989773/2500000000 : ℝ)|=(308989773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_box_15 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3309703133/10000000000 : ℝ)*x 0 + (873333801/2000000000 : ℝ)*x 1 + (873334723/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3309703133/10000000000 : ℝ)^5999 ≤ (13180067484951/50000000000000 : ℝ)^4975 := by
    have hnat : (3309703133 : ℕ)^5999*50000000000000^4975 ≤ 13180067484951^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3309703133 10000000000 13180067484951 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (873333801/2000000000 : ℝ)^5999 ≤ (36819909075237/100000000000000 : ℝ)^4975 := by
    have hnat : (873333801 : ℕ)^5999*100000000000000^4975 ≤ 36819909075237^4975*2000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873333801 2000000000 36819909075237 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (873334723/2000000000 : ℝ)^5999 ≤ (9204988986963/25000000000000 : ℝ)^4975 := by
    have hnat : (873334723 : ℕ)^5999*25000000000000^4975 ≤ 9204988986963^4975*2000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873334723 2000000000 9204988986963 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3309703133/10000000000 : ℝ), (873333801/2000000000 : ℝ), (873334723/2000000000 : ℝ)] ![(13180067484951/50000000000000 : ℝ), (36819909075237/100000000000000 : ℝ), (9204988986963/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3309703133/10000000000 : ℝ)|^5999 ≤ (13180067484951/50000000000000 : ℝ)^4975
        have hw : |(3309703133/10000000000 : ℝ)|=(3309703133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(873333801/2000000000 : ℝ)|^5999 ≤ (36819909075237/100000000000000 : ℝ)^4975
        have hw : |(873333801/2000000000 : ℝ)|=(873333801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(873334723/2000000000 : ℝ)|^5999 ≤ (9204988986963/25000000000000 : ℝ)^4975
        have hw : |(873334723/2000000000 : ℝ)|=(873334723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1764_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44738407/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8853/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(69189/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11759/20000 : ℝ) ∧ (41171/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2911/3125 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8853/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2299/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8853/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2299/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8853/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2299/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8853/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2299/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8853/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2299/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8853/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2299/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2299/25000 : ℝ) ^ (5983/1024 : ℝ) ≤ (4400616799921/5000000000000000000 : ℝ) := by
    have hpowers : (2299/25000 : ℝ)^5983 ≤ (4400616799921/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2299 : ℕ)^5983*5000000000000000000^1024 ≤ 4400616799921^1024*25000^5983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2299 25000 4400616799921 5000000000000000000 5983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2299/25000 : ℝ)) (X := (4400616799921/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8853/50000 : ℝ) ^ (5983/1024 : ℝ) ≤ (2022591599529/50000000000000000 : ℝ) := by
    have hpowers : (8853/50000 : ℝ)^5983 ≤ (2022591599529/50000000000000000 : ℝ)^1024 := by
      have hnat : (8853 : ℕ)^5983*50000000000000000^1024 ≤ 2022591599529^1024*50000^5983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8853 50000 2022591599529 50000000000000000 5983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8853/50000 : ℝ)) (X := (2022591599529/50000000000000000 : ℝ)) (by norm_num) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500004400616799921/2500000000000000000 : ℝ) ≤ (10000003012688161/10000000000000000 : ℝ) ^ (5983/1024 : ℝ) := by
    have hpowers : (2500004400616799921/2500000000000000000 : ℝ)^1024 ≤ (10000003012688161/10000000000000000 : ℝ)^5983 := by
      have hnat : (2500004400616799921 : ℕ)^1024*10000000000000000^5983 ≤ 10000003012688161^5983*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500004400616799921 2500000000000000000 10000003012688161 10000000000000000 1024 5983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000003012688161/10000000000000000 : ℝ)) (X := (2500004400616799921/2500000000000000000 : ℝ)) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5000206659776752821/5000000000000000000 : ℝ) ≤ (5000035369544821/5000000000000000 : ℝ) ^ (5983/1024 : ℝ) := by
    have hpowers : (5000206659776752821/5000000000000000000 : ℝ)^1024 ≤ (5000035369544821/5000000000000000 : ℝ)^5983 := by
      have hnat : (5000206659776752821 : ℕ)^1024*5000000000000000^5983 ≤ 5000035369544821^5983*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000206659776752821 5000000000000000000 5000035369544821 5000000000000000 1024 5983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000035369544821/5000000000000000 : ℝ)) (X := (5000206659776752821/5000000000000000000 : ℝ)) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25002022591599529/25000000000000000 : ℝ) ≤ (10000138465491123/10000000000000000 : ℝ) ^ (5983/1024 : ℝ) := by
    have hpowers : (25002022591599529/25000000000000000 : ℝ)^1024 ≤ (10000138465491123/10000000000000000 : ℝ)^5983 := by
      have hnat : (25002022591599529 : ℕ)^1024*10000000000000000^5983 ≤ 10000138465491123^5983*25000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002022591599529 25000000000000000 10000138465491123 10000000000000000 1024 5983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000138465491123/10000000000000000 : ℝ)) (X := (25002022591599529/25000000000000000 : ℝ)) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4400616799921/5000000000000000000 : ℝ) ≤ ((42549390007000105779/42550000000000000000 : ℝ)+2*(67726401481/851000000000000 : ℝ)*(2299/25000 : ℝ))^(5983/1024 : ℝ) := by
    rw [show (42549390007000105779/42550000000000000000 : ℝ)+2*(67726401481/851000000000000 : ℝ)*(2299/25000 : ℝ)=(10000003012688161/10000000000000000 : ℝ) by norm_num, show 1+2*(4400616799921/5000000000000000000 : ℝ)=(2500004400616799921/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2022591599529/50000000000000000 : ℝ)+(4400616799921/5000000000000000000 : ℝ) ≤ ((42549390007000105779/42550000000000000000 : ℝ)+(67726401481/851000000000000 : ℝ)*((8853/50000 : ℝ)+(2299/25000 : ℝ)))^(5983/1024 : ℝ) := by
    rw [show (42549390007000105779/42550000000000000000 : ℝ)+(67726401481/851000000000000 : ℝ)*((8853/50000 : ℝ)+(2299/25000 : ℝ))=(5000035369544821/5000000000000000 : ℝ) by norm_num, show 1+(2022591599529/50000000000000000 : ℝ)+(4400616799921/5000000000000000000 : ℝ)=(5000206659776752821/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2022591599529/50000000000000000 : ℝ) ≤ ((42549390007000105779/42550000000000000000 : ℝ)+2*(67726401481/851000000000000 : ℝ)*(8853/50000 : ℝ))^(5983/1024 : ℝ) := by
    rw [show (42549390007000105779/42550000000000000000 : ℝ)+2*(67726401481/851000000000000 : ℝ)*(8853/50000 : ℝ)=(10000138465491123/10000000000000000 : ℝ) by norm_num, show 1+2*(2022591599529/50000000000000000 : ℝ)=(25002022591599529/25000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (42549390007000105779/42550000000000000000 : ℝ)*(X 1 0+X 2 0)+(67726401481/851000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5983/1024 : ℝ)) (lo := (2299/25000 : ℝ)) (hi := (8853/50000 : ℝ)) (c := (42549390007000105779/42550000000000000000 : ℝ)) (alpha := (67726401481/851000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (42549390007000105779/42550000000000000000 : ℝ)*(X 0 1+X 2 1)+(67726401481/851000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5983/1024 : ℝ)) (lo := (2299/25000 : ℝ)) (hi := (8853/50000 : ℝ)) (c := (42549390007000105779/42550000000000000000 : ℝ)) (alpha := (67726401481/851000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (42549390007000105779/42550000000000000000 : ℝ)*(X 0 2+X 1 2)+(67726401481/851000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5983/1024 : ℝ)) (lo := (2299/25000 : ℝ)) (hi := (8853/50000 : ℝ)) (c := (42549390007000105779/42550000000000000000 : ℝ)) (alpha := (67726401481/851000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-783551211/10000000000 : ℝ)*X 0 0+(1082121579/2000000000 : ℝ)*X 0 1+(1082121559/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2596363707/5000000000 : ℝ)*X 1 0+(-1094902223/10000000000 : ℝ)*X 1 1+(135265199/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5192727191/10000000000 : ℝ)*X 2 0+(5410608087/10000000000 : ℝ)*X 2 1+(-547451177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4517140481/10000000000 : ℝ)*X 0 0+(3768030351/10000000000 : ℝ)*X 0 1+(117750921/312500000 : ℝ)*X 0 2+(4517140481/10000000000 : ℝ)*X 1 0+(3768030351/10000000000 : ℝ)*X 1 1+(117750921/312500000 : ℝ)*X 1 2+(4517140481/10000000000 : ℝ)*X 2 0+(3768030351/10000000000 : ℝ)*X 2 1+(117750921/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-387997039/2500000000 : ℝ)*X 0 0+(1282425909/2500000000 : ℝ)*X 0 1+(5129702547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1344921733/2500000000 : ℝ)*X 1 0+(-1223057401/10000000000 : ℝ)*X 1 1+(641212877/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2689843079/5000000000 : ℝ)*X 2 0+(2564851939/5000000000 : ℝ)*X 2 1+(-611528647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((428700669/1250000000 : ℝ)*X 0 0+(861951839/2000000000 : ℝ)*X 0 1+(1077439503/2500000000 : ℝ)*X 0 2+(428700669/1250000000 : ℝ)*X 1 0+(861951839/2000000000 : ℝ)*X 1 1+(1077439503/2500000000 : ℝ)*X 1 2+(428700669/1250000000 : ℝ)*X 2 0+(861951839/2000000000 : ℝ)*X 2 1+(1077439503/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-43267607/312500000 : ℝ)*X 0 0+(4914464873/10000000000 : ℝ)*X 0 1+(5471109769/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5152537641/10000000000 : ℝ)*X 1 0+(-532995627/5000000000 : ℝ)*X 1 1+(5471109631/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5152537627/10000000000 : ℝ)*X 2 0+(5471109403/10000000000 : ℝ)*X 2 1+(-1065991593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2370465599/5000000000 : ℝ)*X 0 0+(3650916681/10000000000 : ℝ)*X 0 1+(3650917523/10000000000 : ℝ)*X 0 2+(2370465599/5000000000 : ℝ)*X 1 0+(3650916681/10000000000 : ℝ)*X 1 1+(3650917523/10000000000 : ℝ)*X 1 2+(2370465599/5000000000 : ℝ)*X 2 0+(3650916681/10000000000 : ℝ)*X 2 1+(3650917523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-936545067/10000000000 : ℝ)*X 0 0+(5613747233/10000000000 : ℝ)*X 0 1+(5100072199/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5399483941/10000000000 : ℝ)*X 1 0+(-1235957691/10000000000 : ℝ)*X 1 1+(1275017953/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1079896721/2000000000 : ℝ)*X 2 0+(1020014221/2000000000 : ℝ)*X 2 1+(-308989773/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3309703133/10000000000 : ℝ)*X 0 0+(873333801/2000000000 : ℝ)*X 0 1+(873334723/2000000000 : ℝ)*X 0 2+(3309703133/10000000000 : ℝ)*X 1 0+(873333801/2000000000 : ℝ)*X 1 1+(873334723/2000000000 : ℝ)*X 1 2+(3309703133/10000000000 : ℝ)*X 2 0+(873333801/2000000000 : ℝ)*X 2 1+(873334723/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-69189/100000 : ℝ) ≤ (-735974279795904383668535668767027/1063750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101758093/100000000000000 : ℝ)*(upper3) + (9545569/100000000000000 : ℝ)*(lower4) + (10297289/50000000000000 : ℝ)*(lower5) + (548730557555371/50000000000000 : ℝ)*(major0) + (548730557555371/50000000000000 : ℝ)*(major1) + (548730557555371/50000000000000 : ℝ)*(major2) + (2987577803/100000000000000 : ℝ)*(sp1) + (134528559/100000000000000 : ℝ)*(sp3) + (1727370123436459/100000000000000 : ℝ)*(sp4) + (863684493190799/50000000000000 : ℝ)*(sp5) + (863668737934679/50000000000000 : ℝ)*(sp6) + (61326547354551/12500000000000 : ℝ)*(sp7) + (925261471/50000000000000 : ℝ)*(sp8) + (34498090043/100000000000000 : ℝ)*(sp14) + (490612513364967/100000000000000 : ℝ)*(f.failure) + (1727371973959401/100000000000000 : ℝ)*(f.sum) + (6034766298187/10637500000000000000000000000 : ℝ)*base66 + (4038323928150360991/2127500000000000000000000000000000 : ℝ)*base68 + (12118280924959639009/2127500000000000000000000000000000 : ℝ)*base69 + (3086212818435360991/2127500000000000000000000000000000 : ℝ)*base72 + (90078647835599/21275000000000000000000000000 : ℝ)*base74 + (2844870148892139009/2127500000000000000000000000000000 : ℝ)*base75 + (2404177922437139009/2127500000000000000000000000000000 : ℝ)*base77 + (5621384413852139009/2127500000000000000000000000000000 : ℝ)*base79 + (25940934426051/21275000000000000000000000000 : ℝ)*base81 + (6812431/2000000000000000000000 : ℝ)*base90 + (6812431/2000000000000000000000 : ℝ)*base92 + (6812431/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11759/20000 : ℝ) ≤ (12509201780457149164408523241/21275000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9658009/50000000000000 : ℝ)*(lower0) + (6078417/50000000000000 : ℝ)*(upper1) + (4702549/20000000000000 : ℝ)*(upper2) + (10833527/25000000000000 : ℝ)*(upper3) + (2754781/25000000000000 : ℝ)*(lower5) + (614676116241071/50000000000000 : ℝ)*(major0) + (614676116241071/50000000000000 : ℝ)*(major1) + (614676116241071/50000000000000 : ℝ)*(major2) + (1889531706892433/100000000000000 : ℝ)*(sp0) + (1889531706892433/100000000000000 : ℝ)*(sp1) + (23619133884351/1250000000000 : ℝ)*(sp2) + (17174104573419/3125000000000 : ℝ)*(sp3) + (996144353/100000000000000 : ℝ)*(sp6) + (2192324931/100000000000000 : ℝ)*(sp11) + (549573538674339/100000000000000 : ℝ)*(f.failure) + (1889531706892433/100000000000000 : ℝ)*(f.sum) + (41958423890913/10637500000000000000000000000 : ℝ)*base65 + (8867543129036799309/2127500000000000000000000000000000 : ℝ)*base67 + (4236620729638200691/2127500000000000000000000000000000 : ℝ)*base70 + (281187885948200691/2127500000000000000000000000000000 : ℝ)*base72 + (24623817709651/21275000000000000000000000000 : ℝ)*base73 + (13555126821124299309/2127500000000000000000000000000000 : ℝ)*base75 + (2734009804071799309/2127500000000000000000000000000000 : ℝ)*base77 + (4310330922235700691/2127500000000000000000000000000000 : ℝ)*base80 + (21848430508863/10637500000000000000000000000 : ℝ)*base81 + (21362027/2000000000000000000000 : ℝ)*base90 + (21362027/2000000000000000000000 : ℝ)*base92 + (21362027/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (41171/50000 : ℝ) ≤ (1751882882922652198078321217848557/2127500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8930589/20000000000000 : ℝ)*(upper0) + (35933693/100000000000000 : ℝ)*(upper2) + (18652431/50000000000000 : ℝ)*(lower5) + (1174486504852313/100000000000000 : ℝ)*(major0) + (1174486504852313/100000000000000 : ℝ)*(major1) + (1174486504852313/100000000000000 : ℝ)*(major2) + (8315205731/100000000000000 : ℝ)*(sp1) + (716183013/50000000000000 : ℝ)*(sp3) + (178526699/12500000000000 : ℝ)*(sp4) + (1796476458824793/100000000000000 : ℝ)*(sp8) + (449117570430391/25000000000000 : ℝ)*(sp9) + (359295719385459/20000000000000 : ℝ)*(sp10) + (525044756628729/100000000000000 : ℝ)*(sp11) + (70988891/10000000000000 : ℝ)*(sp12) + (105009237798951/20000000000000 : ℝ)*(f.failure) + (359295719385459/20000000000000 : ℝ)*(f.sum) + (78552219915853/42550000000000000000000000000 : ℝ)*base65 + (40630118004020466827/4255000000000000000000000000000000 : ℝ)*base67 + (24336510907700466827/4255000000000000000000000000000000 : ℝ)*base69 + (6715216706020466827/4255000000000000000000000000000000 : ℝ)*base71 + (213956914355253/42550000000000000000000000000 : ℝ)*base73 + (10748309192885466827/4255000000000000000000000000000000 : ℝ)*base75 + (11541115132235466827/4255000000000000000000000000000000 : ℝ)*base77 + (21887047014250466827/4255000000000000000000000000000000 : ℝ)*base79 + (74994318974647/42550000000000000000000000000 : ℝ)*base82 + (2011057/400000000000000000000 : ℝ)*base89 + (2011057/400000000000000000000 : ℝ)*base91 + (2011057/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-2911/3125 : ℝ) ≤ (-465747374044346791532189853879/500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27144753/50000000000000 : ℝ)*(upper3) + (329274821/100000000000000 : ℝ)*(lower4) + (207715369/100000000000000 : ℝ)*(upper5) + (246718181030083/20000000000000 : ℝ)*(major0) + (246718181030083/20000000000000 : ℝ)*(major1) + (246718181030083/20000000000000 : ℝ)*(major2) + (5115702261/100000000000000 : ℝ)*(sp4) + (4886309949/10000000000000 : ℝ)*(sp5) + (7285745447/4000000000000 : ℝ)*(sp6) + (19653062541/50000000000000 : ℝ)*(sp7) + (243344763890831/12500000000000 : ℝ)*(sp12) + (973357181864709/50000000000000 : ℝ)*(sp13) + (973290541596367/50000000000000 : ℝ)*(sp14) + (551429102283119/100000000000000 : ℝ)*(sp15) + (2757342042041/500000000000 : ℝ)*(f.failure) + (1946763226828909/100000000000000 : ℝ)*(f.sum) + (49314301509/230000000000000000000000000 : ℝ)*base65 + (78392248161829739/23000000000000000000000000000000 : ℝ)*base68 + (10623629590829739/23000000000000000000000000000000 : ℝ)*base70 + (60542698526170261/23000000000000000000000000000000 : ℝ)*base71 + (974850789031/230000000000000000000000000 : ℝ)*base74 + (60220751058170261/23000000000000000000000000000000 : ℝ)*base75 + (123331967619829739/23000000000000000000000000000000 : ℝ)*base78 + (34008038181829739/23000000000000000000000000000000 : ℝ)*base80 + (411681513851/230000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (131313/10000000000000000000 : ℝ)*base90 + (131313/10000000000000000000 : ℝ)*base92 + (131313/10000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1764_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44738407/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8853/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(69189/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11759/20000 : ℝ) else (41171/50000 : ℝ) ≤ X j i ∧ X j i ≤ (2911/3125 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1764_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1764_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44738407/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8853/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1839/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(69189/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11759/20000 : ℝ) else (41171/50000 : ℝ) ≤ X j i ∧ X j i ≤ (2911/3125 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1764_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1764_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44738407/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8853/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1839/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(69189/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11759/20000 : ℝ) else (41171/50000 : ℝ) ≤ X j i ∧ X j i ≤ (2911/3125 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1764_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

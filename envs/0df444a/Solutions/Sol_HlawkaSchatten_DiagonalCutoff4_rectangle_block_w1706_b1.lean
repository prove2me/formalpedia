-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1706_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:49:58.360531+00:00
-- url     : https://prove2.me/submissions/bf3b5ed2-b28a-41a9-a2d0-7114cf0b9004

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
theorem support_rectangle_w1706_s3_0 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-356664629/2500000000 : ℝ)*x 0 + (1094519923/2000000000 : ℝ)*x 1 + (5137780481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (356664629/2500000000 : ℝ)^5271 ≤ (4460535290709/50000000000000 : ℝ)^4247 := by
    have hnat : (356664629 : ℕ)^5271*50000000000000^4247 ≤ 4460535290709^4247*2500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356664629 2500000000 4460535290709 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094519923/2000000000 : ℝ)^5271 ≤ (23661332452127/50000000000000 : ℝ)^4247 := by
    have hnat : (1094519923 : ℕ)^5271*50000000000000^4247 ≤ 23661332452127^4247*2000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094519923 2000000000 23661332452127 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137780481/10000000000 : ℝ)^5271 ≤ (10939066126581/25000000000000 : ℝ)^4247 := by
    have hnat : (5137780481 : ℕ)^5271*25000000000000^4247 ≤ 10939066126581^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137780481 10000000000 10939066126581 25000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-356664629/2500000000 : ℝ), (1094519923/2000000000 : ℝ), (5137780481/10000000000 : ℝ)] ![(4460535290709/50000000000000 : ℝ), (23661332452127/50000000000000 : ℝ), (10939066126581/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-356664629/2500000000 : ℝ)|^5271 ≤ (4460535290709/50000000000000 : ℝ)^4247
        have hw : |(-356664629/2500000000 : ℝ)|=(356664629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1094519923/2000000000 : ℝ)|^5271 ≤ (23661332452127/50000000000000 : ℝ)^4247
        have hw : |(1094519923/2000000000 : ℝ)|=(1094519923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137780481/10000000000 : ℝ)|^5271 ≤ (10939066126581/25000000000000 : ℝ)^4247
        have hw : |(5137780481/10000000000 : ℝ)|=(5137780481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s3_1 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336215159/2500000000 : ℝ)*x 0 + (-1600329533/10000000000 : ℝ)*x 1 + (513778051/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336215159/2500000000 : ℝ)^5271 ≤ (45955633179741/100000000000000 : ℝ)^4247 := by
    have hnat : (1336215159 : ℕ)^5271*100000000000000^4247 ≤ 45955633179741^4247*2500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336215159 2500000000 45955633179741 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1600329533/10000000000 : ℝ)^5271 ≤ (643006374107/6250000000000 : ℝ)^4247 := by
    have hnat : (1600329533 : ℕ)^5271*6250000000000^4247 ≤ 643006374107^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1600329533 10000000000 643006374107 6250000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513778051/1000000000 : ℝ)^5271 ≤ (8751252962571/20000000000000 : ℝ)^4247 := by
    have hnat : (513778051 : ℕ)^5271*20000000000000^4247 ≤ 8751252962571^4247*1000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513778051 1000000000 8751252962571 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336215159/2500000000 : ℝ), (-1600329533/10000000000 : ℝ), (513778051/1000000000 : ℝ)] ![(45955633179741/100000000000000 : ℝ), (643006374107/6250000000000 : ℝ), (8751252962571/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336215159/2500000000 : ℝ)|^5271 ≤ (45955633179741/100000000000000 : ℝ)^4247
        have hw : |(1336215159/2500000000 : ℝ)|=(1336215159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1600329533/10000000000 : ℝ)|^5271 ≤ (643006374107/6250000000000 : ℝ)^4247
        have hw : |(-1600329533/10000000000 : ℝ)|=(1600329533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513778051/1000000000 : ℝ)|^5271 ≤ (8751252962571/20000000000000 : ℝ)^4247
        have hw : |(513778051/1000000000 : ℝ)|=(513778051/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s3_2 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344860673/10000000000 : ℝ)*x 0 + (256889027/500000000 : ℝ)*x 1 + (-800164723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344860673/10000000000 : ℝ)^5271 ≤ (1838225342983/4000000000000 : ℝ)^4247 := by
    have hnat : (5344860673 : ℕ)^5271*4000000000000^4247 ≤ 1838225342983^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344860673 10000000000 1838225342983 4000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256889027/500000000 : ℝ)^5271 ≤ (8751253025991/20000000000000 : ℝ)^4247 := by
    have hnat : (256889027 : ℕ)^5271*20000000000000^4247 ≤ 8751253025991^4247*500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256889027 500000000 8751253025991 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (800164723/5000000000 : ℝ)^5271 ≤ (5144050645779/50000000000000 : ℝ)^4247 := by
    have hnat : (800164723 : ℕ)^5271*50000000000000^4247 ≤ 5144050645779^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800164723 5000000000 5144050645779 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344860673/10000000000 : ℝ), (256889027/500000000 : ℝ), (-800164723/5000000000 : ℝ)] ![(1838225342983/4000000000000 : ℝ), (8751253025991/20000000000000 : ℝ), (5144050645779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344860673/10000000000 : ℝ)|^5271 ≤ (1838225342983/4000000000000 : ℝ)^4247
        have hw : |(5344860673/10000000000 : ℝ)|=(5344860673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256889027/500000000 : ℝ)|^5271 ≤ (8751253025991/20000000000000 : ℝ)^4247
        have hw : |(256889027/500000000 : ℝ)|=(256889027/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-800164723/5000000000 : ℝ)|^5271 ≤ (5144050645779/50000000000000 : ℝ)^4247
        have hw : |(-800164723/5000000000 : ℝ)|=(800164723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s3_3 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4109875909/10000000000 : ℝ)*x 0 + (729386267/2000000000 : ℝ)*x 1 + (4608796467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4109875909/10000000000 : ℝ)^5271 ≤ (33167933899223/100000000000000 : ℝ)^4247 := by
    have hnat : (4109875909 : ℕ)^5271*100000000000000^4247 ≤ 33167933899223^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109875909 10000000000 33167933899223 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (729386267/2000000000 : ℝ)^5271 ≤ (28595872066477/100000000000000 : ℝ)^4247 := by
    have hnat : (729386267 : ℕ)^5271*100000000000000^4247 ≤ 28595872066477^4247*2000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729386267 2000000000 28595872066477 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4608796467/10000000000 : ℝ)^5271 ≤ (38236194022061/100000000000000 : ℝ)^4247 := by
    have hnat : (4608796467 : ℕ)^5271*100000000000000^4247 ≤ 38236194022061^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4608796467 10000000000 38236194022061 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4109875909/10000000000 : ℝ), (729386267/2000000000 : ℝ), (4608796467/10000000000 : ℝ)] ![(33167933899223/100000000000000 : ℝ), (28595872066477/100000000000000 : ℝ), (38236194022061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4109875909/10000000000 : ℝ)|^5271 ≤ (33167933899223/100000000000000 : ℝ)^4247
        have hw : |(4109875909/10000000000 : ℝ)|=(4109875909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(729386267/2000000000 : ℝ)|^5271 ≤ (28595872066477/100000000000000 : ℝ)^4247
        have hw : |(729386267/2000000000 : ℝ)|=(729386267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4608796467/10000000000 : ℝ)|^5271 ≤ (38236194022061/100000000000000 : ℝ)^4247
        have hw : |(4608796467/10000000000 : ℝ)|=(4608796467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s3_4 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1426810983/10000000000 : ℝ)*x 0 + (1285368881/2500000000 : ℝ)*x 1 + (5468849509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1426810983/10000000000 : ℝ)^5271 ≤ (4461126932921/50000000000000 : ℝ)^4247 := by
    have hnat : (1426810983 : ℕ)^5271*50000000000000^4247 ≤ 4461126932921^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426810983 10000000000 4461126932921 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285368881/2500000000 : ℝ)^5271 ≤ (43795324538113/100000000000000 : ℝ)^4247 := by
    have hnat : (1285368881 : ℕ)^5271*100000000000000^4247 ≤ 43795324538113^4247*2500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285368881 2500000000 43795324538113 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468849509/10000000000 : ℝ)^5271 ≤ (11820605393067/25000000000000 : ℝ)^4247 := by
    have hnat : (5468849509 : ℕ)^5271*25000000000000^4247 ≤ 11820605393067^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468849509 10000000000 11820605393067 25000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1426810983/10000000000 : ℝ), (1285368881/2500000000 : ℝ), (5468849509/10000000000 : ℝ)] ![(4461126932921/50000000000000 : ℝ), (43795324538113/100000000000000 : ℝ), (11820605393067/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1426810983/10000000000 : ℝ)|^5271 ≤ (4461126932921/50000000000000 : ℝ)^4247
        have hw : |(-1426810983/10000000000 : ℝ)|=(1426810983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1285368881/2500000000 : ℝ)|^5271 ≤ (43795324538113/100000000000000 : ℝ)^4247
        have hw : |(1285368881/2500000000 : ℝ)|=(1285368881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468849509/10000000000 : ℝ)|^5271 ≤ (11820605393067/25000000000000 : ℝ)^4247
        have hw : |(5468849509/10000000000 : ℝ)|=(5468849509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s3_5 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255250011/10000000000 : ℝ)*x 0 + (-253852107/2000000000 : ℝ)*x 1 + (2734424753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255250011/10000000000 : ℝ)^5271 ≤ (11250330405011/25000000000000 : ℝ)^4247 := by
    have hnat : (5255250011 : ℕ)^5271*25000000000000^4247 ≤ 11250330405011^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255250011 10000000000 11250330405011 25000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253852107/2000000000 : ℝ)^5271 ≤ (482266051429/6250000000000 : ℝ)^4247 := by
    have hnat : (253852107 : ℕ)^5271*6250000000000^4247 ≤ 482266051429^4247*2000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253852107 2000000000 482266051429 6250000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734424753/5000000000 : ℝ)^5271 ≤ (47282421540077/100000000000000 : ℝ)^4247 := by
    have hnat : (2734424753 : ℕ)^5271*100000000000000^4247 ≤ 47282421540077^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734424753 5000000000 47282421540077 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255250011/10000000000 : ℝ), (-253852107/2000000000 : ℝ), (2734424753/5000000000 : ℝ)] ![(11250330405011/25000000000000 : ℝ), (482266051429/6250000000000 : ℝ), (47282421540077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255250011/10000000000 : ℝ)|^5271 ≤ (11250330405011/25000000000000 : ℝ)^4247
        have hw : |(5255250011/10000000000 : ℝ)|=(5255250011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-253852107/2000000000 : ℝ)|^5271 ≤ (482266051429/6250000000000 : ℝ)^4247
        have hw : |(-253852107/2000000000 : ℝ)|=(253852107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734424753/5000000000 : ℝ)|^5271 ≤ (47282421540077/100000000000000 : ℝ)^4247
        have hw : |(2734424753/5000000000 : ℝ)|=(2734424753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s3_6 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627625007/5000000000 : ℝ)*x 0 + (1093769901/2000000000 : ℝ)*x 1 + (-317315133/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627625007/5000000000 : ℝ)^5271 ≤ (45001321651927/100000000000000 : ℝ)^4247 := by
    have hnat : (2627625007 : ℕ)^5271*100000000000000^4247 ≤ 45001321651927^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627625007 5000000000 45001321651927 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093769901/2000000000 : ℝ)^5271 ≤ (23641210764673/50000000000000 : ℝ)^4247 := by
    have hnat : (1093769901 : ℕ)^5271*50000000000000^4247 ≤ 23641210764673^4247*2000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093769901 2000000000 23641210764673 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317315133/2500000000 : ℝ)^5271 ≤ (7716256800229/100000000000000 : ℝ)^4247 := by
    have hnat : (317315133 : ℕ)^5271*100000000000000^4247 ≤ 7716256800229^4247*2500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317315133 2500000000 7716256800229 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627625007/5000000000 : ℝ), (1093769901/2000000000 : ℝ), (-317315133/2500000000 : ℝ)] ![(45001321651927/100000000000000 : ℝ), (23641210764673/50000000000000 : ℝ), (7716256800229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627625007/5000000000 : ℝ)|^5271 ≤ (45001321651927/100000000000000 : ℝ)^4247
        have hw : |(2627625007/5000000000 : ℝ)|=(2627625007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093769901/2000000000 : ℝ)|^5271 ≤ (23641210764673/50000000000000 : ℝ)^4247
        have hw : |(1093769901/2000000000 : ℝ)|=(1093769901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-317315133/2500000000 : ℝ)|^5271 ≤ (7716256800229/100000000000000 : ℝ)^4247
        have hw : |(-317315133/2500000000 : ℝ)|=(317315133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s3_7 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4110314101/10000000000 : ℝ)*x 0 + (2299090807/5000000000 : ℝ)*x 1 + (457213069/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4110314101/10000000000 : ℝ)^5271 ≤ (33172322948853/100000000000000 : ℝ)^4247 := by
    have hnat : (4110314101 : ℕ)^5271*100000000000000^4247 ≤ 33172322948853^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4110314101 10000000000 33172322948853 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2299090807/5000000000 : ℝ)^5271 ≤ (19063463237557/50000000000000 : ℝ)^4247 := by
    have hnat : (2299090807 : ℕ)^5271*50000000000000^4247 ≤ 19063463237557^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2299090807 5000000000 19063463237557 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (457213069/1250000000 : ℝ)^5271 ≤ (28700750560663/100000000000000 : ℝ)^4247 := by
    have hnat : (457213069 : ℕ)^5271*100000000000000^4247 ≤ 28700750560663^4247*1250000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457213069 1250000000 28700750560663 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4110314101/10000000000 : ℝ), (2299090807/5000000000 : ℝ), (457213069/1250000000 : ℝ)] ![(33172322948853/100000000000000 : ℝ), (19063463237557/50000000000000 : ℝ), (28700750560663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4110314101/10000000000 : ℝ)|^5271 ≤ (33172322948853/100000000000000 : ℝ)^4247
        have hw : |(4110314101/10000000000 : ℝ)|=(4110314101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2299090807/5000000000 : ℝ)|^5271 ≤ (19063463237557/50000000000000 : ℝ)^4247
        have hw : |(2299090807/5000000000 : ℝ)|=(2299090807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(457213069/1250000000 : ℝ)|^5271 ≤ (28700750560663/100000000000000 : ℝ)^4247
        have hw : |(457213069/1250000000 : ℝ)|=(457213069/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1706_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96819777/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8567/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4983/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4989/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17121/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8567/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4983/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8567/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4983/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8567/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4983/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8567/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4983/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8567/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4983/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8567/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4983/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4983/50000 : ℝ) ^ (5263/1024 : ℝ) ≤ (356220923002927/50000000000000000000 : ℝ) := by
    have hpowers : (4983/50000 : ℝ)^5263 ≤ (356220923002927/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4983 : ℕ)^5263*50000000000000000000^1024 ≤ 356220923002927^1024*50000^5263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4983 50000 356220923002927 50000000000000000000 5263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4983/50000 : ℝ)) (X := (356220923002927/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8567/50000 : ℝ) ^ (5263/1024 : ℝ) ≤ (11542593098712903/100000000000000000000 : ℝ) := by
    have hpowers : (8567/50000 : ℝ)^5263 ≤ (11542593098712903/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8567 : ℕ)^5263*100000000000000000000^1024 ≤ 11542593098712903^1024*50000^5263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8567 50000 11542593098712903 100000000000000000000 5263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8567/50000 : ℝ)) (X := (11542593098712903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000356220923002927/25000000000000000000 : ℝ) ≤ (10000027723209731/10000000000000000 : ℝ) ^ (5263/1024 : ℝ) := by
    have hpowers : (25000356220923002927/25000000000000000000 : ℝ)^1024 ≤ (10000027723209731/10000000000000000 : ℝ)^5263 := by
      have hnat : (25000356220923002927 : ℕ)^1024*10000000000000000^5263 ≤ 10000027723209731^5263*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000356220923002927 25000000000000000000 10000027723209731 10000000000000000 1024 5263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000027723209731/10000000000000000 : ℝ)) (X := (25000356220923002927/25000000000000000000 : ℝ)) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100012255034944718757/100000000000000000000 : ℝ) ≤ (5000119214673087/5000000000000000 : ℝ) ^ (5263/1024 : ℝ) := by
    have hpowers : (100012255034944718757/100000000000000000000 : ℝ)^1024 ≤ (5000119214673087/5000000000000000 : ℝ)^5263 := by
      have hnat : (100012255034944718757 : ℕ)^1024*5000000000000000^5263 ≤ 5000119214673087^5263*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100012255034944718757 100000000000000000000 5000119214673087 5000000000000000 1024 5263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000119214673087/5000000000000000 : ℝ)) (X := (100012255034944718757/100000000000000000000 : ℝ)) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50011542593098712903/50000000000000000000 : ℝ) ≤ (10000449135482617/10000000000000000 : ℝ) ^ (5263/1024 : ℝ) := by
    have hpowers : (50011542593098712903/50000000000000000000 : ℝ)^1024 ≤ (10000449135482617/10000000000000000 : ℝ)^5263 := by
      have hnat : (50011542593098712903 : ℕ)^1024*10000000000000000^5263 ≤ 10000449135482617^5263*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011542593098712903 50000000000000000000 10000449135482617 10000000000000000 1024 5263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000449135482617/10000000000000000 : ℝ)) (X := (50011542593098712903/50000000000000000000 : ℝ)) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(356220923002927/50000000000000000000 : ℝ) ≤ ((17918999731313942483/17920000000000000000 : ℝ)+2*(210706136443/716800000000000 : ℝ)*(4983/50000 : ℝ))^(5263/1024 : ℝ) := by
    rw [show (17918999731313942483/17920000000000000000 : ℝ)+2*(210706136443/716800000000000 : ℝ)*(4983/50000 : ℝ)=(10000027723209731/10000000000000000 : ℝ) by norm_num, show 1+2*(356220923002927/50000000000000000000 : ℝ)=(25000356220923002927/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11542593098712903/100000000000000000000 : ℝ)+(356220923002927/50000000000000000000 : ℝ) ≤ ((17918999731313942483/17920000000000000000 : ℝ)+(210706136443/716800000000000 : ℝ)*((8567/50000 : ℝ)+(4983/50000 : ℝ)))^(5263/1024 : ℝ) := by
    rw [show (17918999731313942483/17920000000000000000 : ℝ)+(210706136443/716800000000000 : ℝ)*((8567/50000 : ℝ)+(4983/50000 : ℝ))=(5000119214673087/5000000000000000 : ℝ) by norm_num, show 1+(11542593098712903/100000000000000000000 : ℝ)+(356220923002927/50000000000000000000 : ℝ)=(100012255034944718757/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11542593098712903/100000000000000000000 : ℝ) ≤ ((17918999731313942483/17920000000000000000 : ℝ)+2*(210706136443/716800000000000 : ℝ)*(8567/50000 : ℝ))^(5263/1024 : ℝ) := by
    rw [show (17918999731313942483/17920000000000000000 : ℝ)+2*(210706136443/716800000000000 : ℝ)*(8567/50000 : ℝ)=(10000449135482617/10000000000000000 : ℝ) by norm_num, show 1+2*(11542593098712903/100000000000000000000 : ℝ)=(50011542593098712903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17918999731313942483/17920000000000000000 : ℝ)*(X 1 0+X 2 0)+(210706136443/716800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5263/1024 : ℝ)) (lo := (4983/50000 : ℝ)) (hi := (8567/50000 : ℝ)) (c := (17918999731313942483/17920000000000000000 : ℝ)) (alpha := (210706136443/716800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17918999731313942483/17920000000000000000 : ℝ)*(X 0 1+X 2 1)+(210706136443/716800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5263/1024 : ℝ)) (lo := (4983/50000 : ℝ)) (hi := (8567/50000 : ℝ)) (c := (17918999731313942483/17920000000000000000 : ℝ)) (alpha := (210706136443/716800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17918999731313942483/17920000000000000000 : ℝ)*(X 0 2+X 1 2)+(210706136443/716800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5263/1024 : ℝ)) (lo := (4983/50000 : ℝ)) (hi := (8567/50000 : ℝ)) (c := (17918999731313942483/17920000000000000000 : ℝ)) (alpha := (210706136443/716800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-356664629/2500000000 : ℝ)*X 0 0+(1094519923/2000000000 : ℝ)*X 0 1+(5137780481/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336215159/2500000000 : ℝ)*X 1 0+(-1600329533/10000000000 : ℝ)*X 1 1+(513778051/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344860673/10000000000 : ℝ)*X 2 0+(256889027/500000000 : ℝ)*X 2 1+(-800164723/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4109875909/10000000000 : ℝ)*X 0 0+(729386267/2000000000 : ℝ)*X 0 1+(4608796467/10000000000 : ℝ)*X 0 2+(4109875909/10000000000 : ℝ)*X 1 0+(729386267/2000000000 : ℝ)*X 1 1+(4608796467/10000000000 : ℝ)*X 1 2+(4109875909/10000000000 : ℝ)*X 2 0+(729386267/2000000000 : ℝ)*X 2 1+(4608796467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1426810983/10000000000 : ℝ)*X 0 0+(1285368881/2500000000 : ℝ)*X 0 1+(5468849509/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5255250011/10000000000 : ℝ)*X 1 0+(-253852107/2000000000 : ℝ)*X 1 1+(2734424753/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2627625007/5000000000 : ℝ)*X 2 0+(1093769901/2000000000 : ℝ)*X 2 1+(-317315133/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4110314101/10000000000 : ℝ)*X 0 0+(2299090807/5000000000 : ℝ)*X 0 1+(457213069/1250000000 : ℝ)*X 0 2+(4110314101/10000000000 : ℝ)*X 1 0+(2299090807/5000000000 : ℝ)*X 1 1+(457213069/1250000000 : ℝ)*X 1 2+(4110314101/10000000000 : ℝ)*X 2 0+(2299090807/5000000000 : ℝ)*X 2 1+(457213069/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1133588374583045676774214671/448000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (432792831/100000000000000 : ℝ)*(base19) + (443001073/100000000000000 : ℝ)*(base23) + (8118299/20000000000000 : ℝ)*(upper3) + (5594613/100000000000000 : ℝ)*(upper4) + (91879181/100000000000000 : ℝ)*(upper5) + (2013173299902759/100000000000000 : ℝ)*(major0) + (2013173299902759/100000000000000 : ℝ)*(major1) + (50329332497569/2500000000000 : ℝ)*(major2) + (746672822668699/25000000000000 : ℝ)*(sp0) + (1493348124803217/50000000000000 : ℝ)*(sp1) + (186668514962387/6250000000000 : ℝ)*(sp2) + (519824210239999/50000000000000 : ℝ)*(sp3) + (5391724469/100000000000000 : ℝ)*(sp4) + (1412581877/100000000000000 : ℝ)*(sp7) + (1663439732899/160000000000 : ℝ)*(f.failure) + (597339336479853/20000000000000 : ℝ)*(f.sum) + (286750225915637/71680000000000000000000000000 : ℝ)*base65 + (1601049314068855629/256000000000000000000000000000000 : ℝ)*base68 + (21866021421347561/1400000000000000000000000000000 : ℝ)*base69 + (122777487892855629/256000000000000000000000000000000 : ℝ)*base72 + (36757490487563/71680000000000000000000000000 : ℝ)*base74 + (4205849181147561/1400000000000000000000000000000 : ℝ)*base75 + (916984844725064403/1792000000000000000000000000000000 : ℝ)*base78 + (12957274276021064403/1792000000000000000000000000000000 : ℝ)*base80 + (151953808304317/35840000000000000000000000000 : ℝ)*base81 + (23523/8000000000000000000 : ℝ)*base89 + (23523/8000000000000000000 : ℝ)*base91 + (56477/8000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106811200259845601048414799/44800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (329719483/100000000000000 : ℝ)*(base19) + (90288593/25000000000000 : ℝ)*(base23) + (24381877/25000000000000 : ℝ)*(lower1) + (50956977/100000000000000 : ℝ)*(upper3) + (13125969/100000000000000 : ℝ)*(lower4) + (50027991/100000000000000 : ℝ)*(upper5) + (102947411769849/5000000000000 : ℝ)*(major0) + (102947411769849/5000000000000 : ℝ)*(major1) + (102947411769849/5000000000000 : ℝ)*(major2) + (276469933/100000000000000 : ℝ)*(sp2) + (3054607309692381/100000000000000 : ℝ)*(sp4) + (1527303489986449/50000000000000 : ℝ)*(sp5) + (763651668017019/25000000000000 : ℝ)*(sp6) + (531644540814471/50000000000000 : ℝ)*(sp7) + (531644540814471/50000000000000 : ℝ)*(f.failure) + (3054607309692381/100000000000000 : ℝ)*(f.sum) + (1035665117859/1792000000000000000000000000 : ℝ)*base65 + (1195355734369929933/89600000000000000000000000000000 : ℝ)*base68 + (268387508292470067/89600000000000000000000000000000 : ℝ)*base69 + (2723542690094729933/89600000000000000000000000000000 : ℝ)*base72 + (3773348481629/1792000000000000000000000000 : ℝ)*base74 + (6867624855966070067/89600000000000000000000000000000 : ℝ)*base75 + (594130619793270067/89600000000000000000000000000000 : ℝ)*base77 + (458604395012470067/89600000000000000000000000000000 : ℝ)*base79 + (1725322710621/1792000000000000000000000000 : ℝ)*base82 + (19407033/2500000000000000000000 : ℝ)*base90 + (19407033/2500000000000000000000 : ℝ)*base92 + (19407033/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1706_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96819777/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8567/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4983/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4989/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17121/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1706_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1706_box_0 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1104910811/10000000000 : ℝ)*x 0 + (135483819/250000000 : ℝ)*x 1 + (677418913/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104910811/10000000000 : ℝ)^5271 ≤ (3248123553451/50000000000000 : ℝ)^4247 := by
    have hnat : (1104910811 : ℕ)^5271*50000000000000^4247 ≤ 3248123553451^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104910811 10000000000 3248123553451 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135483819/250000000 : ℝ)^5271 ≤ (23375942115709/50000000000000 : ℝ)^4247 := by
    have hnat : (135483819 : ℕ)^5271*50000000000000^4247 ≤ 23375942115709^4247*250000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135483819 250000000 23375942115709 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677418913/1250000000 : ℝ)^5271 ≤ (23375934321109/50000000000000 : ℝ)^4247 := by
    have hnat : (677418913 : ℕ)^5271*50000000000000^4247 ≤ 23375934321109^4247*1250000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677418913 1250000000 23375934321109 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1104910811/10000000000 : ℝ), (135483819/250000000 : ℝ), (677418913/1250000000 : ℝ)] ![(3248123553451/50000000000000 : ℝ), (23375942115709/50000000000000 : ℝ), (23375934321109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1104910811/10000000000 : ℝ)|^5271 ≤ (3248123553451/50000000000000 : ℝ)^4247
        have hw : |(-1104910811/10000000000 : ℝ)|=(1104910811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135483819/250000000 : ℝ)|^5271 ≤ (23375942115709/50000000000000 : ℝ)^4247
        have hw : |(135483819/250000000 : ℝ)|=(135483819/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677418913/1250000000 : ℝ)|^5271 ≤ (23375934321109/50000000000000 : ℝ)^4247
        have hw : |(677418913/1250000000 : ℝ)|=(677418913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_box_1 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225583343/10000000000 : ℝ)*x 0 + (-1380190833/10000000000 : ℝ)*x 1 + (5419352673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225583343/10000000000 : ℝ)^5271 ≤ (44686245616503/100000000000000 : ℝ)^4247 := by
    have hnat : (5225583343 : ℕ)^5271*100000000000000^4247 ≤ 44686245616503^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225583343 10000000000 44686245616503 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1380190833/10000000000 : ℝ)^5271 ≤ (4280935534631/50000000000000 : ℝ)^4247 := by
    have hnat : (1380190833 : ℕ)^5271*50000000000000^4247 ≤ 4280935534631^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380190833 10000000000 4280935534631 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419352673/10000000000 : ℝ)^5271 ≤ (584398541249/1250000000000 : ℝ)^4247 := by
    have hnat : (5419352673 : ℕ)^5271*1250000000000^4247 ≤ 584398541249^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419352673 10000000000 584398541249 1250000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225583343/10000000000 : ℝ), (-1380190833/10000000000 : ℝ), (5419352673/10000000000 : ℝ)] ![(44686245616503/100000000000000 : ℝ), (4280935534631/50000000000000 : ℝ), (584398541249/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225583343/10000000000 : ℝ)|^5271 ≤ (44686245616503/100000000000000 : ℝ)^4247
        have hw : |(5225583343/10000000000 : ℝ)|=(5225583343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1380190833/10000000000 : ℝ)|^5271 ≤ (4280935534631/50000000000000 : ℝ)^4247
        have hw : |(-1380190833/10000000000 : ℝ)|=(1380190833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419352673/10000000000 : ℝ)|^5271 ≤ (584398541249/1250000000000 : ℝ)^4247
        have hw : |(5419352673/10000000000 : ℝ)|=(5419352673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_box_2 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20412439/39062500 : ℝ)*x 0 + (10584671/19531250 : ℝ)*x 1 + (-345047739/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20412439/39062500 : ℝ)^5271 ≤ (44686256664933/100000000000000 : ℝ)^4247 := by
    have hnat : (20412439 : ℕ)^5271*100000000000000^4247 ≤ 44686256664933^4247*39062500^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20412439 39062500 44686256664933 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10584671/19531250 : ℝ)^5271 ≤ (46751871297521/100000000000000 : ℝ)^4247 := by
    have hnat : (10584671 : ℕ)^5271*100000000000000^4247 ≤ 46751871297521^4247*19531250^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10584671 19531250 46751871297521 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345047739/2500000000 : ℝ)^5271 ≤ (2140468004063/25000000000000 : ℝ)^4247 := by
    have hnat : (345047739 : ℕ)^5271*25000000000000^4247 ≤ 2140468004063^4247*2500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345047739 2500000000 2140468004063 25000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20412439/39062500 : ℝ), (10584671/19531250 : ℝ), (-345047739/2500000000 : ℝ)] ![(44686256664933/100000000000000 : ℝ), (46751871297521/100000000000000 : ℝ), (2140468004063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20412439/39062500 : ℝ)|^5271 ≤ (44686256664933/100000000000000 : ℝ)^4247
        have hw : |(20412439/39062500 : ℝ)|=(20412439/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10584671/19531250 : ℝ)|^5271 ≤ (46751871297521/100000000000000 : ℝ)^4247
        have hw : |(10584671/19531250 : ℝ)|=(10584671/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-345047739/2500000000 : ℝ)|^5271 ≤ (2140468004063/25000000000000 : ℝ)^4247
        have hw : |(-345047739/2500000000 : ℝ)|=(345047739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_box_3 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (224608847/500000000 : ℝ)*x 0 + (157622019/400000000 : ℝ)*x 1 + (1970275039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224608847/500000000 : ℝ)^5271 ≤ (37039084969883/100000000000000 : ℝ)^4247 := by
    have hnat : (224608847 : ℕ)^5271*100000000000000^4247 ≤ 37039084969883^4247*500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224608847 500000000 37039084969883 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (157622019/400000000 : ℝ)^5271 ≤ (15740229738179/50000000000000 : ℝ)^4247 := by
    have hnat : (157622019 : ℕ)^5271*50000000000000^4247 ≤ 15740229738179^4247*400000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157622019 400000000 15740229738179 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1970275039/5000000000 : ℝ)^5271 ≤ (31480455540083/100000000000000 : ℝ)^4247 := by
    have hnat : (1970275039 : ℕ)^5271*100000000000000^4247 ≤ 31480455540083^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970275039 5000000000 31480455540083 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(224608847/500000000 : ℝ), (157622019/400000000 : ℝ), (1970275039/5000000000 : ℝ)] ![(37039084969883/100000000000000 : ℝ), (15740229738179/50000000000000 : ℝ), (31480455540083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(224608847/500000000 : ℝ)|^5271 ≤ (37039084969883/100000000000000 : ℝ)^4247
        have hw : |(224608847/500000000 : ℝ)|=(224608847/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(157622019/400000000 : ℝ)|^5271 ≤ (15740229738179/50000000000000 : ℝ)^4247
        have hw : |(157622019/400000000 : ℝ)|=(157622019/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1970275039/5000000000 : ℝ)|^5271 ≤ (31480455540083/100000000000000 : ℝ)^4247
        have hw : |(1970275039/5000000000 : ℝ)|=(1970275039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_box_4 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1769113107/10000000000 : ℝ)*x 0 + (1035457907/2000000000 : ℝ)*x 1 + (2588644793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1769113107/10000000000 : ℝ)^5271 ≤ (2912868834219/25000000000000 : ℝ)^4247 := by
    have hnat : (1769113107 : ℕ)^5271*25000000000000^4247 ≤ 2912868834219^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769113107 10000000000 2912868834219 25000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035457907/2000000000 : ℝ)^5271 ≤ (44174262052613/100000000000000 : ℝ)^4247 := by
    have hnat : (1035457907 : ℕ)^5271*100000000000000^4247 ≤ 44174262052613^4247*2000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035457907 2000000000 44174262052613 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588644793/5000000000 : ℝ)^5271 ≤ (1104356564817/2500000000000 : ℝ)^4247 := by
    have hnat : (2588644793 : ℕ)^5271*2500000000000^4247 ≤ 1104356564817^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588644793 5000000000 1104356564817 2500000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1769113107/10000000000 : ℝ), (1035457907/2000000000 : ℝ), (2588644793/5000000000 : ℝ)] ![(2912868834219/25000000000000 : ℝ), (44174262052613/100000000000000 : ℝ), (1104356564817/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1769113107/10000000000 : ℝ)|^5271 ≤ (2912868834219/25000000000000 : ℝ)^4247
        have hw : |(-1769113107/10000000000 : ℝ)|=(1769113107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035457907/2000000000 : ℝ)|^5271 ≤ (44174262052613/100000000000000 : ℝ)^4247
        have hw : |(1035457907/2000000000 : ℝ)|=(1035457907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588644793/5000000000 : ℝ)|^5271 ≤ (1104356564817/2500000000000 : ℝ)^4247
        have hw : |(2588644793/5000000000 : ℝ)|=(2588644793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_box_5 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389902927/10000000000 : ℝ)*x 0 + (-1486646169/10000000000 : ℝ)*x 1 + (5177289817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389902927/10000000000 : ℝ)^5271 ≤ (23218387804481/50000000000000 : ℝ)^4247 := by
    have hnat : (5389902927 : ℕ)^5271*50000000000000^4247 ≤ 23218387804481^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389902927 10000000000 23218387804481 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1486646169/10000000000 : ℝ)^5271 ≤ (9388959333701/100000000000000 : ℝ)^4247 := by
    have hnat : (1486646169 : ℕ)^5271*100000000000000^4247 ≤ 9388959333701^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1486646169 10000000000 9388959333701 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177289817/10000000000 : ℝ)^5271 ≤ (22087132519433/50000000000000 : ℝ)^4247 := by
    have hnat : (5177289817 : ℕ)^5271*50000000000000^4247 ≤ 22087132519433^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177289817 10000000000 22087132519433 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389902927/10000000000 : ℝ), (-1486646169/10000000000 : ℝ), (5177289817/10000000000 : ℝ)] ![(23218387804481/50000000000000 : ℝ), (9388959333701/100000000000000 : ℝ), (22087132519433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389902927/10000000000 : ℝ)|^5271 ≤ (23218387804481/50000000000000 : ℝ)^4247
        have hw : |(5389902927/10000000000 : ℝ)|=(5389902927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1486646169/10000000000 : ℝ)|^5271 ≤ (9388959333701/100000000000000 : ℝ)^4247
        have hw : |(-1486646169/10000000000 : ℝ)|=(1486646169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177289817/10000000000 : ℝ)|^5271 ≤ (22087132519433/50000000000000 : ℝ)^4247
        have hw : |(5177289817/10000000000 : ℝ)|=(5177289817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_box_6 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2694951487/5000000000 : ℝ)*x 0 + (323580611/625000000 : ℝ)*x 1 + (-18583077/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2694951487/5000000000 : ℝ)^5271 ≤ (11609194027881/25000000000000 : ℝ)^4247 := by
    have hnat : (2694951487 : ℕ)^5271*25000000000000^4247 ≤ 11609194027881^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694951487 5000000000 11609194027881 25000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323580611/625000000 : ℝ)^5271 ≤ (8834852920939/20000000000000 : ℝ)^4247 := by
    have hnat : (323580611 : ℕ)^5271*20000000000000^4247 ≤ 8834852920939^4247*625000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323580611 625000000 8834852920939 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18583077/125000000 : ℝ)^5271 ≤ (2347239815789/25000000000000 : ℝ)^4247 := by
    have hnat : (18583077 : ℕ)^5271*25000000000000^4247 ≤ 2347239815789^4247*125000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18583077 125000000 2347239815789 25000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2694951487/5000000000 : ℝ), (323580611/625000000 : ℝ), (-18583077/125000000 : ℝ)] ![(11609194027881/25000000000000 : ℝ), (8834852920939/20000000000000 : ℝ), (2347239815789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2694951487/5000000000 : ℝ)|^5271 ≤ (11609194027881/25000000000000 : ℝ)^4247
        have hw : |(2694951487/5000000000 : ℝ)|=(2694951487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323580611/625000000 : ℝ)|^5271 ≤ (8834852920939/20000000000000 : ℝ)^4247
        have hw : |(323580611/625000000 : ℝ)|=(323580611/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18583077/125000000 : ℝ)|^5271 ≤ (2347239815789/25000000000000 : ℝ)^4247
        have hw : |(-18583077/125000000 : ℝ)|=(18583077/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_box_7 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3712141583/10000000000 : ℝ)*x 0 + (2164867149/5000000000 : ℝ)*x 1 + (4329734413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3712141583/10000000000 : ℝ)^5271 ≤ (14615918630479/50000000000000 : ℝ)^4247 := by
    have hnat : (3712141583 : ℕ)^5271*50000000000000^4247 ≤ 14615918630479^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3712141583 10000000000 14615918630479 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2164867149/5000000000 : ℝ)^5271 ≤ (17692040391049/50000000000000 : ℝ)^4247 := by
    have hnat : (2164867149 : ℕ)^5271*50000000000000^4247 ≤ 17692040391049^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164867149 5000000000 17692040391049 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4329734413/10000000000 : ℝ)^5271 ≤ (35384081948519/100000000000000 : ℝ)^4247 := by
    have hnat : (4329734413 : ℕ)^5271*100000000000000^4247 ≤ 35384081948519^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329734413 10000000000 35384081948519 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3712141583/10000000000 : ℝ), (2164867149/5000000000 : ℝ), (4329734413/10000000000 : ℝ)] ![(14615918630479/50000000000000 : ℝ), (17692040391049/50000000000000 : ℝ), (35384081948519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3712141583/10000000000 : ℝ)|^5271 ≤ (14615918630479/50000000000000 : ℝ)^4247
        have hw : |(3712141583/10000000000 : ℝ)|=(3712141583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2164867149/5000000000 : ℝ)|^5271 ≤ (17692040391049/50000000000000 : ℝ)^4247
        have hw : |(2164867149/5000000000 : ℝ)|=(2164867149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4329734413/10000000000 : ℝ)|^5271 ≤ (35384081948519/100000000000000 : ℝ)^4247
        have hw : |(4329734413/10000000000 : ℝ)|=(4329734413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_box_8 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-65052683/400000000 : ℝ)*x 0 + (499883329/1000000000 : ℝ)*x 1 + (2731130379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65052683/400000000 : ℝ)^5271 ≤ (327995474543/3125000000000 : ℝ)^4247 := by
    have hnat : (65052683 : ℕ)^5271*3125000000000^4247 ≤ 327995474543^4247*400000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65052683 400000000 327995474543 3125000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499883329/1000000000 : ℝ)^5271 ≤ (10573103162777/25000000000000 : ℝ)^4247 := by
    have hnat : (499883329 : ℕ)^5271*25000000000000^4247 ≤ 10573103162777^4247*1000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499883329 1000000000 10573103162777 25000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731130379/5000000000 : ℝ)^5271 ≤ (9442346428233/20000000000000 : ℝ)^4247 := by
    have hnat : (2731130379 : ℕ)^5271*20000000000000^4247 ≤ 9442346428233^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731130379 5000000000 9442346428233 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65052683/400000000 : ℝ), (499883329/1000000000 : ℝ), (2731130379/5000000000 : ℝ)] ![(327995474543/3125000000000 : ℝ), (10573103162777/25000000000000 : ℝ), (9442346428233/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65052683/400000000 : ℝ)|^5271 ≤ (327995474543/3125000000000 : ℝ)^4247
        have hw : |(-65052683/400000000 : ℝ)|=(65052683/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(499883329/1000000000 : ℝ)|^5271 ≤ (10573103162777/25000000000000 : ℝ)^4247
        have hw : |(499883329/1000000000 : ℝ)|=(499883329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731130379/5000000000 : ℝ)|^5271 ≤ (9442346428233/20000000000000 : ℝ)^4247
        have hw : |(2731130379/5000000000 : ℝ)|=(2731130379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_box_9 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196473777/10000000000 : ℝ)*x 0 + (-680264861/5000000000 : ℝ)*x 1 + (5462261093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196473777/10000000000 : ℝ)^5271 ≤ (2773594078467/6250000000000 : ℝ)^4247 := by
    have hnat : (5196473777 : ℕ)^5271*6250000000000^4247 ≤ 2773594078467^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196473777 10000000000 2773594078467 6250000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680264861/5000000000 : ℝ)^5271 ≤ (8410758992881/100000000000000 : ℝ)^4247 := by
    have hnat : (680264861 : ℕ)^5271*100000000000000^4247 ≤ 8410758992881^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680264861 5000000000 8410758992881 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462261093/10000000000 : ℝ)^5271 ≤ (47211735734793/100000000000000 : ℝ)^4247 := by
    have hnat : (5462261093 : ℕ)^5271*100000000000000^4247 ≤ 47211735734793^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462261093 10000000000 47211735734793 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196473777/10000000000 : ℝ), (-680264861/5000000000 : ℝ), (5462261093/10000000000 : ℝ)] ![(2773594078467/6250000000000 : ℝ), (8410758992881/100000000000000 : ℝ), (47211735734793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196473777/10000000000 : ℝ)|^5271 ≤ (2773594078467/6250000000000 : ℝ)^4247
        have hw : |(5196473777/10000000000 : ℝ)|=(5196473777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-680264861/5000000000 : ℝ)|^5271 ≤ (8410758992881/100000000000000 : ℝ)^4247
        have hw : |(-680264861/5000000000 : ℝ)|=(680264861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462261093/10000000000 : ℝ)|^5271 ≤ (47211735734793/100000000000000 : ℝ)^4247
        have hw : |(5462261093/10000000000 : ℝ)|=(5462261093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_box_10 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196474469/10000000000 : ℝ)*x 0 + (546226037/1000000000 : ℝ)*x 1 + (-680264889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196474469/10000000000 : ℝ)^5271 ≤ (2218875629499/5000000000000 : ℝ)^4247 := by
    have hnat : (5196474469 : ℕ)^5271*5000000000000^4247 ≤ 2218875629499^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196474469 10000000000 2218875629499 5000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546226037/1000000000 : ℝ)^5271 ≤ (23605863989497/50000000000000 : ℝ)^4247 := by
    have hnat : (546226037 : ℕ)^5271*50000000000000^4247 ≤ 23605863989497^4247*1000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546226037 1000000000 23605863989497 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680264889/5000000000 : ℝ)^5271 ≤ (4205379711271/50000000000000 : ℝ)^4247 := by
    have hnat : (680264889 : ℕ)^5271*50000000000000^4247 ≤ 4205379711271^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680264889 5000000000 4205379711271 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196474469/10000000000 : ℝ), (546226037/1000000000 : ℝ), (-680264889/5000000000 : ℝ)] ![(2218875629499/5000000000000 : ℝ), (23605863989497/50000000000000 : ℝ), (4205379711271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196474469/10000000000 : ℝ)|^5271 ≤ (2218875629499/5000000000000 : ℝ)^4247
        have hw : |(5196474469/10000000000 : ℝ)|=(5196474469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546226037/1000000000 : ℝ)|^5271 ≤ (23605863989497/50000000000000 : ℝ)^4247
        have hw : |(546226037/1000000000 : ℝ)|=(546226037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-680264889/5000000000 : ℝ)|^5271 ≤ (4205379711271/50000000000000 : ℝ)^4247
        have hw : |(-680264889/5000000000 : ℝ)|=(680264889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_box_11 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2312728013/5000000000 : ℝ)*x 0 + (3871380163/10000000000 : ℝ)*x 1 + (483922679/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2312728013/5000000000 : ℝ)^5271 ≤ (38407807117481/100000000000000 : ℝ)^4247 := by
    have hnat : (2312728013 : ℕ)^5271*100000000000000^4247 ≤ 38407807117481^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312728013 5000000000 38407807117481 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3871380163/10000000000 : ℝ)^5271 ≤ (15398045086581/50000000000000 : ℝ)^4247 := by
    have hnat : (3871380163 : ℕ)^5271*50000000000000^4247 ≤ 15398045086581^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3871380163 10000000000 15398045086581 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (483922679/1250000000 : ℝ)^5271 ≤ (123184410807/400000000000 : ℝ)^4247 := by
    have hnat : (483922679 : ℕ)^5271*400000000000^4247 ≤ 123184410807^4247*1250000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483922679 1250000000 123184410807 400000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2312728013/5000000000 : ℝ), (3871380163/10000000000 : ℝ), (483922679/1250000000 : ℝ)] ![(38407807117481/100000000000000 : ℝ), (15398045086581/50000000000000 : ℝ), (123184410807/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2312728013/5000000000 : ℝ)|^5271 ≤ (38407807117481/100000000000000 : ℝ)^4247
        have hw : |(2312728013/5000000000 : ℝ)|=(2312728013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3871380163/10000000000 : ℝ)|^5271 ≤ (15398045086581/50000000000000 : ℝ)^4247
        have hw : |(3871380163/10000000000 : ℝ)|=(3871380163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(483922679/1250000000 : ℝ)|^5271 ≤ (123184410807/400000000000 : ℝ)^4247
        have hw : |(483922679/1250000000 : ℝ)|=(483922679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_box_12 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-621185467/5000000000 : ℝ)*x 0 + (2794643197/5000000000 : ℝ)*x 1 + (2576062739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (621185467/5000000000 : ℝ)^5271 ≤ (7513892295593/100000000000000 : ℝ)^4247 := by
    have hnat : (621185467 : ℕ)^5271*100000000000000^4247 ≤ 7513892295593^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621185467 5000000000 7513892295593 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2794643197/5000000000 : ℝ)^5271 ≤ (48578165407917/100000000000000 : ℝ)^4247 := by
    have hnat : (2794643197 : ℕ)^5271*100000000000000^4247 ≤ 48578165407917^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794643197 5000000000 48578165407917 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576062739/5000000000 : ℝ)^5271 ≤ (8781588457491/20000000000000 : ℝ)^4247 := by
    have hnat : (2576062739 : ℕ)^5271*20000000000000^4247 ≤ 8781588457491^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576062739 5000000000 8781588457491 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-621185467/5000000000 : ℝ), (2794643197/5000000000 : ℝ), (2576062739/5000000000 : ℝ)] ![(7513892295593/100000000000000 : ℝ), (48578165407917/100000000000000 : ℝ), (8781588457491/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-621185467/5000000000 : ℝ)|^5271 ≤ (7513892295593/100000000000000 : ℝ)^4247
        have hw : |(-621185467/5000000000 : ℝ)|=(621185467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2794643197/5000000000 : ℝ)|^5271 ≤ (48578165407917/100000000000000 : ℝ)^4247
        have hw : |(2794643197/5000000000 : ℝ)|=(2794643197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576062739/5000000000 : ℝ)|^5271 ≤ (8781588457491/20000000000000 : ℝ)^4247
        have hw : |(2576062739/5000000000 : ℝ)|=(2576062739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_box_13 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1351753869/2500000000 : ℝ)*x 0 + (-374315149/2500000000 : ℝ)*x 1 + (2576062797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1351753869/2500000000 : ℝ)^5271 ≤ (23309913416289/50000000000000 : ℝ)^4247 := by
    have hnat : (1351753869 : ℕ)^5271*50000000000000^4247 ≤ 23309913416289^4247*2500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351753869 2500000000 23309913416289 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374315149/2500000000 : ℝ)^5271 ≤ (2960071761/31250000000 : ℝ)^4247 := by
    have hnat : (374315149 : ℕ)^5271*31250000000^4247 ≤ 2960071761^4247*2500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374315149 2500000000 2960071761 31250000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576062797/5000000000 : ℝ)^5271 ≤ (43907943514401/100000000000000 : ℝ)^4247 := by
    have hnat : (2576062797 : ℕ)^5271*100000000000000^4247 ≤ 43907943514401^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576062797 5000000000 43907943514401 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1351753869/2500000000 : ℝ), (-374315149/2500000000 : ℝ), (2576062797/5000000000 : ℝ)] ![(23309913416289/50000000000000 : ℝ), (2960071761/31250000000 : ℝ), (43907943514401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1351753869/2500000000 : ℝ)|^5271 ≤ (23309913416289/50000000000000 : ℝ)^4247
        have hw : |(1351753869/2500000000 : ℝ)|=(1351753869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-374315149/2500000000 : ℝ)|^5271 ≤ (2960071761/31250000000 : ℝ)^4247
        have hw : |(-374315149/2500000000 : ℝ)|=(374315149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576062797/5000000000 : ℝ)|^5271 ≤ (43907943514401/100000000000000 : ℝ)^4247
        have hw : |(2576062797/5000000000 : ℝ)|=(2576062797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_box_14 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1351753867/2500000000 : ℝ)*x 0 + (5152125787/10000000000 : ℝ)*x 1 + (-1497260349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1351753867/2500000000 : ℝ)^5271 ≤ (4661982674697/10000000000000 : ℝ)^4247 := by
    have hnat : (1351753867 : ℕ)^5271*10000000000000^4247 ≤ 4661982674697^4247*2500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351753867 2500000000 4661982674697 10000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152125787/10000000000 : ℝ)^5271 ≤ (8781589111157/20000000000000 : ℝ)^4247 := by
    have hnat : (5152125787 : ℕ)^5271*20000000000000^4247 ≤ 8781589111157^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152125787 10000000000 8781589111157 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1497260349/10000000000 : ℝ)^5271 ≤ (4736113847911/50000000000000 : ℝ)^4247 := by
    have hnat : (1497260349 : ℕ)^5271*50000000000000^4247 ≤ 4736113847911^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1497260349 10000000000 4736113847911 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1351753867/2500000000 : ℝ), (5152125787/10000000000 : ℝ), (-1497260349/10000000000 : ℝ)] ![(4661982674697/10000000000000 : ℝ), (8781589111157/20000000000000 : ℝ), (4736113847911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1351753867/2500000000 : ℝ)|^5271 ≤ (4661982674697/10000000000000 : ℝ)^4247
        have hw : |(1351753867/2500000000 : ℝ)|=(1351753867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5152125787/10000000000 : ℝ)|^5271 ≤ (8781589111157/20000000000000 : ℝ)^4247
        have hw : |(5152125787/10000000000 : ℝ)|=(5152125787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1497260349/10000000000 : ℝ)|^5271 ≤ (4736113847911/50000000000000 : ℝ)^4247
        have hw : |(-1497260349/10000000000 : ℝ)|=(1497260349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_box_15 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3628067793/10000000000 : ℝ)*x 0 + (874016691/2000000000 : ℝ)*x 1 + (2185041811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3628067793/10000000000 : ℝ)^5271 ≤ (28412413284459/100000000000000 : ℝ)^4247 := by
    have hnat : (3628067793 : ℕ)^5271*100000000000000^4247 ≤ 28412413284459^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3628067793 10000000000 28412413284459 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (874016691/2000000000 : ℝ)^5271 ≤ (4474224063179/12500000000000 : ℝ)^4247 := by
    have hnat : (874016691 : ℕ)^5271*12500000000000^4247 ≤ 4474224063179^4247*2000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874016691 2000000000 4474224063179 12500000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185041811/5000000000 : ℝ)^5271 ≤ (35793794203071/100000000000000 : ℝ)^4247 := by
    have hnat : (2185041811 : ℕ)^5271*100000000000000^4247 ≤ 35793794203071^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185041811 5000000000 35793794203071 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3628067793/10000000000 : ℝ), (874016691/2000000000 : ℝ), (2185041811/5000000000 : ℝ)] ![(28412413284459/100000000000000 : ℝ), (4474224063179/12500000000000 : ℝ), (35793794203071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3628067793/10000000000 : ℝ)|^5271 ≤ (28412413284459/100000000000000 : ℝ)^4247
        have hw : |(3628067793/10000000000 : ℝ)|=(3628067793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(874016691/2000000000 : ℝ)|^5271 ≤ (4474224063179/12500000000000 : ℝ)^4247
        have hw : |(874016691/2000000000 : ℝ)|=(874016691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2185041811/5000000000 : ℝ)|^5271 ≤ (35793794203071/100000000000000 : ℝ)^4247
        have hw : |(2185041811/5000000000 : ℝ)|=(2185041811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1706_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96819777/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4989/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6671/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58309/100000 : ℝ) ∧ (81351/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (45183/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4989/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4989/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4989/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4989/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4989/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4989/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4989/50000 : ℝ) ^ (5263/1024 : ℝ) ≤ (143372375955679/20000000000000000000 : ℝ) := by
    have hpowers : (4989/50000 : ℝ)^5263 ≤ (143372375955679/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4989 : ℕ)^5263*20000000000000000000^1024 ≤ 143372375955679^1024*50000^5263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4989 50000 143372375955679 20000000000000000000 5263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4989/50000 : ℝ)) (X := (143372375955679/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17121/100000 : ℝ) ^ (5263/1024 : ℝ) ≤ (11497652446900401/100000000000000000000 : ℝ) := by
    have hpowers : (17121/100000 : ℝ)^5263 ≤ (11497652446900401/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17121 : ℕ)^5263*100000000000000000000^1024 ≤ 11497652446900401^1024*100000^5263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17121 100000 11497652446900401 100000000000000000000 5263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17121/100000 : ℝ)) (X := (11497652446900401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000143372375955679/10000000000000000000 : ℝ) ≤ (2000005579041053/2000000000000000 : ℝ) ^ (5263/1024 : ℝ) := by
    have hpowers : (10000143372375955679/10000000000000000000 : ℝ)^1024 ≤ (2000005579041053/2000000000000000 : ℝ)^5263 := by
      have hnat : (10000143372375955679 : ℕ)^1024*2000000000000000^5263 ≤ 2000005579041053^5263*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000143372375955679 10000000000000000000 2000005579041053 2000000000000000 1024 5263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000005579041053/2000000000000000 : ℝ)) (X := (10000143372375955679/10000000000000000000 : ℝ)) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25003053628581669699/25000000000000000000 : ℝ) ≤ (10000237641031059/10000000000000000 : ℝ) ^ (5263/1024 : ℝ) := by
    have hpowers : (25003053628581669699/25000000000000000000 : ℝ)^1024 ≤ (10000237641031059/10000000000000000 : ℝ)^5263 := by
      have hnat : (25003053628581669699 : ℕ)^1024*10000000000000000^5263 ≤ 10000237641031059^5263*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003053628581669699 25000000000000000000 10000237641031059 10000000000000000 1024 5263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000237641031059/10000000000000000 : ℝ)) (X := (25003053628581669699/25000000000000000000 : ℝ)) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50011497652446900401/50000000000000000000 : ℝ) ≤ (10000447386856853/10000000000000000 : ℝ) ^ (5263/1024 : ℝ) := by
    have hpowers : (50011497652446900401/50000000000000000000 : ℝ)^1024 ≤ (10000447386856853/10000000000000000 : ℝ)^5263 := by
      have hnat : (50011497652446900401 : ℕ)^1024*10000000000000000^5263 ≤ 10000447386856853^5263*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011497652446900401 50000000000000000000 10000447386856853 10000000000000000 1024 5263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000447386856853/10000000000000000 : ℝ)) (X := (50011497652446900401/50000000000000000000 : ℝ)) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(143372375955679/20000000000000000000 : ℝ) ≤ ((23808671189250554277/23810000000000000000 : ℝ)+2*(104872912897/357150000000000 : ℝ)*(4989/50000 : ℝ))^(5263/1024 : ℝ) := by
    rw [show (23808671189250554277/23810000000000000000 : ℝ)+2*(104872912897/357150000000000 : ℝ)*(4989/50000 : ℝ)=(2000005579041053/2000000000000000 : ℝ) by norm_num, show 1+2*(143372375955679/20000000000000000000 : ℝ)=(10000143372375955679/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11497652446900401/100000000000000000000 : ℝ)+(143372375955679/20000000000000000000 : ℝ) ≤ ((23808671189250554277/23810000000000000000 : ℝ)+(104872912897/357150000000000 : ℝ)*((17121/100000 : ℝ)+(4989/50000 : ℝ)))^(5263/1024 : ℝ) := by
    rw [show (23808671189250554277/23810000000000000000 : ℝ)+(104872912897/357150000000000 : ℝ)*((17121/100000 : ℝ)+(4989/50000 : ℝ))=(10000237641031059/10000000000000000 : ℝ) by norm_num, show 1+(11497652446900401/100000000000000000000 : ℝ)+(143372375955679/20000000000000000000 : ℝ)=(25003053628581669699/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11497652446900401/100000000000000000000 : ℝ) ≤ ((23808671189250554277/23810000000000000000 : ℝ)+2*(104872912897/357150000000000 : ℝ)*(17121/100000 : ℝ))^(5263/1024 : ℝ) := by
    rw [show (23808671189250554277/23810000000000000000 : ℝ)+2*(104872912897/357150000000000 : ℝ)*(17121/100000 : ℝ)=(10000447386856853/10000000000000000 : ℝ) by norm_num, show 1+2*(11497652446900401/100000000000000000000 : ℝ)=(50011497652446900401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23808671189250554277/23810000000000000000 : ℝ)*(X 1 0+X 2 0)+(104872912897/357150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5263/1024 : ℝ)) (lo := (4989/50000 : ℝ)) (hi := (17121/100000 : ℝ)) (c := (23808671189250554277/23810000000000000000 : ℝ)) (alpha := (104872912897/357150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23808671189250554277/23810000000000000000 : ℝ)*(X 0 1+X 2 1)+(104872912897/357150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5263/1024 : ℝ)) (lo := (4989/50000 : ℝ)) (hi := (17121/100000 : ℝ)) (c := (23808671189250554277/23810000000000000000 : ℝ)) (alpha := (104872912897/357150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23808671189250554277/23810000000000000000 : ℝ)*(X 0 2+X 1 2)+(104872912897/357150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5263/1024 : ℝ)) (lo := (4989/50000 : ℝ)) (hi := (17121/100000 : ℝ)) (c := (23808671189250554277/23810000000000000000 : ℝ)) (alpha := (104872912897/357150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1104910811/10000000000 : ℝ)*X 0 0+(135483819/250000000 : ℝ)*X 0 1+(677418913/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5225583343/10000000000 : ℝ)*X 1 0+(-1380190833/10000000000 : ℝ)*X 1 1+(5419352673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((20412439/39062500 : ℝ)*X 2 0+(10584671/19531250 : ℝ)*X 2 1+(-345047739/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((224608847/500000000 : ℝ)*X 0 0+(157622019/400000000 : ℝ)*X 0 1+(1970275039/5000000000 : ℝ)*X 0 2+(224608847/500000000 : ℝ)*X 1 0+(157622019/400000000 : ℝ)*X 1 1+(1970275039/5000000000 : ℝ)*X 1 2+(224608847/500000000 : ℝ)*X 2 0+(157622019/400000000 : ℝ)*X 2 1+(1970275039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1769113107/10000000000 : ℝ)*X 0 0+(1035457907/2000000000 : ℝ)*X 0 1+(2588644793/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5389902927/10000000000 : ℝ)*X 1 0+(-1486646169/10000000000 : ℝ)*X 1 1+(5177289817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2694951487/5000000000 : ℝ)*X 2 0+(323580611/625000000 : ℝ)*X 2 1+(-18583077/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3712141583/10000000000 : ℝ)*X 0 0+(2164867149/5000000000 : ℝ)*X 0 1+(4329734413/10000000000 : ℝ)*X 0 2+(3712141583/10000000000 : ℝ)*X 1 0+(2164867149/5000000000 : ℝ)*X 1 1+(4329734413/10000000000 : ℝ)*X 1 2+(3712141583/10000000000 : ℝ)*X 2 0+(2164867149/5000000000 : ℝ)*X 2 1+(4329734413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-65052683/400000000 : ℝ)*X 0 0+(499883329/1000000000 : ℝ)*X 0 1+(2731130379/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5196473777/10000000000 : ℝ)*X 1 0+(-680264861/5000000000 : ℝ)*X 1 1+(5462261093/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5196474469/10000000000 : ℝ)*X 2 0+(546226037/1000000000 : ℝ)*X 2 1+(-680264889/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2312728013/5000000000 : ℝ)*X 0 0+(3871380163/10000000000 : ℝ)*X 0 1+(483922679/1250000000 : ℝ)*X 0 2+(2312728013/5000000000 : ℝ)*X 1 0+(3871380163/10000000000 : ℝ)*X 1 1+(483922679/1250000000 : ℝ)*X 1 2+(2312728013/5000000000 : ℝ)*X 2 0+(3871380163/10000000000 : ℝ)*X 2 1+(483922679/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-621185467/5000000000 : ℝ)*X 0 0+(2794643197/5000000000 : ℝ)*X 0 1+(2576062739/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1351753869/2500000000 : ℝ)*X 1 0+(-374315149/2500000000 : ℝ)*X 1 1+(2576062797/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1351753867/2500000000 : ℝ)*X 2 0+(5152125787/10000000000 : ℝ)*X 2 1+(-1497260349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3628067793/10000000000 : ℝ)*X 0 0+(874016691/2000000000 : ℝ)*X 0 1+(2185041811/5000000000 : ℝ)*X 0 2+(3628067793/10000000000 : ℝ)*X 1 0+(874016691/2000000000 : ℝ)*X 1 1+(2185041811/5000000000 : ℝ)*X 1 2+(3628067793/10000000000 : ℝ)*X 2 0+(874016691/2000000000 : ℝ)*X 2 1+(2185041811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6671/10000 : ℝ) ≤ (-3102151370141016097538970943263/4650390625000000000000000000000 : ℝ) := by norm_num
    linear_combination (17597/50000000000000 : ℝ)*(upper1) + (1840743/10000000000000 : ℝ)*(upper3) + (30369/12500000000000 : ℝ)*(upper4) + (16997557/50000000000000 : ℝ)*(upper5) + (10519543740471/781250000000 : ℝ)*(major0) + (10519543740471/781250000000 : ℝ)*(major1) + (10519543740471/781250000000 : ℝ)*(major2) + (76183637/50000000000000 : ℝ)*(sp3) + (2019874018222759/100000000000000 : ℝ)*(sp4) + (504965694330457/25000000000000 : ℝ)*(sp5) + (2019868182959641/100000000000000 : ℝ)*(sp6) + (695364803276183/100000000000000 : ℝ)*(sp7) + (11240900931/100000000000000 : ℝ)*(sp13) + (5835263117/100000000000000 : ℝ)*(sp14) + (695364955643457/100000000000000 : ℝ)*(f.failure) + (2019874018222759/100000000000000 : ℝ)*(f.sum) + (1388372599339/2976250000000000000000000000 : ℝ)*base66 + (31349972290701691/37203125000000000000000000000000 : ℝ)*base68 + (157615340570923309/37203125000000000000000000000000 : ℝ)*base69 + (248191035662139191/37203125000000000000000000000000 : ℝ)*base72 + (14666082888111/2976250000000000000000000000 : ℝ)*base73 + (140469695730360809/37203125000000000000000000000000 : ℝ)*base75 + (103052321728204559/37203125000000000000000000000000 : ℝ)*base77 + (105330535446329559/37203125000000000000000000000000 : ℝ)*base79 + (51383983696617/5952500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1750911/5000000000000000000000 : ℝ)*base90 + (1750911/5000000000000000000000 : ℝ)*base92 + (1750911/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58309/100000 : ℝ) ≤ (694193739457524523882837576695861/1190500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2664277/12500000000000 : ℝ)*(lower1) + (74550401/100000000000000 : ℝ)*(lower2) + (28120887/100000000000000 : ℝ)*(upper4) + (362540505478783/25000000000000 : ℝ)*(major0) + (362540505478783/25000000000000 : ℝ)*(major1) + (1450162021915133/100000000000000 : ℝ)*(major2) + (17055854225173/800000000000 : ℝ)*(sp0) + (532994888321203/25000000000000 : ℝ)*(sp1) + (2131986811613281/100000000000000 : ℝ)*(sp2) + (748895529175211/100000000000000 : ℝ)*(sp3) + (4914545753/50000000000000 : ℝ)*(sp5) + (2570763037/100000000000000 : ℝ)*(sp6) + (1048157319/50000000000000 : ℝ)*(sp7) + (7604229693/100000000000000 : ℝ)*(sp8) + (93612203186231/12500000000000 : ℝ)*(f.failure) + (1065994691188159/50000000000000 : ℝ)*(f.sum) + (11556758450317/2381000000000000000000000000 : ℝ)*base66 + (11619024620098985327/1785750000000000000000000000000000 : ℝ)*base68 + (32221615448215321523/7143000000000000000000000000000000 : ℝ)*base69 + (12063509497118735327/1785750000000000000000000000000000 : ℝ)*base72 + (2600377285853/595250000000000000000000000 : ℝ)*base74 + (43448550096703321523/7143000000000000000000000000000000 : ℝ)*base75 + (6986243216026585327/1785750000000000000000000000000000 : ℝ)*base78 + (11511153242774335327/1785750000000000000000000000000000 : ℝ)*base80 + (14636916028333/8928750000000000000000000000 : ℝ)*base82 + (109513/625000000000000000000 : ℝ)*base90 + (109513/625000000000000000000 : ℝ)*base92 + (6359513/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (81351/100000 : ℝ) ≤ (968509919863132061533335693845623/1190500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (131943/2500000000000 : ℝ)*(upper0) + (2913621/10000000000000 : ℝ)*(lower1) + (142466739/100000000000000 : ℝ)*(lower3) + (12442397/100000000000000 : ℝ)*(upper4) + (1472763755073767/100000000000000 : ℝ)*(major0) + (1472763755073767/100000000000000 : ℝ)*(major1) + (1472763755073767/100000000000000 : ℝ)*(major2) + (3763150449/100000000000000 : ℝ)*(sp0) + (4702238989/10000000000000 : ℝ)*(sp1) + (17777586877/100000000000000 : ℝ)*(sp3) + (1078918160927281/50000000000000 : ℝ)*(sp8) + (1078896531307561/50000000000000 : ℝ)*(sp9) + (2157840085005011/100000000000000 : ℝ)*(sp10) + (38027595607709/5000000000000 : ℝ)*(sp11) + (760569689741057/100000000000000 : ℝ)*(f.failure) + (2157840085005011/100000000000000 : ℝ)*(f.sum) + (55802087199733/35715000000000000000000000000 : ℝ)*base65 + (7847696539611854377/7143000000000000000000000000000000 : ℝ)*base67 + (8785632713177145623/7143000000000000000000000000000000 : ℝ)*base70 + (14853858167184854377/7143000000000000000000000000000000 : ℝ)*base71 + (296990529086383/35715000000000000000000000000 : ℝ)*base73 + (10367884529009145623/7143000000000000000000000000000000 : ℝ)*base76 + (3094293730599854377/7143000000000000000000000000000000 : ℝ)*base77 + (67210627703061854377/7143000000000000000000000000000000 : ℝ)*base79 + (75339232539361/17857500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (23515711/5000000000000000000000 : ℝ)*base90 + (23515711/5000000000000000000000 : ℝ)*base92 + (23515711/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-45183/50000 : ℝ) ≤ (-53788830065055473443931210585751/59525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21702451/100000000000000 : ℝ)*(lower0) + (1875833/3125000000000 : ℝ)*(lower1) + (12157591/25000000000000 : ℝ)*(lower2) + (76078585217679/5000000000000 : ℝ)*(major0) + (76078585217679/5000000000000 : ℝ)*(major1) + (76078585217679/5000000000000 : ℝ)*(major2) + (380718513/20000000000000 : ℝ)*(sp0) + (8381014783/25000000000000 : ℝ)*(sp5) + (504591483/12500000000000 : ℝ)*(sp6) + (270546761/6250000000000 : ℝ)*(sp7) + (2287487389879327/100000000000000 : ℝ)*(sp12) + (57186394235319/2500000000000 : ℝ)*(sp13) + (571871314185007/25000000000000 : ℝ)*(sp14) + (12277670764073/1562500000000 : ℝ)*(sp15) + (49110953603053/6250000000000 : ℝ)*(f.failure) + (571872323367973/25000000000000 : ℝ)*(f.sum) + (3839666025317/2381000000000000000000000000 : ℝ)*base65 + (155263861642636917/119050000000000000000000000000000 : ℝ)*base68 + (37395432894763083/119050000000000000000000000000000 : ℝ)*base69 + (705332503509736917/119050000000000000000000000000000 : ℝ)*base72 + (3014365886757/595250000000000000000000000 : ℝ)*base73 + (243085202558136917/119050000000000000000000000000000 : ℝ)*base76 + (755948220089536917/119050000000000000000000000000000 : ℝ)*base78 + (439591099266263083/119050000000000000000000000000000 : ℝ)*base79 + (58038475677/595250000000000000000000000 : ℝ)*base81 + (479181/312500000000000000000 : ℝ)*base89 + (479181/312500000000000000000 : ℝ)*base91 + (479181/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1706_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96819777/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4989/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6671/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58309/100000 : ℝ) else (81351/100000 : ℝ) ≤ X j i ∧ X j i ≤ (45183/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1706_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1706_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96819777/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8567/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4983/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6671/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58309/100000 : ℝ) else (81351/100000 : ℝ) ≤ X j i ∧ X j i ≤ (45183/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1706_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1706_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96819777/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8567/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4983/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6671/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58309/100000 : ℝ) else (81351/100000 : ℝ) ≤ X j i ∧ X j i ≤ (45183/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1706_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

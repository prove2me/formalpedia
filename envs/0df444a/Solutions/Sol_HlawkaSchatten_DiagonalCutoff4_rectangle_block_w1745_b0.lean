-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1745_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:14:16.386694+00:00
-- url     : https://prove2.me/submissions/8e824e31-f247-4956-b2a7-2d32744567c1

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
theorem support_rectangle_w1745_s0_0 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1201514171/10000000000 : ℝ)*x 0 + (5646094011/10000000000 : ℝ)*x 1 + (621262689/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1201514171/10000000000 : ℝ)^5695 ≤ (7550617320463/100000000000000 : ℝ)^4671 := by
    have hnat : (1201514171 : ℕ)^5695*100000000000000^4671 ≤ 7550617320463^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201514171 10000000000 7550617320463 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5646094011/10000000000 : ℝ)^5695 ≤ (49810979527263/100000000000000 : ℝ)^4671 := by
    have hnat : (5646094011 : ℕ)^5695*100000000000000^4671 ≤ 49810979527263^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5646094011 10000000000 49810979527263 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (621262689/1250000000 : ℝ)^5695 ≤ (1332450097869/3125000000000 : ℝ)^4671 := by
    have hnat : (621262689 : ℕ)^5695*3125000000000^4671 ≤ 1332450097869^4671*1250000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621262689 1250000000 1332450097869 3125000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1201514171/10000000000 : ℝ), (5646094011/10000000000 : ℝ), (621262689/1250000000 : ℝ)] ![(7550617320463/100000000000000 : ℝ), (49810979527263/100000000000000 : ℝ), (1332450097869/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1201514171/10000000000 : ℝ)|^5695 ≤ (7550617320463/100000000000000 : ℝ)^4671
        have hw : |(-1201514171/10000000000 : ℝ)|=(1201514171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5646094011/10000000000 : ℝ)|^5695 ≤ (49810979527263/100000000000000 : ℝ)^4671
        have hw : |(5646094011/10000000000 : ℝ)|=(5646094011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(621262689/1250000000 : ℝ)|^5695 ≤ (1332450097869/3125000000000 : ℝ)^4671
        have hw : |(621262689/1250000000 : ℝ)|=(621262689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s0_1 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377717351/10000000000 : ℝ)*x 0 + (-782535329/5000000000 : ℝ)*x 1 + (4970101789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377717351/10000000000 : ℝ)^5695 ≤ (46939484017939/100000000000000 : ℝ)^4671 := by
    have hnat : (5377717351 : ℕ)^5695*100000000000000^4671 ≤ 46939484017939^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377717351 10000000000 46939484017939 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (782535329/5000000000 : ℝ)^5695 ≤ (10422109939429/100000000000000 : ℝ)^4671 := by
    have hnat : (782535329 : ℕ)^5695*100000000000000^4671 ≤ 10422109939429^4671*5000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782535329 5000000000 10422109939429 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4970101789/10000000000 : ℝ)^5695 ≤ (42638406029147/100000000000000 : ℝ)^4671 := by
    have hnat : (4970101789 : ℕ)^5695*100000000000000^4671 ≤ 42638406029147^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4970101789 10000000000 42638406029147 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377717351/10000000000 : ℝ), (-782535329/5000000000 : ℝ), (4970101789/10000000000 : ℝ)] ![(46939484017939/100000000000000 : ℝ), (10422109939429/100000000000000 : ℝ), (42638406029147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377717351/10000000000 : ℝ)|^5695 ≤ (46939484017939/100000000000000 : ℝ)^4671
        have hw : |(5377717351/10000000000 : ℝ)|=(5377717351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-782535329/5000000000 : ℝ)|^5695 ≤ (10422109939429/100000000000000 : ℝ)^4671
        have hw : |(-782535329/5000000000 : ℝ)|=(782535329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4970101789/10000000000 : ℝ)|^5695 ≤ (42638406029147/100000000000000 : ℝ)^4671
        have hw : |(4970101789/10000000000 : ℝ)|=(4970101789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s0_2 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377718297/10000000000 : ℝ)*x 0 + (4970101239/10000000000 : ℝ)*x 1 + (-1565070127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377718297/10000000000 : ℝ)^5695 ≤ (46939494085293/100000000000000 : ℝ)^4671 := by
    have hnat : (5377718297 : ℕ)^5695*100000000000000^4671 ≤ 46939494085293^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377718297 10000000000 46939494085293 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4970101239/10000000000 : ℝ)^5695 ≤ (42638400276307/100000000000000 : ℝ)^4671 := by
    have hnat : (4970101239 : ℕ)^5695*100000000000000^4671 ≤ 42638400276307^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4970101239 10000000000 42638400276307 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1565070127/10000000000 : ℝ)^5695 ≤ (1042210562821/10000000000000 : ℝ)^4671 := by
    have hnat : (1565070127 : ℕ)^5695*10000000000000^4671 ≤ 1042210562821^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1565070127 10000000000 1042210562821 10000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377718297/10000000000 : ℝ), (4970101239/10000000000 : ℝ), (-1565070127/10000000000 : ℝ)] ![(46939494085293/100000000000000 : ℝ), (42638400276307/100000000000000 : ℝ), (1042210562821/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377718297/10000000000 : ℝ)|^5695 ≤ (46939494085293/100000000000000 : ℝ)^4671
        have hw : |(5377718297/10000000000 : ℝ)|=(5377718297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4970101239/10000000000 : ℝ)|^5695 ≤ (42638400276307/100000000000000 : ℝ)^4671
        have hw : |(4970101239/10000000000 : ℝ)|=(4970101239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1565070127/10000000000 : ℝ)|^5695 ≤ (1042210562821/10000000000000 : ℝ)^4671
        have hw : |(-1565070127/10000000000 : ℝ)|=(1565070127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s0_3 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3984981291/10000000000 : ℝ)*x 0 + (2979374527/10000000000 : ℝ)*x 1 + (1031025131/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3984981291/10000000000 : ℝ)^5695 ≤ (6514179672861/20000000000000 : ℝ)^4671 := by
    have hnat : (3984981291 : ℕ)^5695*20000000000000^4671 ≤ 6514179672861^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3984981291 10000000000 6514179672861 20000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2979374527/10000000000 : ℝ)^5695 ≤ (22847578209149/100000000000000 : ℝ)^4671 := by
    have hnat : (2979374527 : ℕ)^5695*100000000000000^4671 ≤ 22847578209149^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2979374527 10000000000 22847578209149 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031025131/2000000000 : ℝ)^5695 ≤ (5572690426529/12500000000000 : ℝ)^4671 := by
    have hnat : (1031025131 : ℕ)^5695*12500000000000^4671 ≤ 5572690426529^4671*2000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031025131 2000000000 5572690426529 12500000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3984981291/10000000000 : ℝ), (2979374527/10000000000 : ℝ), (1031025131/2000000000 : ℝ)] ![(6514179672861/20000000000000 : ℝ), (22847578209149/100000000000000 : ℝ), (5572690426529/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3984981291/10000000000 : ℝ)|^5695 ≤ (6514179672861/20000000000000 : ℝ)^4671
        have hw : |(3984981291/10000000000 : ℝ)|=(3984981291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2979374527/10000000000 : ℝ)|^5695 ≤ (22847578209149/100000000000000 : ℝ)^4671
        have hw : |(2979374527/10000000000 : ℝ)|=(2979374527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1031025131/2000000000 : ℝ)|^5695 ≤ (5572690426529/12500000000000 : ℝ)^4671
        have hw : |(1031025131/2000000000 : ℝ)|=(1031025131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s0_4 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1202988511/10000000000 : ℝ)*x 0 + (4987460681/10000000000 : ℝ)*x 1 + (2814075181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1202988511/10000000000 : ℝ)^5695 ≤ (7561915109557/100000000000000 : ℝ)^4671 := by
    have hnat : (1202988511 : ℕ)^5695*100000000000000^4671 ≤ 7561915109557^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202988511 10000000000 7561915109557 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4987460681/10000000000 : ℝ)^5695 ≤ (10705011102547/25000000000000 : ℝ)^4671 := by
    have hnat : (4987460681 : ℕ)^5695*25000000000000^4671 ≤ 10705011102547^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4987460681 10000000000 10705011102547 25000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2814075181/5000000000 : ℝ)^5695 ≤ (49618040465243/100000000000000 : ℝ)^4671 := by
    have hnat : (2814075181 : ℕ)^5695*100000000000000^4671 ≤ 49618040465243^4671*5000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2814075181 5000000000 49618040465243 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1202988511/10000000000 : ℝ), (4987460681/10000000000 : ℝ), (2814075181/5000000000 : ℝ)] ![(7561915109557/100000000000000 : ℝ), (10705011102547/25000000000000 : ℝ), (49618040465243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1202988511/10000000000 : ℝ)|^5695 ≤ (7561915109557/100000000000000 : ℝ)^4671
        have hw : |(-1202988511/10000000000 : ℝ)|=(1202988511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4987460681/10000000000 : ℝ)|^5695 ≤ (10705011102547/25000000000000 : ℝ)^4671
        have hw : |(4987460681/10000000000 : ℝ)|=(4987460681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2814075181/5000000000 : ℝ)|^5695 ≤ (49618040465243/100000000000000 : ℝ)^4671
        have hw : |(2814075181/5000000000 : ℝ)|=(2814075181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s0_5 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (162404211/312500000 : ℝ)*x 0 + (-90702127/1000000000 : ℝ)*x 1 + (2814075237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162404211/312500000 : ℝ)^5695 ≤ (45022743619283/100000000000000 : ℝ)^4671 := by
    have hnat : (162404211 : ℕ)^5695*100000000000000^4671 ≤ 45022743619283^4671*312500000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162404211 312500000 45022743619283 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90702127/1000000000 : ℝ)^5695 ≤ (5359214701821/100000000000000 : ℝ)^4671 := by
    have hnat : (90702127 : ℕ)^5695*100000000000000^4671 ≤ 5359214701821^4671*1000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90702127 1000000000 5359214701821 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2814075237/5000000000 : ℝ)^5695 ≤ (24809020834551/50000000000000 : ℝ)^4671 := by
    have hnat : (2814075237 : ℕ)^5695*50000000000000^4671 ≤ 24809020834551^4671*5000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2814075237 5000000000 24809020834551 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(162404211/312500000 : ℝ), (-90702127/1000000000 : ℝ), (2814075237/5000000000 : ℝ)] ![(45022743619283/100000000000000 : ℝ), (5359214701821/100000000000000 : ℝ), (24809020834551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(162404211/312500000 : ℝ)|^5695 ≤ (45022743619283/100000000000000 : ℝ)^4671
        have hw : |(162404211/312500000 : ℝ)|=(162404211/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90702127/1000000000 : ℝ)|^5695 ≤ (5359214701821/100000000000000 : ℝ)^4671
        have hw : |(-90702127/1000000000 : ℝ)|=(90702127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2814075237/5000000000 : ℝ)|^5695 ≤ (24809020834551/50000000000000 : ℝ)^4671
        have hw : |(2814075237/5000000000 : ℝ)|=(2814075237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s0_6 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299233623/2500000000 : ℝ)*x 0 + (1407037607/2500000000 : ℝ)*x 1 + (-22675543/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299233623/2500000000 : ℝ)^5695 ≤ (22511370436511/50000000000000 : ℝ)^4671 := by
    have hnat : (1299233623 : ℕ)^5695*50000000000000^4671 ≤ 22511370436511^4671*2500000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299233623 2500000000 22511370436511 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1407037607/2500000000 : ℝ)^5695 ≤ (2480902058733/5000000000000 : ℝ)^4671 := by
    have hnat : (1407037607 : ℕ)^5695*5000000000000^4671 ≤ 2480902058733^4671*2500000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1407037607 2500000000 2480902058733 5000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22675543/250000000 : ℝ)^5695 ≤ (214368717743/4000000000000 : ℝ)^4671 := by
    have hnat : (22675543 : ℕ)^5695*4000000000000^4671 ≤ 214368717743^4671*250000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22675543 250000000 214368717743 4000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299233623/2500000000 : ℝ), (1407037607/2500000000 : ℝ), (-22675543/250000000 : ℝ)] ![(22511370436511/50000000000000 : ℝ), (2480902058733/5000000000000 : ℝ), (214368717743/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299233623/2500000000 : ℝ)|^5695 ≤ (22511370436511/50000000000000 : ℝ)^4671
        have hw : |(1299233623/2500000000 : ℝ)|=(1299233623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1407037607/2500000000 : ℝ)|^5695 ≤ (2480902058733/5000000000000 : ℝ)^4671
        have hw : |(1407037607/2500000000 : ℝ)|=(1407037607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22675543/250000000 : ℝ)|^5695 ≤ (214368717743/4000000000000 : ℝ)^4671
        have hw : |(-22675543/250000000 : ℝ)|=(22675543/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s0_7 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1994863429/5000000000 : ℝ)*x 0 + (20397011/40000000 : ℝ)*x 1 + (1518563809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994863429/5000000000 : ℝ)^5695 ≤ (16309097600201/50000000000000 : ℝ)^4671 := by
    have hnat : (1994863429 : ℕ)^5695*50000000000000^4671 ≤ 16309097600201^4671*5000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994863429 5000000000 16309097600201 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20397011/40000000 : ℝ)^5695 ≤ (10998277337507/25000000000000 : ℝ)^4671 := by
    have hnat : (20397011 : ℕ)^5695*25000000000000^4671 ≤ 10998277337507^4671*40000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20397011 40000000 10998277337507 25000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1518563809/5000000000 : ℝ)^5695 ≤ (182724183033/781250000000 : ℝ)^4671 := by
    have hnat : (1518563809 : ℕ)^5695*781250000000^4671 ≤ 182724183033^4671*5000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518563809 5000000000 182724183033 781250000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1994863429/5000000000 : ℝ), (20397011/40000000 : ℝ), (1518563809/5000000000 : ℝ)] ![(16309097600201/50000000000000 : ℝ), (10998277337507/25000000000000 : ℝ), (182724183033/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1994863429/5000000000 : ℝ)|^5695 ≤ (16309097600201/50000000000000 : ℝ)^4671
        have hw : |(1994863429/5000000000 : ℝ)|=(1994863429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20397011/40000000 : ℝ)|^5695 ≤ (10998277337507/25000000000000 : ℝ)^4671
        have hw : |(20397011/40000000 : ℝ)|=(20397011/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1518563809/5000000000 : ℝ)|^5695 ≤ (182724183033/781250000000 : ℝ)^4671
        have hw : |(1518563809/5000000000 : ℝ)|=(1518563809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1745_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (210930053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6517/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21111/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5679/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5679 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5679*1^1024 ≤ 0^1024*1^5679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5679 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5679/1024 : ℝ) ≤ (620962147999377049/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5679 ≤ (620962147999377049/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5679*100000000000000000000^1024 ≤ 620962147999377049^1024*5^5679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 620962147999377049 100000000000000000000 5679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (620962147999377049/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5679 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5679/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5679 := by
      have hnat : (1 : ℕ)^1024*1^5679 ≤ 1^5679*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5679 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100620962147999377049/100000000000000000000 : ℝ) ≤ (1001116839318889/1000000000000000 : ℝ) ^ (5679/1024 : ℝ) := by
    have hpowers : (100620962147999377049/100000000000000000000 : ℝ)^1024 ≤ (1001116839318889/1000000000000000 : ℝ)^5679 := by
      have hnat : (100620962147999377049 : ℕ)^1024*1000000000000000^5679 ≤ 1001116839318889^5679*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100620962147999377049 100000000000000000000 1001116839318889 1000000000000000 1024 5679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001116839318889/1000000000000000 : ℝ)) (X := (100620962147999377049/100000000000000000000 : ℝ)) (by norm_num) 5679 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50620962147999377049/50000000000000000000 : ℝ) ≤ (501116839318889/500000000000000 : ℝ) ^ (5679/1024 : ℝ) := by
    have hpowers : (50620962147999377049/50000000000000000000 : ℝ)^1024 ≤ (501116839318889/500000000000000 : ℝ)^5679 := by
      have hnat : (50620962147999377049 : ℕ)^1024*500000000000000^5679 ≤ 501116839318889^5679*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50620962147999377049 50000000000000000000 501116839318889 500000000000000 1024 5679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (501116839318889/500000000000000 : ℝ)) (X := (50620962147999377049/50000000000000000000 : ℝ)) (by norm_num) 5679 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1116839318889/400000000000000 : ℝ)*(0 : ℝ))^(5679/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1116839318889/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(620962147999377049/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1116839318889/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5679/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1116839318889/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1001116839318889/1000000000000000 : ℝ) by norm_num, show 1+(620962147999377049/100000000000000000000 : ℝ)+(0 : ℝ)=(100620962147999377049/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(620962147999377049/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1116839318889/400000000000000 : ℝ)*(2/5 : ℝ))^(5679/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1116839318889/400000000000000 : ℝ)*(2/5 : ℝ)=(501116839318889/500000000000000 : ℝ) by norm_num, show 1+2*(620962147999377049/100000000000000000000 : ℝ)=(50620962147999377049/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1116839318889/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5679/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1116839318889/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1116839318889/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5679/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1116839318889/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1116839318889/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5679/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1116839318889/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1201514171/10000000000 : ℝ)*X 0 0+(5646094011/10000000000 : ℝ)*X 0 1+(621262689/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5377717351/10000000000 : ℝ)*X 1 0+(-782535329/5000000000 : ℝ)*X 1 1+(4970101789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5377718297/10000000000 : ℝ)*X 2 0+(4970101239/10000000000 : ℝ)*X 2 1+(-1565070127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3984981291/10000000000 : ℝ)*X 0 0+(2979374527/10000000000 : ℝ)*X 0 1+(1031025131/2000000000 : ℝ)*X 0 2+(3984981291/10000000000 : ℝ)*X 1 0+(2979374527/10000000000 : ℝ)*X 1 1+(1031025131/2000000000 : ℝ)*X 1 2+(3984981291/10000000000 : ℝ)*X 2 0+(2979374527/10000000000 : ℝ)*X 2 1+(1031025131/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1202988511/10000000000 : ℝ)*X 0 0+(4987460681/10000000000 : ℝ)*X 0 1+(2814075181/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((162404211/312500000 : ℝ)*X 1 0+(-90702127/1000000000 : ℝ)*X 1 1+(2814075237/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1299233623/2500000000 : ℝ)*X 2 0+(1407037607/2500000000 : ℝ)*X 2 1+(-22675543/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1994863429/5000000000 : ℝ)*X 0 0+(20397011/40000000 : ℝ)*X 0 1+(1518563809/5000000000 : ℝ)*X 0 2+(1994863429/5000000000 : ℝ)*X 1 0+(20397011/40000000 : ℝ)*X 1 1+(1518563809/5000000000 : ℝ)*X 1 2+(1994863429/5000000000 : ℝ)*X 2 0+(20397011/40000000 : ℝ)*X 2 1+(1518563809/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4468677965036791805169/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1223871153/100000000000000 : ℝ)*(base19) + (726399939/50000000000000 : ℝ)*(base23) + (38819579/50000000000000 : ℝ)*(upper3) + (16832153/100000000000000 : ℝ)*(upper4) + (8395143/2500000000000 : ℝ)*(upper5) + (121183523046993/12500000000000 : ℝ)*(major0) + (121183523046993/12500000000000 : ℝ)*(major1) + (121183523046993/12500000000000 : ℝ)*(major2) + (739655687217653/50000000000000 : ℝ)*(sp0) + (369829737070241/25000000000000 : ℝ)*(sp1) + (18491483991903/1250000000000 : ℝ)*(sp2) + (2872587200781/625000000000 : ℝ)*(sp3) + (2199429203/25000000000000 : ℝ)*(sp4) + (62692041/3125000000000 : ℝ)*(sp7) + (459615958270273/100000000000000 : ℝ)*(f.failure) + (739660086076059/50000000000000 : ℝ)*(f.sum) + (16890947555777/2500000000000000000000000000 : ℝ)*base65 + (10112443260777/5000000000000000000000000000 : ℝ)*base67 + (9835661609223/5000000000000000000000000000 : ℝ)*base70 + (26310462450777/5000000000000000000000000000 : ℝ)*base71 + (7685690530777/2500000000000000000000000000 : ℝ)*base73 + (15549458490777/5000000000000000000000000000 : ℝ)*base75 + (10240182129223/5000000000000000000000000000 : ℝ)*base78 + (14286423150777/5000000000000000000000000000 : ℝ)*base79 + (2486706710777/2500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (72214469/10000000000000000000000 : ℝ)*base89 + (72214469/10000000000000000000000 : ℝ)*base91 + (72214469/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8212666574813393352897/800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5163989/250000000000 : ℝ)*(base19) + (1959624097/100000000000000 : ℝ)*(base23) + (7405259/50000000000000 : ℝ)*(base32) + (354534107/100000000000000 : ℝ)*(upper3) + (61622811/20000000000000 : ℝ)*(upper5) + (40915086226509/4000000000000 : ℝ)*(major0) + (40915086226509/4000000000000 : ℝ)*(major1) + (40915086226509/4000000000000 : ℝ)*(major2) + (4300550809/50000000000000 : ℝ)*(sp1) + (3899725723/50000000000000 : ℝ)*(sp2) + (780408654160559/50000000000000 : ℝ)*(sp4) + (15608066416239/1000000000000 : ℝ)*(sp5) + (780403774622787/50000000000000 : ℝ)*(sp6) + (484936645999369/100000000000000 : ℝ)*(sp7) + (484936660809887/100000000000000 : ℝ)*(f.failure) + (780408654160559/50000000000000 : ℝ)*(f.sum) + (2138594385301/800000000000000000000000000 : ℝ)*base65 + (6612825544299/1600000000000000000000000000 : ℝ)*base68 + (2878332184299/1600000000000000000000000000 : ℝ)*base70 + (2685697316501/1600000000000000000000000000 : ℝ)*base71 + (1321693456299/800000000000000000000000000 : ℝ)*base74 + (9315737761899/1600000000000000000000000000 : ℝ)*base76 + (10110178673301/1600000000000000000000000000 : ℝ)*base77 + (3750077002901/1600000000000000000000000000 : ℝ)*base79 + (1059094532501/800000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (12165989/10000000000000000000000 : ℝ)*base90 + (12165989/10000000000000000000000 : ℝ)*base92 + (12165989/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1745_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (210930053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6517/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21111/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1745_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1745_s1_0 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1249315193/10000000000 : ℝ)*x 0 + (275400869/500000000 : ℝ)*x 1 + (50762961/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1249315193/10000000000 : ℝ)^5695 ≤ (7918445656843/100000000000000 : ℝ)^4671 := by
    have hnat : (1249315193 : ℕ)^5695*100000000000000^4671 ≤ 7918445656843^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249315193 10000000000 7918445656843 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275400869/500000000 : ℝ)^5695 ≤ (48329799745757/100000000000000 : ℝ)^4671 := by
    have hnat : (275400869 : ℕ)^5695*100000000000000^4671 ≤ 48329799745757^4671*500000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275400869 500000000 48329799745757 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50762961/100000000 : ℝ)^5695 ≤ (21875877292647/50000000000000 : ℝ)^4671 := by
    have hnat : (50762961 : ℕ)^5695*50000000000000^4671 ≤ 21875877292647^4671*100000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50762961 100000000 21875877292647 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1249315193/10000000000 : ℝ), (275400869/500000000 : ℝ), (50762961/100000000 : ℝ)] ![(7918445656843/100000000000000 : ℝ), (48329799745757/100000000000000 : ℝ), (21875877292647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1249315193/10000000000 : ℝ)|^5695 ≤ (7918445656843/100000000000000 : ℝ)^4671
        have hw : |(-1249315193/10000000000 : ℝ)|=(1249315193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(275400869/500000000 : ℝ)|^5695 ≤ (48329799745757/100000000000000 : ℝ)^4671
        have hw : |(275400869/500000000 : ℝ)|=(275400869/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(50762961/100000000 : ℝ)|^5695 ≤ (21875877292647/50000000000000 : ℝ)^4671
        have hw : |(50762961/100000000 : ℝ)|=(50762961/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s1_1 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1335236437/2500000000 : ℝ)*x 0 + (-1475534987/10000000000 : ℝ)*x 1 + (634536999/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335236437/2500000000 : ℝ)^5695 ≤ (46548453589933/100000000000000 : ℝ)^4671 := by
    have hnat : (1335236437 : ℕ)^5695*100000000000000^4671 ≤ 46548453589933^4671*2500000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335236437 2500000000 46548453589933 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1475534987/10000000000 : ℝ)^5695 ≤ (1212474118597/12500000000000 : ℝ)^4671 := by
    have hnat : (1475534987 : ℕ)^5695*12500000000000^4671 ≤ 1212474118597^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1475534987 10000000000 1212474118597 12500000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634536999/1250000000 : ℝ)^5695 ≤ (21875876725199/50000000000000 : ℝ)^4671 := by
    have hnat : (634536999 : ℕ)^5695*50000000000000^4671 ≤ 21875876725199^4671*1250000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634536999 1250000000 21875876725199 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1335236437/2500000000 : ℝ), (-1475534987/10000000000 : ℝ), (634536999/1250000000 : ℝ)] ![(46548453589933/100000000000000 : ℝ), (1212474118597/12500000000000 : ℝ), (21875876725199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1335236437/2500000000 : ℝ)|^5695 ≤ (46548453589933/100000000000000 : ℝ)^4671
        have hw : |(1335236437/2500000000 : ℝ)|=(1335236437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1475534987/10000000000 : ℝ)|^5695 ≤ (1212474118597/12500000000000 : ℝ)^4671
        have hw : |(-1475534987/10000000000 : ℝ)|=(1475534987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634536999/1250000000 : ℝ)|^5695 ≤ (21875876725199/50000000000000 : ℝ)^4671
        have hw : |(634536999/1250000000 : ℝ)|=(634536999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s1_2 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1335236329/2500000000 : ℝ)*x 0 + (2538148143/5000000000 : ℝ)*x 1 + (-737767587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335236329/2500000000 : ℝ)^5695 ≤ (46548448999489/100000000000000 : ℝ)^4671 := by
    have hnat : (1335236329 : ℕ)^5695*100000000000000^4671 ≤ 46548448999489^4671*2500000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335236329 2500000000 46548448999489 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2538148143/5000000000 : ℝ)^5695 ≤ (43751756539837/100000000000000 : ℝ)^4671 := by
    have hnat : (2538148143 : ℕ)^5695*100000000000000^4671 ≤ 43751756539837^4671*5000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538148143 5000000000 43751756539837 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (737767587/5000000000 : ℝ)^5695 ≤ (4849897223779/50000000000000 : ℝ)^4671 := by
    have hnat : (737767587 : ℕ)^5695*50000000000000^4671 ≤ 4849897223779^4671*5000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737767587 5000000000 4849897223779 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1335236329/2500000000 : ℝ), (2538148143/5000000000 : ℝ), (-737767587/5000000000 : ℝ)] ![(46548448999489/100000000000000 : ℝ), (43751756539837/100000000000000 : ℝ), (4849897223779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1335236329/2500000000 : ℝ)|^5695 ≤ (46548448999489/100000000000000 : ℝ)^4671
        have hw : |(1335236329/2500000000 : ℝ)|=(1335236329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2538148143/5000000000 : ℝ)|^5695 ≤ (43751756539837/100000000000000 : ℝ)^4671
        have hw : |(2538148143/5000000000 : ℝ)|=(2538148143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-737767587/5000000000 : ℝ)|^5695 ≤ (4849897223779/50000000000000 : ℝ)^4671
        have hw : |(-737767587/5000000000 : ℝ)|=(737767587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s1_3 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4030383329/10000000000 : ℝ)*x 0 + (673791391/2000000000 : ℝ)*x 1 + (4758494491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4030383329/10000000000 : ℝ)^5695 ≤ (33023903463161/100000000000000 : ℝ)^4671 := by
    have hnat : (4030383329 : ℕ)^5695*100000000000000^4671 ≤ 33023903463161^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030383329 10000000000 33023903463161 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673791391/2000000000 : ℝ)^5695 ≤ (13270297418553/50000000000000 : ℝ)^4671 := by
    have hnat : (673791391 : ℕ)^5695*50000000000000^4671 ≤ 13270297418553^4671*2000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673791391 2000000000 13270297418553 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4758494491/10000000000 : ℝ)^5695 ≤ (10108875421513/25000000000000 : ℝ)^4671 := by
    have hnat : (4758494491 : ℕ)^5695*25000000000000^4671 ≤ 10108875421513^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4758494491 10000000000 10108875421513 25000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4030383329/10000000000 : ℝ), (673791391/2000000000 : ℝ), (4758494491/10000000000 : ℝ)] ![(33023903463161/100000000000000 : ℝ), (13270297418553/50000000000000 : ℝ), (10108875421513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4030383329/10000000000 : ℝ)|^5695 ≤ (33023903463161/100000000000000 : ℝ)^4671
        have hw : |(4030383329/10000000000 : ℝ)|=(4030383329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673791391/2000000000 : ℝ)|^5695 ≤ (13270297418553/50000000000000 : ℝ)^4671
        have hw : |(673791391/2000000000 : ℝ)|=(673791391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4758494491/10000000000 : ℝ)|^5695 ≤ (10108875421513/25000000000000 : ℝ)^4671
        have hw : |(4758494491/10000000000 : ℝ)|=(4758494491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s1_4 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-124969619/1000000000 : ℝ)*x 0 + (1016676603/2000000000 : ℝ)*x 1 + (2750389409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (124969619/1000000000 : ℝ)^5695 ≤ (198034749903/2500000000000 : ℝ)^4671 := by
    have hnat : (124969619 : ℕ)^5695*2500000000000^4671 ≤ 198034749903^4671*1000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124969619 1000000000 198034749903 2500000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016676603/2000000000 : ℝ)^5695 ≤ (43826237393559/100000000000000 : ℝ)^4671 := by
    have hnat : (1016676603 : ℕ)^5695*100000000000000^4671 ≤ 43826237393559^4671*2000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016676603 2000000000 43826237393559 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2750389409/5000000000 : ℝ)^5695 ≤ (24126186298493/50000000000000 : ℝ)^4671 := by
    have hnat : (2750389409 : ℕ)^5695*50000000000000^4671 ≤ 24126186298493^4671*5000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750389409 5000000000 24126186298493 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-124969619/1000000000 : ℝ), (1016676603/2000000000 : ℝ), (2750389409/5000000000 : ℝ)] ![(198034749903/2500000000000 : ℝ), (43826237393559/100000000000000 : ℝ), (24126186298493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-124969619/1000000000 : ℝ)|^5695 ≤ (198034749903/2500000000000 : ℝ)^4671
        have hw : |(-124969619/1000000000 : ℝ)|=(124969619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016676603/2000000000 : ℝ)|^5695 ≤ (43826237393559/100000000000000 : ℝ)^4671
        have hw : |(1016676603/2000000000 : ℝ)|=(1016676603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2750389409/5000000000 : ℝ)|^5695 ≤ (24126186298493/50000000000000 : ℝ)^4671
        have hw : |(2750389409/5000000000 : ℝ)|=(2750389409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s1_5 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226333771/10000000000 : ℝ)*x 0 + (-525526031/5000000000 : ℝ)*x 1 + (1100155819/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226333771/10000000000 : ℝ)^5695 ≤ (11333366083981/25000000000000 : ℝ)^4671 := by
    have hnat : (5226333771 : ℕ)^5695*25000000000000^4671 ≤ 11333366083981^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226333771 10000000000 11333366083981 25000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525526031/5000000000 : ℝ)^5695 ≤ (6414160084461/100000000000000 : ℝ)^4671 := by
    have hnat : (525526031 : ℕ)^5695*100000000000000^4671 ≤ 6414160084461^4671*5000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525526031 5000000000 6414160084461 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100155819/2000000000 : ℝ)^5695 ≤ (12063093889871/25000000000000 : ℝ)^4671 := by
    have hnat : (1100155819 : ℕ)^5695*25000000000000^4671 ≤ 12063093889871^4671*2000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100155819 2000000000 12063093889871 25000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226333771/10000000000 : ℝ), (-525526031/5000000000 : ℝ), (1100155819/2000000000 : ℝ)] ![(11333366083981/25000000000000 : ℝ), (6414160084461/100000000000000 : ℝ), (12063093889871/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226333771/10000000000 : ℝ)|^5695 ≤ (11333366083981/25000000000000 : ℝ)^4671
        have hw : |(5226333771/10000000000 : ℝ)|=(5226333771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-525526031/5000000000 : ℝ)|^5695 ≤ (6414160084461/100000000000000 : ℝ)^4671
        have hw : |(-525526031/5000000000 : ℝ)|=(525526031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1100155819/2000000000 : ℝ)|^5695 ≤ (12063093889871/25000000000000 : ℝ)^4671
        have hw : |(1100155819/2000000000 : ℝ)|=(1100155819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s1_6 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653291699/1250000000 : ℝ)*x 0 + (2750389609/5000000000 : ℝ)*x 1 + (-52552607/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653291699/1250000000 : ℝ)^5695 ≤ (45333462442889/100000000000000 : ℝ)^4671 := by
    have hnat : (653291699 : ℕ)^5695*100000000000000^4671 ≤ 45333462442889^4671*1250000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653291699 1250000000 45333462442889 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2750389609/5000000000 : ℝ)^5695 ≤ (24126188437481/50000000000000 : ℝ)^4671 := by
    have hnat : (2750389609 : ℕ)^5695*50000000000000^4671 ≤ 24126188437481^4671*5000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750389609 5000000000 24126188437481 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52552607/500000000 : ℝ)^5695 ≤ (6414160664817/100000000000000 : ℝ)^4671 := by
    have hnat : (52552607 : ℕ)^5695*100000000000000^4671 ≤ 6414160664817^4671*500000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52552607 500000000 6414160664817 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653291699/1250000000 : ℝ), (2750389609/5000000000 : ℝ), (-52552607/500000000 : ℝ)] ![(45333462442889/100000000000000 : ℝ), (24126188437481/50000000000000 : ℝ), (6414160664817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653291699/1250000000 : ℝ)|^5695 ≤ (45333462442889/100000000000000 : ℝ)^4671
        have hw : |(653291699/1250000000 : ℝ)|=(653291699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2750389609/5000000000 : ℝ)|^5695 ≤ (24126188437481/50000000000000 : ℝ)^4671
        have hw : |(2750389609/5000000000 : ℝ)|=(2750389609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52552607/500000000 : ℝ)|^5695 ≤ (6414160664817/100000000000000 : ℝ)^4671
        have hw : |(-52552607/500000000 : ℝ)|=(52552607/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s1_7 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (806321933/2000000000 : ℝ)*x 0 + (4735685711/10000000000 : ℝ)*x 1 + (1696126703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (806321933/2000000000 : ℝ)^5695 ≤ (33036154980363/100000000000000 : ℝ)^4671 := by
    have hnat : (806321933 : ℕ)^5695*100000000000000^4671 ≤ 33036154980363^4671*2000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806321933 2000000000 33036154980363 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4735685711/10000000000 : ℝ)^5695 ≤ (20099658793043/50000000000000 : ℝ)^4671 := by
    have hnat : (4735685711 : ℕ)^5695*50000000000000^4671 ≤ 20099658793043^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4735685711 10000000000 20099658793043 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1696126703/5000000000 : ℝ)^5695 ≤ (1672782963631/6250000000000 : ℝ)^4671 := by
    have hnat : (1696126703 : ℕ)^5695*6250000000000^4671 ≤ 1672782963631^4671*5000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696126703 5000000000 1672782963631 6250000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(806321933/2000000000 : ℝ), (4735685711/10000000000 : ℝ), (1696126703/5000000000 : ℝ)] ![(33036154980363/100000000000000 : ℝ), (20099658793043/50000000000000 : ℝ), (1672782963631/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(806321933/2000000000 : ℝ)|^5695 ≤ (33036154980363/100000000000000 : ℝ)^4671
        have hw : |(806321933/2000000000 : ℝ)|=(806321933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4735685711/10000000000 : ℝ)|^5695 ≤ (20099658793043/50000000000000 : ℝ)^4671
        have hw : |(4735685711/10000000000 : ℝ)|=(4735685711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1696126703/5000000000 : ℝ)|^5695 ≤ (1672782963631/6250000000000 : ℝ)^4671
        have hw : |(1696126703/5000000000 : ℝ)|=(1696126703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1745_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (210930053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6517/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8901/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18161/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6517/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6517/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6517/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6517/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6517/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6517/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6517/100000 : ℝ) ^ (5679/1024 : ℝ) ≤ (6618645454953/25000000000000000000 : ℝ) := by
    have hpowers : (6517/100000 : ℝ)^5679 ≤ (6618645454953/25000000000000000000 : ℝ)^1024 := by
      have hnat : (6517 : ℕ)^5679*25000000000000000000^1024 ≤ 6618645454953^1024*100000^5679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6517 100000 6618645454953 25000000000000000000 5679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6517/100000 : ℝ)) (X := (6618645454953/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5679 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21111/100000 : ℝ) ^ (5679/1024 : ℝ) ≤ (2242355438454713/12500000000000000000 : ℝ) := by
    have hpowers : (21111/100000 : ℝ)^5679 ≤ (2242355438454713/12500000000000000000 : ℝ)^1024 := by
      have hnat : (21111 : ℕ)^5679*12500000000000000000^1024 ≤ 2242355438454713^1024*100000^5679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21111 100000 2242355438454713 12500000000000000000 5679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21111/100000 : ℝ)) (X := (2242355438454713/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5679 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500006618645454953/12500000000000000000 : ℝ) ≤ (10000000954744353/10000000000000000 : ℝ) ^ (5679/1024 : ℝ) := by
    have hpowers : (12500006618645454953/12500000000000000000 : ℝ)^1024 ≤ (10000000954744353/10000000000000000 : ℝ)^5679 := by
      have hnat : (12500006618645454953 : ℕ)^1024*10000000000000000^5679 ≤ 10000000954744353^5679*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500006618645454953 12500000000000000000 10000000954744353 10000000000000000 1024 5679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000954744353/10000000000000000 : ℝ)) (X := (12500006618645454953/12500000000000000000 : ℝ)) (by norm_num) 5679 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25004491329522364379/25000000000000000000 : ℝ) ≤ (10000323914973489/10000000000000000 : ℝ) ^ (5679/1024 : ℝ) := by
    have hpowers : (25004491329522364379/25000000000000000000 : ℝ)^1024 ≤ (10000323914973489/10000000000000000 : ℝ)^5679 := by
      have hnat : (25004491329522364379 : ℕ)^1024*10000000000000000^5679 ≤ 10000323914973489^5679*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004491329522364379 25000000000000000000 10000323914973489 10000000000000000 1024 5679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000323914973489/10000000000000000 : ℝ)) (X := (25004491329522364379/25000000000000000000 : ℝ)) (by norm_num) 5679 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252242355438454713/6250000000000000000 : ℝ) ≤ (80005175001621/80000000000000 : ℝ) ^ (5679/1024 : ℝ) := by
    have hpowers : (6252242355438454713/6250000000000000000 : ℝ)^1024 ≤ (80005175001621/80000000000000 : ℝ)^5679 := by
      have hnat : (6252242355438454713 : ℕ)^1024*80000000000000^5679 ≤ 80005175001621^5679*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252242355438454713 6250000000000000000 80005175001621 80000000000000 1024 5679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80005175001621/80000000000000 : ℝ)) (X := (6252242355438454713/6250000000000000000 : ℝ)) (by norm_num) 5679 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6618645454953/25000000000000000000 : ℝ) ≤ ((72967902234956264529/72970000000000000000 : ℝ)+2*(20185014321/91212500000000 : ℝ)*(6517/100000 : ℝ))^(5679/1024 : ℝ) := by
    rw [show (72967902234956264529/72970000000000000000 : ℝ)+2*(20185014321/91212500000000 : ℝ)*(6517/100000 : ℝ)=(10000000954744353/10000000000000000 : ℝ) by norm_num, show 1+2*(6618645454953/25000000000000000000 : ℝ)=(12500006618645454953/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2242355438454713/12500000000000000000 : ℝ)+(6618645454953/25000000000000000000 : ℝ) ≤ ((72967902234956264529/72970000000000000000 : ℝ)+(20185014321/91212500000000 : ℝ)*((21111/100000 : ℝ)+(6517/100000 : ℝ)))^(5679/1024 : ℝ) := by
    rw [show (72967902234956264529/72970000000000000000 : ℝ)+(20185014321/91212500000000 : ℝ)*((21111/100000 : ℝ)+(6517/100000 : ℝ))=(10000323914973489/10000000000000000 : ℝ) by norm_num, show 1+(2242355438454713/12500000000000000000 : ℝ)+(6618645454953/25000000000000000000 : ℝ)=(25004491329522364379/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2242355438454713/12500000000000000000 : ℝ) ≤ ((72967902234956264529/72970000000000000000 : ℝ)+2*(20185014321/91212500000000 : ℝ)*(21111/100000 : ℝ))^(5679/1024 : ℝ) := by
    rw [show (72967902234956264529/72970000000000000000 : ℝ)+2*(20185014321/91212500000000 : ℝ)*(21111/100000 : ℝ)=(80005175001621/80000000000000 : ℝ) by norm_num, show 1+2*(2242355438454713/12500000000000000000 : ℝ)=(6252242355438454713/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (72967902234956264529/72970000000000000000 : ℝ)*(X 1 0+X 2 0)+(20185014321/91212500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5679/1024 : ℝ)) (lo := (6517/100000 : ℝ)) (hi := (21111/100000 : ℝ)) (c := (72967902234956264529/72970000000000000000 : ℝ)) (alpha := (20185014321/91212500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (72967902234956264529/72970000000000000000 : ℝ)*(X 0 1+X 2 1)+(20185014321/91212500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5679/1024 : ℝ)) (lo := (6517/100000 : ℝ)) (hi := (21111/100000 : ℝ)) (c := (72967902234956264529/72970000000000000000 : ℝ)) (alpha := (20185014321/91212500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (72967902234956264529/72970000000000000000 : ℝ)*(X 0 2+X 1 2)+(20185014321/91212500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5679/1024 : ℝ)) (lo := (6517/100000 : ℝ)) (hi := (21111/100000 : ℝ)) (c := (72967902234956264529/72970000000000000000 : ℝ)) (alpha := (20185014321/91212500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1249315193/10000000000 : ℝ)*X 0 0+(275400869/500000000 : ℝ)*X 0 1+(50762961/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1335236437/2500000000 : ℝ)*X 1 0+(-1475534987/10000000000 : ℝ)*X 1 1+(634536999/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1335236329/2500000000 : ℝ)*X 2 0+(2538148143/5000000000 : ℝ)*X 2 1+(-737767587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4030383329/10000000000 : ℝ)*X 0 0+(673791391/2000000000 : ℝ)*X 0 1+(4758494491/10000000000 : ℝ)*X 0 2+(4030383329/10000000000 : ℝ)*X 1 0+(673791391/2000000000 : ℝ)*X 1 1+(4758494491/10000000000 : ℝ)*X 1 2+(4030383329/10000000000 : ℝ)*X 2 0+(673791391/2000000000 : ℝ)*X 2 1+(4758494491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-124969619/1000000000 : ℝ)*X 0 0+(1016676603/2000000000 : ℝ)*X 0 1+(2750389409/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5226333771/10000000000 : ℝ)*X 1 0+(-525526031/5000000000 : ℝ)*X 1 1+(1100155819/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((653291699/1250000000 : ℝ)*X 2 0+(2750389609/5000000000 : ℝ)*X 2 1+(-52552607/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((806321933/2000000000 : ℝ)*X 0 0+(4735685711/10000000000 : ℝ)*X 0 1+(1696126703/5000000000 : ℝ)*X 0 2+(806321933/2000000000 : ℝ)*X 1 0+(4735685711/10000000000 : ℝ)*X 1 1+(1696126703/5000000000 : ℝ)*X 1 2+(806321933/2000000000 : ℝ)*X 2 0+(4735685711/10000000000 : ℝ)*X 2 1+(1696126703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21112452670068394355108736999/3648500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (179575289/20000000000000 : ℝ)*(base19) + (121390531/20000000000000 : ℝ)*(base23) + (57904729/100000000000000 : ℝ)*(lower2) + (8000077/4000000000000 : ℝ)*(upper3) + (647251/25000000000000 : ℝ)*(lower4) + (1517994926263841/100000000000000 : ℝ)*(major0) + (1517994926263841/100000000000000 : ℝ)*(major1) + (1517994926263841/100000000000000 : ℝ)*(major2) + (463263419885307/20000000000000 : ℝ)*(sp0) + (1158160657646867/50000000000000 : ℝ)*(sp1) + (579080401554381/25000000000000 : ℝ)*(sp2) + (44979076638079/6250000000000 : ℝ)*(sp3) + (1278435911/25000000000000 : ℝ)*(sp4) + (2220261173/100000000000000 : ℝ)*(sp7) + (359833723235219/50000000000000 : ℝ)*(f.failure) + (115816110658509/5000000000000 : ℝ)*(f.sum) + (68961179405489/18242500000000000000000000000 : ℝ)*base65 + (13465459988561395889/7297000000000000000000000000000000 : ℝ)*base67 + (31518959873474395889/7297000000000000000000000000000000 : ℝ)*base69 + (30619795958111395889/7297000000000000000000000000000000 : ℝ)*base71 + (60285037843163/36485000000000000000000000000 : ℝ)*base73 + (26027472374182395889/7297000000000000000000000000000000 : ℝ)*base75 + (64867721452167395889/7297000000000000000000000000000000 : ℝ)*base77 + (44095851382073395889/7297000000000000000000000000000000 : ℝ)*base79 + (86416581203489/18242500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (25136607/5000000000000000000000 : ℝ)*base89 + (25136607/5000000000000000000000 : ℝ)*base91 + (25136607/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5558188578364026025720800297/912125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (794474821/100000000000000 : ℝ)*(base19) + (87708199/10000000000000 : ℝ)*(base23) + (90194521/50000000000000 : ℝ)*(upper3) + (33657403/50000000000000 : ℝ)*(lower4) + (70620089/100000000000000 : ℝ)*(upper5) + (785041852204331/50000000000000 : ℝ)*(major0) + (785041852204331/50000000000000 : ℝ)*(major1) + (785041852204331/50000000000000 : ℝ)*(major2) + (5734657669/100000000000000 : ℝ)*(sp1) + (7370048443/100000000000000 : ℝ)*(sp2) + (239580494812297/10000000000000 : ℝ)*(sp4) + (29947480237381/1250000000000 : ℝ)*(sp5) + (1197898350496269/50000000000000 : ℝ)*(sp6) + (372181128786011/50000000000000 : ℝ)*(sp7) + (372181128786011/50000000000000 : ℝ)*(f.failure) + (239580494812297/10000000000000 : ℝ)*(f.sum) + (35202888916017/18242500000000000000000000000 : ℝ)*base66 + (11554208106915724901/3648500000000000000000000000000000 : ℝ)*base68 + (14967103300615724901/3648500000000000000000000000000000 : ℝ)*base70 + (7028250898520724901/3648500000000000000000000000000000 : ℝ)*base72 + (180982116906799/36485000000000000000000000000 : ℝ)*base74 + (14988800916366275099/3648500000000000000000000000000000 : ℝ)*base75 + (23782301512332724901/3648500000000000000000000000000000 : ℝ)*base78 + (11609312978567724901/3648500000000000000000000000000000 : ℝ)*base80 + (70449828817017/18242500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (25888583/5000000000000000000000 : ℝ)*base89 + (25888583/5000000000000000000000 : ℝ)*base91 + (25888583/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1745_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (210930053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6517/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8901/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18161/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1745_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1745_s2_0 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-156323871/1250000000 : ℝ)*x 0 + (1100786559/2000000000 : ℝ)*x 1 + (317469723/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156323871/1250000000 : ℝ)^5695 ≤ (991038200151/12500000000000 : ℝ)^4671 := by
    have hnat : (156323871 : ℕ)^5695*12500000000000^4671 ≤ 991038200151^4671*1250000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156323871 1250000000 991038200151 12500000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100786559/2000000000 : ℝ)^5695 ≤ (12071526577831/25000000000000 : ℝ)^4671 := by
    have hnat : (1100786559 : ℕ)^5695*25000000000000^4671 ≤ 12071526577831^4671*2000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100786559 2000000000 12071526577831 25000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317469723/625000000 : ℝ)^5695 ≤ (21892794033299/50000000000000 : ℝ)^4671 := by
    have hnat : (317469723 : ℕ)^5695*50000000000000^4671 ≤ 21892794033299^4671*625000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317469723 625000000 21892794033299 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-156323871/1250000000 : ℝ), (1100786559/2000000000 : ℝ), (317469723/625000000 : ℝ)] ![(991038200151/12500000000000 : ℝ), (12071526577831/25000000000000 : ℝ), (21892794033299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-156323871/1250000000 : ℝ)|^5695 ≤ (991038200151/12500000000000 : ℝ)^4671
        have hw : |(-156323871/1250000000 : ℝ)|=(156323871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1100786559/2000000000 : ℝ)|^5695 ≤ (12071526577831/25000000000000 : ℝ)^4671
        have hw : |(1100786559/2000000000 : ℝ)|=(1100786559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317469723/625000000 : ℝ)|^5695 ≤ (21892794033299/50000000000000 : ℝ)^4671
        have hw : |(317469723/625000000 : ℝ)|=(317469723/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s2_1 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067963263/2000000000 : ℝ)*x 0 + (-1472810107/10000000000 : ℝ)*x 1 + (1269878931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067963263/2000000000 : ℝ)^5695 ≤ (23268226240777/50000000000000 : ℝ)^4671 := by
    have hnat : (1067963263 : ℕ)^5695*50000000000000^4671 ≤ 23268226240777^4671*2000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067963263 2000000000 23268226240777 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1472810107/10000000000 : ℝ)^5695 ≤ (4838978898057/50000000000000 : ℝ)^4671 := by
    have hnat : (1472810107 : ℕ)^5695*50000000000000^4671 ≤ 4838978898057^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1472810107 10000000000 4838978898057 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1269878931/2500000000 : ℝ)^5695 ≤ (1094639742653/2500000000000 : ℝ)^4671 := by
    have hnat : (1269878931 : ℕ)^5695*2500000000000^4671 ≤ 1094639742653^4671*2500000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269878931 2500000000 1094639742653 2500000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067963263/2000000000 : ℝ), (-1472810107/10000000000 : ℝ), (1269878931/2500000000 : ℝ)] ![(23268226240777/50000000000000 : ℝ), (4838978898057/50000000000000 : ℝ), (1094639742653/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067963263/2000000000 : ℝ)|^5695 ≤ (23268226240777/50000000000000 : ℝ)^4671
        have hw : |(1067963263/2000000000 : ℝ)|=(1067963263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1472810107/10000000000 : ℝ)|^5695 ≤ (4838978898057/50000000000000 : ℝ)^4671
        have hw : |(-1472810107/10000000000 : ℝ)|=(1472810107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1269878931/2500000000 : ℝ)|^5695 ≤ (1094639742653/2500000000000 : ℝ)^4671
        have hw : |(1269878931/2500000000 : ℝ)|=(1269878931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s2_2 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5339816461/10000000000 : ℝ)*x 0 + (1269878893/2500000000 : ℝ)*x 1 + (-1472810113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5339816461/10000000000 : ℝ)^5695 ≤ (23268227016441/50000000000000 : ℝ)^4671 := by
    have hnat : (5339816461 : ℕ)^5695*50000000000000^4671 ≤ 23268227016441^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5339816461 10000000000 23268227016441 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269878893/2500000000 : ℝ)^5695 ≤ (43785588108637/100000000000000 : ℝ)^4671 := by
    have hnat : (1269878893 : ℕ)^5695*100000000000000^4671 ≤ 43785588108637^4671*2500000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269878893 2500000000 43785588108637 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1472810113/10000000000 : ℝ)^5695 ≤ (1209744730523/12500000000000 : ℝ)^4671 := by
    have hnat : (1472810113 : ℕ)^5695*12500000000000^4671 ≤ 1209744730523^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1472810113 10000000000 1209744730523 12500000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5339816461/10000000000 : ℝ), (1269878893/2500000000 : ℝ), (-1472810113/10000000000 : ℝ)] ![(23268227016441/50000000000000 : ℝ), (43785588108637/100000000000000 : ℝ), (1209744730523/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5339816461/10000000000 : ℝ)|^5695 ≤ (23268227016441/50000000000000 : ℝ)^4671
        have hw : |(5339816461/10000000000 : ℝ)|=(5339816461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1269878893/2500000000 : ℝ)|^5695 ≤ (43785588108637/100000000000000 : ℝ)^4671
        have hw : |(1269878893/2500000000 : ℝ)|=(1269878893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1472810113/10000000000 : ℝ)|^5695 ≤ (1209744730523/12500000000000 : ℝ)^4671
        have hw : |(-1472810113/10000000000 : ℝ)|=(1472810113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s2_3 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (161257/400000 : ℝ)*x 0 + (1690315061/5000000000 : ℝ)*x 1 + (2373330311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161257/400000 : ℝ)^5695 ≤ (33034310061429/100000000000000 : ℝ)^4671 := by
    have hnat : (161257 : ℕ)^5695*100000000000000^4671 ≤ 33034310061429^4671*400000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161257 400000 33034310061429 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1690315061/5000000000 : ℝ)^5695 ≤ (2665275858553/10000000000000 : ℝ)^4671 := by
    have hnat : (1690315061 : ℕ)^5695*10000000000000^4671 ≤ 2665275858553^4671*5000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690315061 5000000000 2665275858553 10000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2373330311/5000000000 : ℝ)^5695 ≤ (20156465671131/50000000000000 : ℝ)^4671 := by
    have hnat : (2373330311 : ℕ)^5695*50000000000000^4671 ≤ 20156465671131^4671*5000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2373330311 5000000000 20156465671131 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161257/400000 : ℝ), (1690315061/5000000000 : ℝ), (2373330311/5000000000 : ℝ)] ![(33034310061429/100000000000000 : ℝ), (2665275858553/10000000000000 : ℝ), (20156465671131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161257/400000 : ℝ)|^5695 ≤ (33034310061429/100000000000000 : ℝ)^4671
        have hw : |(161257/400000 : ℝ)|=(161257/400000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1690315061/5000000000 : ℝ)|^5695 ≤ (2665275858553/10000000000000 : ℝ)^4671
        have hw : |(1690315061/5000000000 : ℝ)|=(1690315061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2373330311/5000000000 : ℝ)|^5695 ≤ (20156465671131/50000000000000 : ℝ)^4671
        have hw : |(2373330311/5000000000 : ℝ)|=(2373330311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s2_4 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-25019053/200000000 : ℝ)*x 0 + (5086364529/10000000000 : ℝ)*x 1 + (5496939929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25019053/200000000 : ℝ)^5695 ≤ (991387661887/12500000000000 : ℝ)^4671 := by
    have hnat : (25019053 : ℕ)^5695*12500000000000^4671 ≤ 991387661887^4671*200000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25019053 200000000 991387661887 12500000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5086364529/10000000000 : ℝ)^5695 ≤ (43857579630041/100000000000000 : ℝ)^4671 := by
    have hnat : (5086364529 : ℕ)^5695*100000000000000^4671 ≤ 43857579630041^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5086364529 10000000000 43857579630041 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5496939929/10000000000 : ℝ)^5695 ≤ (1506603720339/3125000000000 : ℝ)^4671 := by
    have hnat : (5496939929 : ℕ)^5695*3125000000000^4671 ≤ 1506603720339^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496939929 10000000000 1506603720339 3125000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25019053/200000000 : ℝ), (5086364529/10000000000 : ℝ), (5496939929/10000000000 : ℝ)] ![(991387661887/12500000000000 : ℝ), (43857579630041/100000000000000 : ℝ), (1506603720339/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25019053/200000000 : ℝ)|^5695 ≤ (991387661887/12500000000000 : ℝ)^4671
        have hw : |(-25019053/200000000 : ℝ)|=(25019053/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5086364529/10000000000 : ℝ)|^5695 ≤ (43857579630041/100000000000000 : ℝ)^4671
        have hw : |(5086364529/10000000000 : ℝ)|=(5086364529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5496939929/10000000000 : ℝ)|^5695 ≤ (1506603720339/3125000000000 : ℝ)^4671
        have hw : |(5496939929/10000000000 : ℝ)|=(5496939929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s2_5 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5227165657/10000000000 : ℝ)*x 0 + (-263846419/2500000000 : ℝ)*x 1 + (2748469967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5227165657/10000000000 : ℝ)^5695 ≤ (45342262195389/100000000000000 : ℝ)^4671 := by
    have hnat : (5227165657 : ℕ)^5695*100000000000000^4671 ≤ 45342262195389^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227165657 10000000000 45342262195389 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263846419/2500000000 : ℝ)^5695 ≤ (1611604674097/25000000000000 : ℝ)^4671 := by
    have hnat : (263846419 : ℕ)^5695*25000000000000^4671 ≤ 1611604674097^4671*2500000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263846419 2500000000 1611604674097 25000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2748469967/5000000000 : ℝ)^5695 ≤ (9642263820863/20000000000000 : ℝ)^4671 := by
    have hnat : (2748469967 : ℕ)^5695*20000000000000^4671 ≤ 9642263820863^4671*5000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748469967 5000000000 9642263820863 20000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5227165657/10000000000 : ℝ), (-263846419/2500000000 : ℝ), (2748469967/5000000000 : ℝ)] ![(45342262195389/100000000000000 : ℝ), (1611604674097/25000000000000 : ℝ), (9642263820863/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5227165657/10000000000 : ℝ)|^5695 ≤ (45342262195389/100000000000000 : ℝ)^4671
        have hw : |(5227165657/10000000000 : ℝ)|=(5227165657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-263846419/2500000000 : ℝ)|^5695 ≤ (1611604674097/25000000000000 : ℝ)^4671
        have hw : |(-263846419/2500000000 : ℝ)|=(263846419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2748469967/5000000000 : ℝ)|^5695 ≤ (9642263820863/20000000000000 : ℝ)^4671
        have hw : |(2748469967/5000000000 : ℝ)|=(2748469967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s2_6 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (261358283/500000000 : ℝ)*x 0 + (5496939931/10000000000 : ℝ)*x 1 + (-527692837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261358283/500000000 : ℝ)^5695 ≤ (45342262227117/100000000000000 : ℝ)^4671 := by
    have hnat : (261358283 : ℕ)^5695*100000000000000^4671 ≤ 45342262227117^4671*500000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261358283 500000000 45342262227117 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5496939931/10000000000 : ℝ)^5695 ≤ (9642263814447/20000000000000 : ℝ)^4671 := by
    have hnat : (5496939931 : ℕ)^5695*20000000000000^4671 ≤ 9642263814447^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496939931 10000000000 9642263814447 20000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527692837/5000000000 : ℝ)^5695 ≤ (3223209340747/50000000000000 : ℝ)^4671 := by
    have hnat : (527692837 : ℕ)^5695*50000000000000^4671 ≤ 3223209340747^4671*5000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527692837 5000000000 3223209340747 50000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261358283/500000000 : ℝ), (5496939931/10000000000 : ℝ), (-527692837/5000000000 : ℝ)] ![(45342262227117/100000000000000 : ℝ), (9642263814447/20000000000000 : ℝ), (3223209340747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261358283/500000000 : ℝ)|^5695 ≤ (45342262227117/100000000000000 : ℝ)^4671
        have hw : |(261358283/500000000 : ℝ)|=(261358283/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5496939931/10000000000 : ℝ)|^5695 ≤ (9642263814447/20000000000000 : ℝ)^4671
        have hw : |(5496939931/10000000000 : ℝ)|=(5496939931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-527692837/5000000000 : ℝ)|^5695 ≤ (3223209340747/50000000000000 : ℝ)^4671
        have hw : |(-527692837/5000000000 : ℝ)|=(527692837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1745_s2_7 (p : ℝ) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1008147479/2500000000 : ℝ)*x 0 + (295288517/625000000 : ℝ)*x 1 + (3403137839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1008147479/2500000000 : ℝ)^5695 ≤ (33045948611569/100000000000000 : ℝ)^4671 := by
    have hnat : (1008147479 : ℕ)^5695*100000000000000^4671 ≤ 33045948611569^4671*2500000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008147479 2500000000 33045948611569 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (295288517/625000000 : ℝ)^5695 ≤ (40084783718417/100000000000000 : ℝ)^4671 := by
    have hnat : (295288517 : ℕ)^5695*100000000000000^4671 ≤ 40084783718417^4671*625000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295288517 625000000 40084783718417 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3403137839/10000000000 : ℝ)^5695 ≤ (26869267655223/100000000000000 : ℝ)^4671 := by
    have hnat : (3403137839 : ℕ)^5695*100000000000000^4671 ≤ 26869267655223^4671*10000000000^5695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3403137839 10000000000 26869267655223 100000000000000 5695 4671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5695/1024 : ℝ)) 5695 4671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1008147479/2500000000 : ℝ), (295288517/625000000 : ℝ), (3403137839/10000000000 : ℝ)] ![(33045948611569/100000000000000 : ℝ), (40084783718417/100000000000000 : ℝ), (26869267655223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1008147479/2500000000 : ℝ)|^5695 ≤ (33045948611569/100000000000000 : ℝ)^4671
        have hw : |(1008147479/2500000000 : ℝ)|=(1008147479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(295288517/625000000 : ℝ)|^5695 ≤ (40084783718417/100000000000000 : ℝ)^4671
        have hw : |(295288517/625000000 : ℝ)|=(295288517/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3403137839/10000000000 : ℝ)|^5695 ≤ (26869267655223/100000000000000 : ℝ)^4671
        have hw : |(3403137839/10000000000 : ℝ)|=(3403137839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1745_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (210930053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18161/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2243/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (723/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18161/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8901/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18161/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8901/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18161/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8901/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18161/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8901/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18161/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8901/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18161/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8901/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8901/100000 : ℝ) ^ (5679/1024 : ℝ) ≤ (149174396030271/100000000000000000000 : ℝ) := by
    have hpowers : (8901/100000 : ℝ)^5679 ≤ (149174396030271/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8901 : ℕ)^5679*100000000000000000000^1024 ≤ 149174396030271^1024*100000^5679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8901 100000 149174396030271 100000000000000000000 5679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8901/100000 : ℝ)) (X := (149174396030271/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5679 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18161/100000 : ℝ) ^ (5679/1024 : ℝ) ≤ (19462756648113/250000000000000000 : ℝ) := by
    have hpowers : (18161/100000 : ℝ)^5679 ≤ (19462756648113/250000000000000000 : ℝ)^1024 := by
      have hnat : (18161 : ℕ)^5679*250000000000000000^1024 ≤ 19462756648113^1024*100000^5679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18161 100000 19462756648113 250000000000000000 5679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18161/100000 : ℝ)) (X := (19462756648113/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5679 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000149174396030271/50000000000000000000 : ℝ) ≤ (10000005379622989/10000000000000000 : ℝ) ^ (5679/1024 : ℝ) := by
    have hpowers : (50000149174396030271/50000000000000000000 : ℝ)^1024 ≤ (10000005379622989/10000000000000000 : ℝ)^5679 := by
      have hnat : (50000149174396030271 : ℕ)^1024*10000000000000000^5679 ≤ 10000005379622989^5679*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000149174396030271 50000000000000000000 10000005379622989 10000000000000000 1024 5679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000005379622989/10000000000000000 : ℝ)) (X := (50000149174396030271/50000000000000000000 : ℝ)) (by norm_num) 5679 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100007934277055275471/100000000000000000000 : ℝ) ≤ (625008941313961/625000000000000 : ℝ) ^ (5679/1024 : ℝ) := by
    have hpowers : (100007934277055275471/100000000000000000000 : ℝ)^1024 ≤ (625008941313961/625000000000000 : ℝ)^5679 := by
      have hnat : (100007934277055275471 : ℕ)^1024*625000000000000^5679 ≤ 625008941313961^5679*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100007934277055275471 100000000000000000000 625008941313961 625000000000000 1024 5679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625008941313961/625000000000000 : ℝ)) (X := (100007934277055275471/100000000000000000000 : ℝ)) (by norm_num) 5679 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (125019462756648113/125000000000000000 : ℝ) ≤ (10000280742423763/10000000000000000 : ℝ) ^ (5679/1024 : ℝ) := by
    have hpowers : (125019462756648113/125000000000000000 : ℝ)^1024 ≤ (10000280742423763/10000000000000000 : ℝ)^5679 := by
      have hnat : (125019462756648113 : ℕ)^1024*10000000000000000^5679 ≤ 10000280742423763^5679*125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125019462756648113 125000000000000000 10000280742423763 10000000000000000 1024 5679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000280742423763/10000000000000000 : ℝ)) (X := (125019462756648113/125000000000000000 : ℝ)) (by norm_num) 5679 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(149174396030271/100000000000000000000 : ℝ) ≤ ((46298799405509594383/46300000000000000000 : ℝ)+2*(137681400387/926000000000000 : ℝ)*(8901/100000 : ℝ))^(5679/1024 : ℝ) := by
    rw [show (46298799405509594383/46300000000000000000 : ℝ)+2*(137681400387/926000000000000 : ℝ)*(8901/100000 : ℝ)=(10000005379622989/10000000000000000 : ℝ) by norm_num, show 1+2*(149174396030271/100000000000000000000 : ℝ)=(50000149174396030271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19462756648113/250000000000000000 : ℝ)+(149174396030271/100000000000000000000 : ℝ) ≤ ((46298799405509594383/46300000000000000000 : ℝ)+(137681400387/926000000000000 : ℝ)*((18161/100000 : ℝ)+(8901/100000 : ℝ)))^(5679/1024 : ℝ) := by
    rw [show (46298799405509594383/46300000000000000000 : ℝ)+(137681400387/926000000000000 : ℝ)*((18161/100000 : ℝ)+(8901/100000 : ℝ))=(625008941313961/625000000000000 : ℝ) by norm_num, show 1+(19462756648113/250000000000000000 : ℝ)+(149174396030271/100000000000000000000 : ℝ)=(100007934277055275471/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19462756648113/250000000000000000 : ℝ) ≤ ((46298799405509594383/46300000000000000000 : ℝ)+2*(137681400387/926000000000000 : ℝ)*(18161/100000 : ℝ))^(5679/1024 : ℝ) := by
    rw [show (46298799405509594383/46300000000000000000 : ℝ)+2*(137681400387/926000000000000 : ℝ)*(18161/100000 : ℝ)=(10000280742423763/10000000000000000 : ℝ) by norm_num, show 1+2*(19462756648113/250000000000000000 : ℝ)=(125019462756648113/125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46298799405509594383/46300000000000000000 : ℝ)*(X 1 0+X 2 0)+(137681400387/926000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5679/1024 : ℝ)) (lo := (8901/100000 : ℝ)) (hi := (18161/100000 : ℝ)) (c := (46298799405509594383/46300000000000000000 : ℝ)) (alpha := (137681400387/926000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46298799405509594383/46300000000000000000 : ℝ)*(X 0 1+X 2 1)+(137681400387/926000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5679/1024 : ℝ)) (lo := (8901/100000 : ℝ)) (hi := (18161/100000 : ℝ)) (c := (46298799405509594383/46300000000000000000 : ℝ)) (alpha := (137681400387/926000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46298799405509594383/46300000000000000000 : ℝ)*(X 0 2+X 1 2)+(137681400387/926000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5679/1024 : ℝ)) (lo := (8901/100000 : ℝ)) (hi := (18161/100000 : ℝ)) (c := (46298799405509594383/46300000000000000000 : ℝ)) (alpha := (137681400387/926000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-156323871/1250000000 : ℝ)*X 0 0+(1100786559/2000000000 : ℝ)*X 0 1+(317469723/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1067963263/2000000000 : ℝ)*X 1 0+(-1472810107/10000000000 : ℝ)*X 1 1+(1269878931/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5339816461/10000000000 : ℝ)*X 2 0+(1269878893/2500000000 : ℝ)*X 2 1+(-1472810113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((161257/400000 : ℝ)*X 0 0+(1690315061/5000000000 : ℝ)*X 0 1+(2373330311/5000000000 : ℝ)*X 0 2+(161257/400000 : ℝ)*X 1 0+(1690315061/5000000000 : ℝ)*X 1 1+(2373330311/5000000000 : ℝ)*X 1 2+(161257/400000 : ℝ)*X 2 0+(1690315061/5000000000 : ℝ)*X 2 1+(2373330311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-25019053/200000000 : ℝ)*X 0 0+(5086364529/10000000000 : ℝ)*X 0 1+(5496939929/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5227165657/10000000000 : ℝ)*X 1 0+(-263846419/2500000000 : ℝ)*X 1 1+(2748469967/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((261358283/500000000 : ℝ)*X 2 0+(5496939931/10000000000 : ℝ)*X 2 1+(-527692837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1008147479/2500000000 : ℝ)*X 0 0+(295288517/625000000 : ℝ)*X 0 1+(3403137839/10000000000 : ℝ)*X 0 2+(1008147479/2500000000 : ℝ)*X 1 0+(295288517/625000000 : ℝ)*X 1 1+(3403137839/10000000000 : ℝ)*X 1 2+(1008147479/2500000000 : ℝ)*X 2 0+(295288517/625000000 : ℝ)*X 2 1+(3403137839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1745_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9717383311688140496850602979/1157500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (543275851/50000000000000 : ℝ)*(base19) + (27670161/2500000000000 : ℝ)*(base23) + (25624511/12500000000000 : ℝ)*(upper3) + (2358469/10000000000000 : ℝ)*(upper4) + (180563841/100000000000000 : ℝ)*(upper5) + (772060868609329/50000000000000 : ℝ)*(major0) + (772060868609329/50000000000000 : ℝ)*(major1) + (772060868609329/50000000000000 : ℝ)*(major2) + (2356180489565909/100000000000000 : ℝ)*(sp0) + (589047045142251/25000000000000 : ℝ)*(sp1) + (2356188160314267/100000000000000 : ℝ)*(sp2) + (73205085675481/10000000000000 : ℝ)*(sp3) + (8777554797/100000000000000 : ℝ)*(sp4) + (3070723537/100000000000000 : ℝ)*(sp7) + (366026963739173/50000000000000 : ℝ)*(f.failure) + (1178094633560353/50000000000000 : ℝ)*(f.sum) + (171728803619177/23150000000000000000000000000 : ℝ)*base66 + (18923217398715949007/2315000000000000000000000000000000 : ℝ)*base67 + (23166364841875949007/2315000000000000000000000000000000 : ℝ)*base69 + (1314376016284050993/2315000000000000000000000000000000 : ℝ)*base72 + (63040167696077/23150000000000000000000000000 : ℝ)*base74 + (4316111176010949007/2315000000000000000000000000000000 : ℝ)*base75 + (7211192949210949007/2315000000000000000000000000000000 : ℝ)*base77 + (1834425616924050993/2315000000000000000000000000000000 : ℝ)*base80 + (28701691065523/23150000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (60933831/5000000000000000000000 : ℝ)*base90 + (60933831/5000000000000000000000 : ℝ)*base92 + (60933831/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29630486863897313977901894499/2315000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (840262379/50000000000000 : ℝ)*(base19) + (901810597/50000000000000 : ℝ)*(base23) + (17461369/6250000000000 : ℝ)*(upper3) + (26880621/50000000000000 : ℝ)*(lower4) + (267623977/100000000000000 : ℝ)*(upper5) + (1596167019888849/100000000000000 : ℝ)*(major0) + (1596167019888849/100000000000000 : ℝ)*(major1) + (1596167019888849/100000000000000 : ℝ)*(major2) + (11465226017/100000000000000 : ℝ)*(sp1) + (2467965567/20000000000000 : ℝ)*(sp2) + (2435605495357749/100000000000000 : ℝ)*(sp4) + (1217796174803487/50000000000000 : ℝ)*(sp5) + (2435591351908719/100000000000000 : ℝ)*(sp6) + (378364058887533/50000000000000 : ℝ)*(sp7) + (378364058887533/50000000000000 : ℝ)*(f.failure) + (2435605495357749/100000000000000 : ℝ)*(f.sum) + (147282448826763/46300000000000000000000000000 : ℝ)*base65 + (15493160640027114833/4630000000000000000000000000000000 : ℝ)*base68 + (7640527768112885167/4630000000000000000000000000000000 : ℝ)*base69 + (21067937365692885167/4630000000000000000000000000000000 : ℝ)*base71 + (88614481742137/46300000000000000000000000000 : ℝ)*base74 + (4088332701777114833/4630000000000000000000000000000000 : ℝ)*base76 + (30463030570432885167/4630000000000000000000000000000000 : ℝ)*base77 + (5152843741532885167/4630000000000000000000000000000000 : ℝ)*base79 + (136083135962663/46300000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6729249/5000000000000000000000 : ℝ)*base89 + (6729249/5000000000000000000000 : ℝ)*base91 + (6729249/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1745_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (210930053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18161/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2243/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (723/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1745_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1745_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (210930053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2243/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (723/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1745_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1745_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1745_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5679/1024 : ℝ) ≤ p) (hpb : p ≤ (5695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (210930053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2243/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (723/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1745_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

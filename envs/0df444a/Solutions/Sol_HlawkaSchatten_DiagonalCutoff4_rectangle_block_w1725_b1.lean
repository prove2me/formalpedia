-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1725_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:00:54.1401+00:00
-- url     : https://prove2.me/submissions/6d2d0ec7-8d0e-4263-b39b-1d9cc9747fe3

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
theorem support_rectangle_w1725_s3_0 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1359673837/10000000000 : ℝ)*x 0 + (2730310431/5000000000 : ℝ)*x 1 + (5139920487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1359673837/10000000000 : ℝ)^5423 ≤ (8545068061253/100000000000000 : ℝ)^4399 := by
    have hnat : (1359673837 : ℕ)^5423*100000000000000^4399 ≤ 8545068061253^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359673837 10000000000 8545068061253 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730310431/5000000000 : ℝ)^5423 ≤ (23716313363083/50000000000000 : ℝ)^4399 := by
    have hnat : (2730310431 : ℕ)^5423*50000000000000^4399 ≤ 23716313363083^4399*5000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730310431 5000000000 23716313363083 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139920487/10000000000 : ℝ)^5423 ≤ (44022305196763/100000000000000 : ℝ)^4399 := by
    have hnat : (5139920487 : ℕ)^5423*100000000000000^4399 ≤ 44022305196763^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139920487 10000000000 44022305196763 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1359673837/10000000000 : ℝ), (2730310431/5000000000 : ℝ), (5139920487/10000000000 : ℝ)] ![(8545068061253/100000000000000 : ℝ), (23716313363083/50000000000000 : ℝ), (44022305196763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1359673837/10000000000 : ℝ)|^5423 ≤ (8545068061253/100000000000000 : ℝ)^4399
        have hw : |(-1359673837/10000000000 : ℝ)|=(1359673837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730310431/5000000000 : ℝ)|^5423 ≤ (23716313363083/50000000000000 : ℝ)^4399
        have hw : |(2730310431/5000000000 : ℝ)|=(2730310431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139920487/10000000000 : ℝ)|^5423 ≤ (44022305196763/100000000000000 : ℝ)^4399
        have hw : |(5139920487/10000000000 : ℝ)|=(5139920487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_s3_1 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067694731/2000000000 : ℝ)*x 0 + (-762882901/5000000000 : ℝ)*x 1 + (1027984097/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067694731/2000000000 : ℝ)^5423 ≤ (46128062019183/100000000000000 : ℝ)^4399 := by
    have hnat : (1067694731 : ℕ)^5423*100000000000000^4399 ≤ 46128062019183^4399*2000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067694731 2000000000 46128062019183 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (762882901/5000000000 : ℝ)^5423 ≤ (76950256181/781250000000 : ℝ)^4399 := by
    have hnat : (762882901 : ℕ)^5423*781250000000^4399 ≤ 76950256181^4399*5000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      762882901 5000000000 76950256181 781250000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027984097/2000000000 : ℝ)^5423 ≤ (22011152587823/50000000000000 : ℝ)^4399 := by
    have hnat : (1027984097 : ℕ)^5423*50000000000000^4399 ≤ 22011152587823^4399*2000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027984097 2000000000 22011152587823 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067694731/2000000000 : ℝ), (-762882901/5000000000 : ℝ), (1027984097/2000000000 : ℝ)] ![(46128062019183/100000000000000 : ℝ), (76950256181/781250000000 : ℝ), (22011152587823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067694731/2000000000 : ℝ)|^5423 ≤ (46128062019183/100000000000000 : ℝ)^4399
        have hw : |(1067694731/2000000000 : ℝ)|=(1067694731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-762882901/5000000000 : ℝ)|^5423 ≤ (76950256181/781250000000 : ℝ)^4399
        have hw : |(-762882901/5000000000 : ℝ)|=(762882901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027984097/2000000000 : ℝ)|^5423 ≤ (22011152587823/50000000000000 : ℝ)^4399
        have hw : |(1027984097/2000000000 : ℝ)|=(1027984097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_s3_2 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2669236827/5000000000 : ℝ)*x 0 + (1027984097/2000000000 : ℝ)*x 1 + (-1525765803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2669236827/5000000000 : ℝ)^5423 ≤ (46128062008531/100000000000000 : ℝ)^4399 := by
    have hnat : (2669236827 : ℕ)^5423*100000000000000^4399 ≤ 46128062008531^4399*5000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2669236827 5000000000 46128062008531 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027984097/2000000000 : ℝ)^5423 ≤ (22011152587823/50000000000000 : ℝ)^4399 := by
    have hnat : (1027984097 : ℕ)^5423*50000000000000^4399 ≤ 22011152587823^4399*2000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027984097 2000000000 22011152587823 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1525765803/10000000000 : ℝ)^5423 ≤ (4924816399563/50000000000000 : ℝ)^4399 := by
    have hnat : (1525765803 : ℕ)^5423*50000000000000^4399 ≤ 4924816399563^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1525765803 10000000000 4924816399563 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2669236827/5000000000 : ℝ), (1027984097/2000000000 : ℝ), (-1525765803/10000000000 : ℝ)] ![(46128062008531/100000000000000 : ℝ), (22011152587823/50000000000000 : ℝ), (4924816399563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2669236827/5000000000 : ℝ)|^5423 ≤ (46128062008531/100000000000000 : ℝ)^4399
        have hw : |(2669236827/5000000000 : ℝ)|=(2669236827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027984097/2000000000 : ℝ)|^5423 ≤ (22011152587823/50000000000000 : ℝ)^4399
        have hw : |(1027984097/2000000000 : ℝ)|=(1027984097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1525765803/10000000000 : ℝ)|^5423 ≤ (4924816399563/50000000000000 : ℝ)^4399
        have hw : |(-1525765803/10000000000 : ℝ)|=(1525765803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_s3_3 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4085910323/10000000000 : ℝ)*x 0 + (724459257/2000000000 : ℝ)*x 1 + (4583959347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4085910323/10000000000 : ℝ)^5423 ≤ (33174514486201/100000000000000 : ℝ)^4399 := by
    have hnat : (4085910323 : ℕ)^5423*100000000000000^4399 ≤ 33174514486201^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4085910323 10000000000 33174514486201 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (724459257/2000000000 : ℝ)^5423 ≤ (28597243999361/100000000000000 : ℝ)^4399 := by
    have hnat : (724459257 : ℕ)^5423*100000000000000^4399 ≤ 28597243999361^4399*2000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      724459257 2000000000 28597243999361 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4583959347/10000000000 : ℝ)^5423 ≤ (38228241495141/100000000000000 : ℝ)^4399 := by
    have hnat : (4583959347 : ℕ)^5423*100000000000000^4399 ≤ 38228241495141^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4583959347 10000000000 38228241495141 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4085910323/10000000000 : ℝ), (724459257/2000000000 : ℝ), (4583959347/10000000000 : ℝ)] ![(33174514486201/100000000000000 : ℝ), (28597243999361/100000000000000 : ℝ), (38228241495141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4085910323/10000000000 : ℝ)|^5423 ≤ (33174514486201/100000000000000 : ℝ)^4399
        have hw : |(4085910323/10000000000 : ℝ)|=(4085910323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(724459257/2000000000 : ℝ)|^5423 ≤ (28597243999361/100000000000000 : ℝ)^4399
        have hw : |(724459257/2000000000 : ℝ)|=(724459257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4583959347/10000000000 : ℝ)|^5423 ≤ (38228241495141/100000000000000 : ℝ)^4399
        have hw : |(4583959347/10000000000 : ℝ)|=(4583959347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_s3_4 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-339954149/2500000000 : ℝ)*x 0 + (321469919/625000000 : ℝ)*x 1 + (2728484561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (339954149/2500000000 : ℝ)^5423 ≤ (1709234822491/20000000000000 : ℝ)^4399 := by
    have hnat : (339954149 : ℕ)^5423*20000000000000^4399 ≤ 1709234822491^4399*2500000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339954149 2500000000 1709234822491 20000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321469919/625000000 : ℝ)^5423 ≤ (22030150024131/50000000000000 : ℝ)^4399 := by
    have hnat : (321469919 : ℕ)^5423*50000000000000^4399 ≤ 22030150024131^4399*625000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321469919 625000000 22030150024131 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728484561/5000000000 : ℝ)^5423 ≤ (1184838145477/2500000000000 : ℝ)^4399 := by
    have hnat : (2728484561 : ℕ)^5423*2500000000000^4399 ≤ 1184838145477^4399*5000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728484561 5000000000 1184838145477 2500000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-339954149/2500000000 : ℝ), (321469919/625000000 : ℝ), (2728484561/5000000000 : ℝ)] ![(1709234822491/20000000000000 : ℝ), (22030150024131/50000000000000 : ℝ), (1184838145477/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-339954149/2500000000 : ℝ)|^5423 ≤ (1709234822491/20000000000000 : ℝ)^4399
        have hw : |(-339954149/2500000000 : ℝ)|=(339954149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321469919/625000000 : ℝ)|^5423 ≤ (22030150024131/50000000000000 : ℝ)^4399
        have hw : |(321469919/625000000 : ℝ)|=(321469919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728484561/5000000000 : ℝ)|^5423 ≤ (1184838145477/2500000000000 : ℝ)^4399
        have hw : |(2728484561/5000000000 : ℝ)|=(2728484561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_s3_5 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313158039/2500000000 : ℝ)*x 0 + (-302179289/2500000000 : ℝ)*x 1 + (5456969133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313158039/2500000000 : ℝ)^5423 ≤ (45215391311137/100000000000000 : ℝ)^4399 := by
    have hnat : (1313158039 : ℕ)^5423*100000000000000^4399 ≤ 45215391311137^4399*2500000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313158039 2500000000 45215391311137 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (302179289/2500000000 : ℝ)^5423 ≤ (7391082741027/100000000000000 : ℝ)^4399 := by
    have hnat : (302179289 : ℕ)^5423*100000000000000^4399 ≤ 7391082741027^4399*2500000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302179289 2500000000 7391082741027 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456969133/10000000000 : ℝ)^5423 ≤ (47393525936853/100000000000000 : ℝ)^4399 := by
    have hnat : (5456969133 : ℕ)^5423*100000000000000^4399 ≤ 47393525936853^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456969133 10000000000 47393525936853 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313158039/2500000000 : ℝ), (-302179289/2500000000 : ℝ), (5456969133/10000000000 : ℝ)] ![(45215391311137/100000000000000 : ℝ), (7391082741027/100000000000000 : ℝ), (47393525936853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313158039/2500000000 : ℝ)|^5423 ≤ (45215391311137/100000000000000 : ℝ)^4399
        have hw : |(1313158039/2500000000 : ℝ)|=(1313158039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-302179289/2500000000 : ℝ)|^5423 ≤ (7391082741027/100000000000000 : ℝ)^4399
        have hw : |(-302179289/2500000000 : ℝ)|=(302179289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456969133/10000000000 : ℝ)|^5423 ≤ (47393525936853/100000000000000 : ℝ)^4399
        have hw : |(5456969133/10000000000 : ℝ)|=(5456969133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_s3_6 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252632143/10000000000 : ℝ)*x 0 + (5456969169/10000000000 : ℝ)*x 1 + (-1208717123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252632143/10000000000 : ℝ)^5423 ≤ (22607695586591/50000000000000 : ℝ)^4399 := by
    have hnat : (5252632143 : ℕ)^5423*50000000000000^4399 ≤ 22607695586591^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252632143 10000000000 22607695586591 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456969169/10000000000 : ℝ)^5423 ≤ (11848381580573/25000000000000 : ℝ)^4399 := by
    have hnat : (5456969169 : ℕ)^5423*25000000000000^4399 ≤ 11848381580573^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456969169 10000000000 11848381580573 25000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1208717123/10000000000 : ℝ)^5423 ≤ (3695541246133/50000000000000 : ℝ)^4399 := by
    have hnat : (1208717123 : ℕ)^5423*50000000000000^4399 ≤ 3695541246133^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208717123 10000000000 3695541246133 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252632143/10000000000 : ℝ), (5456969169/10000000000 : ℝ), (-1208717123/10000000000 : ℝ)] ![(22607695586591/50000000000000 : ℝ), (11848381580573/25000000000000 : ℝ), (3695541246133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252632143/10000000000 : ℝ)|^5423 ≤ (22607695586591/50000000000000 : ℝ)^4399
        have hw : |(5252632143/10000000000 : ℝ)|=(5252632143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456969169/10000000000 : ℝ)|^5423 ≤ (11848381580573/25000000000000 : ℝ)^4399
        have hw : |(5456969169/10000000000 : ℝ)|=(5456969169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1208717123/10000000000 : ℝ)|^5423 ≤ (3695541246133/50000000000000 : ℝ)^4399
        have hw : |(-1208717123/10000000000 : ℝ)|=(1208717123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_s3_7 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (63849039/156250000 : ℝ)*x 0 + (4573169651/10000000000 : ℝ)*x 1 + (3633246537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63849039/156250000 : ℝ)^5423 ≤ (33178800227599/100000000000000 : ℝ)^4399 := by
    have hnat : (63849039 : ℕ)^5423*100000000000000^4399 ≤ 33178800227599^4399*156250000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63849039 156250000 33178800227599 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4573169651/10000000000 : ℝ)^5423 ≤ (38117344609999/100000000000000 : ℝ)^4399 := by
    have hnat : (4573169651 : ℕ)^5423*100000000000000^4399 ≤ 38117344609999^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4573169651 10000000000 38117344609999 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3633246537/10000000000 : ℝ)^5423 ≤ (14351927574661/50000000000000 : ℝ)^4399 := by
    have hnat : (3633246537 : ℕ)^5423*50000000000000^4399 ≤ 14351927574661^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3633246537 10000000000 14351927574661 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(63849039/156250000 : ℝ), (4573169651/10000000000 : ℝ), (3633246537/10000000000 : ℝ)] ![(33178800227599/100000000000000 : ℝ), (38117344609999/100000000000000 : ℝ), (14351927574661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(63849039/156250000 : ℝ)|^5423 ≤ (33178800227599/100000000000000 : ℝ)^4399
        have hw : |(63849039/156250000 : ℝ)|=(63849039/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4573169651/10000000000 : ℝ)|^5423 ≤ (38117344609999/100000000000000 : ℝ)^4399
        have hw : |(4573169651/10000000000 : ℝ)|=(4573169651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3633246537/10000000000 : ℝ)|^5423 ≤ (14351927574661/50000000000000 : ℝ)^4399
        have hw : |(3633246537/10000000000 : ℝ)|=(3633246537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1725_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (99965851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (531/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2529/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10121/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3397/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (531/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2529/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (531/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2529/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (531/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2529/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (531/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2529/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (531/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2529/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (531/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2529/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2529/25000 : ℝ) ^ (5415/1024 : ℝ) ≤ (273760724153579/50000000000000000000 : ℝ) := by
    have hpowers : (2529/25000 : ℝ)^5415 ≤ (273760724153579/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2529 : ℕ)^5415*50000000000000000000^1024 ≤ 273760724153579^1024*25000^5415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2529 25000 273760724153579 50000000000000000000 5415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2529/25000 : ℝ)) (X := (273760724153579/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5415 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (531/3125 : ℝ) ^ (5415/1024 : ℝ) ≤ (425046815075289/5000000000000000000 : ℝ) := by
    have hpowers : (531/3125 : ℝ)^5415 ≤ (425046815075289/5000000000000000000 : ℝ)^1024 := by
      have hnat : (531 : ℕ)^5415*5000000000000000000^1024 ≤ 425046815075289^1024*3125^5415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        531 3125 425046815075289 5000000000000000000 5415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (531/3125 : ℝ)) (X := (425046815075289/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5415 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000273760724153579/25000000000000000000 : ℝ) ≤ (625001294227779/625000000000000 : ℝ) ^ (5415/1024 : ℝ) := by
    have hpowers : (25000273760724153579/25000000000000000000 : ℝ)^1024 ≤ (625001294227779/625000000000000 : ℝ)^5415 := by
      have hnat : (25000273760724153579 : ℕ)^1024*625000000000000^5415 ≤ 625001294227779^5415*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000273760724153579 25000000000000000000 625001294227779 625000000000000 1024 5415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625001294227779/625000000000000 : ℝ)) (X := (25000273760724153579/25000000000000000000 : ℝ)) (by norm_num) 5415 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004524228874906469/50000000000000000000 : ℝ) ≤ (2000034220797151/2000000000000000 : ℝ) ^ (5415/1024 : ℝ) := by
    have hpowers : (50004524228874906469/50000000000000000000 : ℝ)^1024 ≤ (2000034220797151/2000000000000000 : ℝ)^5415 := by
      have hnat : (50004524228874906469 : ℕ)^1024*2000000000000000^5415 ≤ 2000034220797151^5415*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004524228874906469 50000000000000000000 2000034220797151 2000000000000000 1024 5415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000034220797151/2000000000000000 : ℝ)) (X := (50004524228874906469/50000000000000000000 : ℝ)) (by norm_num) 5415 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2500425046815075289/2500000000000000000 : ℝ) ≤ (5000160750163523/5000000000000000 : ℝ) ^ (5415/1024 : ℝ) := by
    have hpowers : (2500425046815075289/2500000000000000000 : ℝ)^1024 ≤ (5000160750163523/5000000000000000 : ℝ)^5415 := by
      have hnat : (2500425046815075289 : ℕ)^1024*5000000000000000^5415 ≤ 5000160750163523^5415*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500425046815075289 2500000000000000000 5000160750163523 5000000000000000 1024 5415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000160750163523/5000000000000000 : ℝ)) (X := (2500425046815075289/2500000000000000000 : ℝ)) (by norm_num) 5415 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(273760724153579/50000000000000000000 : ℝ) ≤ ((954959716208143541/955000000000000000 : ℝ)+2*(150396341291/687600000000000 : ℝ)*(2529/25000 : ℝ))^(5415/1024 : ℝ) := by
    rw [show (954959716208143541/955000000000000000 : ℝ)+2*(150396341291/687600000000000 : ℝ)*(2529/25000 : ℝ)=(625001294227779/625000000000000 : ℝ) by norm_num, show 1+2*(273760724153579/50000000000000000000 : ℝ)=(25000273760724153579/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(425046815075289/5000000000000000000 : ℝ)+(273760724153579/50000000000000000000 : ℝ) ≤ ((954959716208143541/955000000000000000 : ℝ)+(150396341291/687600000000000 : ℝ)*((531/3125 : ℝ)+(2529/25000 : ℝ)))^(5415/1024 : ℝ) := by
    rw [show (954959716208143541/955000000000000000 : ℝ)+(150396341291/687600000000000 : ℝ)*((531/3125 : ℝ)+(2529/25000 : ℝ))=(2000034220797151/2000000000000000 : ℝ) by norm_num, show 1+(425046815075289/5000000000000000000 : ℝ)+(273760724153579/50000000000000000000 : ℝ)=(50004524228874906469/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(425046815075289/5000000000000000000 : ℝ) ≤ ((954959716208143541/955000000000000000 : ℝ)+2*(150396341291/687600000000000 : ℝ)*(531/3125 : ℝ))^(5415/1024 : ℝ) := by
    rw [show (954959716208143541/955000000000000000 : ℝ)+2*(150396341291/687600000000000 : ℝ)*(531/3125 : ℝ)=(5000160750163523/5000000000000000 : ℝ) by norm_num, show 1+2*(425046815075289/5000000000000000000 : ℝ)=(2500425046815075289/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (954959716208143541/955000000000000000 : ℝ)*(X 1 0+X 2 0)+(150396341291/687600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5415/1024 : ℝ)) (lo := (2529/25000 : ℝ)) (hi := (531/3125 : ℝ)) (c := (954959716208143541/955000000000000000 : ℝ)) (alpha := (150396341291/687600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (954959716208143541/955000000000000000 : ℝ)*(X 0 1+X 2 1)+(150396341291/687600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5415/1024 : ℝ)) (lo := (2529/25000 : ℝ)) (hi := (531/3125 : ℝ)) (c := (954959716208143541/955000000000000000 : ℝ)) (alpha := (150396341291/687600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (954959716208143541/955000000000000000 : ℝ)*(X 0 2+X 1 2)+(150396341291/687600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5415/1024 : ℝ)) (lo := (2529/25000 : ℝ)) (hi := (531/3125 : ℝ)) (c := (954959716208143541/955000000000000000 : ℝ)) (alpha := (150396341291/687600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1359673837/10000000000 : ℝ)*X 0 0+(2730310431/5000000000 : ℝ)*X 0 1+(5139920487/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1067694731/2000000000 : ℝ)*X 1 0+(-762882901/5000000000 : ℝ)*X 1 1+(1027984097/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2669236827/5000000000 : ℝ)*X 2 0+(1027984097/2000000000 : ℝ)*X 2 1+(-1525765803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4085910323/10000000000 : ℝ)*X 0 0+(724459257/2000000000 : ℝ)*X 0 1+(4583959347/10000000000 : ℝ)*X 0 2+(4085910323/10000000000 : ℝ)*X 1 0+(724459257/2000000000 : ℝ)*X 1 1+(4583959347/10000000000 : ℝ)*X 1 2+(4085910323/10000000000 : ℝ)*X 2 0+(724459257/2000000000 : ℝ)*X 2 1+(4583959347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-339954149/2500000000 : ℝ)*X 0 0+(321469919/625000000 : ℝ)*X 0 1+(2728484561/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1313158039/2500000000 : ℝ)*X 1 0+(-302179289/2500000000 : ℝ)*X 1 1+(5456969133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5252632143/10000000000 : ℝ)*X 2 0+(5456969169/10000000000 : ℝ)*X 2 1+(-1208717123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((63849039/156250000 : ℝ)*X 0 0+(4573169651/10000000000 : ℝ)*X 0 1+(3633246537/10000000000 : ℝ)*X 0 2+(63849039/156250000 : ℝ)*X 1 0+(4573169651/10000000000 : ℝ)*X 1 1+(3633246537/10000000000 : ℝ)*X 1 2+(63849039/156250000 : ℝ)*X 2 0+(4573169651/10000000000 : ℝ)*X 2 1+(3633246537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (544499120648778053529966959/47750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (164583349/10000000000000 : ℝ)*(base19) + (774220887/50000000000000 : ℝ)*(base23) + (5168049/10000000000000 : ℝ)*(lower2) + (274409423/100000000000000 : ℝ)*(upper3) + (205408043/100000000000000 : ℝ)*(upper5) + (2079042823396833/100000000000000 : ℝ)*(major0) + (2079042823396833/100000000000000 : ℝ)*(major1) + (2079042823396833/100000000000000 : ℝ)*(major2) + (3118192193155273/100000000000000 : ℝ)*(sp0) + (623641420345027/20000000000000 : ℝ)*(sp1) + (3118207199116851/100000000000000 : ℝ)*(sp2) + (51993526843413/5000000000000 : ℝ)*(sp3) + (2069300419/12500000000000 : ℝ)*(sp4) + (239290507/4000000000000 : ℝ)*(sp7) + (207975303826187/20000000000000 : ℝ)*(f.failure) + (1559104373779313/50000000000000 : ℝ)*(f.sum) + (56226483257219/11460000000000000000000000000 : ℝ)*base66 + (1417909427349570541/286500000000000000000000000000000 : ℝ)*base68 + (186794841581070541/286500000000000000000000000000000 : ℝ)*base70 + (992173735278570541/286500000000000000000000000000000 : ℝ)*base72 + (51739833298499/11460000000000000000000000000 : ℝ)*base74 + (854971994748929459/286500000000000000000000000000000 : ℝ)*base75 + (1817902584737070541/286500000000000000000000000000000 : ℝ)*base78 + (174402678963929459/286500000000000000000000000000000 : ℝ)*base79 + (2235258635519/11460000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (9540137/1000000000000000000000 : ℝ)*base89 + (9540137/1000000000000000000000 : ℝ)*base91 + (9540137/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (191422514054136290480258079/23875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (210897141/20000000000000 : ℝ)*(base19) + (144320413/12500000000000 : ℝ)*(base23) + (157836459/50000000000000 : ℝ)*(lower1) + (16689251/10000000000000 : ℝ)*(upper3) + (46002359/100000000000000 : ℝ)*(lower4) + (161824321/100000000000000 : ℝ)*(upper5) + (1063550008276273/50000000000000 : ℝ)*(major0) + (1063550008276273/50000000000000 : ℝ)*(major1) + (1063550008276273/50000000000000 : ℝ)*(major2) + (623945843/50000000000000 : ℝ)*(sp2) + (638057288362243/20000000000000 : ℝ)*(sp4) + (319028538732551/10000000000000 : ℝ)*(sp5) + (1595142019678113/50000000000000 : ℝ)*(sp6) + (1063913324037299/100000000000000 : ℝ)*(sp7) + (1063913324037299/100000000000000 : ℝ)*(f.failure) + (638057288362243/20000000000000 : ℝ)*(f.sum) + (48792774550717/17190000000000000000000000000 : ℝ)*base66 + (11341201368845688263/429750000000000000000000000000000 : ℝ)*base68 + (690161806230311737/429750000000000000000000000000000 : ℝ)*base69 + (13911615130531938263/429750000000000000000000000000000 : ℝ)*base72 + (1097333988533/17190000000000000000000000000 : ℝ)*base73 + (10365905873130311737/429750000000000000000000000000000 : ℝ)*base75 + (5233378315041438263/429750000000000000000000000000000 : ℝ)*base78 + (5253070013129688263/429750000000000000000000000000000 : ℝ)*base80 + (118753449807113/17190000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (50276449/5000000000000000000000 : ℝ)*base89 + (50276449/5000000000000000000000 : ℝ)*base91 + (50276449/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1725_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (99965851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (531/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2529/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10121/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3397/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1725_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1725_box_0 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-526121807/5000000000 : ℝ)*x 0 + (108188539/200000000 : ℝ)*x 1 + (5409426989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526121807/5000000000 : ℝ)^5423 ≤ (6229947076659/100000000000000 : ℝ)^4399 := by
    have hnat : (526121807 : ℕ)^5423*100000000000000^4399 ≤ 6229947076659^4399*5000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526121807 5000000000 6229947076659 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108188539/200000000 : ℝ)^5423 ≤ (11721256560987/25000000000000 : ℝ)^4399 := by
    have hnat : (108188539 : ℕ)^5423*25000000000000^4399 ≤ 11721256560987^4399*200000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108188539 200000000 11721256560987 25000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409426989/10000000000 : ℝ)^5423 ≤ (23442513330329/50000000000000 : ℝ)^4399 := by
    have hnat : (5409426989 : ℕ)^5423*50000000000000^4399 ≤ 23442513330329^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409426989 10000000000 23442513330329 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526121807/5000000000 : ℝ), (108188539/200000000 : ℝ), (5409426989/10000000000 : ℝ)] ![(6229947076659/100000000000000 : ℝ), (11721256560987/25000000000000 : ℝ), (23442513330329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526121807/5000000000 : ℝ)|^5423 ≤ (6229947076659/100000000000000 : ℝ)^4399
        have hw : |(-526121807/5000000000 : ℝ)|=(526121807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108188539/200000000 : ℝ)|^5423 ≤ (11721256560987/25000000000000 : ℝ)^4399
        have hw : |(108188539/200000000 : ℝ)|=(108188539/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409426989/10000000000 : ℝ)|^5423 ≤ (23442513330329/50000000000000 : ℝ)^4399
        have hw : |(5409426989/10000000000 : ℝ)|=(5409426989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_box_1 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224527571/10000000000 : ℝ)*x 0 + (-164331949/1250000000 : ℝ)*x 1 + (5409426929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224527571/10000000000 : ℝ)^5423 ≤ (11229333254333/25000000000000 : ℝ)^4399 := by
    have hnat : (5224527571 : ℕ)^5423*25000000000000^4399 ≤ 11229333254333^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224527571 10000000000 11229333254333 25000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164331949/1250000000 : ℝ)^5423 ≤ (4098820474179/50000000000000 : ℝ)^4399 := by
    have hnat : (164331949 : ℕ)^5423*50000000000000^4399 ≤ 4098820474179^4399*1250000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164331949 1250000000 4098820474179 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409426929/10000000000 : ℝ)^5423 ≤ (23442513009783/50000000000000 : ℝ)^4399 := by
    have hnat : (5409426929 : ℕ)^5423*50000000000000^4399 ≤ 23442513009783^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409426929 10000000000 23442513009783 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224527571/10000000000 : ℝ), (-164331949/1250000000 : ℝ), (5409426929/10000000000 : ℝ)] ![(11229333254333/25000000000000 : ℝ), (4098820474179/50000000000000 : ℝ), (23442513009783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224527571/10000000000 : ℝ)|^5423 ≤ (11229333254333/25000000000000 : ℝ)^4399
        have hw : |(5224527571/10000000000 : ℝ)|=(5224527571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-164331949/1250000000 : ℝ)|^5423 ≤ (4098820474179/50000000000000 : ℝ)^4399
        have hw : |(-164331949/1250000000 : ℝ)|=(164331949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409426929/10000000000 : ℝ)|^5423 ≤ (23442513009783/50000000000000 : ℝ)^4399
        have hw : |(5409426929/10000000000 : ℝ)|=(5409426929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_box_2 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224527533/10000000000 : ℝ)*x 0 + (676178357/1250000000 : ℝ)*x 1 + (-657327873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224527533/10000000000 : ℝ)^5423 ≤ (44917332614581/100000000000000 : ℝ)^4399 := by
    have hnat : (5224527533 : ℕ)^5423*100000000000000^4399 ≤ 44917332614581^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224527533 10000000000 44917332614581 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676178357/1250000000 : ℝ)^5423 ≤ (11721256309893/25000000000000 : ℝ)^4399 := by
    have hnat : (676178357 : ℕ)^5423*25000000000000^4399 ≤ 11721256309893^4399*1250000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676178357 1250000000 11721256309893 25000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657327873/5000000000 : ℝ)^5423 ≤ (8197642132171/100000000000000 : ℝ)^4399 := by
    have hnat : (657327873 : ℕ)^5423*100000000000000^4399 ≤ 8197642132171^4399*5000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657327873 5000000000 8197642132171 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224527533/10000000000 : ℝ), (676178357/1250000000 : ℝ), (-657327873/5000000000 : ℝ)] ![(44917332614581/100000000000000 : ℝ), (11721256309893/25000000000000 : ℝ), (8197642132171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224527533/10000000000 : ℝ)|^5423 ≤ (44917332614581/100000000000000 : ℝ)^4399
        have hw : |(5224527533/10000000000 : ℝ)|=(5224527533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676178357/1250000000 : ℝ)|^5423 ≤ (11721256309893/25000000000000 : ℝ)^4399
        have hw : |(676178357/1250000000 : ℝ)|=(676178357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-657327873/5000000000 : ℝ)|^5423 ≤ (8197642132171/100000000000000 : ℝ)^4399
        have hw : |(-657327873/5000000000 : ℝ)|=(657327873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_box_3 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2233152951/5000000000 : ℝ)*x 0 + (1958337501/5000000000 : ℝ)*x 1 + (3916674791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2233152951/5000000000 : ℝ)^5423 ≤ (3702230093659/10000000000000 : ℝ)^4399 := by
    have hnat : (2233152951 : ℕ)^5423*10000000000000^4399 ≤ 3702230093659^4399*5000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233152951 5000000000 3702230093659 10000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1958337501/5000000000 : ℝ)^5423 ≤ (1968053160821/6250000000000 : ℝ)^4399 := by
    have hnat : (1958337501 : ℕ)^5423*6250000000000^4399 ≤ 1968053160821^4399*5000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958337501 5000000000 1968053160821 6250000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3916674791/10000000000 : ℝ)^5423 ≤ (787221212047/2500000000000 : ℝ)^4399 := by
    have hnat : (3916674791 : ℕ)^5423*2500000000000^4399 ≤ 787221212047^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3916674791 10000000000 787221212047 2500000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2233152951/5000000000 : ℝ), (1958337501/5000000000 : ℝ), (3916674791/10000000000 : ℝ)] ![(3702230093659/10000000000000 : ℝ), (1968053160821/6250000000000 : ℝ), (787221212047/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2233152951/5000000000 : ℝ)|^5423 ≤ (3702230093659/10000000000000 : ℝ)^4399
        have hw : |(2233152951/5000000000 : ℝ)|=(2233152951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1958337501/5000000000 : ℝ)|^5423 ≤ (1968053160821/6250000000000 : ℝ)^4399
        have hw : |(1958337501/5000000000 : ℝ)|=(1958337501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3916674791/10000000000 : ℝ)|^5423 ≤ (787221212047/2500000000000 : ℝ)^4399
        have hw : |(3916674791/10000000000 : ℝ)|=(3916674791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_box_4 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1687498737/10000000000 : ℝ)*x 0 + (5177922457/10000000000 : ℝ)*x 1 + (5177922477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1687498737/10000000000 : ℝ)^5423 ≤ (5576106444243/50000000000000 : ℝ)^4399 := by
    have hnat : (1687498737 : ℕ)^5423*50000000000000^4399 ≤ 5576106444243^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687498737 10000000000 5576106444243 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177922457/10000000000 : ℝ)^5423 ≤ (44423893441463/100000000000000 : ℝ)^4399 := by
    have hnat : (5177922457 : ℕ)^5423*100000000000000^4399 ≤ 44423893441463^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177922457 10000000000 44423893441463 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177922477/10000000000 : ℝ)^5423 ≤ (11105973413249/25000000000000 : ℝ)^4399 := by
    have hnat : (5177922477 : ℕ)^5423*25000000000000^4399 ≤ 11105973413249^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177922477 10000000000 11105973413249 25000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1687498737/10000000000 : ℝ), (5177922457/10000000000 : ℝ), (5177922477/10000000000 : ℝ)] ![(5576106444243/50000000000000 : ℝ), (44423893441463/100000000000000 : ℝ), (11105973413249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1687498737/10000000000 : ℝ)|^5423 ≤ (5576106444243/50000000000000 : ℝ)^4399
        have hw : |(-1687498737/10000000000 : ℝ)|=(1687498737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177922457/10000000000 : ℝ)|^5423 ≤ (44423893441463/100000000000000 : ℝ)^4399
        have hw : |(5177922457/10000000000 : ℝ)|=(5177922457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177922477/10000000000 : ℝ)|^5423 ≤ (11105973413249/25000000000000 : ℝ)^4399
        have hw : |(5177922477/10000000000 : ℝ)|=(5177922477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_box_5 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345243793/2500000000 : ℝ)*x 0 + (-88590737/625000000 : ℝ)*x 1 + (5177922353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345243793/2500000000 : ℝ)^5423 ≤ (46581209536051/100000000000000 : ℝ)^4399 := by
    have hnat : (1345243793 : ℕ)^5423*100000000000000^4399 ≤ 46581209536051^4399*2500000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345243793 2500000000 46581209536051 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88590737/625000000 : ℝ)^5423 ≤ (281090565999/3125000000000 : ℝ)^4399 := by
    have hnat : (88590737 : ℕ)^5423*3125000000000^4399 ≤ 281090565999^4399*625000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88590737 625000000 281090565999 3125000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177922353/10000000000 : ℝ)^5423 ≤ (8884778468299/20000000000000 : ℝ)^4399 := by
    have hnat : (5177922353 : ℕ)^5423*20000000000000^4399 ≤ 8884778468299^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177922353 10000000000 8884778468299 20000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345243793/2500000000 : ℝ), (-88590737/625000000 : ℝ), (5177922353/10000000000 : ℝ)] ![(46581209536051/100000000000000 : ℝ), (281090565999/3125000000000 : ℝ), (8884778468299/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345243793/2500000000 : ℝ)|^5423 ≤ (46581209536051/100000000000000 : ℝ)^4399
        have hw : |(1345243793/2500000000 : ℝ)|=(1345243793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88590737/625000000 : ℝ)|^5423 ≤ (281090565999/3125000000000 : ℝ)^4399
        have hw : |(-88590737/625000000 : ℝ)|=(88590737/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177922353/10000000000 : ℝ)|^5423 ≤ (8884778468299/20000000000000 : ℝ)^4399
        have hw : |(5177922353/10000000000 : ℝ)|=(5177922353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_box_6 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380974939/10000000000 : ℝ)*x 0 + (5177922583/10000000000 : ℝ)*x 1 + (-708725899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380974939/10000000000 : ℝ)^5423 ≤ (23290603524767/50000000000000 : ℝ)^4399 := by
    have hnat : (5380974939 : ℕ)^5423*50000000000000^4399 ≤ 23290603524767^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380974939 10000000000 23290603524767 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177922583/10000000000 : ℝ)^5423 ≤ (44423894774117/100000000000000 : ℝ)^4399 := by
    have hnat : (5177922583 : ℕ)^5423*100000000000000^4399 ≤ 44423894774117^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177922583 10000000000 44423894774117 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (708725899/5000000000 : ℝ)^5423 ≤ (4497449079453/50000000000000 : ℝ)^4399 := by
    have hnat : (708725899 : ℕ)^5423*50000000000000^4399 ≤ 4497449079453^4399*5000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708725899 5000000000 4497449079453 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380974939/10000000000 : ℝ), (5177922583/10000000000 : ℝ), (-708725899/5000000000 : ℝ)] ![(23290603524767/50000000000000 : ℝ), (44423894774117/100000000000000 : ℝ), (4497449079453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380974939/10000000000 : ℝ)|^5423 ≤ (23290603524767/50000000000000 : ℝ)^4399
        have hw : |(5380974939/10000000000 : ℝ)|=(5380974939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177922583/10000000000 : ℝ)|^5423 ≤ (44423894774117/100000000000000 : ℝ)^4399
        have hw : |(5177922583/10000000000 : ℝ)|=(5177922583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-708725899/5000000000 : ℝ)|^5423 ≤ (4497449079453/50000000000000 : ℝ)^4399
        have hw : |(-708725899/5000000000 : ℝ)|=(708725899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_box_7 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1844550437/5000000000 : ℝ)*x 0 + (4304472571/10000000000 : ℝ)*x 1 + (860894459/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1844550437/5000000000 : ℝ)^5423 ≤ (29248810919537/100000000000000 : ℝ)^4399 := by
    have hnat : (1844550437 : ℕ)^5423*100000000000000^4399 ≤ 29248810919537^4399*5000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844550437 5000000000 29248810919537 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4304472571/10000000000 : ℝ)^5423 ≤ (35375595925567/100000000000000 : ℝ)^4399 := by
    have hnat : (4304472571 : ℕ)^5423*100000000000000^4399 ≤ 35375595925567^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304472571 10000000000 35375595925567 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (860894459/2000000000 : ℝ)^5423 ≤ (35375593129301/100000000000000 : ℝ)^4399 := by
    have hnat : (860894459 : ℕ)^5423*100000000000000^4399 ≤ 35375593129301^4399*2000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860894459 2000000000 35375593129301 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1844550437/5000000000 : ℝ), (4304472571/10000000000 : ℝ), (860894459/2000000000 : ℝ)] ![(29248810919537/100000000000000 : ℝ), (35375595925567/100000000000000 : ℝ), (35375593129301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1844550437/5000000000 : ℝ)|^5423 ≤ (29248810919537/100000000000000 : ℝ)^4399
        have hw : |(1844550437/5000000000 : ℝ)|=(1844550437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4304472571/10000000000 : ℝ)|^5423 ≤ (35375595925567/100000000000000 : ℝ)^4399
        have hw : |(4304472571/10000000000 : ℝ)|=(4304472571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(860894459/2000000000 : ℝ)|^5423 ≤ (35375593129301/100000000000000 : ℝ)^4399
        have hw : |(860894459/2000000000 : ℝ)|=(860894459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_box_8 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-775340131/5000000000 : ℝ)*x 0 + (1251584071/2500000000 : ℝ)*x 1 + (5451554871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (775340131/5000000000 : ℝ)^5423 ≤ (10048283666951/100000000000000 : ℝ)^4399 := by
    have hnat : (775340131 : ℕ)^5423*100000000000000^4399 ≤ 10048283666951^4399*5000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775340131 5000000000 10048283666951 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1251584071/2500000000 : ℝ)^5423 ≤ (21308076117243/50000000000000 : ℝ)^4399 := by
    have hnat : (1251584071 : ℕ)^5423*50000000000000^4399 ≤ 21308076117243^4399*2500000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251584071 2500000000 21308076117243 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451554871/10000000000 : ℝ)^5423 ≤ (11833891020817/25000000000000 : ℝ)^4399 := by
    have hnat : (5451554871 : ℕ)^5423*25000000000000^4399 ≤ 11833891020817^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451554871 10000000000 11833891020817 25000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-775340131/5000000000 : ℝ), (1251584071/2500000000 : ℝ), (5451554871/10000000000 : ℝ)] ![(10048283666951/100000000000000 : ℝ), (21308076117243/50000000000000 : ℝ), (11833891020817/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-775340131/5000000000 : ℝ)|^5423 ≤ (10048283666951/100000000000000 : ℝ)^4399
        have hw : |(-775340131/5000000000 : ℝ)|=(775340131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1251584071/2500000000 : ℝ)|^5423 ≤ (21308076117243/50000000000000 : ℝ)^4399
        have hw : |(1251584071/2500000000 : ℝ)|=(1251584071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451554871/10000000000 : ℝ)|^5423 ≤ (11833891020817/25000000000000 : ℝ)^4399
        have hw : |(5451554871/10000000000 : ℝ)|=(5451554871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_box_9 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299020521/2500000000 : ℝ)*x 0 + (-323801699/2500000000 : ℝ)*x 1 + (5451555079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299020521/2500000000 : ℝ)^5423 ≤ (1394251223927/3125000000000 : ℝ)^4399 := by
    have hnat : (1299020521 : ℕ)^5423*3125000000000^4399 ≤ 1394251223927^4399*2500000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299020521 2500000000 1394251223927 3125000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323801699/2500000000 : ℝ)^5423 ≤ (8048394510879/100000000000000 : ℝ)^4399 := by
    have hnat : (323801699 : ℕ)^5423*100000000000000^4399 ≤ 8048394510879^4399*2500000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323801699 2500000000 8048394510879 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451555079/10000000000 : ℝ)^5423 ≤ (23667783154867/50000000000000 : ℝ)^4399 := by
    have hnat : (5451555079 : ℕ)^5423*50000000000000^4399 ≤ 23667783154867^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451555079 10000000000 23667783154867 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299020521/2500000000 : ℝ), (-323801699/2500000000 : ℝ), (5451555079/10000000000 : ℝ)] ![(1394251223927/3125000000000 : ℝ), (8048394510879/100000000000000 : ℝ), (23667783154867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299020521/2500000000 : ℝ)|^5423 ≤ (1394251223927/3125000000000 : ℝ)^4399
        have hw : |(1299020521/2500000000 : ℝ)|=(1299020521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-323801699/2500000000 : ℝ)|^5423 ≤ (8048394510879/100000000000000 : ℝ)^4399
        have hw : |(-323801699/2500000000 : ℝ)|=(323801699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451555079/10000000000 : ℝ)|^5423 ≤ (23667783154867/50000000000000 : ℝ)^4399
        have hw : |(5451555079/10000000000 : ℝ)|=(5451555079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_box_10 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649510211/1250000000 : ℝ)*x 0 + (5451555129/10000000000 : ℝ)*x 1 + (-1295207273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649510211/1250000000 : ℝ)^5423 ≤ (44616034973909/100000000000000 : ℝ)^4399 := by
    have hnat : (649510211 : ℕ)^5423*100000000000000^4399 ≤ 44616034973909^4399*1250000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649510211 1250000000 44616034973909 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451555129/10000000000 : ℝ)^5423 ≤ (23667783422471/50000000000000 : ℝ)^4399 := by
    have hnat : (5451555129 : ℕ)^5423*50000000000000^4399 ≤ 23667783422471^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451555129 10000000000 23667783422471 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295207273/10000000000 : ℝ)^5423 ≤ (8048398164927/100000000000000 : ℝ)^4399 := by
    have hnat : (1295207273 : ℕ)^5423*100000000000000^4399 ≤ 8048398164927^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295207273 10000000000 8048398164927 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649510211/1250000000 : ℝ), (5451555129/10000000000 : ℝ), (-1295207273/10000000000 : ℝ)] ![(44616034973909/100000000000000 : ℝ), (23667783422471/50000000000000 : ℝ), (8048398164927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649510211/1250000000 : ℝ)|^5423 ≤ (44616034973909/100000000000000 : ℝ)^4399
        have hw : |(649510211/1250000000 : ℝ)|=(649510211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451555129/10000000000 : ℝ)|^5423 ≤ (23667783422471/50000000000000 : ℝ)^4399
        have hw : |(5451555129/10000000000 : ℝ)|=(5451555129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1295207273/10000000000 : ℝ)|^5423 ≤ (8048398164927/100000000000000 : ℝ)^4399
        have hw : |(-1295207273/10000000000 : ℝ)|=(1295207273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_box_11 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (460278441/1000000000 : ℝ)*x 0 + (3845920023/10000000000 : ℝ)*x 1 + (961479847/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (460278441/1000000000 : ℝ)^5423 ≤ (3842187163631/10000000000000 : ℝ)^4399 := by
    have hnat : (460278441 : ℕ)^5423*10000000000000^4399 ≤ 3842187163631^4399*1000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460278441 1000000000 3842187163631 10000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3845920023/10000000000 : ℝ)^5423 ≤ (7697266826899/25000000000000 : ℝ)^4399 := by
    have hnat : (3845920023 : ℕ)^5423*25000000000000^4399 ≤ 7697266826899^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3845920023 10000000000 7697266826899 25000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961479847/2500000000 : ℝ)^5423 ≤ (15394530520327/50000000000000 : ℝ)^4399 := by
    have hnat : (961479847 : ℕ)^5423*50000000000000^4399 ≤ 15394530520327^4399*2500000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961479847 2500000000 15394530520327 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(460278441/1000000000 : ℝ), (3845920023/10000000000 : ℝ), (961479847/2500000000 : ℝ)] ![(3842187163631/10000000000000 : ℝ), (7697266826899/25000000000000 : ℝ), (15394530520327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(460278441/1000000000 : ℝ)|^5423 ≤ (3842187163631/10000000000000 : ℝ)^4399
        have hw : |(460278441/1000000000 : ℝ)|=(460278441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3845920023/10000000000 : ℝ)|^5423 ≤ (7697266826899/25000000000000 : ℝ)^4399
        have hw : |(3845920023/10000000000 : ℝ)|=(3845920023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(961479847/2500000000 : ℝ)|^5423 ≤ (15394530520327/50000000000000 : ℝ)^4399
        have hw : |(961479847/2500000000 : ℝ)|=(961479847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_box_12 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-236641227/2000000000 : ℝ)*x 0 + (5573158539/10000000000 : ℝ)*x 1 + (5152972911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (236641227/2000000000 : ℝ)^5423 ≤ (7199249938923/100000000000000 : ℝ)^4399 := by
    have hnat : (236641227 : ℕ)^5423*100000000000000^4399 ≤ 7199249938923^4399*2000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236641227 2000000000 7199249938923 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5573158539/10000000000 : ℝ)^5423 ≤ (9728118037289/20000000000000 : ℝ)^4399 := by
    have hnat : (5573158539 : ℕ)^5423*20000000000000^4399 ≤ 9728118037289^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5573158539 10000000000 9728118037289 20000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152972911/10000000000 : ℝ)^5423 ≤ (2208007992889/5000000000000 : ℝ)^4399 := by
    have hnat : (5152972911 : ℕ)^5423*5000000000000^4399 ≤ 2208007992889^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152972911 10000000000 2208007992889 5000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-236641227/2000000000 : ℝ), (5573158539/10000000000 : ℝ), (5152972911/10000000000 : ℝ)] ![(7199249938923/100000000000000 : ℝ), (9728118037289/20000000000000 : ℝ), (2208007992889/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-236641227/2000000000 : ℝ)|^5423 ≤ (7199249938923/100000000000000 : ℝ)^4399
        have hw : |(-236641227/2000000000 : ℝ)|=(236641227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5573158539/10000000000 : ℝ)|^5423 ≤ (9728118037289/20000000000000 : ℝ)^4399
        have hw : |(5573158539/10000000000 : ℝ)|=(5573158539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152972911/10000000000 : ℝ)|^5423 ≤ (2208007992889/5000000000000 : ℝ)^4399
        have hw : |(5152972911/10000000000 : ℝ)|=(5152972911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_box_13 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698934167/5000000000 : ℝ)*x 0 + (-1428101581/10000000000 : ℝ)*x 1 + (2576486507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698934167/5000000000 : ℝ)^5423 ≤ (46761554864239/100000000000000 : ℝ)^4399 := by
    have hnat : (2698934167 : ℕ)^5423*100000000000000^4399 ≤ 46761554864239^4399*5000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698934167 5000000000 46761554864239 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1428101581/10000000000 : ℝ)^5423 ≤ (9078284177943/100000000000000 : ℝ)^4399 := by
    have hnat : (1428101581 : ℕ)^5423*100000000000000^4399 ≤ 9078284177943^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428101581 10000000000 9078284177943 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576486507/5000000000 : ℝ)^5423 ≤ (44160160945947/100000000000000 : ℝ)^4399 := by
    have hnat : (2576486507 : ℕ)^5423*100000000000000^4399 ≤ 44160160945947^4399*5000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576486507 5000000000 44160160945947 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698934167/5000000000 : ℝ), (-1428101581/10000000000 : ℝ), (2576486507/5000000000 : ℝ)] ![(46761554864239/100000000000000 : ℝ), (9078284177943/100000000000000 : ℝ), (44160160945947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698934167/5000000000 : ℝ)|^5423 ≤ (46761554864239/100000000000000 : ℝ)^4399
        have hw : |(2698934167/5000000000 : ℝ)|=(2698934167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1428101581/10000000000 : ℝ)|^5423 ≤ (9078284177943/100000000000000 : ℝ)^4399
        have hw : |(-1428101581/10000000000 : ℝ)|=(1428101581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576486507/5000000000 : ℝ)|^5423 ≤ (44160160945947/100000000000000 : ℝ)^4399
        have hw : |(2576486507/5000000000 : ℝ)|=(2576486507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_box_14 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698934217/5000000000 : ℝ)*x 0 + (5152972891/10000000000 : ℝ)*x 1 + (-1428101609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698934217/5000000000 : ℝ)^5423 ≤ (46761555932193/100000000000000 : ℝ)^4399 := by
    have hnat : (2698934217 : ℕ)^5423*100000000000000^4399 ≤ 46761555932193^4399*5000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698934217 5000000000 46761555932193 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152972891/10000000000 : ℝ)^5423 ≤ (22080079823243/50000000000000 : ℝ)^4399 := by
    have hnat : (5152972891 : ℕ)^5423*50000000000000^4399 ≤ 22080079823243^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152972891 10000000000 22080079823243 50000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1428101609/10000000000 : ℝ)^5423 ≤ (9078284397369/100000000000000 : ℝ)^4399 := by
    have hnat : (1428101609 : ℕ)^5423*100000000000000^4399 ≤ 9078284397369^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428101609 10000000000 9078284397369 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698934217/5000000000 : ℝ), (5152972891/10000000000 : ℝ), (-1428101609/10000000000 : ℝ)] ![(46761555932193/100000000000000 : ℝ), (22080079823243/50000000000000 : ℝ), (9078284397369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698934217/5000000000 : ℝ)|^5423 ≤ (46761555932193/100000000000000 : ℝ)^4399
        have hw : |(2698934217/5000000000 : ℝ)|=(2698934217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5152972891/10000000000 : ℝ)|^5423 ≤ (22080079823243/50000000000000 : ℝ)^4399
        have hw : |(5152972891/10000000000 : ℝ)|=(5152972891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1428101609/10000000000 : ℝ)|^5423 ≤ (9078284397369/100000000000000 : ℝ)^4399
        have hw : |(-1428101609/10000000000 : ℝ)|=(1428101609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1725_box_15 (p : ℝ) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (90058963/250000000 : ℝ)*x 0 + (4346151861/10000000000 : ℝ)*x 1 + (4346151471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90058963/250000000 : ℝ)^5423 ≤ (5680664708929/20000000000000 : ℝ)^4399 := by
    have hnat : (90058963 : ℕ)^5423*20000000000000^4399 ≤ 5680664708929^4399*250000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90058963 250000000 5680664708929 20000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4346151861/10000000000 : ℝ)^5423 ≤ (35798340200489/100000000000000 : ℝ)^4399 := by
    have hnat : (4346151861 : ℕ)^5423*100000000000000^4399 ≤ 35798340200489^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346151861 10000000000 35798340200489 100000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4346151471/10000000000 : ℝ)^5423 ≤ (3579833624037/10000000000000 : ℝ)^4399 := by
    have hnat : (4346151471 : ℕ)^5423*10000000000000^4399 ≤ 3579833624037^4399*10000000000^5423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346151471 10000000000 3579833624037 10000000000000 5423 4399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5423/1024 : ℝ)) 5423 4399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(90058963/250000000 : ℝ), (4346151861/10000000000 : ℝ), (4346151471/10000000000 : ℝ)] ![(5680664708929/20000000000000 : ℝ), (35798340200489/100000000000000 : ℝ), (3579833624037/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(90058963/250000000 : ℝ)|^5423 ≤ (5680664708929/20000000000000 : ℝ)^4399
        have hw : |(90058963/250000000 : ℝ)|=(90058963/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4346151861/10000000000 : ℝ)|^5423 ≤ (35798340200489/100000000000000 : ℝ)^4399
        have hw : |(4346151861/10000000000 : ℝ)|=(4346151861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4346151471/10000000000 : ℝ)|^5423 ≤ (3579833624037/10000000000000 : ℝ)^4399
        have hw : |(4346151471/10000000000 : ℝ)|=(4346151471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1725_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (99965851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3397/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(16723/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1836/3125 : ℝ) ∧ (16391/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90633/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3397/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10121/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3397/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10121/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3397/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10121/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3397/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10121/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3397/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10121/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3397/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10121/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10121/100000 : ℝ) ^ (5415/1024 : ℝ) ≤ (548954035500277/100000000000000000000 : ℝ) := by
    have hpowers : (10121/100000 : ℝ)^5415 ≤ (548954035500277/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10121 : ℕ)^5415*100000000000000000000^1024 ≤ 548954035500277^1024*100000^5415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10121 100000 548954035500277 100000000000000000000 5415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10121/100000 : ℝ)) (X := (548954035500277/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5415 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3397/20000 : ℝ) ^ (5415/1024 : ℝ) ≤ (8482433596826637/100000000000000000000 : ℝ) := by
    have hpowers : (3397/20000 : ℝ)^5415 ≤ (8482433596826637/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3397 : ℕ)^5415*100000000000000000000^1024 ≤ 8482433596826637^1024*20000^5415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3397 20000 8482433596826637 100000000000000000000 5415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3397/20000 : ℝ)) (X := (8482433596826637/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5415 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000548954035500277/50000000000000000000 : ℝ) ≤ (10000020761825673/10000000000000000 : ℝ) ^ (5415/1024 : ℝ) := by
    have hpowers : (50000548954035500277/50000000000000000000 : ℝ)^1024 ≤ (10000020761825673/10000000000000000 : ℝ)^5415 := by
      have hnat : (50000548954035500277 : ℕ)^1024*10000000000000000^5415 ≤ 10000020761825673^5415*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000548954035500277 50000000000000000000 10000020761825673 10000000000000000 1024 5415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000020761825673/10000000000000000 : ℝ)) (X := (50000548954035500277/50000000000000000000 : ℝ)) (by norm_num) 5415 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004515693816163457/50000000000000000000 : ℝ) ≤ (10000170781206087/10000000000000000 : ℝ) ^ (5415/1024 : ℝ) := by
    have hpowers : (50004515693816163457/50000000000000000000 : ℝ)^1024 ≤ (10000170781206087/10000000000000000 : ℝ)^5415 := by
      have hnat : (50004515693816163457 : ℕ)^1024*10000000000000000^5415 ≤ 10000170781206087^5415*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004515693816163457 50000000000000000000 10000170781206087 10000000000000000 1024 5415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000170781206087/10000000000000000 : ℝ)) (X := (50004515693816163457/50000000000000000000 : ℝ)) (by norm_num) 5415 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008482433596826637/50000000000000000000 : ℝ) ≤ (10000320800586501/10000000000000000 : ℝ) ^ (5415/1024 : ℝ) := by
    have hpowers : (50008482433596826637/50000000000000000000 : ℝ)^1024 ≤ (10000320800586501/10000000000000000 : ℝ)^5415 := by
      have hnat : (50008482433596826637 : ℕ)^1024*10000000000000000^5415 ≤ 10000320800586501^5415*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008482433596826637 50000000000000000000 10000320800586501 10000000000000000 1024 5415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000320800586501/10000000000000000 : ℝ)) (X := (50008482433596826637/50000000000000000000 : ℝ)) (by norm_num) 5415 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(548954035500277/100000000000000000000 : ℝ) ≤ ((5719758818072756607/5720000000000000000 : ℝ)+2*(25003230069/114400000000000 : ℝ)*(10121/100000 : ℝ))^(5415/1024 : ℝ) := by
    rw [show (5719758818072756607/5720000000000000000 : ℝ)+2*(25003230069/114400000000000 : ℝ)*(10121/100000 : ℝ)=(10000020761825673/10000000000000000 : ℝ) by norm_num, show 1+2*(548954035500277/100000000000000000000 : ℝ)=(50000548954035500277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8482433596826637/100000000000000000000 : ℝ)+(548954035500277/100000000000000000000 : ℝ) ≤ ((5719758818072756607/5720000000000000000 : ℝ)+(25003230069/114400000000000 : ℝ)*((3397/20000 : ℝ)+(10121/100000 : ℝ)))^(5415/1024 : ℝ) := by
    rw [show (5719758818072756607/5720000000000000000 : ℝ)+(25003230069/114400000000000 : ℝ)*((3397/20000 : ℝ)+(10121/100000 : ℝ))=(10000170781206087/10000000000000000 : ℝ) by norm_num, show 1+(8482433596826637/100000000000000000000 : ℝ)+(548954035500277/100000000000000000000 : ℝ)=(50004515693816163457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8482433596826637/100000000000000000000 : ℝ) ≤ ((5719758818072756607/5720000000000000000 : ℝ)+2*(25003230069/114400000000000 : ℝ)*(3397/20000 : ℝ))^(5415/1024 : ℝ) := by
    rw [show (5719758818072756607/5720000000000000000 : ℝ)+2*(25003230069/114400000000000 : ℝ)*(3397/20000 : ℝ)=(10000320800586501/10000000000000000 : ℝ) by norm_num, show 1+2*(8482433596826637/100000000000000000000 : ℝ)=(50008482433596826637/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5719758818072756607/5720000000000000000 : ℝ)*(X 1 0+X 2 0)+(25003230069/114400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5415/1024 : ℝ)) (lo := (10121/100000 : ℝ)) (hi := (3397/20000 : ℝ)) (c := (5719758818072756607/5720000000000000000 : ℝ)) (alpha := (25003230069/114400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5719758818072756607/5720000000000000000 : ℝ)*(X 0 1+X 2 1)+(25003230069/114400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5415/1024 : ℝ)) (lo := (10121/100000 : ℝ)) (hi := (3397/20000 : ℝ)) (c := (5719758818072756607/5720000000000000000 : ℝ)) (alpha := (25003230069/114400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5719758818072756607/5720000000000000000 : ℝ)*(X 0 2+X 1 2)+(25003230069/114400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5415/1024 : ℝ)) (lo := (10121/100000 : ℝ)) (hi := (3397/20000 : ℝ)) (c := (5719758818072756607/5720000000000000000 : ℝ)) (alpha := (25003230069/114400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-526121807/5000000000 : ℝ)*X 0 0+(108188539/200000000 : ℝ)*X 0 1+(5409426989/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5224527571/10000000000 : ℝ)*X 1 0+(-164331949/1250000000 : ℝ)*X 1 1+(5409426929/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5224527533/10000000000 : ℝ)*X 2 0+(676178357/1250000000 : ℝ)*X 2 1+(-657327873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2233152951/5000000000 : ℝ)*X 0 0+(1958337501/5000000000 : ℝ)*X 0 1+(3916674791/10000000000 : ℝ)*X 0 2+(2233152951/5000000000 : ℝ)*X 1 0+(1958337501/5000000000 : ℝ)*X 1 1+(3916674791/10000000000 : ℝ)*X 1 2+(2233152951/5000000000 : ℝ)*X 2 0+(1958337501/5000000000 : ℝ)*X 2 1+(3916674791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1687498737/10000000000 : ℝ)*X 0 0+(5177922457/10000000000 : ℝ)*X 0 1+(5177922477/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1345243793/2500000000 : ℝ)*X 1 0+(-88590737/625000000 : ℝ)*X 1 1+(5177922353/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5380974939/10000000000 : ℝ)*X 2 0+(5177922583/10000000000 : ℝ)*X 2 1+(-708725899/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1844550437/5000000000 : ℝ)*X 0 0+(4304472571/10000000000 : ℝ)*X 0 1+(860894459/2000000000 : ℝ)*X 0 2+(1844550437/5000000000 : ℝ)*X 1 0+(4304472571/10000000000 : ℝ)*X 1 1+(860894459/2000000000 : ℝ)*X 1 2+(1844550437/5000000000 : ℝ)*X 2 0+(4304472571/10000000000 : ℝ)*X 2 1+(860894459/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-775340131/5000000000 : ℝ)*X 0 0+(1251584071/2500000000 : ℝ)*X 0 1+(5451554871/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1299020521/2500000000 : ℝ)*X 1 0+(-323801699/2500000000 : ℝ)*X 1 1+(5451555079/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((649510211/1250000000 : ℝ)*X 2 0+(5451555129/10000000000 : ℝ)*X 2 1+(-1295207273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((460278441/1000000000 : ℝ)*X 0 0+(3845920023/10000000000 : ℝ)*X 0 1+(961479847/2500000000 : ℝ)*X 0 2+(460278441/1000000000 : ℝ)*X 1 0+(3845920023/10000000000 : ℝ)*X 1 1+(961479847/2500000000 : ℝ)*X 1 2+(460278441/1000000000 : ℝ)*X 2 0+(3845920023/10000000000 : ℝ)*X 2 1+(961479847/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-236641227/2000000000 : ℝ)*X 0 0+(5573158539/10000000000 : ℝ)*X 0 1+(5152972911/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2698934167/5000000000 : ℝ)*X 1 0+(-1428101581/10000000000 : ℝ)*X 1 1+(2576486507/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2698934217/5000000000 : ℝ)*X 2 0+(5152972891/10000000000 : ℝ)*X 2 1+(-1428101609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((90058963/250000000 : ℝ)*X 0 0+(4346151861/10000000000 : ℝ)*X 0 1+(4346151471/10000000000 : ℝ)*X 0 2+(90058963/250000000 : ℝ)*X 1 0+(4346151861/10000000000 : ℝ)*X 1 1+(4346151471/10000000000 : ℝ)*X 1 2+(90058963/250000000 : ℝ)*X 2 0+(4346151861/10000000000 : ℝ)*X 2 1+(4346151471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1725_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-16723/25000 : ℝ) ≤ (-11956575884897965931598315656577/17875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18611643/100000000000000 : ℝ)*(lower0) + (901137/12500000000000 : ℝ)*(upper1) + (141427/20000000000000 : ℝ)*(upper3) + (23216563/100000000000000 : ℝ)*(lower4) + (10756741/100000000000000 : ℝ)*(lower5) + (87152564695763/6250000000000 : ℝ)*(major0) + (87152564695763/6250000000000 : ℝ)*(major1) + (87152564695763/6250000000000 : ℝ)*(major2) + (851307863/100000000000000 : ℝ)*(sp1) + (16909760180289/800000000000 : ℝ)*(sp4) + (1056859585614131/50000000000000 : ℝ)*(sp5) + (132107031012697/6250000000000 : ℝ)*(sp6) + (348729346367543/50000000000000 : ℝ)*(sp7) + (3763166487/50000000000000 : ℝ)*(sp14) + (348729346367543/50000000000000 : ℝ)*(f.failure) + (16909760180289/800000000000 : ℝ)*(f.sum) + (3360392902409/715000000000000000000000000 : ℝ)*base65 + (11505123577256141/35750000000000000000000000000000 : ℝ)*base67 + (382879537235743859/35750000000000000000000000000000 : ℝ)*base70 + (5549825299756141/35750000000000000000000000000000 : ℝ)*base71 + (160724801187/89375000000000000000000000 : ℝ)*base74 + (135303694006743859/35750000000000000000000000000000 : ℝ)*base76 + (404625962400493859/35750000000000000000000000000000 : ℝ)*base78 + (647250485541493859/35750000000000000000000000000000 : ℝ)*base80 + (2142111880537/357500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5225907/2500000000000000000000 : ℝ)*base90 + (5225907/2500000000000000000000 : ℝ)*base92 + (5225907/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (1836/3125 : ℝ) ≤ (84019237440464097996641740484253/143000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1419717/6250000000000 : ℝ)*(lower0) + (14173037/50000000000000 : ℝ)*(upper2) + (14008969/100000000000000 : ℝ)*(lower5) + (751806657204331/50000000000000 : ℝ)*(major0) + (751806657204331/50000000000000 : ℝ)*(major1) + (751806657204331/50000000000000 : ℝ)*(major2) + (223557793405587/10000000000000 : ℝ)*(sp0) + (2235576958312911/100000000000000 : ℝ)*(sp1) + (111778498992443/5000000000000 : ℝ)*(sp2) + (150412623547831/20000000000000 : ℝ)*(sp3) + (45202843/12500000000000 : ℝ)*(sp7) + (1287310231/100000000000000 : ℝ)*(sp9) + (8265774283/100000000000000 : ℝ)*(sp10) + (38945909/12500000000000 : ℝ)*(sp12) + (752063479361899/100000000000000 : ℝ)*(f.failure) + (1117789122811571/50000000000000 : ℝ)*(f.sum) + (921785225921/2860000000000000000000000000 : ℝ)*base66 + (269029240540785083/286000000000000000000000000000000 : ℝ)*base68 + (2025547737130785083/286000000000000000000000000000000 : ℝ)*base70 + (1009583743514785083/286000000000000000000000000000000 : ℝ)*base72 + (14821490416721/2860000000000000000000000000 : ℝ)*base74 + (2382032250086785083/286000000000000000000000000000000 : ℝ)*base76 + (2231524892228785083/286000000000000000000000000000000 : ℝ)*base78 + (3514128114414785083/286000000000000000000000000000000 : ℝ)*base80 + (819300271921/2860000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (70511049/5000000000000000000000 : ℝ)*base89 + (70511049/5000000000000000000000 : ℝ)*base91 + (70511049/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (16391/20000 : ℝ) ≤ (163914451195431438785150179863/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47939103/100000000000000 : ℝ)*(upper1) + (50331127/50000000000000 : ℝ)*(upper2) + (23845497/100000000000000 : ℝ)*(upper3) + (75483741/100000000000000 : ℝ)*(lower5) + (151577593085457/10000000000000 : ℝ)*(major0) + (151577593085457/10000000000000 : ℝ)*(major1) + (151577593085457/10000000000000 : ℝ)*(major2) + (16808759649/100000000000000 : ℝ)*(sp1) + (507576187/4000000000000 : ℝ)*(sp2) + (5285355047/100000000000000 : ℝ)*(sp3) + (2246085921509683/100000000000000 : ℝ)*(sp8) + (1123034556375017/50000000000000 : ℝ)*(sp9) + (140379577006563/6250000000000 : ℝ)*(sp10) + (758141579645167/100000000000000 : ℝ)*(sp11) + (379073432500107/50000000000000 : ℝ)*(f.failure) + (2246085921509683/100000000000000 : ℝ)*(f.sum) + (137106868233/52000000000000000000000000 : ℝ)*base66 + (40279537432601309/5200000000000000000000000000000 : ℝ)*base67 + (14138711245801309/5200000000000000000000000000000 : ℝ)*base69 + (3778369394201309/5200000000000000000000000000000 : ℝ)*base71 + (229960157027/52000000000000000000000000 : ℝ)*base73 + (98030338733001309/5200000000000000000000000000000 : ℝ)*base75 + (6234137805401309/5200000000000000000000000000000 : ℝ)*base77 + (1977898160601309/5200000000000000000000000000000 : ℝ)*base79 + (8420680603/2080000000000000000000000 : ℝ)*base81 + (3846057/2500000000000000000000 : ℝ)*base89 + (3846057/2500000000000000000000 : ℝ)*base91 + (3846057/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-90633/100000 : ℝ) ≤ (-259201924001448689617592159909679/286000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1294819/10000000000000 : ℝ)*(lower0) + (14778193/100000000000000 : ℝ)*(lower2) + (18588651/100000000000000 : ℝ)*(upper3) + (1566638887329833/100000000000000 : ℝ)*(major0) + (1566638887329833/100000000000000 : ℝ)*(major1) + (1566638887329833/100000000000000 : ℝ)*(major2) + (30604419/12500000000000 : ℝ)*(sp0) + (11366249/781250000000 : ℝ)*(sp5) + (3397333507/50000000000000 : ℝ)*(sp6) + (137117/125000000000 : ℝ)*(sp8) + (118995020189151/5000000000000 : ℝ)*(sp12) + (23798993034321/1000000000000 : ℝ)*(sp13) + (2379893963644959/100000000000000 : ℝ)*(sp14) + (12243547356251/1562500000000 : ℝ)*(sp15) + (12243547356251/1562500000000 : ℝ)*(f.failure) + (2379900758311973/100000000000000 : ℝ)*(f.sum) + (27221099467037/5720000000000000000000000000 : ℝ)*base65 + (5228335754114806631/572000000000000000000000000000000 : ℝ)*base67 + (5293966800738806631/572000000000000000000000000000000 : ℝ)*base69 + (4813659217554806631/572000000000000000000000000000000 : ℝ)*base71 + (29839222814877/5720000000000000000000000000 : ℝ)*base73 + (2610991495442806631/572000000000000000000000000000000 : ℝ)*base75 + (5174232591858806631/572000000000000000000000000000000 : ℝ)*base77 + (4089336720942806631/572000000000000000000000000000000 : ℝ)*base79 + (23106636605957/5720000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (646649/78125000000000000000 : ℝ)*base90 + (646649/78125000000000000000 : ℝ)*base92 + (646649/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1725_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (99965851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3397/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16723/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(1836/3125 : ℝ) else (16391/20000 : ℝ) ≤ X j i ∧ X j i ≤ (90633/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1725_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1725_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (99965851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (531/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2529/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16723/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(1836/3125 : ℝ) else (16391/20000 : ℝ) ≤ X j i ∧ X j i ≤ (90633/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1725_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1725_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5415/1024 : ℝ) ≤ p) (hpb : p ≤ (5423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (99965851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (531/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2529/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16723/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(1836/3125 : ℝ) else (16391/20000 : ℝ) ≤ X j i ∧ X j i ≤ (90633/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1725_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

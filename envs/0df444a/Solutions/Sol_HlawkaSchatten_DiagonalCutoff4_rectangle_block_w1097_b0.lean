-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1097_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:59:28.385866+00:00
-- url     : https://prove2.me/submissions/3b4336a4-3cae-4593-b8d5-03f617d0c260

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
theorem support_rectangle_w1097_s0_0 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-381227057/2000000000 : ℝ)*x 0 + (606478943/1000000000 : ℝ)*x 1 + (1193688689/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (381227057/2000000000 : ℝ)^4145 ≤ (11065528972783/100000000000000 : ℝ)^3121 := by
    have hnat : (381227057 : ℕ)^4145*100000000000000^3121 ≤ 11065528972783^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381227057 2000000000 11065528972783 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (606478943/1000000000 : ℝ)^4145 ≤ (51470403585779/100000000000000 : ℝ)^3121 := by
    have hnat : (606478943 : ℕ)^4145*100000000000000^3121 ≤ 51470403585779^3121*1000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606478943 1000000000 51470403585779 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1193688689/2500000000 : ℝ)^4145 ≤ (37464067420269/100000000000000 : ℝ)^3121 := by
    have hnat : (1193688689 : ℕ)^4145*100000000000000^3121 ≤ 37464067420269^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193688689 2500000000 37464067420269 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-381227057/2000000000 : ℝ), (606478943/1000000000 : ℝ), (1193688689/2500000000 : ℝ)] ![(11065528972783/100000000000000 : ℝ), (51470403585779/100000000000000 : ℝ), (37464067420269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-381227057/2000000000 : ℝ)|^4145 ≤ (11065528972783/100000000000000 : ℝ)^3121
        have hw : |(-381227057/2000000000 : ℝ)|=(381227057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(606478943/1000000000 : ℝ)|^4145 ≤ (51470403585779/100000000000000 : ℝ)^3121
        have hw : |(606478943/1000000000 : ℝ)|=(606478943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1193688689/2500000000 : ℝ)|^4145 ≤ (37464067420269/100000000000000 : ℝ)^3121
        have hw : |(1193688689/2500000000 : ℝ)|=(1193688689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s0_1 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1103865607/2000000000 : ℝ)*x 0 + (-2647773467/10000000000 : ℝ)*x 1 + (2387377393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103865607/2000000000 : ℝ)^4145 ≤ (45414974983689/100000000000000 : ℝ)^3121 := by
    have hnat : (1103865607 : ℕ)^4145*100000000000000^3121 ≤ 45414974983689^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103865607 2000000000 45414974983689 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2647773467/10000000000 : ℝ)^4145 ≤ (8560478633493/50000000000000 : ℝ)^3121 := by
    have hnat : (2647773467 : ℕ)^4145*50000000000000^3121 ≤ 8560478633493^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647773467 10000000000 8560478633493 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2387377393/5000000000 : ℝ)^4145 ≤ (4683008466611/12500000000000 : ℝ)^3121 := by
    have hnat : (2387377393 : ℕ)^4145*12500000000000^3121 ≤ 4683008466611^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2387377393 5000000000 4683008466611 12500000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103865607/2000000000 : ℝ), (-2647773467/10000000000 : ℝ), (2387377393/5000000000 : ℝ)] ![(45414974983689/100000000000000 : ℝ), (8560478633493/50000000000000 : ℝ), (4683008466611/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103865607/2000000000 : ℝ)|^4145 ≤ (45414974983689/100000000000000 : ℝ)^3121
        have hw : |(1103865607/2000000000 : ℝ)|=(1103865607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2647773467/10000000000 : ℝ)|^4145 ≤ (8560478633493/50000000000000 : ℝ)^3121
        have hw : |(-2647773467/10000000000 : ℝ)|=(2647773467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2387377393/5000000000 : ℝ)|^4145 ≤ (4683008466611/12500000000000 : ℝ)^3121
        have hw : |(2387377393/5000000000 : ℝ)|=(2387377393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s0_2 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2759664121/5000000000 : ℝ)*x 0 + (954950939/2000000000 : ℝ)*x 1 + (-1323886657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2759664121/5000000000 : ℝ)^4145 ≤ (45414977245801/100000000000000 : ℝ)^3121 := by
    have hnat : (2759664121 : ℕ)^4145*100000000000000^3121 ≤ 45414977245801^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759664121 5000000000 45414977245801 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (954950939/2000000000 : ℝ)^4145 ≤ (3746406678461/10000000000000 : ℝ)^3121 := by
    have hnat : (954950939 : ℕ)^4145*10000000000000^3121 ≤ 3746406678461^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954950939 2000000000 3746406678461 10000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1323886657/5000000000 : ℝ)^4145 ≤ (3424191190613/20000000000000 : ℝ)^3121 := by
    have hnat : (1323886657 : ℕ)^4145*20000000000000^3121 ≤ 3424191190613^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323886657 5000000000 3424191190613 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2759664121/5000000000 : ℝ), (954950939/2000000000 : ℝ), (-1323886657/5000000000 : ℝ)] ![(45414977245801/100000000000000 : ℝ), (3746406678461/10000000000000 : ℝ), (3424191190613/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2759664121/5000000000 : ℝ)|^4145 ≤ (45414977245801/100000000000000 : ℝ)^3121
        have hw : |(2759664121/5000000000 : ℝ)|=(2759664121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(954950939/2000000000 : ℝ)|^4145 ≤ (3746406678461/10000000000000 : ℝ)^3121
        have hw : |(954950939/2000000000 : ℝ)|=(954950939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1323886657/5000000000 : ℝ)|^4145 ≤ (3424191190613/20000000000000 : ℝ)^3121
        have hw : |(-1323886657/5000000000 : ℝ)|=(1323886657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s0_3 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210232767/500000000 : ℝ)*x 0 + (312325613/1000000000 : ℝ)*x 1 + (5667113419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210232767/500000000 : ℝ)^4145 ≤ (31642905845203/100000000000000 : ℝ)^3121 := by
    have hnat : (210232767 : ℕ)^4145*100000000000000^3121 ≤ 31642905845203^3121*500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210232767 500000000 31642905845203 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312325613/1000000000 : ℝ)^4145 ≤ (21320057474709/100000000000000 : ℝ)^3121 := by
    have hnat : (312325613 : ℕ)^4145*100000000000000^3121 ≤ 21320057474709^3121*1000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312325613 1000000000 21320057474709 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5667113419/10000000000 : ℝ)^4145 ≤ (47037036654699/100000000000000 : ℝ)^3121 := by
    have hnat : (5667113419 : ℕ)^4145*100000000000000^3121 ≤ 47037036654699^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5667113419 10000000000 47037036654699 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210232767/500000000 : ℝ), (312325613/1000000000 : ℝ), (5667113419/10000000000 : ℝ)] ![(31642905845203/100000000000000 : ℝ), (21320057474709/100000000000000 : ℝ), (47037036654699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210232767/500000000 : ℝ)|^4145 ≤ (31642905845203/100000000000000 : ℝ)^3121
        have hw : |(210232767/500000000 : ℝ)|=(210232767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(312325613/1000000000 : ℝ)|^4145 ≤ (21320057474709/100000000000000 : ℝ)^3121
        have hw : |(312325613/1000000000 : ℝ)|=(312325613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5667113419/10000000000 : ℝ)|^4145 ≤ (47037036654699/100000000000000 : ℝ)^3121
        have hw : |(5667113419/10000000000 : ℝ)|=(5667113419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s0_4 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-955707709/5000000000 : ℝ)*x 0 + (4808053909/10000000000 : ℝ)*x 1 + (603032253/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (955707709/5000000000 : ℝ)^4145 ≤ (2776564200821/25000000000000 : ℝ)^3121 := by
    have hnat : (955707709 : ℕ)^4145*25000000000000^3121 ≤ 2776564200821^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955707709 5000000000 2776564200821 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4808053909/10000000000 : ℝ)^4145 ≤ (7562292493477/20000000000000 : ℝ)^3121 := by
    have hnat : (4808053909 : ℕ)^4145*20000000000000^3121 ≤ 7562292493477^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4808053909 10000000000 7562292493477 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (603032253/1000000000 : ℝ)^4145 ≤ (51082280717669/100000000000000 : ℝ)^3121 := by
    have hnat : (603032253 : ℕ)^4145*100000000000000^3121 ≤ 51082280717669^3121*1000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603032253 1000000000 51082280717669 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-955707709/5000000000 : ℝ), (4808053909/10000000000 : ℝ), (603032253/1000000000 : ℝ)] ![(2776564200821/25000000000000 : ℝ), (7562292493477/20000000000000 : ℝ), (51082280717669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-955707709/5000000000 : ℝ)|^4145 ≤ (2776564200821/25000000000000 : ℝ)^3121
        have hw : |(-955707709/5000000000 : ℝ)|=(955707709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4808053909/10000000000 : ℝ)|^4145 ≤ (7562292493477/20000000000000 : ℝ)^3121
        have hw : |(4808053909/10000000000 : ℝ)|=(4808053909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(603032253/1000000000 : ℝ)|^4145 ≤ (51082280717669/100000000000000 : ℝ)^3121
        have hw : |(603032253/1000000000 : ℝ)|=(603032253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s0_5 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (516902567/1000000000 : ℝ)*x 0 + (-174025921/1250000000 : ℝ)*x 1 + (188447587/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516902567/1000000000 : ℝ)^4145 ≤ (41627285243701/100000000000000 : ℝ)^3121 := by
    have hnat : (516902567 : ℕ)^4145*100000000000000^3121 ≤ 41627285243701^3121*1000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516902567 1000000000 41627285243701 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174025921/1250000000 : ℝ)^4145 ≤ (1458086233793/20000000000000 : ℝ)^3121 := by
    have hnat : (174025921 : ℕ)^4145*20000000000000^3121 ≤ 1458086233793^3121*1250000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174025921 1250000000 1458086233793 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188447587/312500000 : ℝ)^4145 ≤ (51082283575221/100000000000000 : ℝ)^3121 := by
    have hnat : (188447587 : ℕ)^4145*100000000000000^3121 ≤ 51082283575221^3121*312500000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188447587 312500000 51082283575221 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(516902567/1000000000 : ℝ), (-174025921/1250000000 : ℝ), (188447587/312500000 : ℝ)] ![(41627285243701/100000000000000 : ℝ), (1458086233793/20000000000000 : ℝ), (51082283575221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(516902567/1000000000 : ℝ)|^4145 ≤ (41627285243701/100000000000000 : ℝ)^3121
        have hw : |(516902567/1000000000 : ℝ)|=(516902567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-174025921/1250000000 : ℝ)|^4145 ≤ (1458086233793/20000000000000 : ℝ)^3121
        have hw : |(-174025921/1250000000 : ℝ)|=(174025921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(188447587/312500000 : ℝ)|^4145 ≤ (51082283575221/100000000000000 : ℝ)^3121
        have hw : |(188447587/312500000 : ℝ)|=(188447587/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s0_6 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1292256693/2500000000 : ℝ)*x 0 + (3015161439/5000000000 : ℝ)*x 1 + (-1392205521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292256693/2500000000 : ℝ)^4145 ≤ (41627297030117/100000000000000 : ℝ)^3121 := by
    have hnat : (1292256693 : ℕ)^4145*100000000000000^3121 ≤ 41627297030117^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292256693 2500000000 41627297030117 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3015161439/5000000000 : ℝ)^4145 ≤ (51082284632741/100000000000000 : ℝ)^3121 := by
    have hnat : (3015161439 : ℕ)^4145*100000000000000^3121 ≤ 51082284632741^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3015161439 5000000000 51082284632741 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1392205521/10000000000 : ℝ)^4145 ≤ (1822604580897/25000000000000 : ℝ)^3121 := by
    have hnat : (1392205521 : ℕ)^4145*25000000000000^3121 ≤ 1822604580897^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392205521 10000000000 1822604580897 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292256693/2500000000 : ℝ), (3015161439/5000000000 : ℝ), (-1392205521/10000000000 : ℝ)] ![(41627297030117/100000000000000 : ℝ), (51082284632741/100000000000000 : ℝ), (1822604580897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292256693/2500000000 : ℝ)|^4145 ≤ (41627297030117/100000000000000 : ℝ)^3121
        have hw : |(1292256693/2500000000 : ℝ)|=(1292256693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3015161439/5000000000 : ℝ)|^4145 ≤ (51082284632741/100000000000000 : ℝ)^3121
        have hw : |(3015161439/5000000000 : ℝ)|=(3015161439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1392205521/10000000000 : ℝ)|^4145 ≤ (1822604580897/25000000000000 : ℝ)^3121
        have hw : |(-1392205521/10000000000 : ℝ)|=(1392205521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s0_7 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053766153/2500000000 : ℝ)*x 0 + (1120290041/2000000000 : ℝ)*x 1 + (1595610893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053766153/2500000000 : ℝ)^4145 ≤ (15873493646797/50000000000000 : ℝ)^3121 := by
    have hnat : (1053766153 : ℕ)^4145*50000000000000^3121 ≤ 15873493646797^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053766153 2500000000 15873493646797 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120290041/2000000000 : ℝ)^4145 ≤ (46314595460367/100000000000000 : ℝ)^3121 := by
    have hnat : (1120290041 : ℕ)^4145*100000000000000^3121 ≤ 46314595460367^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120290041 2000000000 46314595460367 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1595610893/5000000000 : ℝ)^4145 ≤ (10969208618793/50000000000000 : ℝ)^3121 := by
    have hnat : (1595610893 : ℕ)^4145*50000000000000^3121 ≤ 10969208618793^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595610893 5000000000 10969208618793 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053766153/2500000000 : ℝ), (1120290041/2000000000 : ℝ), (1595610893/5000000000 : ℝ)] ![(15873493646797/50000000000000 : ℝ), (46314595460367/100000000000000 : ℝ), (10969208618793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053766153/2500000000 : ℝ)|^4145 ≤ (15873493646797/50000000000000 : ℝ)^3121
        have hw : |(1053766153/2500000000 : ℝ)|=(1053766153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120290041/2000000000 : ℝ)|^4145 ≤ (46314595460367/100000000000000 : ℝ)^3121
        have hw : |(1120290041/2000000000 : ℝ)|=(1120290041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1595610893/5000000000 : ℝ)|^4145 ≤ (10969208618793/50000000000000 : ℝ)^3121
        have hw : |(1595610893/5000000000 : ℝ)|=(1595610893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1097_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (227/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27989/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8289/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8289 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8289*1^2048 ≤ 0^2048*1^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8289/2048 : ℝ) ≤ (1225638021504470809/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8289 ≤ (1225638021504470809/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8289*50000000000000000000^2048 ≤ 1225638021504470809^2048*5^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1225638021504470809 50000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1225638021504470809/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8289 := by
      have hnat : (1 : ℕ)^2048*1^8289 ≤ 1^8289*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51225638021504470809/50000000000000000000 : ℝ) ≤ (10060013736857383/10000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (51225638021504470809/50000000000000000000 : ℝ)^2048 ≤ (10060013736857383/10000000000000000 : ℝ)^8289 := by
      have hnat : (51225638021504470809 : ℕ)^2048*10000000000000000^8289 ≤ 10060013736857383^8289*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51225638021504470809 50000000000000000000 10060013736857383 10000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10060013736857383/10000000000000000 : ℝ)) (X := (51225638021504470809/50000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26225638021504470809/25000000000000000000 : ℝ) ≤ (5060013736857383/5000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (26225638021504470809/25000000000000000000 : ℝ)^2048 ≤ (5060013736857383/5000000000000000 : ℝ)^8289 := by
      have hnat : (26225638021504470809 : ℕ)^2048*5000000000000000^8289 ≤ 5060013736857383^8289*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26225638021504470809 25000000000000000000 5060013736857383 5000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5060013736857383/5000000000000000 : ℝ)) (X := (26225638021504470809/25000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(60013736857383/4000000000000000 : ℝ)*(0 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(60013736857383/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1225638021504470809/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(60013736857383/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8289/2048 : ℝ) := by
    rw [show (1 : ℝ)+(60013736857383/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10060013736857383/10000000000000000 : ℝ) by norm_num, show 1+(1225638021504470809/50000000000000000000 : ℝ)+(0 : ℝ)=(51225638021504470809/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1225638021504470809/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(60013736857383/4000000000000000 : ℝ)*(2/5 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(60013736857383/4000000000000000 : ℝ)*(2/5 : ℝ)=(5060013736857383/5000000000000000 : ℝ) by norm_num, show 1+2*(1225638021504470809/50000000000000000000 : ℝ)=(26225638021504470809/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(60013736857383/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60013736857383/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(60013736857383/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60013736857383/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(60013736857383/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60013736857383/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-381227057/2000000000 : ℝ)*X 0 0+(606478943/1000000000 : ℝ)*X 0 1+(1193688689/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1103865607/2000000000 : ℝ)*X 1 0+(-2647773467/10000000000 : ℝ)*X 1 1+(2387377393/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2759664121/5000000000 : ℝ)*X 2 0+(954950939/2000000000 : ℝ)*X 2 1+(-1323886657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((210232767/500000000 : ℝ)*X 0 0+(312325613/1000000000 : ℝ)*X 0 1+(5667113419/10000000000 : ℝ)*X 0 2+(210232767/500000000 : ℝ)*X 1 0+(312325613/1000000000 : ℝ)*X 1 1+(5667113419/10000000000 : ℝ)*X 1 2+(210232767/500000000 : ℝ)*X 2 0+(312325613/1000000000 : ℝ)*X 2 1+(5667113419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-955707709/5000000000 : ℝ)*X 0 0+(4808053909/10000000000 : ℝ)*X 0 1+(603032253/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((516902567/1000000000 : ℝ)*X 1 0+(-174025921/1250000000 : ℝ)*X 1 1+(188447587/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1292256693/2500000000 : ℝ)*X 2 0+(3015161439/5000000000 : ℝ)*X 2 1+(-1392205521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1053766153/2500000000 : ℝ)*X 0 0+(1120290041/2000000000 : ℝ)*X 0 1+(1595610893/5000000000 : ℝ)*X 0 2+(1053766153/2500000000 : ℝ)*X 1 0+(1120290041/2000000000 : ℝ)*X 1 1+(1595610893/5000000000 : ℝ)*X 1 2+(1053766153/2500000000 : ℝ)*X 2 0+(1120290041/2000000000 : ℝ)*X 2 1+(1595610893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (636975405095852678949189/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6334401/25000000000000 : ℝ)*(base1) + (164327351/20000000000000 : ℝ)*(base19) + (31177641/4000000000000 : ℝ)*(base23) + (71268391/100000000000000 : ℝ)*(base24) + (191402877/100000000000000 : ℝ)*(upper3) + (584141873671013/100000000000000 : ℝ)*(major0) + (584141873671013/100000000000000 : ℝ)*(major1) + (584141873671013/100000000000000 : ℝ)*(major2) + (775175678500191/100000000000000 : ℝ)*(sp0) + (387588324315713/50000000000000 : ℝ)*(sp1) + (193794154889691/25000000000000 : ℝ)*(sp2) + (393104665846953/100000000000000 : ℝ)*(sp3) + (1817105593/100000000000000 : ℝ)*(sp4) + (739863359/50000000000000 : ℝ)*(sp7) + (15724246836451/4000000000000 : ℝ)*(f.failure) + (38758873513409/5000000000000 : ℝ)*(f.sum) + (60553783261021/200000000000000000000000000000 : ℝ)*base66 + (1395770943338979/400000000000000000000000000000 : ℝ)*base67 + (3262904505738979/400000000000000000000000000000 : ℝ)*base69 + (864824103738979/400000000000000000000000000000 : ℝ)*base71 + (65313214538979/200000000000000000000000000000 : ℝ)*base73 + (1082069954261021/400000000000000000000000000000 : ℝ)*base76 + (136830112538979/400000000000000000000000000000 : ℝ)*base77 + (948489818138979/400000000000000000000000000000 : ℝ)*base79 + (361024890338979/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (50857/80000000000000000000 : ℝ)*base90 + (50857/80000000000000000000 : ℝ)*base92 + (50857/80000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (429329557905950452565427/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (326540857/20000000000000 : ℝ)*(base19) + (1084352343/50000000000000 : ℝ)*(base23) + (80205977/25000000000000 : ℝ)*(base39) + (22398609/5000000000000 : ℝ)*(base45) + (11046981/5000000000000 : ℝ)*(upper3) + (1127143/312500000000 : ℝ)*(upper5) + (308260649848331/50000000000000 : ℝ)*(major0) + (308260649848331/50000000000000 : ℝ)*(major1) + (308260489436377/50000000000000 : ℝ)*(major2) + (738772101/100000000000000 : ℝ)*(sp2) + (163629129791287/20000000000000 : ℝ)*(sp4) + (16362880325043/2000000000000 : ℝ)*(sp5) + (163628612460711/20000000000000 : ℝ)*(sp6) + (414896343393271/100000000000000 : ℝ)*(sp7) + (414896343393271/100000000000000 : ℝ)*(f.failure) + (409072984890171/50000000000000 : ℝ)*(f.sum) + (53592556099791/50000000000000000000000000000 : ℝ)*base65 + (640916092778609/200000000000000000000000000000 : ℝ)*base68 + (1292572983622227/200000000000000000000000000000 : ℝ)*base70 + (605454369178609/200000000000000000000000000000 : ℝ)*base72 + (53458360550209/50000000000000000000000000000 : ℝ)*base74 + (385573993622227/200000000000000000000000000000 : ℝ)*base76 + (51868176777773/200000000000000000000000000000 : ℝ)*base77 + (993310319577773/200000000000000000000000000000 : ℝ)*base79 + (299767313877773/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (4922597/2000000000000000000000 : ℝ)*base90 + (4922597/2000000000000000000000 : ℝ)*base92 + (4922597/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1097_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (227/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27989/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1097_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1097_s1_0 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2114038779/10000000000 : ℝ)*x 0 + (714214939/1250000000 : ℝ)*x 1 + (4992703019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114038779/10000000000 : ℝ)^4145 ≤ (3174114131401/25000000000000 : ℝ)^3121 := by
    have hnat : (2114038779 : ℕ)^4145*25000000000000^3121 ≤ 3174114131401^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114038779 10000000000 3174114131401 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (714214939/1250000000 : ℝ)^4145 ≤ (47551478121083/100000000000000 : ℝ)^3121 := by
    have hnat : (714214939 : ℕ)^4145*100000000000000^3121 ≤ 47551478121083^3121*1250000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714214939 1250000000 47551478121083 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4992703019/10000000000 : ℝ)^4145 ≤ (19876032669277/50000000000000 : ℝ)^3121 := by
    have hnat : (4992703019 : ℕ)^4145*50000000000000^3121 ≤ 19876032669277^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992703019 10000000000 19876032669277 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2114038779/10000000000 : ℝ), (714214939/1250000000 : ℝ), (4992703019/10000000000 : ℝ)] ![(3174114131401/25000000000000 : ℝ), (47551478121083/100000000000000 : ℝ), (19876032669277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2114038779/10000000000 : ℝ)|^4145 ≤ (3174114131401/25000000000000 : ℝ)^3121
        have hw : |(-2114038779/10000000000 : ℝ)|=(2114038779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(714214939/1250000000 : ℝ)|^4145 ≤ (47551478121083/100000000000000 : ℝ)^3121
        have hw : |(714214939/1250000000 : ℝ)|=(714214939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4992703019/10000000000 : ℝ)|^4145 ≤ (19876032669277/50000000000000 : ℝ)^3121
        have hw : |(4992703019/10000000000 : ℝ)|=(4992703019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s1_1 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5421603147/10000000000 : ℝ)*x 0 + (-31300567/125000000 : ℝ)*x 1 + (1248175793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421603147/10000000000 : ℝ)^4145 ≤ (5543768069497/12500000000000 : ℝ)^3121 := by
    have hnat : (5421603147 : ℕ)^4145*12500000000000^3121 ≤ 5543768069497^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421603147 10000000000 5543768069497 12500000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31300567/125000000 : ℝ)^4145 ≤ (15897788468633/100000000000000 : ℝ)^3121 := by
    have hnat : (31300567 : ℕ)^4145*100000000000000^3121 ≤ 15897788468633^3121*125000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31300567 125000000 15897788468633 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1248175793/2500000000 : ℝ)^4145 ≤ (39752066956433/100000000000000 : ℝ)^3121 := by
    have hnat : (1248175793 : ℕ)^4145*100000000000000^3121 ≤ 39752066956433^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248175793 2500000000 39752066956433 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421603147/10000000000 : ℝ), (-31300567/125000000 : ℝ), (1248175793/2500000000 : ℝ)] ![(5543768069497/12500000000000 : ℝ), (15897788468633/100000000000000 : ℝ), (39752066956433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421603147/10000000000 : ℝ)|^4145 ≤ (5543768069497/12500000000000 : ℝ)^3121
        have hw : |(5421603147/10000000000 : ℝ)|=(5421603147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31300567/125000000 : ℝ)|^4145 ≤ (15897788468633/100000000000000 : ℝ)^3121
        have hw : |(-31300567/125000000 : ℝ)|=(31300567/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1248175793/2500000000 : ℝ)|^4145 ≤ (39752066956433/100000000000000 : ℝ)^3121
        have hw : |(1248175793/2500000000 : ℝ)|=(1248175793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s1_2 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2710802083/5000000000 : ℝ)*x 0 + (4992702157/10000000000 : ℝ)*x 1 + (-62601133/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710802083/5000000000 : ℝ)^4145 ≤ (11087538906651/25000000000000 : ℝ)^3121 := by
    have hnat : (2710802083 : ℕ)^4145*25000000000000^3121 ≤ 11087538906651^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710802083 5000000000 11087538906651 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4992702157/10000000000 : ℝ)^4145 ≤ (19876028111721/50000000000000 : ℝ)^3121 := by
    have hnat : (4992702157 : ℕ)^4145*50000000000000^3121 ≤ 19876028111721^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992702157 10000000000 19876028111721 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62601133/250000000 : ℝ)^4145 ≤ (15897788131357/100000000000000 : ℝ)^3121 := by
    have hnat : (62601133 : ℕ)^4145*100000000000000^3121 ≤ 15897788131357^3121*250000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62601133 250000000 15897788131357 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710802083/5000000000 : ℝ), (4992702157/10000000000 : ℝ), (-62601133/250000000 : ℝ)] ![(11087538906651/25000000000000 : ℝ), (19876028111721/50000000000000 : ℝ), (15897788131357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710802083/5000000000 : ℝ)|^4145 ≤ (11087538906651/25000000000000 : ℝ)^3121
        have hw : |(2710802083/5000000000 : ℝ)|=(2710802083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4992702157/10000000000 : ℝ)|^4145 ≤ (19876028111721/50000000000000 : ℝ)^3121
        have hw : |(4992702157/10000000000 : ℝ)|=(4992702157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62601133/250000000 : ℝ)|^4145 ≤ (15897788131357/100000000000000 : ℝ)^3121
        have hw : |(-62601133/250000000 : ℝ)|=(62601133/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s1_3 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4321222131/10000000000 : ℝ)*x 0 + (3668493259/10000000000 : ℝ)*x 1 + (1018057059/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321222131/10000000000 : ℝ)^4145 ≤ (6562648166697/20000000000000 : ℝ)^3121 := by
    have hnat : (4321222131 : ℕ)^4145*20000000000000^3121 ≤ 6562648166697^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321222131 10000000000 6562648166697 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3668493259/10000000000 : ℝ)^4145 ≤ (13199763996591/50000000000000 : ℝ)^3121 := by
    have hnat : (3668493259 : ℕ)^4145*50000000000000^3121 ≤ 13199763996591^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3668493259 10000000000 13199763996591 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1018057059/2000000000 : ℝ)^4145 ≤ (40787231150827/100000000000000 : ℝ)^3121 := by
    have hnat : (1018057059 : ℕ)^4145*100000000000000^3121 ≤ 40787231150827^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018057059 2000000000 40787231150827 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321222131/10000000000 : ℝ), (3668493259/10000000000 : ℝ), (1018057059/2000000000 : ℝ)] ![(6562648166697/20000000000000 : ℝ), (13199763996591/50000000000000 : ℝ), (40787231150827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321222131/10000000000 : ℝ)|^4145 ≤ (6562648166697/20000000000000 : ℝ)^3121
        have hw : |(4321222131/10000000000 : ℝ)|=(4321222131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3668493259/10000000000 : ℝ)|^4145 ≤ (13199763996591/50000000000000 : ℝ)^3121
        have hw : |(3668493259/10000000000 : ℝ)|=(3668493259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1018057059/2000000000 : ℝ)|^4145 ≤ (40787231150827/100000000000000 : ℝ)^3121
        have hw : |(1018057059/2000000000 : ℝ)|=(1018057059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s1_4 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-422981987/2000000000 : ℝ)*x 0 + (5002718613/10000000000 : ℝ)*x 1 + (2851751333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422981987/2000000000 : ℝ)^4145 ≤ (6351702789383/50000000000000 : ℝ)^3121 := by
    have hnat : (422981987 : ℕ)^4145*50000000000000^3121 ≤ 6351702789383^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422981987 2000000000 6351702789383 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5002718613/10000000000 : ℝ)^4145 ≤ (39858008828837/100000000000000 : ℝ)^3121 := by
    have hnat : (5002718613 : ℕ)^4145*100000000000000^3121 ≤ 39858008828837^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5002718613 10000000000 39858008828837 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2851751333/5000000000 : ℝ)^4145 ≤ (47438585579287/100000000000000 : ℝ)^3121 := by
    have hnat : (2851751333 : ℕ)^4145*100000000000000^3121 ≤ 47438585579287^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2851751333 5000000000 47438585579287 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-422981987/2000000000 : ℝ), (5002718613/10000000000 : ℝ), (2851751333/5000000000 : ℝ)] ![(6351702789383/50000000000000 : ℝ), (39858008828837/100000000000000 : ℝ), (47438585579287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-422981987/2000000000 : ℝ)|^4145 ≤ (6351702789383/50000000000000 : ℝ)^3121
        have hw : |(-422981987/2000000000 : ℝ)|=(422981987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5002718613/10000000000 : ℝ)|^4145 ≤ (39858008828837/100000000000000 : ℝ)^3121
        have hw : |(5002718613/10000000000 : ℝ)|=(5002718613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2851751333/5000000000 : ℝ)|^4145 ≤ (47438585579287/100000000000000 : ℝ)^3121
        have hw : |(2851751333/5000000000 : ℝ)|=(2851751333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s1_5 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5237169279/10000000000 : ℝ)*x 0 + (-1793245579/10000000000 : ℝ)*x 1 + (2851751249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5237169279/10000000000 : ℝ)^4145 ≤ (5294710656951/12500000000000 : ℝ)^3121 := by
    have hnat : (5237169279 : ℕ)^4145*12500000000000^3121 ≤ 5294710656951^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237169279 10000000000 5294710656951 12500000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1793245579/10000000000 : ℝ)^4145 ≤ (10203731001269/100000000000000 : ℝ)^3121 := by
    have hnat : (1793245579 : ℕ)^4145*100000000000000^3121 ≤ 10203731001269^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793245579 10000000000 10203731001269 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2851751249/5000000000 : ℝ)^4145 ≤ (11859645930873/25000000000000 : ℝ)^3121 := by
    have hnat : (2851751249 : ℕ)^4145*25000000000000^3121 ≤ 11859645930873^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2851751249 5000000000 11859645930873 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5237169279/10000000000 : ℝ), (-1793245579/10000000000 : ℝ), (2851751249/5000000000 : ℝ)] ![(5294710656951/12500000000000 : ℝ), (10203731001269/100000000000000 : ℝ), (11859645930873/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5237169279/10000000000 : ℝ)|^4145 ≤ (5294710656951/12500000000000 : ℝ)^3121
        have hw : |(5237169279/10000000000 : ℝ)|=(5237169279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1793245579/10000000000 : ℝ)|^4145 ≤ (10203731001269/100000000000000 : ℝ)^3121
        have hw : |(-1793245579/10000000000 : ℝ)|=(1793245579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2851751249/5000000000 : ℝ)|^4145 ≤ (11859645930873/25000000000000 : ℝ)^3121
        have hw : |(2851751249/5000000000 : ℝ)|=(2851751249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s1_6 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52371693/100000000 : ℝ)*x 0 + (45628021/80000000 : ℝ)*x 1 + (-448311341/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52371693/100000000 : ℝ)^4145 ≤ (42357685481181/100000000000000 : ℝ)^3121 := by
    have hnat : (52371693 : ℕ)^4145*100000000000000^3121 ≤ 42357685481181^3121*100000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52371693 100000000 42357685481181 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45628021/80000000 : ℝ)^4145 ≤ (9487717025277/20000000000000 : ℝ)^3121 := by
    have hnat : (45628021 : ℕ)^4145*20000000000000^3121 ≤ 9487717025277^3121*80000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45628021 80000000 9487717025277 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448311341/2500000000 : ℝ)^4145 ≤ (10203729376511/100000000000000 : ℝ)^3121 := by
    have hnat : (448311341 : ℕ)^4145*100000000000000^3121 ≤ 10203729376511^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448311341 2500000000 10203729376511 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52371693/100000000 : ℝ), (45628021/80000000 : ℝ), (-448311341/2500000000 : ℝ)] ![(42357685481181/100000000000000 : ℝ), (9487717025277/20000000000000 : ℝ), (10203729376511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52371693/100000000 : ℝ)|^4145 ≤ (42357685481181/100000000000000 : ℝ)^3121
        have hw : |(52371693/100000000 : ℝ)|=(52371693/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45628021/80000000 : ℝ)|^4145 ≤ (9487717025277/20000000000000 : ℝ)^3121
        have hw : |(45628021/80000000 : ℝ)|=(45628021/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-448311341/2500000000 : ℝ)|^4145 ≤ (10203729376511/100000000000000 : ℝ)^3121
        have hw : |(-448311341/2500000000 : ℝ)|=(448311341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s1_7 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4322938963/10000000000 : ℝ)*x 0 + (633817001/1250000000 : ℝ)*x 1 + (18443197/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322938963/10000000000 : ℝ)^4145 ≤ (6566111221773/20000000000000 : ℝ)^3121 := by
    have hnat : (4322938963 : ℕ)^4145*20000000000000^3121 ≤ 6566111221773^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322938963 10000000000 6566111221773 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (633817001/1250000000 : ℝ)^4145 ≤ (8115439629879/20000000000000 : ℝ)^3121 := by
    have hnat : (633817001 : ℕ)^4145*20000000000000^3121 ≤ 8115439629879^3121*1250000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633817001 1250000000 8115439629879 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18443197/50000000 : ℝ)^4145 ≤ (3324030715619/12500000000000 : ℝ)^3121 := by
    have hnat : (18443197 : ℕ)^4145*12500000000000^3121 ≤ 3324030715619^3121*50000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18443197 50000000 3324030715619 12500000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322938963/10000000000 : ℝ), (633817001/1250000000 : ℝ), (18443197/50000000 : ℝ)] ![(6566111221773/20000000000000 : ℝ), (8115439629879/20000000000000 : ℝ), (3324030715619/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322938963/10000000000 : ℝ)|^4145 ≤ (6566111221773/20000000000000 : ℝ)^3121
        have hw : |(4322938963/10000000000 : ℝ)|=(4322938963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(633817001/1250000000 : ℝ)|^4145 ≤ (8115439629879/20000000000000 : ℝ)^3121
        have hw : |(633817001/1250000000 : ℝ)|=(633817001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(18443197/50000000 : ℝ)|^4145 ≤ (3324030715619/12500000000000 : ℝ)^3121
        have hw : |(18443197/50000000 : ℝ)|=(18443197/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1097_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2697/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4129/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (227/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (227/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (227/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (227/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (227/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (227/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (227/100000 : ℝ) ^ (8289/2048 : ℝ) ≤ (995052837/50000000000000000000 : ℝ) := by
    have hpowers : (227/100000 : ℝ)^8289 ≤ (995052837/50000000000000000000 : ℝ)^2048 := by
      have hnat : (227 : ℕ)^8289*50000000000000000000^2048 ≤ 995052837^2048*100000^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        227 100000 995052837 50000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (227/100000 : ℝ)) (X := (995052837/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27989/100000 : ℝ) ^ (8289/2048 : ℝ) ≤ (11555454504689049/2000000000000000000 : ℝ) := by
    have hpowers : (27989/100000 : ℝ)^8289 ≤ (11555454504689049/2000000000000000000 : ℝ)^2048 := by
      have hnat : (27989 : ℕ)^8289*2000000000000000000^2048 ≤ 11555454504689049^2048*100000^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27989 100000 11555454504689049 2000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27989/100000 : ℝ)) (X := (11555454504689049/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000000995052837/25000000000000000000 : ℝ) ≤ (10000000000098341/10000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (25000000000995052837/25000000000000000000 : ℝ)^2048 ≤ (10000000000098341/10000000000000000 : ℝ)^8289 := by
      have hnat : (25000000000995052837 : ℕ)^2048*10000000000000000^8289 ≤ 10000000000098341^8289*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000000995052837 25000000000000000000 10000000000098341 10000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000098341/10000000000000000 : ℝ)) (X := (25000000000995052837/25000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25144443181806139531/25000000000000000000 : ℝ) ≤ (10014244341314393/10000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (25144443181806139531/25000000000000000000 : ℝ)^2048 ≤ (10014244341314393/10000000000000000 : ℝ)^8289 := by
      have hnat : (25144443181806139531 : ℕ)^2048*10000000000000000^8289 ≤ 10014244341314393^8289*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25144443181806139531 25000000000000000000 10014244341314393 10000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014244341314393/10000000000000000 : ℝ)) (X := (25144443181806139531/25000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1011555454504689049/1000000000000000000 : ℝ) ≤ (2005697736506089/2000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (1011555454504689049/1000000000000000000 : ℝ)^2048 ≤ (2005697736506089/2000000000000000 : ℝ)^8289 := by
      have hnat : (1011555454504689049 : ℕ)^2048*2000000000000000^8289 ≤ 2005697736506089^8289*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1011555454504689049 1000000000000000000 2005697736506089 2000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005697736506089/2000000000000000 : ℝ)) (X := (1011555454504689049/1000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(995052837/50000000000000000000 : ℝ) ≤ ((46268922178636342539/46270000000000000000 : ℝ)+2*(1187028434671/231350000000000 : ℝ)*(227/100000 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (46268922178636342539/46270000000000000000 : ℝ)+2*(1187028434671/231350000000000 : ℝ)*(227/100000 : ℝ)=(10000000000098341/10000000000000000 : ℝ) by norm_num, show 1+2*(995052837/50000000000000000000 : ℝ)=(25000000000995052837/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11555454504689049/2000000000000000000 : ℝ)+(995052837/50000000000000000000 : ℝ) ≤ ((46268922178636342539/46270000000000000000 : ℝ)+(1187028434671/231350000000000 : ℝ)*((27989/100000 : ℝ)+(227/100000 : ℝ)))^(8289/2048 : ℝ) := by
    rw [show (46268922178636342539/46270000000000000000 : ℝ)+(1187028434671/231350000000000 : ℝ)*((27989/100000 : ℝ)+(227/100000 : ℝ))=(10014244341314393/10000000000000000 : ℝ) by norm_num, show 1+(11555454504689049/2000000000000000000 : ℝ)+(995052837/50000000000000000000 : ℝ)=(25144443181806139531/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11555454504689049/2000000000000000000 : ℝ) ≤ ((46268922178636342539/46270000000000000000 : ℝ)+2*(1187028434671/231350000000000 : ℝ)*(27989/100000 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (46268922178636342539/46270000000000000000 : ℝ)+2*(1187028434671/231350000000000 : ℝ)*(27989/100000 : ℝ)=(2005697736506089/2000000000000000 : ℝ) by norm_num, show 1+2*(11555454504689049/2000000000000000000 : ℝ)=(1011555454504689049/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46268922178636342539/46270000000000000000 : ℝ)*(X 1 0+X 2 0)+(1187028434671/231350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (227/100000 : ℝ)) (hi := (27989/100000 : ℝ)) (c := (46268922178636342539/46270000000000000000 : ℝ)) (alpha := (1187028434671/231350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46268922178636342539/46270000000000000000 : ℝ)*(X 0 1+X 2 1)+(1187028434671/231350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (227/100000 : ℝ)) (hi := (27989/100000 : ℝ)) (c := (46268922178636342539/46270000000000000000 : ℝ)) (alpha := (1187028434671/231350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46268922178636342539/46270000000000000000 : ℝ)*(X 0 2+X 1 2)+(1187028434671/231350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (227/100000 : ℝ)) (hi := (27989/100000 : ℝ)) (c := (46268922178636342539/46270000000000000000 : ℝ)) (alpha := (1187028434671/231350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2114038779/10000000000 : ℝ)*X 0 0+(714214939/1250000000 : ℝ)*X 0 1+(4992703019/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5421603147/10000000000 : ℝ)*X 1 0+(-31300567/125000000 : ℝ)*X 1 1+(1248175793/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2710802083/5000000000 : ℝ)*X 2 0+(4992702157/10000000000 : ℝ)*X 2 1+(-62601133/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321222131/10000000000 : ℝ)*X 0 0+(3668493259/10000000000 : ℝ)*X 0 1+(1018057059/2000000000 : ℝ)*X 0 2+(4321222131/10000000000 : ℝ)*X 1 0+(3668493259/10000000000 : ℝ)*X 1 1+(1018057059/2000000000 : ℝ)*X 1 2+(4321222131/10000000000 : ℝ)*X 2 0+(3668493259/10000000000 : ℝ)*X 2 1+(1018057059/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-422981987/2000000000 : ℝ)*X 0 0+(5002718613/10000000000 : ℝ)*X 0 1+(2851751333/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5237169279/10000000000 : ℝ)*X 1 0+(-1793245579/10000000000 : ℝ)*X 1 1+(2851751249/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((52371693/100000000 : ℝ)*X 2 0+(45628021/80000000 : ℝ)*X 2 1+(-448311341/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4322938963/10000000000 : ℝ)*X 0 0+(633817001/1250000000 : ℝ)*X 0 1+(18443197/50000000 : ℝ)*X 0 2+(4322938963/10000000000 : ℝ)*X 1 0+(633817001/1250000000 : ℝ)*X 1 1+(18443197/50000000 : ℝ)*X 1 2+(4322938963/10000000000 : ℝ)*X 2 0+(633817001/1250000000 : ℝ)*X 2 1+(18443197/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (171468559374824600621651769/57837500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (150188233/100000000000000 : ℝ)*(base1) + (497965599/100000000000000 : ℝ)*(base19) + (758642293/100000000000000 : ℝ)*(base23) + (868961/12500000000000 : ℝ)*(upper3) + (91073747/100000000000000 : ℝ)*(upper5) + (52256841409643/5000000000000 : ℝ)*(major0) + (52256841409643/5000000000000 : ℝ)*(major1) + (52256841409643/5000000000000 : ℝ)*(major2) + (693466048111937/50000000000000 : ℝ)*(sp0) + (1386934101842361/100000000000000 : ℝ)*(sp1) + (1386933841165667/100000000000000 : ℝ)*(sp2) + (703338314569731/100000000000000 : ℝ)*(sp3) + (16586077/625000000000 : ℝ)*(sp4) + (246498883/50000000000000 : ℝ)*(sp7) + (703338957755731/100000000000000 : ℝ)*(f.failure) + (34673364995199/2500000000000 : ℝ)*(f.sum) + (18564540405753/4627000000000000000000000000 : ℝ)*base65 + (942946247285446423/231350000000000000000000000000000 : ℝ)*base68 + (1195920670585453577/231350000000000000000000000000000 : ℝ)*base69 + (1198369113570203577/231350000000000000000000000000000 : ℝ)*base71 + (236789079601/925400000000000000000000000 : ℝ)*base73 + (1077472162111353577/231350000000000000000000000000000 : ℝ)*base75 + (1289091013735953577/231350000000000000000000000000000 : ℝ)*base77 + (1207909596588703577/231350000000000000000000000000000 : ℝ)*base79 + (22315680621289/4627000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (7981817/2000000000000000000000 : ℝ)*base90 + (7981817/2000000000000000000000 : ℝ)*base92 + (7981817/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10692780468192707150863744491/1156750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26800031/25000000000000 : ℝ)*(base1) + (1027763587/50000000000000 : ℝ)*(base19) + (519098753/25000000000000 : ℝ)*(base23) + (210052819/100000000000000 : ℝ)*(upper3) + (210573943/100000000000000 : ℝ)*(upper5) + (1075308319787077/100000000000000 : ℝ)*(major0) + (1075308319787077/100000000000000 : ℝ)*(major1) + (1075308319787077/100000000000000 : ℝ)*(major2) + (8272224387/100000000000000 : ℝ)*(sp1) + (4351130519/50000000000000 : ℝ)*(sp2) + (1426973167734187/100000000000000 : ℝ)*(sp4) + (713481366391251/50000000000000 : ℝ)*(sp5) + (356740570469503/25000000000000 : ℝ)*(sp6) + (361821581856433/50000000000000 : ℝ)*(sp7) + (723643270912991/100000000000000 : ℝ)*(f.failure) + (1426973060534063/100000000000000 : ℝ)*(f.sum) + (43098799229079/23135000000000000000000000000 : ℝ)*base65 + (4507473834357968503/4627000000000000000000000000000000 : ℝ)*base67 + (3500817315216968503/4627000000000000000000000000000000 : ℝ)*base69 + (3914583912584031497/4627000000000000000000000000000000 : ℝ)*base72 + (9911325685021/5783750000000000000000000000 : ℝ)*base73 + (38737721850930968503/4627000000000000000000000000000000 : ℝ)*base75 + (27922813089868968503/4627000000000000000000000000000000 : ℝ)*base77 + (58966718611812968503/4627000000000000000000000000000000 : ℝ)*base79 + (16731989557693/11567500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (17035363/2000000000000000000000 : ℝ)*base89 + (17035363/2000000000000000000000 : ℝ)*base91 + (17035363/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1097_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2697/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4129/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1097_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1097_s2_0 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1084863589/5000000000 : ℝ)*x 0 + (5519601247/10000000000 : ℝ)*x 1 + (2575728661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084863589/5000000000 : ℝ)^4145 ≤ (3285637765831/25000000000000 : ℝ)^3121 := by
    have hnat : (1084863589 : ℕ)^4145*25000000000000^3121 ≤ 3285637765831^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084863589 5000000000 3285637765831 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5519601247/10000000000 : ℝ)^4145 ≤ (45417960688969/100000000000000 : ℝ)^3121 := by
    have hnat : (5519601247 : ℕ)^4145*100000000000000^3121 ≤ 45417960688969^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519601247 10000000000 45417960688969 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575728661/5000000000 : ℝ)^4145 ≤ (41439488226303/100000000000000 : ℝ)^3121 := by
    have hnat : (2575728661 : ℕ)^4145*100000000000000^3121 ≤ 41439488226303^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575728661 5000000000 41439488226303 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1084863589/5000000000 : ℝ), (5519601247/10000000000 : ℝ), (2575728661/5000000000 : ℝ)] ![(3285637765831/25000000000000 : ℝ), (45417960688969/100000000000000 : ℝ), (41439488226303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1084863589/5000000000 : ℝ)|^4145 ≤ (3285637765831/25000000000000 : ℝ)^3121
        have hw : |(-1084863589/5000000000 : ℝ)|=(1084863589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5519601247/10000000000 : ℝ)|^4145 ≤ (45417960688969/100000000000000 : ℝ)^3121
        have hw : |(5519601247/10000000000 : ℝ)|=(5519601247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575728661/5000000000 : ℝ)|^4145 ≤ (41439488226303/100000000000000 : ℝ)^3121
        have hw : |(2575728661/5000000000 : ℝ)|=(2575728661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s2_1 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687913229/5000000000 : ℝ)*x 0 + (-472294227/2000000000 : ℝ)*x 1 + (2575729199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687913229/5000000000 : ℝ)^4145 ≤ (21926753624239/50000000000000 : ℝ)^3121 := by
    have hnat : (2687913229 : ℕ)^4145*50000000000000^3121 ≤ 21926753624239^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687913229 5000000000 21926753624239 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (472294227/2000000000 : ℝ)^4145 ≤ (14706993015327/100000000000000 : ℝ)^3121 := by
    have hnat : (472294227 : ℕ)^4145*100000000000000^3121 ≤ 14706993015327^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472294227 2000000000 14706993015327 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575729199/5000000000 : ℝ)^4145 ≤ (41439499721789/100000000000000 : ℝ)^3121 := by
    have hnat : (2575729199 : ℕ)^4145*100000000000000^3121 ≤ 41439499721789^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575729199 5000000000 41439499721789 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687913229/5000000000 : ℝ), (-472294227/2000000000 : ℝ), (2575729199/5000000000 : ℝ)] ![(21926753624239/50000000000000 : ℝ), (14706993015327/100000000000000 : ℝ), (41439499721789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687913229/5000000000 : ℝ)|^4145 ≤ (21926753624239/50000000000000 : ℝ)^3121
        have hw : |(2687913229/5000000000 : ℝ)|=(2687913229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-472294227/2000000000 : ℝ)|^4145 ≤ (14706993015327/100000000000000 : ℝ)^3121
        have hw : |(-472294227/2000000000 : ℝ)|=(472294227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575729199/5000000000 : ℝ)|^4145 ≤ (41439499721789/100000000000000 : ℝ)^3121
        have hw : |(2575729199/5000000000 : ℝ)|=(2575729199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s2_2 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375826413/10000000000 : ℝ)*x 0 + (2575729223/5000000000 : ℝ)*x 1 + (-590367783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375826413/10000000000 : ℝ)^4145 ≤ (43853506760947/100000000000000 : ℝ)^3121 := by
    have hnat : (5375826413 : ℕ)^4145*100000000000000^3121 ≤ 43853506760947^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375826413 10000000000 43853506760947 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2575729223/5000000000 : ℝ)^4145 ≤ (41439500234599/100000000000000 : ℝ)^3121 := by
    have hnat : (2575729223 : ℕ)^4145*100000000000000^3121 ≤ 41439500234599^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575729223 5000000000 41439500234599 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (590367783/2500000000 : ℝ)^4145 ≤ (14706992990513/100000000000000 : ℝ)^3121 := by
    have hnat : (590367783 : ℕ)^4145*100000000000000^3121 ≤ 14706992990513^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590367783 2500000000 14706992990513 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375826413/10000000000 : ℝ), (2575729223/5000000000 : ℝ), (-590367783/2500000000 : ℝ)] ![(43853506760947/100000000000000 : ℝ), (41439500234599/100000000000000 : ℝ), (14706992990513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375826413/10000000000 : ℝ)|^4145 ≤ (43853506760947/100000000000000 : ℝ)^3121
        have hw : |(5375826413/10000000000 : ℝ)|=(5375826413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2575729223/5000000000 : ℝ)|^4145 ≤ (41439500234599/100000000000000 : ℝ)^3121
        have hw : |(2575729223/5000000000 : ℝ)|=(2575729223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-590367783/2500000000 : ℝ)|^4145 ≤ (14706992990513/100000000000000 : ℝ)^3121
        have hw : |(-590367783/2500000000 : ℝ)|=(590367783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s2_3 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (871861307/2000000000 : ℝ)*x 0 + (12535819/31250000 : ℝ)*x 1 + (2368706977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871861307/2000000000 : ℝ)^4145 ≤ (6639574793369/20000000000000 : ℝ)^3121 := by
    have hnat : (871861307 : ℕ)^4145*20000000000000^3121 ≤ 6639574793369^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871861307 2000000000 6639574793369 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12535819/31250000 : ℝ)^4145 ≤ (29726673758783/100000000000000 : ℝ)^3121 := by
    have hnat : (12535819 : ℕ)^4145*100000000000000^3121 ≤ 29726673758783^3121*31250000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12535819 31250000 29726673758783 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2368706977/5000000000 : ℝ)^4145 ≤ (37075452250893/100000000000000 : ℝ)^3121 := by
    have hnat : (2368706977 : ℕ)^4145*100000000000000^3121 ≤ 37075452250893^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2368706977 5000000000 37075452250893 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871861307/2000000000 : ℝ), (12535819/31250000 : ℝ), (2368706977/5000000000 : ℝ)] ![(6639574793369/20000000000000 : ℝ), (29726673758783/100000000000000 : ℝ), (37075452250893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871861307/2000000000 : ℝ)|^4145 ≤ (6639574793369/20000000000000 : ℝ)^3121
        have hw : |(871861307/2000000000 : ℝ)|=(871861307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12535819/31250000 : ℝ)|^4145 ≤ (29726673758783/100000000000000 : ℝ)^3121
        have hw : |(12535819/31250000 : ℝ)|=(12535819/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2368706977/5000000000 : ℝ)|^4145 ≤ (37075452250893/100000000000000 : ℝ)^3121
        have hw : |(2368706977/5000000000 : ℝ)|=(2368706977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s2_4 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-433968561/2000000000 : ℝ)*x 0 + (2577038849/5000000000 : ℝ)*x 1 + (5516954011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433968561/2000000000 : ℝ)^4145 ≤ (13143481246253/100000000000000 : ℝ)^3121 := by
    have hnat : (433968561 : ℕ)^4145*100000000000000^3121 ≤ 13143481246253^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433968561 2000000000 13143481246253 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2577038849/5000000000 : ℝ)^4145 ≤ (8293497089019/20000000000000 : ℝ)^3121 := by
    have hnat : (2577038849 : ℕ)^4145*20000000000000^3121 ≤ 8293497089019^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577038849 5000000000 8293497089019 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5516954011/10000000000 : ℝ)^4145 ≤ (45389033303861/100000000000000 : ℝ)^3121 := by
    have hnat : (5516954011 : ℕ)^4145*100000000000000^3121 ≤ 45389033303861^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516954011 10000000000 45389033303861 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-433968561/2000000000 : ℝ), (2577038849/5000000000 : ℝ), (5516954011/10000000000 : ℝ)] ![(13143481246253/100000000000000 : ℝ), (8293497089019/20000000000000 : ℝ), (45389033303861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-433968561/2000000000 : ℝ)|^4145 ≤ (13143481246253/100000000000000 : ℝ)^3121
        have hw : |(-433968561/2000000000 : ℝ)|=(433968561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2577038849/5000000000 : ℝ)|^4145 ≤ (8293497089019/20000000000000 : ℝ)^3121
        have hw : |(2577038849/5000000000 : ℝ)|=(2577038849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5516954011/10000000000 : ℝ)|^4145 ≤ (45389033303861/100000000000000 : ℝ)^3121
        have hw : |(5516954011/10000000000 : ℝ)|=(5516954011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s2_5 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1320675681/2500000000 : ℝ)*x 0 + (-1995974997/10000000000 : ℝ)*x 1 + (55169541/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320675681/2500000000 : ℝ)^4145 ≤ (42847480624937/100000000000000 : ℝ)^3121 := by
    have hnat : (1320675681 : ℕ)^4145*100000000000000^3121 ≤ 42847480624937^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320675681 2500000000 42847480624937 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1995974997/10000000000 : ℝ)^4145 ≤ (5881742544959/50000000000000 : ℝ)^3121 := by
    have hnat : (1995974997 : ℕ)^4145*50000000000000^3121 ≤ 5881742544959^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995974997 10000000000 5881742544959 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55169541/100000000 : ℝ)^4145 ≤ (45389034276323/100000000000000 : ℝ)^3121 := by
    have hnat : (55169541 : ℕ)^4145*100000000000000^3121 ≤ 45389034276323^3121*100000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55169541 100000000 45389034276323 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320675681/2500000000 : ℝ), (-1995974997/10000000000 : ℝ), (55169541/100000000 : ℝ)] ![(42847480624937/100000000000000 : ℝ), (5881742544959/50000000000000 : ℝ), (45389034276323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320675681/2500000000 : ℝ)|^4145 ≤ (42847480624937/100000000000000 : ℝ)^3121
        have hw : |(1320675681/2500000000 : ℝ)|=(1320675681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1995974997/10000000000 : ℝ)|^4145 ≤ (5881742544959/50000000000000 : ℝ)^3121
        have hw : |(-1995974997/10000000000 : ℝ)|=(1995974997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(55169541/100000000 : ℝ)|^4145 ≤ (45389034276323/100000000000000 : ℝ)^3121
        have hw : |(55169541/100000000 : ℝ)|=(55169541/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s2_6 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2641351447/5000000000 : ℝ)*x 0 + (2758477013/5000000000 : ℝ)*x 1 + (-399194973/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641351447/5000000000 : ℝ)^4145 ≤ (334745956689/781250000000 : ℝ)^3121 := by
    have hnat : (2641351447 : ℕ)^4145*781250000000^3121 ≤ 334745956689^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641351447 5000000000 334745956689 781250000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2758477013/5000000000 : ℝ)^4145 ≤ (45389033467759/100000000000000 : ℝ)^3121 := by
    have hnat : (2758477013 : ℕ)^4145*100000000000000^3121 ≤ 45389033467759^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758477013 5000000000 45389033467759 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (399194973/2000000000 : ℝ)^4145 ≤ (2352696811343/20000000000000 : ℝ)^3121 := by
    have hnat : (399194973 : ℕ)^4145*20000000000000^3121 ≤ 2352696811343^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399194973 2000000000 2352696811343 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641351447/5000000000 : ℝ), (2758477013/5000000000 : ℝ), (-399194973/2000000000 : ℝ)] ![(334745956689/781250000000 : ℝ), (45389033467759/100000000000000 : ℝ), (2352696811343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641351447/5000000000 : ℝ)|^4145 ≤ (334745956689/781250000000 : ℝ)^3121
        have hw : |(2641351447/5000000000 : ℝ)|=(2641351447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2758477013/5000000000 : ℝ)|^4145 ≤ (45389033467759/100000000000000 : ℝ)^3121
        have hw : |(2758477013/5000000000 : ℝ)|=(2758477013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-399194973/2000000000 : ℝ)|^4145 ≤ (2352696811343/20000000000000 : ℝ)^3121
        have hw : |(-399194973/2000000000 : ℝ)|=(399194973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s2_7 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (871907173/2000000000 : ℝ)*x 0 + (473224747/1000000000 : ℝ)*x 1 + (1004170149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871907173/2000000000 : ℝ)^4145 ≤ (16600096717057/50000000000000 : ℝ)^3121 := by
    have hnat : (871907173 : ℕ)^4145*50000000000000^3121 ≤ 16600096717057^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871907173 2000000000 16600096717057 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (473224747/1000000000 : ℝ)^4145 ≤ (46277202837/125000000000 : ℝ)^3121 := by
    have hnat : (473224747 : ℕ)^4145*125000000000^3121 ≤ 46277202837^3121*1000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473224747 1000000000 46277202837 125000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004170149/2500000000 : ℝ)^4145 ≤ (14889022145099/50000000000000 : ℝ)^3121 := by
    have hnat : (1004170149 : ℕ)^4145*50000000000000^3121 ≤ 14889022145099^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004170149 2500000000 14889022145099 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871907173/2000000000 : ℝ), (473224747/1000000000 : ℝ), (1004170149/2500000000 : ℝ)] ![(16600096717057/50000000000000 : ℝ), (46277202837/125000000000 : ℝ), (14889022145099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871907173/2000000000 : ℝ)|^4145 ≤ (16600096717057/50000000000000 : ℝ)^3121
        have hw : |(871907173/2000000000 : ℝ)|=(871907173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(473224747/1000000000 : ℝ)|^4145 ≤ (46277202837/125000000000 : ℝ)^3121
        have hw : |(473224747/1000000000 : ℝ)|=(473224747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004170149/2500000000 : ℝ)|^4145 ≤ (14889022145099/50000000000000 : ℝ)^3121
        have hw : |(1004170149/2500000000 : ℝ)|=(1004170149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1097_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4129/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2697/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8861/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16641/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4129/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2697/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4129/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2697/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4129/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2697/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4129/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2697/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4129/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2697/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4129/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2697/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2697/50000 : ℝ) ^ (8289/2048 : ℝ) ≤ (73719589761339/10000000000000000000 : ℝ) := by
    have hpowers : (2697/50000 : ℝ)^8289 ≤ (73719589761339/10000000000000000000 : ℝ)^2048 := by
      have hnat : (2697 : ℕ)^8289*10000000000000000000^2048 ≤ 73719589761339^2048*50000^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2697 50000 73719589761339 10000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2697/50000 : ℝ)) (X := (73719589761339/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4129/20000 : ℝ) ^ (8289/2048 : ℝ) ≤ (168580343195551537/100000000000000000000 : ℝ) := by
    have hpowers : (4129/20000 : ℝ)^8289 ≤ (168580343195551537/100000000000000000000 : ℝ)^2048 := by
      have hnat : (4129 : ℕ)^8289*100000000000000000000^2048 ≤ 168580343195551537^2048*20000^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4129 20000 168580343195551537 100000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4129/20000 : ℝ)) (X := (168580343195551537/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000073719589761339/5000000000000000000 : ℝ) ≤ (1000003642824993/1000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (5000073719589761339/5000000000000000000 : ℝ)^2048 ≤ (1000003642824993/1000000000000000 : ℝ)^8289 := by
      have hnat : (5000073719589761339 : ℕ)^2048*1000000000000000^8289 ≤ 1000003642824993^8289*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000073719589761339 5000000000000000000 1000003642824993 1000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000003642824993/1000000000000000 : ℝ)) (X := (5000073719589761339/5000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100169317539093164927/100000000000000000000 : ℝ) ≤ (10004180739607991/10000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (100169317539093164927/100000000000000000000 : ℝ)^2048 ≤ (10004180739607991/10000000000000000 : ℝ)^8289 := by
      have hnat : (100169317539093164927 : ℕ)^2048*10000000000000000^8289 ≤ 10004180739607991^8289*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100169317539093164927 100000000000000000000 10004180739607991 10000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004180739607991/10000000000000000 : ℝ)) (X := (100169317539093164927/100000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50168580343195551537/50000000000000000000 : ℝ) ≤ (2502081262741513/2500000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (50168580343195551537/50000000000000000000 : ℝ)^2048 ≤ (2502081262741513/2500000000000000 : ℝ)^8289 := by
      have hnat : (50168580343195551537 : ℕ)^2048*2500000000000000^8289 ≤ 2502081262741513^8289*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50168580343195551537 50000000000000000000 2502081262741513 2500000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502081262741513/2500000000000000 : ℝ)) (X := (50168580343195551537/50000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(73719589761339/10000000000000000000 : ℝ) ≤ ((76232923368154460181/76255000000000000000 : ℝ)+2*(4144311358061/1525100000000000 : ℝ)*(2697/50000 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (76232923368154460181/76255000000000000000 : ℝ)+2*(4144311358061/1525100000000000 : ℝ)*(2697/50000 : ℝ)=(1000003642824993/1000000000000000 : ℝ) by norm_num, show 1+2*(73719589761339/10000000000000000000 : ℝ)=(5000073719589761339/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(168580343195551537/100000000000000000000 : ℝ)+(73719589761339/10000000000000000000 : ℝ) ≤ ((76232923368154460181/76255000000000000000 : ℝ)+(4144311358061/1525100000000000 : ℝ)*((4129/20000 : ℝ)+(2697/50000 : ℝ)))^(8289/2048 : ℝ) := by
    rw [show (76232923368154460181/76255000000000000000 : ℝ)+(4144311358061/1525100000000000 : ℝ)*((4129/20000 : ℝ)+(2697/50000 : ℝ))=(10004180739607991/10000000000000000 : ℝ) by norm_num, show 1+(168580343195551537/100000000000000000000 : ℝ)+(73719589761339/10000000000000000000 : ℝ)=(100169317539093164927/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(168580343195551537/100000000000000000000 : ℝ) ≤ ((76232923368154460181/76255000000000000000 : ℝ)+2*(4144311358061/1525100000000000 : ℝ)*(4129/20000 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (76232923368154460181/76255000000000000000 : ℝ)+2*(4144311358061/1525100000000000 : ℝ)*(4129/20000 : ℝ)=(2502081262741513/2500000000000000 : ℝ) by norm_num, show 1+2*(168580343195551537/100000000000000000000 : ℝ)=(50168580343195551537/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (76232923368154460181/76255000000000000000 : ℝ)*(X 1 0+X 2 0)+(4144311358061/1525100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (2697/50000 : ℝ)) (hi := (4129/20000 : ℝ)) (c := (76232923368154460181/76255000000000000000 : ℝ)) (alpha := (4144311358061/1525100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (76232923368154460181/76255000000000000000 : ℝ)*(X 0 1+X 2 1)+(4144311358061/1525100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (2697/50000 : ℝ)) (hi := (4129/20000 : ℝ)) (c := (76232923368154460181/76255000000000000000 : ℝ)) (alpha := (4144311358061/1525100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (76232923368154460181/76255000000000000000 : ℝ)*(X 0 2+X 1 2)+(4144311358061/1525100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (2697/50000 : ℝ)) (hi := (4129/20000 : ℝ)) (c := (76232923368154460181/76255000000000000000 : ℝ)) (alpha := (4144311358061/1525100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1084863589/5000000000 : ℝ)*X 0 0+(5519601247/10000000000 : ℝ)*X 0 1+(2575728661/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687913229/5000000000 : ℝ)*X 1 0+(-472294227/2000000000 : ℝ)*X 1 1+(2575729199/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5375826413/10000000000 : ℝ)*X 2 0+(2575729223/5000000000 : ℝ)*X 2 1+(-590367783/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871861307/2000000000 : ℝ)*X 0 0+(12535819/31250000 : ℝ)*X 0 1+(2368706977/5000000000 : ℝ)*X 0 2+(871861307/2000000000 : ℝ)*X 1 0+(12535819/31250000 : ℝ)*X 1 1+(2368706977/5000000000 : ℝ)*X 1 2+(871861307/2000000000 : ℝ)*X 2 0+(12535819/31250000 : ℝ)*X 2 1+(2368706977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-433968561/2000000000 : ℝ)*X 0 0+(2577038849/5000000000 : ℝ)*X 0 1+(5516954011/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1320675681/2500000000 : ℝ)*X 1 0+(-1995974997/10000000000 : ℝ)*X 1 1+(55169541/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2641351447/5000000000 : ℝ)*X 2 0+(2758477013/5000000000 : ℝ)*X 2 1+(-399194973/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871907173/2000000000 : ℝ)*X 0 0+(473224747/1000000000 : ℝ)*X 0 1+(1004170149/2500000000 : ℝ)*X 0 2+(871907173/2000000000 : ℝ)*X 1 0+(473224747/1000000000 : ℝ)*X 1 1+(1004170149/2500000000 : ℝ)*X 1 2+(871907173/2000000000 : ℝ)*X 2 0+(473224747/1000000000 : ℝ)*X 2 1+(1004170149/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20170272175358360390035517493/1906375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (297049517/20000000000000 : ℝ)*(base19) + (125708699/10000000000000 : ℝ)*(base23) + (51791173/20000000000000 : ℝ)*(upper3) + (11043151/10000000000000 : ℝ)*(upper4) + (97841877/100000000000000 : ℝ)*(upper5) + (2046945956611349/100000000000000 : ℝ)*(major0) + (2046945956611349/100000000000000 : ℝ)*(major1) + (2046945956611349/100000000000000 : ℝ)*(major2) + (271635099181279/10000000000000 : ℝ)*(sp0) + (543274024218733/20000000000000 : ℝ)*(sp1) + (135818517462713/5000000000000 : ℝ)*(sp2) + (1377510053032927/100000000000000 : ℝ)*(sp3) + (1030726423/5000000000000 : ℝ)*(sp4) + (9901167429/100000000000000 : ℝ)*(sp7) + (1377519954200357/100000000000000 : ℝ)*(f.failure) + (2173097285073/80000000000 : ℝ)*(f.sum) + (74063940063761/76255000000000000000000000000 : ℝ)*base66 + (42242263027327644169/7625500000000000000000000000000000 : ℝ)*base67 + (35586913589336644169/7625500000000000000000000000000000 : ℝ)*base69 + (9438043747027644169/7625500000000000000000000000000000 : ℝ)*base71 + (56818672103183/9531875000000000000000000000 : ℝ)*base73 + (11229441263028355831/7625500000000000000000000000000000 : ℝ)*base76 + (28062711280372644169/7625500000000000000000000000000000 : ℝ)*base77 + (7686198360702644169/7625500000000000000000000000000000 : ℝ)*base79 + (574266241438179/76255000000000000000000000000 : ℝ)*base81 + (10387601/2000000000000000000000 : ℝ)*base89 + (10387601/2000000000000000000000 : ℝ)*base91 + (10387601/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6484535411965263401236590897/953187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (674608503/50000000000000 : ℝ)*(base19) + (785085021/50000000000000 : ℝ)*(base23) + (186961961/100000000000000 : ℝ)*(upper3) + (691607/1562500000000 : ℝ)*(lower4) + (131138929/100000000000000 : ℝ)*(upper5) + (1038313283916421/50000000000000 : ℝ)*(major0) + (1038313283916421/50000000000000 : ℝ)*(major1) + (1038313283916421/50000000000000 : ℝ)*(major2) + (12104779021/100000000000000 : ℝ)*(sp1) + (7427576853/50000000000000 : ℝ)*(sp2) + (1377879493062203/50000000000000 : ℝ)*(sp4) + (1377872766064189/50000000000000 : ℝ)*(sp5) + (1377871280400329/50000000000000 : ℝ)*(sp6) + (139749392277457/10000000000000 : ℝ)*(sp7) + (139749392277457/10000000000000 : ℝ)*(f.failure) + (1377879493062203/50000000000000 : ℝ)*(f.sum) + (310925621596631/38127500000000000000000000000 : ℝ)*base65 + (10650802149438582201/3812750000000000000000000000000000 : ℝ)*base67 + (26198430675589082201/3812750000000000000000000000000000 : ℝ)*base69 + (43661755399425582201/3812750000000000000000000000000000 : ℝ)*base71 + (95336396494617/76255000000000000000000000000 : ℝ)*base73 + (43846027368416082201/3812750000000000000000000000000000 : ℝ)*base75 + (14875868302790582201/3812750000000000000000000000000000 : ℝ)*base77 + (483772210960417799/3812750000000000000000000000000000 : ℝ)*base80 + (4271398955899/595742187500000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2122099/200000000000000000000 : ℝ)*base90 + (2122099/200000000000000000000 : ℝ)*base92 + (2122099/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1097_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4129/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2697/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8861/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16641/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1097_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1097_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8861/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16641/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1097_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1097_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1097_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8861/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16641/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1097_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

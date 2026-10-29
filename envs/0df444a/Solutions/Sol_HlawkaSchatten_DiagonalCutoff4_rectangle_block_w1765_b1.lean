-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1765_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:29:46.584585+00:00
-- url     : https://prove2.me/submissions/575e53df-0fb0-481d-a4e2-6205a89bbdab

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
theorem support_rectangle_w1765_s3_0 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1065181103/2000000000 : ℝ)*x 0 + (-1348354919/10000000000 : ℝ)*x 1 + (2542413523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065181103/2000000000 : ℝ)^6015 ≤ (9360257343981/20000000000000 : ℝ)^4991 := by
    have hnat : (1065181103 : ℕ)^6015*20000000000000^4991 ≤ 9360257343981^4991*2000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065181103 2000000000 9360257343981 20000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348354919/10000000000 : ℝ)^6015 ≤ (8938543571277/100000000000000 : ℝ)^4991 := by
    have hnat : (1348354919 : ℕ)^6015*100000000000000^4991 ≤ 8938543571277^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348354919 10000000000 8938543571277 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2542413523/5000000000 : ℝ)^6015 ≤ (11065042424559/25000000000000 : ℝ)^4991 := by
    have hnat : (2542413523 : ℕ)^6015*25000000000000^4991 ≤ 11065042424559^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542413523 5000000000 11065042424559 25000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065181103/2000000000 : ℝ), (-1348354919/10000000000 : ℝ), (2542413523/5000000000 : ℝ)] ![(9360257343981/20000000000000 : ℝ), (8938543571277/100000000000000 : ℝ), (11065042424559/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065181103/2000000000 : ℝ)|^6015 ≤ (9360257343981/20000000000000 : ℝ)^4991
        have hw : |(1065181103/2000000000 : ℝ)|=(1065181103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1348354919/10000000000 : ℝ)|^6015 ≤ (8938543571277/100000000000000 : ℝ)^4991
        have hw : |(-1348354919/10000000000 : ℝ)|=(1348354919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2542413523/5000000000 : ℝ)|^6015 ≤ (11065042424559/25000000000000 : ℝ)^4991
        have hw : |(2542413523/5000000000 : ℝ)|=(2542413523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s3_1 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-285936377/2500000000 : ℝ)*x 0 + (5091367293/10000000000 : ℝ)*x 1 + (5470873813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (285936377/2500000000 : ℝ)^6015 ≤ (7330397060331/100000000000000 : ℝ)^4991 := by
    have hnat : (285936377 : ℕ)^6015*100000000000000^4991 ≤ 7330397060331^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285936377 2500000000 7330397060331 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5091367293/10000000000 : ℝ)^6015 ≤ (8865757486761/20000000000000 : ℝ)^4991 := by
    have hnat : (5091367293 : ℕ)^6015*20000000000000^4991 ≤ 8865757486761^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5091367293 10000000000 8865757486761 20000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470873813/10000000000 : ℝ)^6015 ≤ (48340815499339/100000000000000 : ℝ)^4991 := by
    have hnat : (5470873813 : ℕ)^6015*100000000000000^4991 ≤ 48340815499339^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470873813 10000000000 48340815499339 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-285936377/2500000000 : ℝ), (5091367293/10000000000 : ℝ), (5470873813/10000000000 : ℝ)] ![(7330397060331/100000000000000 : ℝ), (8865757486761/20000000000000 : ℝ), (48340815499339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-285936377/2500000000 : ℝ)|^6015 ≤ (7330397060331/100000000000000 : ℝ)^4991
        have hw : |(-285936377/2500000000 : ℝ)|=(285936377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5091367293/10000000000 : ℝ)|^6015 ≤ (8865757486761/20000000000000 : ℝ)^4991
        have hw : |(5091367293/10000000000 : ℝ)|=(5091367293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470873813/10000000000 : ℝ)|^6015 ≤ (48340815499339/100000000000000 : ℝ)^4991
        have hw : |(5470873813/10000000000 : ℝ)|=(5470873813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s3_2 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2611157/5000000 : ℝ)*x 0 + (-48115223/500000000 : ℝ)*x 1 + (1367718419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2611157/5000000 : ℝ)^6015 ≤ (1828256458147/4000000000000 : ℝ)^4991 := by
    have hnat : (2611157 : ℕ)^6015*4000000000000^4991 ≤ 1828256458147^4991*5000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611157 5000000 1828256458147 4000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48115223/500000000 : ℝ)^6015 ≤ (2976387247839/50000000000000 : ℝ)^4991 := by
    have hnat : (48115223 : ℕ)^6015*50000000000000^4991 ≤ 2976387247839^4991*500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48115223 500000000 2976387247839 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367718419/2500000000 : ℝ)^6015 ≤ (24170407020219/50000000000000 : ℝ)^4991 := by
    have hnat : (1367718419 : ℕ)^6015*50000000000000^4991 ≤ 24170407020219^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367718419 2500000000 24170407020219 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2611157/5000000 : ℝ), (-48115223/500000000 : ℝ), (1367718419/2500000000 : ℝ)] ![(1828256458147/4000000000000 : ℝ), (2976387247839/50000000000000 : ℝ), (24170407020219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2611157/5000000 : ℝ)|^6015 ≤ (1828256458147/4000000000000 : ℝ)^4991
        have hw : |(2611157/5000000 : ℝ)|=(2611157/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-48115223/500000000 : ℝ)|^6015 ≤ (2976387247839/50000000000000 : ℝ)^4991
        have hw : |(-48115223/500000000 : ℝ)|=(48115223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367718419/2500000000 : ℝ)|^6015 ≤ (24170407020219/50000000000000 : ℝ)^4991
        have hw : |(1367718419/2500000000 : ℝ)|=(1367718419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s3_3 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5222313827/10000000000 : ℝ)*x 0 + (2735436861/5000000000 : ℝ)*x 1 + (-962304639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5222313827/10000000000 : ℝ)^6015 ≤ (5713301203613/12500000000000 : ℝ)^4991 := by
    have hnat : (5222313827 : ℕ)^6015*12500000000000^4991 ≤ 5713301203613^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222313827 10000000000 5713301203613 12500000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735436861/5000000000 : ℝ)^6015 ≤ (3021300908143/6250000000000 : ℝ)^4991 := by
    have hnat : (2735436861 : ℕ)^6015*6250000000000^4991 ≤ 3021300908143^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735436861 5000000000 3021300908143 6250000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (962304639/10000000000 : ℝ)^6015 ≤ (1190555166029/20000000000000 : ℝ)^4991 := by
    have hnat : (962304639 : ℕ)^6015*20000000000000^4991 ≤ 1190555166029^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962304639 10000000000 1190555166029 20000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5222313827/10000000000 : ℝ), (2735436861/5000000000 : ℝ), (-962304639/10000000000 : ℝ)] ![(5713301203613/12500000000000 : ℝ), (3021300908143/6250000000000 : ℝ), (1190555166029/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5222313827/10000000000 : ℝ)|^6015 ≤ (5713301203613/12500000000000 : ℝ)^4991
        have hw : |(5222313827/10000000000 : ℝ)|=(5222313827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735436861/5000000000 : ℝ)|^6015 ≤ (3021300908143/6250000000000 : ℝ)^4991
        have hw : |(2735436861/5000000000 : ℝ)|=(2735436861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-962304639/10000000000 : ℝ)|^6015 ≤ (1190555166029/20000000000000 : ℝ)^4991
        have hw : |(-962304639/10000000000 : ℝ)|=(962304639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s3_4 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (199603521/500000000 : ℝ)*x 0 + (468278863/1000000000 : ℝ)*x 1 + (1679663049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (199603521/500000000 : ℝ)^6015 ≤ (8266398031277/25000000000000 : ℝ)^4991 := by
    have hnat : (199603521 : ℕ)^6015*25000000000000^4991 ≤ 8266398031277^4991*500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199603521 500000000 8266398031277 25000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (468278863/1000000000 : ℝ)^6015 ≤ (40077645905609/100000000000000 : ℝ)^4991 := by
    have hnat : (468278863 : ℕ)^6015*100000000000000^4991 ≤ 40077645905609^4991*1000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468278863 1000000000 40077645905609 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1679663049/5000000000 : ℝ)^6015 ≤ (13428380975867/50000000000000 : ℝ)^4991 := by
    have hnat : (1679663049 : ℕ)^6015*50000000000000^4991 ≤ 13428380975867^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1679663049 5000000000 13428380975867 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(199603521/500000000 : ℝ), (468278863/1000000000 : ℝ), (1679663049/5000000000 : ℝ)] ![(8266398031277/25000000000000 : ℝ), (40077645905609/100000000000000 : ℝ), (13428380975867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(199603521/500000000 : ℝ)|^6015 ≤ (8266398031277/25000000000000 : ℝ)^4991
        have hw : |(199603521/500000000 : ℝ)|=(199603521/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(468278863/1000000000 : ℝ)|^6015 ≤ (40077645905609/100000000000000 : ℝ)^4991
        have hw : |(468278863/1000000000 : ℝ)|=(468278863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1679663049/5000000000 : ℝ)|^6015 ≤ (13428380975867/50000000000000 : ℝ)^4991
        have hw : |(1679663049/5000000000 : ℝ)|=(1679663049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1765_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (56091581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1841/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1841/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8843/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17687/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1841/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17687/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1841/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17687/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1841/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17687/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1841/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17687/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1841/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17687/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1841/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1841/20000 : ℝ) ^ (5999/1024 : ℝ) ≤ (85278314228661/100000000000000000000 : ℝ) := by
    have hpowers : (1841/20000 : ℝ)^5999 ≤ (85278314228661/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1841 : ℕ)^5999*100000000000000000000^1024 ≤ 85278314228661^1024*20000^5999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1841 20000 85278314228661 100000000000000000000 5999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1841/20000 : ℝ)) (X := (85278314228661/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17687/100000 : ℝ) ^ (5999/1024 : ℝ) ≤ (978134118373421/25000000000000000000 : ℝ) := by
    have hpowers : (17687/100000 : ℝ)^5999 ≤ (978134118373421/25000000000000000000 : ℝ)^1024 := by
      have hnat : (17687 : ℕ)^5999*25000000000000000000^1024 ≤ 978134118373421^1024*100000^5999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17687 100000 978134118373421 25000000000000000000 5999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17687/100000 : ℝ)) (X := (978134118373421/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000085278314228661/50000000000000000000 : ℝ) ≤ (10000002911316287/10000000000000000 : ℝ) ^ (5999/1024 : ℝ) := by
    have hpowers : (50000085278314228661/50000000000000000000 : ℝ)^1024 ≤ (10000002911316287/10000000000000000 : ℝ)^5999 := by
      have hnat : (50000085278314228661 : ℕ)^1024*10000000000000000^5999 ≤ 10000002911316287^5999*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000085278314228661 50000000000000000000 10000002911316287 10000000000000000 1024 5999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002911316287/10000000000000000 : ℝ)) (X := (50000085278314228661/50000000000000000000 : ℝ)) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20000799562957544469/20000000000000000000 : ℝ) ≤ (10000068239614633/10000000000000000 : ℝ) ^ (5999/1024 : ℝ) := by
    have hpowers : (20000799562957544469/20000000000000000000 : ℝ)^1024 ≤ (10000068239614633/10000000000000000 : ℝ)^5999 := by
      have hnat : (20000799562957544469 : ℕ)^1024*10000000000000000^5999 ≤ 10000068239614633^5999*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20000799562957544469 20000000000000000000 10000068239614633 10000000000000000 1024 5999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000068239614633/10000000000000000 : ℝ)) (X := (20000799562957544469/20000000000000000000 : ℝ)) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12500978134118373421/12500000000000000000 : ℝ) ≤ (10000133567912979/10000000000000000 : ℝ) ^ (5999/1024 : ℝ) := by
    have hpowers : (12500978134118373421/12500000000000000000 : ℝ)^1024 ≤ (10000133567912979/10000000000000000 : ℝ)^5999 := by
      have hnat : (12500978134118373421 : ℕ)^1024*10000000000000000^5999 ≤ 10000133567912979^5999*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500978134118373421 12500000000000000000 10000133567912979 10000000000000000 1024 5999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000133567912979/10000000000000000 : ℝ)) (X := (12500978134118373421/12500000000000000000 : ℝ)) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(85278314228661/100000000000000000000 : ℝ) ≤ ((42409410999906098237/42410000000000000000 : ℝ)+2*(32664149173/424100000000000 : ℝ)*(1841/20000 : ℝ))^(5999/1024 : ℝ) := by
    rw [show (42409410999906098237/42410000000000000000 : ℝ)+2*(32664149173/424100000000000 : ℝ)*(1841/20000 : ℝ)=(10000002911316287/10000000000000000 : ℝ) by norm_num, show 1+2*(85278314228661/100000000000000000000 : ℝ)=(50000085278314228661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(978134118373421/25000000000000000000 : ℝ)+(85278314228661/100000000000000000000 : ℝ) ≤ ((42409410999906098237/42410000000000000000 : ℝ)+(32664149173/424100000000000 : ℝ)*((17687/100000 : ℝ)+(1841/20000 : ℝ)))^(5999/1024 : ℝ) := by
    rw [show (42409410999906098237/42410000000000000000 : ℝ)+(32664149173/424100000000000 : ℝ)*((17687/100000 : ℝ)+(1841/20000 : ℝ))=(10000068239614633/10000000000000000 : ℝ) by norm_num, show 1+(978134118373421/25000000000000000000 : ℝ)+(85278314228661/100000000000000000000 : ℝ)=(20000799562957544469/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(978134118373421/25000000000000000000 : ℝ) ≤ ((42409410999906098237/42410000000000000000 : ℝ)+2*(32664149173/424100000000000 : ℝ)*(17687/100000 : ℝ))^(5999/1024 : ℝ) := by
    rw [show (42409410999906098237/42410000000000000000 : ℝ)+2*(32664149173/424100000000000 : ℝ)*(17687/100000 : ℝ)=(10000133567912979/10000000000000000 : ℝ) by norm_num, show 1+2*(978134118373421/25000000000000000000 : ℝ)=(12500978134118373421/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (42409410999906098237/42410000000000000000 : ℝ)*(X 1 0+X 2 0)+(32664149173/424100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5999/1024 : ℝ)) (lo := (1841/20000 : ℝ)) (hi := (17687/100000 : ℝ)) (c := (42409410999906098237/42410000000000000000 : ℝ)) (alpha := (32664149173/424100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (42409410999906098237/42410000000000000000 : ℝ)*(X 0 1+X 2 1)+(32664149173/424100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5999/1024 : ℝ)) (lo := (1841/20000 : ℝ)) (hi := (17687/100000 : ℝ)) (c := (42409410999906098237/42410000000000000000 : ℝ)) (alpha := (32664149173/424100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (42409410999906098237/42410000000000000000 : ℝ)*(X 0 2+X 1 2)+(32664149173/424100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5999/1024 : ℝ)) (lo := (1841/20000 : ℝ)) (hi := (17687/100000 : ℝ)) (c := (42409410999906098237/42410000000000000000 : ℝ)) (alpha := (32664149173/424100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1065181103/2000000000 : ℝ)*X 1 0+(-1348354919/10000000000 : ℝ)*X 1 1+(2542413523/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s3_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-285936377/2500000000 : ℝ)*X 0 0+(5091367293/10000000000 : ℝ)*X 0 1+(5470873813/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s3_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2611157/5000000 : ℝ)*X 1 0+(-48115223/500000000 : ℝ)*X 1 1+(1367718419/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s3_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5222313827/10000000000 : ℝ)*X 2 0+(2735436861/5000000000 : ℝ)*X 2 1+(-962304639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s3_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((199603521/500000000 : ℝ)*X 0 0+(468278863/1000000000 : ℝ)*X 0 1+(1679663049/5000000000 : ℝ)*X 0 2+(199603521/500000000 : ℝ)*X 1 0+(468278863/1000000000 : ℝ)*X 1 1+(1679663049/5000000000 : ℝ)*X 1 2+(199603521/500000000 : ℝ)*X 2 0+(468278863/1000000000 : ℝ)*X 2 1+(1679663049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s3_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2989634928385192123813610517/1060250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170327973/50000000000000 : ℝ)*(base19) + (290725931/100000000000000 : ℝ)*(base23) + (17481293/50000000000000 : ℝ)*(lower1) + (34722799/100000000000000 : ℝ)*(upper3) + (16262801/50000000000000 : ℝ)*(lower4) + (36524397/50000000000000 : ℝ)*(upper5) + (1695296590258147/100000000000000 : ℝ)*(major0) + (1695296590258147/100000000000000 : ℝ)*(major1) + (1695296590258147/100000000000000 : ℝ)*(major2) + (1256389599/100000000000000 : ℝ)*(sp0) + (843199977519/32000000000 : ℝ)*(sp1) + (263499833270133/10000000000000 : ℝ)*(sp2) + (164687477438809/6250000000000 : ℝ)*(sp3) + (755593156777907/100000000000000 : ℝ)*(sp4) + (755593156777907/100000000000000 : ℝ)*(f.failure) + (843199977519/32000000000 : ℝ)*(f.sum) + (13324680017231/21205000000000000000000000000 : ℝ)*base65 + (9975701697570313161/4241000000000000000000000000000000 : ℝ)*base68 + (3770035020286313161/4241000000000000000000000000000000 : ℝ)*base70 + (11460529403810313161/4241000000000000000000000000000000 : ℝ)*base72 + (12495255668493/10602500000000000000000000000 : ℝ)*base73 + (9789707277705313161/4241000000000000000000000000000000 : ℝ)*base76 + (2053696141266686839/4241000000000000000000000000000000 : ℝ)*base77 + (15036377550083313161/4241000000000000000000000000000000 : ℝ)*base80 + (65072636170081/21205000000000000000000000000 : ℝ)*base81 + (5499033/2500000000000000000000 : ℝ)*base90 + (5499033/2500000000000000000000 : ℝ)*base92 + (5499033/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1765_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (56091581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1841/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1841/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8843/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1765_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1765_box_0 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-390030607/5000000000 : ℝ)*x 0 + (5409594873/10000000000 : ℝ)*x 1 + (1352398701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390030607/5000000000 : ℝ)^6015 ≤ (1155493497099/25000000000000 : ℝ)^4991 := by
    have hnat : (390030607 : ℕ)^6015*25000000000000^4991 ≤ 1155493497099^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390030607 5000000000 1155493497099 25000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409594873/10000000000 : ℝ)^6015 ≤ (47689013362247/100000000000000 : ℝ)^4991 := by
    have hnat : (5409594873 : ℕ)^6015*100000000000000^4991 ≤ 47689013362247^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409594873 10000000000 47689013362247 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352398701/2500000000 : ℝ)^6015 ≤ (2980563289323/6250000000000 : ℝ)^4991 := by
    have hnat : (1352398701 : ℕ)^6015*6250000000000^4991 ≤ 2980563289323^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352398701 2500000000 2980563289323 6250000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-390030607/5000000000 : ℝ), (5409594873/10000000000 : ℝ), (1352398701/2500000000 : ℝ)] ![(1155493497099/25000000000000 : ℝ), (47689013362247/100000000000000 : ℝ), (2980563289323/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-390030607/5000000000 : ℝ)|^6015 ≤ (1155493497099/25000000000000 : ℝ)^4991
        have hw : |(-390030607/5000000000 : ℝ)|=(390030607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409594873/10000000000 : ℝ)|^6015 ≤ (47689013362247/100000000000000 : ℝ)^4991
        have hw : |(5409594873/10000000000 : ℝ)|=(5409594873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352398701/2500000000 : ℝ)|^6015 ≤ (2980563289323/6250000000000 : ℝ)^4991
        have hw : |(1352398701/2500000000 : ℝ)|=(1352398701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_box_1 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192584161/10000000000 : ℝ)*x 0 + (-1090089621/10000000000 : ℝ)*x 1 + (2704797497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192584161/10000000000 : ℝ)^6015 ≤ (45393010237257/100000000000000 : ℝ)^4991 := by
    have hnat : (5192584161 : ℕ)^6015*100000000000000^4991 ≤ 45393010237257^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192584161 10000000000 45393010237257 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090089621/10000000000 : ℝ)^6015 ≤ (864746887219/12500000000000 : ℝ)^4991 := by
    have hnat : (1090089621 : ℕ)^6015*12500000000000^4991 ≤ 864746887219^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090089621 10000000000 864746887219 12500000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704797497/5000000000 : ℝ)^6015 ≤ (47689014647791/100000000000000 : ℝ)^4991 := by
    have hnat : (2704797497 : ℕ)^6015*100000000000000^4991 ≤ 47689014647791^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704797497 5000000000 47689014647791 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192584161/10000000000 : ℝ), (-1090089621/10000000000 : ℝ), (2704797497/5000000000 : ℝ)] ![(45393010237257/100000000000000 : ℝ), (864746887219/12500000000000 : ℝ), (47689014647791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192584161/10000000000 : ℝ)|^6015 ≤ (45393010237257/100000000000000 : ℝ)^4991
        have hw : |(5192584161/10000000000 : ℝ)|=(5192584161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1090089621/10000000000 : ℝ)|^6015 ≤ (864746887219/12500000000000 : ℝ)^4991
        have hw : |(-1090089621/10000000000 : ℝ)|=(1090089621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704797497/5000000000 : ℝ)|^6015 ≤ (47689014647791/100000000000000 : ℝ)^4991
        have hw : |(2704797497/5000000000 : ℝ)|=(2704797497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_box_2 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298145983/2500000000 : ℝ)*x 0 + (5409595113/10000000000 : ℝ)*x 1 + (-1090089771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298145983/2500000000 : ℝ)^6015 ≤ (45393007824637/100000000000000 : ℝ)^4991 := by
    have hnat : (1298145983 : ℕ)^6015*100000000000000^4991 ≤ 45393007824637^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298145983 2500000000 45393007824637 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409595113/10000000000 : ℝ)^6015 ≤ (47689015912087/100000000000000 : ℝ)^4991 := by
    have hnat : (5409595113 : ℕ)^6015*100000000000000^4991 ≤ 47689015912087^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409595113 10000000000 47689015912087 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090089771/10000000000 : ℝ)^6015 ≤ (6917976244997/100000000000000 : ℝ)^4991 := by
    have hnat : (1090089771 : ℕ)^6015*100000000000000^4991 ≤ 6917976244997^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090089771 10000000000 6917976244997 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298145983/2500000000 : ℝ), (5409595113/10000000000 : ℝ), (-1090089771/10000000000 : ℝ)] ![(45393007824637/100000000000000 : ℝ), (47689015912087/100000000000000 : ℝ), (6917976244997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298145983/2500000000 : ℝ)|^6015 ≤ (45393007824637/100000000000000 : ℝ)^4991
        have hw : |(1298145983/2500000000 : ℝ)|=(1298145983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409595113/10000000000 : ℝ)|^6015 ≤ (47689015912087/100000000000000 : ℝ)^4991
        have hw : |(5409595113/10000000000 : ℝ)|=(5409595113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1090089771/10000000000 : ℝ)|^6015 ≤ (6917976244997/100000000000000 : ℝ)^4991
        have hw : |(-1090089771/10000000000 : ℝ)|=(1090089771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_box_3 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1128774693/2500000000 : ℝ)*x 0 + (3766057161/10000000000 : ℝ)*x 1 + (753211233/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1128774693/2500000000 : ℝ)^6015 ≤ (38354433825077/100000000000000 : ℝ)^4991 := by
    have hnat : (1128774693 : ℕ)^6015*100000000000000^4991 ≤ 38354433825077^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128774693 2500000000 38354433825077 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3766057161/10000000000 : ℝ)^6015 ≤ (15411393995881/50000000000000 : ℝ)^4991 := by
    have hnat : (3766057161 : ℕ)^6015*50000000000000^4991 ≤ 15411393995881^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3766057161 10000000000 15411393995881 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (753211233/2000000000 : ℝ)^6015 ≤ (3082277816767/10000000000000 : ℝ)^4991 := by
    have hnat : (753211233 : ℕ)^6015*10000000000000^4991 ≤ 3082277816767^4991*2000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753211233 2000000000 3082277816767 10000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1128774693/2500000000 : ℝ), (3766057161/10000000000 : ℝ), (753211233/2000000000 : ℝ)] ![(38354433825077/100000000000000 : ℝ), (15411393995881/50000000000000 : ℝ), (3082277816767/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1128774693/2500000000 : ℝ)|^6015 ≤ (38354433825077/100000000000000 : ℝ)^4991
        have hw : |(1128774693/2500000000 : ℝ)|=(1128774693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3766057161/10000000000 : ℝ)|^6015 ≤ (15411393995881/50000000000000 : ℝ)^4991
        have hw : |(3766057161/10000000000 : ℝ)|=(3766057161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(753211233/2000000000 : ℝ)|^6015 ≤ (3082277816767/10000000000000 : ℝ)^4991
        have hw : |(753211233/2000000000 : ℝ)|=(753211233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_box_4 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-386372151/2500000000 : ℝ)*x 0 + (5129751291/10000000000 : ℝ)*x 1 + (5129751713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (386372151/2500000000 : ℝ)^6015 ≤ (5268136349553/50000000000000 : ℝ)^4991 := by
    have hnat : (386372151 : ℕ)^6015*50000000000000^4991 ≤ 5268136349553^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386372151 2500000000 5268136349553 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129751291/10000000000 : ℝ)^6015 ≤ (1789274456939/4000000000000 : ℝ)^4991 := by
    have hnat : (5129751291 : ℕ)^6015*4000000000000^4991 ≤ 1789274456939^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129751291 10000000000 1789274456939 4000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129751713/10000000000 : ℝ)^6015 ≤ (44731865858347/100000000000000 : ℝ)^4991 := by
    have hnat : (5129751713 : ℕ)^6015*100000000000000^4991 ≤ 44731865858347^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129751713 10000000000 44731865858347 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-386372151/2500000000 : ℝ), (5129751291/10000000000 : ℝ), (5129751713/10000000000 : ℝ)] ![(5268136349553/50000000000000 : ℝ), (1789274456939/4000000000000 : ℝ), (44731865858347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-386372151/2500000000 : ℝ)|^6015 ≤ (5268136349553/50000000000000 : ℝ)^4991
        have hw : |(-386372151/2500000000 : ℝ)|=(386372151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129751291/10000000000 : ℝ)|^6015 ≤ (1789274456939/4000000000000 : ℝ)^4991
        have hw : |(5129751291/10000000000 : ℝ)|=(5129751291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129751713/10000000000 : ℝ)|^6015 ≤ (44731865858347/100000000000000 : ℝ)^4991
        have hw : |(5129751713/10000000000 : ℝ)|=(5129751713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_box_5 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168086329/312500000 : ℝ)*x 0 + (-121784709/1000000000 : ℝ)*x 1 + (5129751577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168086329/312500000 : ℝ)^6015 ≤ (23680816046317/50000000000000 : ℝ)^4991 := by
    have hnat : (168086329 : ℕ)^6015*50000000000000^4991 ≤ 23680816046317^4991*312500000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168086329 312500000 23680816046317 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121784709/1000000000 : ℝ)^6015 ≤ (1581300693021/20000000000000 : ℝ)^4991 := by
    have hnat : (121784709 : ℕ)^6015*20000000000000^4991 ≤ 1581300693021^4991*1000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121784709 1000000000 1581300693021 20000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129751577/10000000000 : ℝ)^6015 ≤ (44731864429099/100000000000000 : ℝ)^4991 := by
    have hnat : (5129751577 : ℕ)^6015*100000000000000^4991 ≤ 44731864429099^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129751577 10000000000 44731864429099 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168086329/312500000 : ℝ), (-121784709/1000000000 : ℝ), (5129751577/10000000000 : ℝ)] ![(23680816046317/50000000000000 : ℝ), (1581300693021/20000000000000 : ℝ), (44731864429099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168086329/312500000 : ℝ)|^6015 ≤ (23680816046317/50000000000000 : ℝ)^4991
        have hw : |(168086329/312500000 : ℝ)|=(168086329/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-121784709/1000000000 : ℝ)|^6015 ≤ (1581300693021/20000000000000 : ℝ)^4991
        have hw : |(-121784709/1000000000 : ℝ)|=(121784709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129751577/10000000000 : ℝ)|^6015 ≤ (44731864429099/100000000000000 : ℝ)^4991
        have hw : |(5129751577/10000000000 : ℝ)|=(5129751577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_box_6 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378762843/10000000000 : ℝ)*x 0 + (1025950251/2000000000 : ℝ)*x 1 + (-243569419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378762843/10000000000 : ℝ)^6015 ≤ (47361635435377/100000000000000 : ℝ)^4991 := by
    have hnat : (5378762843 : ℕ)^6015*100000000000000^4991 ≤ 47361635435377^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378762843 10000000000 47361635435377 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025950251/2000000000 : ℝ)^6015 ≤ (5591482630643/12500000000000 : ℝ)^4991 := by
    have hnat : (1025950251 : ℕ)^6015*12500000000000^4991 ≤ 5591482630643^4991*2000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025950251 2000000000 5591482630643 12500000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (243569419/2000000000 : ℝ)^6015 ≤ (3953251752113/50000000000000 : ℝ)^4991 := by
    have hnat : (243569419 : ℕ)^6015*50000000000000^4991 ≤ 3953251752113^4991*2000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243569419 2000000000 3953251752113 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378762843/10000000000 : ℝ), (1025950251/2000000000 : ℝ), (-243569419/2000000000 : ℝ)] ![(47361635435377/100000000000000 : ℝ), (5591482630643/12500000000000 : ℝ), (3953251752113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378762843/10000000000 : ℝ)|^6015 ≤ (47361635435377/100000000000000 : ℝ)^4991
        have hw : |(5378762843/10000000000 : ℝ)|=(5378762843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1025950251/2000000000 : ℝ)|^6015 ≤ (5591482630643/12500000000000 : ℝ)^4991
        have hw : |(1025950251/2000000000 : ℝ)|=(1025950251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-243569419/2000000000 : ℝ)|^6015 ≤ (3953251752113/50000000000000 : ℝ)^4991
        have hw : |(-243569419/2000000000 : ℝ)|=(243569419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_box_7 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1713827113/5000000000 : ℝ)*x 0 + (269234069/625000000 : ℝ)*x 1 + (861549143/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1713827113/5000000000 : ℝ)^6015 ≤ (13758233248217/50000000000000 : ℝ)^4991 := by
    have hnat : (1713827113 : ℕ)^6015*50000000000000^4991 ≤ 13758233248217^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713827113 5000000000 13758233248217 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269234069/625000000 : ℝ)^6015 ≤ (36241763648693/100000000000000 : ℝ)^4991 := by
    have hnat : (269234069 : ℕ)^6015*100000000000000^4991 ≤ 36241763648693^4991*625000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269234069 625000000 36241763648693 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (861549143/2000000000 : ℝ)^6015 ≤ (36241769843797/100000000000000 : ℝ)^4991 := by
    have hnat : (861549143 : ℕ)^6015*100000000000000^4991 ≤ 36241769843797^4991*2000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861549143 2000000000 36241769843797 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1713827113/5000000000 : ℝ), (269234069/625000000 : ℝ), (861549143/2000000000 : ℝ)] ![(13758233248217/50000000000000 : ℝ), (36241763648693/100000000000000 : ℝ), (36241769843797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1713827113/5000000000 : ℝ)|^6015 ≤ (13758233248217/50000000000000 : ℝ)^4991
        have hw : |(1713827113/5000000000 : ℝ)|=(1713827113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269234069/625000000 : ℝ)|^6015 ≤ (36241763648693/100000000000000 : ℝ)^4991
        have hw : |(269234069/625000000 : ℝ)|=(269234069/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(861549143/2000000000 : ℝ)|^6015 ≤ (36241769843797/100000000000000 : ℝ)^4991
        have hw : |(861549143/2000000000 : ℝ)|=(861549143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_box_8 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-275740487/2000000000 : ℝ)*x 0 + (2457616517/5000000000 : ℝ)*x 1 + (5469971967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275740487/2000000000 : ℝ)^6015 ≤ (9181556522819/100000000000000 : ℝ)^4991 := by
    have hnat : (275740487 : ℕ)^6015*100000000000000^4991 ≤ 9181556522819^4991*2000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275740487 2000000000 9181556522819 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2457616517/5000000000 : ℝ)^6015 ≤ (42487231483163/100000000000000 : ℝ)^4991 := by
    have hnat : (2457616517 : ℕ)^6015*100000000000000^4991 ≤ 42487231483163^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2457616517 5000000000 42487231483163 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469971967/10000000000 : ℝ)^6015 ≤ (48331211980881/100000000000000 : ℝ)^4991 := by
    have hnat : (5469971967 : ℕ)^6015*100000000000000^4991 ≤ 48331211980881^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469971967 10000000000 48331211980881 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-275740487/2000000000 : ℝ), (2457616517/5000000000 : ℝ), (5469971967/10000000000 : ℝ)] ![(9181556522819/100000000000000 : ℝ), (42487231483163/100000000000000 : ℝ), (48331211980881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-275740487/2000000000 : ℝ)|^6015 ≤ (9181556522819/100000000000000 : ℝ)^4991
        have hw : |(-275740487/2000000000 : ℝ)|=(275740487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2457616517/5000000000 : ℝ)|^6015 ≤ (42487231483163/100000000000000 : ℝ)^4991
        have hw : |(2457616517/5000000000 : ℝ)|=(2457616517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469971967/10000000000 : ℝ)|^6015 ≤ (48331211980881/100000000000000 : ℝ)^4991
        have hw : |(5469971967/10000000000 : ℝ)|=(5469971967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_box_9 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2576246907/5000000000 : ℝ)*x 0 + (-530612229/5000000000 : ℝ)*x 1 + (2734986131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2576246907/5000000000 : ℝ)^6015 ≤ (224854876027/500000000000 : ℝ)^4991 := by
    have hnat : (2576246907 : ℕ)^6015*500000000000^4991 ≤ 224854876027^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576246907 5000000000 224854876027 500000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530612229/5000000000 : ℝ)^6015 ≤ (83722620753/1250000000000 : ℝ)^4991 := by
    have hnat : (530612229 : ℕ)^6015*1250000000000^4991 ≤ 83722620753^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530612229 5000000000 83722620753 1250000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734986131/5000000000 : ℝ)^6015 ≤ (9666243024441/20000000000000 : ℝ)^4991 := by
    have hnat : (2734986131 : ℕ)^6015*20000000000000^4991 ≤ 9666243024441^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734986131 5000000000 9666243024441 20000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2576246907/5000000000 : ℝ), (-530612229/5000000000 : ℝ), (2734986131/5000000000 : ℝ)] ![(224854876027/500000000000 : ℝ), (83722620753/1250000000000 : ℝ), (9666243024441/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2576246907/5000000000 : ℝ)|^6015 ≤ (224854876027/500000000000 : ℝ)^4991
        have hw : |(2576246907/5000000000 : ℝ)|=(2576246907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-530612229/5000000000 : ℝ)|^6015 ≤ (83722620753/1250000000000 : ℝ)^4991
        have hw : |(-530612229/5000000000 : ℝ)|=(530612229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734986131/5000000000 : ℝ)|^6015 ≤ (9666243024441/20000000000000 : ℝ)^4991
        have hw : |(2734986131/5000000000 : ℝ)|=(2734986131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_box_10 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (644061743/1250000000 : ℝ)*x 0 + (27349861/50000000 : ℝ)*x 1 + (-265306091/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (644061743/1250000000 : ℝ)^6015 ≤ (22485488286417/50000000000000 : ℝ)^4991 := by
    have hnat : (644061743 : ℕ)^6015*50000000000000^4991 ≤ 22485488286417^4991*1250000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644061743 1250000000 22485488286417 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27349861/50000000 : ℝ)^6015 ≤ (24165607230997/50000000000000 : ℝ)^4991 := by
    have hnat : (27349861 : ℕ)^6015*50000000000000^4991 ≤ 24165607230997^4991*50000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27349861 50000000 24165607230997 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265306091/2500000000 : ℝ)^6015 ≤ (6697808945247/100000000000000 : ℝ)^4991 := by
    have hnat : (265306091 : ℕ)^6015*100000000000000^4991 ≤ 6697808945247^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265306091 2500000000 6697808945247 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(644061743/1250000000 : ℝ), (27349861/50000000 : ℝ), (-265306091/2500000000 : ℝ)] ![(22485488286417/50000000000000 : ℝ), (24165607230997/50000000000000 : ℝ), (6697808945247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(644061743/1250000000 : ℝ)|^6015 ≤ (22485488286417/50000000000000 : ℝ)^4991
        have hw : |(644061743/1250000000 : ℝ)|=(644061743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27349861/50000000 : ℝ)|^6015 ≤ (24165607230997/50000000000000 : ℝ)^4991
        have hw : |(27349861/50000000 : ℝ)|=(27349861/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-265306091/2500000000 : ℝ)|^6015 ≤ (6697808945247/100000000000000 : ℝ)^4991
        have hw : |(-265306091/2500000000 : ℝ)|=(265306091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_box_11 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (592410593/1250000000 : ℝ)*x 0 + (3648750449/10000000000 : ℝ)*x 1 + (145950007/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (592410593/1250000000 : ℝ)^6015 ≤ (40661090675009/100000000000000 : ℝ)^4991 := by
    have hnat : (592410593 : ℕ)^6015*100000000000000^4991 ≤ 40661090675009^4991*1250000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592410593 1250000000 40661090675009 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3648750449/10000000000 : ℝ)^6015 ≤ (29669456000979/100000000000000 : ℝ)^4991 := by
    have hnat : (3648750449 : ℕ)^6015*100000000000000^4991 ≤ 29669456000979^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3648750449 10000000000 29669456000979 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (145950007/400000000 : ℝ)^6015 ≤ (29669453315857/100000000000000 : ℝ)^4991 := by
    have hnat : (145950007 : ℕ)^6015*100000000000000^4991 ≤ 29669453315857^4991*400000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145950007 400000000 29669453315857 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(592410593/1250000000 : ℝ), (3648750449/10000000000 : ℝ), (145950007/400000000 : ℝ)] ![(40661090675009/100000000000000 : ℝ), (29669456000979/100000000000000 : ℝ), (29669453315857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(592410593/1250000000 : ℝ)|^6015 ≤ (40661090675009/100000000000000 : ℝ)^4991
        have hw : |(592410593/1250000000 : ℝ)|=(592410593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3648750449/10000000000 : ℝ)|^6015 ≤ (29669456000979/100000000000000 : ℝ)^4991
        have hw : |(3648750449/10000000000 : ℝ)|=(3648750449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(145950007/400000000 : ℝ)|^6015 ≤ (29669453315857/100000000000000 : ℝ)^4991
        have hw : |(145950007/400000000 : ℝ)|=(145950007/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_box_12 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-233093477/2500000000 : ℝ)*x 0 + (5612091767/10000000000 : ℝ)*x 1 + (2550079497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (233093477/2500000000 : ℝ)^6015 ≤ (573035636433/10000000000000 : ℝ)^4991 := by
    have hnat : (233093477 : ℕ)^6015*10000000000000^4991 ≤ 573035636433^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233093477 2500000000 573035636433 10000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5612091767/10000000000 : ℝ)^6015 ≤ (24924294285569/50000000000000 : ℝ)^4991 := by
    have hnat : (5612091767 : ℕ)^6015*50000000000000^4991 ≤ 24924294285569^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5612091767 10000000000 24924294285569 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2550079497/5000000000 : ℝ)^6015 ≤ (8884211009327/20000000000000 : ℝ)^4991 := by
    have hnat : (2550079497 : ℕ)^6015*20000000000000^4991 ≤ 8884211009327^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2550079497 5000000000 8884211009327 20000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-233093477/2500000000 : ℝ), (5612091767/10000000000 : ℝ), (2550079497/5000000000 : ℝ)] ![(573035636433/10000000000000 : ℝ), (24924294285569/50000000000000 : ℝ), (8884211009327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-233093477/2500000000 : ℝ)|^6015 ≤ (573035636433/10000000000000 : ℝ)^4991
        have hw : |(-233093477/2500000000 : ℝ)|=(233093477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5612091767/10000000000 : ℝ)|^6015 ≤ (24924294285569/50000000000000 : ℝ)^4991
        have hw : |(5612091767/10000000000 : ℝ)|=(5612091767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2550079497/5000000000 : ℝ)|^6015 ≤ (8884211009327/20000000000000 : ℝ)^4991
        have hw : |(2550079497/5000000000 : ℝ)|=(2550079497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_box_13 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539852619/1000000000 : ℝ)*x 0 + (-1230742349/10000000000 : ℝ)*x 1 + (79689979/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539852619/1000000000 : ℝ)^6015 ≤ (4757144068993/10000000000000 : ℝ)^4991 := by
    have hnat : (539852619 : ℕ)^6015*10000000000000^4991 ≤ 4757144068993^4991*1000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539852619 1000000000 4757144068993 10000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1230742349/10000000000 : ℝ)^6015 ≤ (1601501559557/20000000000000 : ℝ)^4991 := by
    have hnat : (1230742349 : ℕ)^6015*20000000000000^4991 ≤ 1601501559557^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230742349 10000000000 1601501559557 20000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79689979/156250000 : ℝ)^6015 ≤ (44421051498747/100000000000000 : ℝ)^4991 := by
    have hnat : (79689979 : ℕ)^6015*100000000000000^4991 ≤ 44421051498747^4991*156250000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79689979 156250000 44421051498747 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539852619/1000000000 : ℝ), (-1230742349/10000000000 : ℝ), (79689979/156250000 : ℝ)] ![(4757144068993/10000000000000 : ℝ), (1601501559557/20000000000000 : ℝ), (44421051498747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539852619/1000000000 : ℝ)|^6015 ≤ (4757144068993/10000000000000 : ℝ)^4991
        have hw : |(539852619/1000000000 : ℝ)|=(539852619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1230742349/10000000000 : ℝ)|^6015 ≤ (1601501559557/20000000000000 : ℝ)^4991
        have hw : |(-1230742349/10000000000 : ℝ)|=(1230742349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79689979/156250000 : ℝ)|^6015 ≤ (44421051498747/100000000000000 : ℝ)^4991
        have hw : |(79689979/156250000 : ℝ)|=(79689979/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_box_14 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2699262993/5000000000 : ℝ)*x 0 + (2550078981/5000000000 : ℝ)*x 1 + (-615371777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2699262993/5000000000 : ℝ)^6015 ≤ (47571438523477/100000000000000 : ℝ)^4991 := by
    have hnat : (2699262993 : ℕ)^6015*100000000000000^4991 ≤ 47571438523477^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699262993 5000000000 47571438523477 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2550078981/5000000000 : ℝ)^6015 ≤ (4442104421403/10000000000000 : ℝ)^4991 := by
    have hnat : (2550078981 : ℕ)^6015*10000000000000^4991 ≤ 4442104421403^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2550078981 5000000000 4442104421403 10000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (615371777/5000000000 : ℝ)^6015 ≤ (8007517246339/100000000000000 : ℝ)^4991 := by
    have hnat : (615371777 : ℕ)^6015*100000000000000^4991 ≤ 8007517246339^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615371777 5000000000 8007517246339 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2699262993/5000000000 : ℝ), (2550078981/5000000000 : ℝ), (-615371777/5000000000 : ℝ)] ![(47571438523477/100000000000000 : ℝ), (4442104421403/10000000000000 : ℝ), (8007517246339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2699262993/5000000000 : ℝ)|^6015 ≤ (47571438523477/100000000000000 : ℝ)^4991
        have hw : |(2699262993/5000000000 : ℝ)|=(2699262993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2550078981/5000000000 : ℝ)|^6015 ≤ (4442104421403/10000000000000 : ℝ)^4991
        have hw : |(2550078981/5000000000 : ℝ)|=(2550078981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-615371777/5000000000 : ℝ)|^6015 ≤ (8007517246339/100000000000000 : ℝ)^4991
        have hw : |(-615371777/5000000000 : ℝ)|=(615371777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_box_15 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3307479413/10000000000 : ℝ)*x 0 + (136399769/312500000 : ℝ)*x 1 + (436479741/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3307479413/10000000000 : ℝ)^6015 ≤ (26358015796271/100000000000000 : ℝ)^4991 := by
    have hnat : (3307479413 : ℕ)^6015*100000000000000^4991 ≤ 26358015796271^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3307479413 10000000000 26358015796271 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136399769/312500000 : ℝ)^6015 ≤ (36820967687929/100000000000000 : ℝ)^4991 := by
    have hnat : (136399769 : ℕ)^6015*100000000000000^4991 ≤ 36820967687929^4991*312500000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136399769 312500000 36820967687929 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436479741/1000000000 : ℝ)^6015 ≤ (9205254127097/25000000000000 : ℝ)^4991 := by
    have hnat : (436479741 : ℕ)^6015*25000000000000^4991 ≤ 9205254127097^4991*1000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436479741 1000000000 9205254127097 25000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3307479413/10000000000 : ℝ), (136399769/312500000 : ℝ), (436479741/1000000000 : ℝ)] ![(26358015796271/100000000000000 : ℝ), (36820967687929/100000000000000 : ℝ), (9205254127097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3307479413/10000000000 : ℝ)|^6015 ≤ (26358015796271/100000000000000 : ℝ)^4991
        have hw : |(3307479413/10000000000 : ℝ)|=(3307479413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136399769/312500000 : ℝ)|^6015 ≤ (36820967687929/100000000000000 : ℝ)^4991
        have hw : |(136399769/312500000 : ℝ)|=(136399769/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(436479741/1000000000 : ℝ)|^6015 ≤ (9205254127097/25000000000000 : ℝ)^4991
        have hw : |(436479741/1000000000 : ℝ)|=(436479741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1765_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (56091581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8843/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1841/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6921/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58843/100000 : ℝ) ∧ (16479/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (93169/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8843/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1841/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8843/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1841/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8843/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1841/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8843/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1841/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8843/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1841/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8843/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1841/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1841/20000 : ℝ) ^ (5999/1024 : ℝ) ≤ (85278314228661/100000000000000000000 : ℝ) := by
    have hpowers : (1841/20000 : ℝ)^5999 ≤ (85278314228661/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1841 : ℕ)^5999*100000000000000000000^1024 ≤ 85278314228661^1024*20000^5999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1841 20000 85278314228661 100000000000000000000 5999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1841/20000 : ℝ)) (X := (85278314228661/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8843/50000 : ℝ) ^ (5999/1024 : ℝ) ≤ (3911240716739669/100000000000000000000 : ℝ) := by
    have hpowers : (8843/50000 : ℝ)^5999 ≤ (3911240716739669/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8843 : ℕ)^5999*100000000000000000000^1024 ≤ 3911240716739669^1024*50000^5999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8843 50000 3911240716739669 100000000000000000000 5999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8843/50000 : ℝ)) (X := (3911240716739669/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000085278314228661/50000000000000000000 : ℝ) ≤ (10000002911316287/10000000000000000 : ℝ) ^ (5999/1024 : ℝ) := by
    have hpowers : (50000085278314228661/50000000000000000000 : ℝ)^1024 ≤ (10000002911316287/10000000000000000 : ℝ)^5999 := by
      have hnat : (50000085278314228661 : ℕ)^1024*10000000000000000^5999 ≤ 10000002911316287^5999*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000085278314228661 50000000000000000000 10000002911316287 10000000000000000 1024 5999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002911316287/10000000000000000 : ℝ)) (X := (50000085278314228661/50000000000000000000 : ℝ)) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10000399651903096833/10000000000000000000 : ℝ) ≤ (1250008527187179/1250000000000000 : ℝ) ^ (5999/1024 : ℝ) := by
    have hpowers : (10000399651903096833/10000000000000000000 : ℝ)^1024 ≤ (1250008527187179/1250000000000000 : ℝ)^5999 := by
      have hnat : (10000399651903096833 : ℕ)^1024*1250000000000000^5999 ≤ 1250008527187179^5999*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000399651903096833 10000000000000000000 1250008527187179 1250000000000000 1024 5999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250008527187179/1250000000000000 : ℝ)) (X := (10000399651903096833/10000000000000000000 : ℝ)) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50003911240716739669/50000000000000000000 : ℝ) ≤ (10000133523678577/10000000000000000 : ℝ) ^ (5999/1024 : ℝ) := by
    have hpowers : (50003911240716739669/50000000000000000000 : ℝ)^1024 ≤ (10000133523678577/10000000000000000 : ℝ)^5999 := by
      have hnat : (50003911240716739669 : ℕ)^1024*10000000000000000^5999 ≤ 10000133523678577^5999*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003911240716739669 50000000000000000000 10000133523678577 10000000000000000 1024 5999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000133523678577/10000000000000000 : ℝ)) (X := (50003911240716739669/50000000000000000000 : ℝ)) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(85278314228661/100000000000000000000 : ℝ) ≤ ((84808822404078550597/84810000000000000000 : ℝ)+2*(13061236229/169620000000000 : ℝ)*(1841/20000 : ℝ))^(5999/1024 : ℝ) := by
    rw [show (84808822404078550597/84810000000000000000 : ℝ)+2*(13061236229/169620000000000 : ℝ)*(1841/20000 : ℝ)=(10000002911316287/10000000000000000 : ℝ) by norm_num, show 1+2*(85278314228661/100000000000000000000 : ℝ)=(50000085278314228661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3911240716739669/100000000000000000000 : ℝ)+(85278314228661/100000000000000000000 : ℝ) ≤ ((84808822404078550597/84810000000000000000 : ℝ)+(13061236229/169620000000000 : ℝ)*((8843/50000 : ℝ)+(1841/20000 : ℝ)))^(5999/1024 : ℝ) := by
    rw [show (84808822404078550597/84810000000000000000 : ℝ)+(13061236229/169620000000000 : ℝ)*((8843/50000 : ℝ)+(1841/20000 : ℝ))=(1250008527187179/1250000000000000 : ℝ) by norm_num, show 1+(3911240716739669/100000000000000000000 : ℝ)+(85278314228661/100000000000000000000 : ℝ)=(10000399651903096833/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3911240716739669/100000000000000000000 : ℝ) ≤ ((84808822404078550597/84810000000000000000 : ℝ)+2*(13061236229/169620000000000 : ℝ)*(8843/50000 : ℝ))^(5999/1024 : ℝ) := by
    rw [show (84808822404078550597/84810000000000000000 : ℝ)+2*(13061236229/169620000000000 : ℝ)*(8843/50000 : ℝ)=(10000133523678577/10000000000000000 : ℝ) by norm_num, show 1+2*(3911240716739669/100000000000000000000 : ℝ)=(50003911240716739669/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (84808822404078550597/84810000000000000000 : ℝ)*(X 1 0+X 2 0)+(13061236229/169620000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5999/1024 : ℝ)) (lo := (1841/20000 : ℝ)) (hi := (8843/50000 : ℝ)) (c := (84808822404078550597/84810000000000000000 : ℝ)) (alpha := (13061236229/169620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (84808822404078550597/84810000000000000000 : ℝ)*(X 0 1+X 2 1)+(13061236229/169620000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5999/1024 : ℝ)) (lo := (1841/20000 : ℝ)) (hi := (8843/50000 : ℝ)) (c := (84808822404078550597/84810000000000000000 : ℝ)) (alpha := (13061236229/169620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (84808822404078550597/84810000000000000000 : ℝ)*(X 0 2+X 1 2)+(13061236229/169620000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5999/1024 : ℝ)) (lo := (1841/20000 : ℝ)) (hi := (8843/50000 : ℝ)) (c := (84808822404078550597/84810000000000000000 : ℝ)) (alpha := (13061236229/169620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-390030607/5000000000 : ℝ)*X 0 0+(5409594873/10000000000 : ℝ)*X 0 1+(1352398701/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5192584161/10000000000 : ℝ)*X 1 0+(-1090089621/10000000000 : ℝ)*X 1 1+(2704797497/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1298145983/2500000000 : ℝ)*X 2 0+(5409595113/10000000000 : ℝ)*X 2 1+(-1090089771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1128774693/2500000000 : ℝ)*X 0 0+(3766057161/10000000000 : ℝ)*X 0 1+(753211233/2000000000 : ℝ)*X 0 2+(1128774693/2500000000 : ℝ)*X 1 0+(3766057161/10000000000 : ℝ)*X 1 1+(753211233/2000000000 : ℝ)*X 1 2+(1128774693/2500000000 : ℝ)*X 2 0+(3766057161/10000000000 : ℝ)*X 2 1+(753211233/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-386372151/2500000000 : ℝ)*X 0 0+(5129751291/10000000000 : ℝ)*X 0 1+(5129751713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((168086329/312500000 : ℝ)*X 1 0+(-121784709/1000000000 : ℝ)*X 1 1+(5129751577/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5378762843/10000000000 : ℝ)*X 2 0+(1025950251/2000000000 : ℝ)*X 2 1+(-243569419/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1713827113/5000000000 : ℝ)*X 0 0+(269234069/625000000 : ℝ)*X 0 1+(861549143/2000000000 : ℝ)*X 0 2+(1713827113/5000000000 : ℝ)*X 1 0+(269234069/625000000 : ℝ)*X 1 1+(861549143/2000000000 : ℝ)*X 1 2+(1713827113/5000000000 : ℝ)*X 2 0+(269234069/625000000 : ℝ)*X 2 1+(861549143/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-275740487/2000000000 : ℝ)*X 0 0+(2457616517/5000000000 : ℝ)*X 0 1+(5469971967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2576246907/5000000000 : ℝ)*X 1 0+(-530612229/5000000000 : ℝ)*X 1 1+(2734986131/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((644061743/1250000000 : ℝ)*X 2 0+(27349861/50000000 : ℝ)*X 2 1+(-265306091/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((592410593/1250000000 : ℝ)*X 0 0+(3648750449/10000000000 : ℝ)*X 0 1+(145950007/400000000 : ℝ)*X 0 2+(592410593/1250000000 : ℝ)*X 1 0+(3648750449/10000000000 : ℝ)*X 1 1+(145950007/400000000 : ℝ)*X 1 2+(592410593/1250000000 : ℝ)*X 2 0+(3648750449/10000000000 : ℝ)*X 2 1+(145950007/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-233093477/2500000000 : ℝ)*X 0 0+(5612091767/10000000000 : ℝ)*X 0 1+(2550079497/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((539852619/1000000000 : ℝ)*X 1 0+(-1230742349/10000000000 : ℝ)*X 1 1+(79689979/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2699262993/5000000000 : ℝ)*X 2 0+(2550078981/5000000000 : ℝ)*X 2 1+(-615371777/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3307479413/10000000000 : ℝ)*X 0 0+(136399769/312500000 : ℝ)*X 0 1+(436479741/1000000000 : ℝ)*X 0 2+(3307479413/10000000000 : ℝ)*X 1 0+(136399769/312500000 : ℝ)*X 1 1+(436479741/1000000000 : ℝ)*X 1 2+(3307479413/10000000000 : ℝ)*X 2 0+(136399769/312500000 : ℝ)*X 2 1+(436479741/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6921/10000 : ℝ) ≤ (-97824626030307252422310927/141350000000000000000000000 : ℝ) := by norm_num
    linear_combination (1361033/50000000000000 : ℝ)*(lower2) + (21947157/50000000000000 : ℝ)*(lower3) + (10168141/50000000000000 : ℝ)*(upper5) + (1100866957242741/100000000000000 : ℝ)*(major0) + (1100866957242741/100000000000000 : ℝ)*(major1) + (1100866957242741/100000000000000 : ℝ)*(major2) + (997459337/50000000000000 : ℝ)*(sp2) + (69091783/50000000000000 : ℝ)*(sp3) + (867073188530819/50000000000000 : ℝ)*(sp4) + (173413951396663/10000000000000 : ℝ)*(sp5) + (1734144988506391/100000000000000 : ℝ)*(sp6) + (490655918222983/100000000000000 : ℝ)*(sp7) + (606363427/100000000000000 : ℝ)*(sp12) + (1867364609/25000000000000 : ℝ)*(sp13) + (490656056406549/100000000000000 : ℝ)*(f.failure) + (867073491712533/50000000000000 : ℝ)*(f.sum) + (7177647531171/2827000000000000000000000000 : ℝ)*base66 + (11407091677699655459/2827000000000000000000000000000000 : ℝ)*base67 + (3609295475965655459/2827000000000000000000000000000000 : ℝ)*base69 + (13886968011055344541/2827000000000000000000000000000000 : ℝ)*base72 + (722742888081/113080000000000000000000000 : ℝ)*base73 + (9060468145472344541/2827000000000000000000000000000000 : ℝ)*base76 + (3396243253982344541/2827000000000000000000000000000000 : ℝ)*base78 + (3726328588799655459/2827000000000000000000000000000000 : ℝ)*base79 + (2325281246009/2827000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (12836031/2500000000000000000000 : ℝ)*base90 + (12836031/2500000000000000000000 : ℝ)*base92 + (12836031/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58843/100000 : ℝ) ≤ (415892202012009835875695353424607/706750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14017459/50000000000000 : ℝ)*(lower0) + (11966323/100000000000000 : ℝ)*(upper1) + (27908337/100000000000000 : ℝ)*(upper2) + (24008381/50000000000000 : ℝ)*(upper3) + (5858457/100000000000000 : ℝ)*(lower5) + (616678383108669/50000000000000 : ℝ)*(major0) + (616678383108669/50000000000000 : ℝ)*(major1) + (616678383108669/50000000000000 : ℝ)*(major2) + (379478313256319/20000000000000 : ℝ)*(sp0) + (379478313256319/20000000000000 : ℝ)*(sp1) + (1897390731496927/100000000000000 : ℝ)*(sp2) + (549704121697287/100000000000000 : ℝ)*(sp3) + (208696167/25000000000000 : ℝ)*(sp6) + (1300437727/50000000000000 : ℝ)*(sp11) + (549706722572741/100000000000000 : ℝ)*(f.failure) + (379478313256319/20000000000000 : ℝ)*(f.sum) + (44008837821/176687500000000000000000000 : ℝ)*base66 + (1374409706800775131/1413500000000000000000000000000000 : ℝ)*base67 + (10087085612091275131/1413500000000000000000000000000000 : ℝ)*base69 + (8938530709266275131/1413500000000000000000000000000000 : ℝ)*base71 + (4889511214083/706750000000000000000000000 : ℝ)*base74 + (646330949083724869/1413500000000000000000000000000000 : ℝ)*base76 + (6494234006610775131/1413500000000000000000000000000000 : ℝ)*base77 + (4018394795955224869/1413500000000000000000000000000000 : ℝ)*base80 + (1659754492889/1413500000000000000000000000 : ℝ)*base81 + (19806479/2500000000000000000000 : ℝ)*base90 + (19806479/2500000000000000000000 : ℝ)*base92 + (19806479/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (16479/20000 : ℝ) ≤ (1164687060564901980607333535549057/1413500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2374761/100000000000000 : ℝ)*(upper0) + (1646301/50000000000000 : ℝ)*(upper1) + (14135807/50000000000000 : ℝ)*(upper4) + (1177453216696819/100000000000000 : ℝ)*(major0) + (1177453216696819/100000000000000 : ℝ)*(major1) + (1177453216696819/100000000000000 : ℝ)*(major2) + (4699998391/50000000000000 : ℝ)*(sp1) + (10606657239/100000000000000 : ℝ)*(sp2) + (1299409143/50000000000000 : ℝ)*(sp3) + (8342613/100000000000000 : ℝ)*(sp4) + (1802650101350747/100000000000000 : ℝ)*(sp8) + (901320354848289/50000000000000 : ℝ)*(sp9) + (1802639503036121/100000000000000 : ℝ)*(sp10) + (524787929325687/100000000000000 : ℝ)*(sp11) + (262395264071987/50000000000000 : ℝ)*(f.failure) + (22533126371167/1250000000000 : ℝ)*(f.sum) + (11444944212947/2120250000000000000000000000 : ℝ)*base65 + (24628073760785950943/8481000000000000000000000000000000 : ℝ)*base67 + (14523262971602950943/8481000000000000000000000000000000 : ℝ)*base69 + (45983799784241950943/8481000000000000000000000000000000 : ℝ)*base71 + (499086487963/2120250000000000000000000000 : ℝ)*base74 + (14036278306203049057/8481000000000000000000000000000000 : ℝ)*base76 + (21367726306223950943/8481000000000000000000000000000000 : ℝ)*base77 + (3734675241120049057/8481000000000000000000000000000000 : ℝ)*base80 + (5826356553511/8481000000000000000000000000 : ℝ)*base82 + (11141447/1250000000000000000000 : ℝ)*base89 + (11141447/1250000000000000000000 : ℝ)*base91 + (11141447/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-93169/100000 : ℝ) ≤ (-263382921191461871957993588319943/282700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4100489/12500000000000 : ℝ)*(upper3) + (302041851/100000000000000 : ℝ)*(lower4) + (233207419/100000000000000 : ℝ)*(upper5) + (247356630491273/20000000000000 : ℝ)*(major0) + (247356630491273/20000000000000 : ℝ)*(major1) + (247356630491273/20000000000000 : ℝ)*(major2) + (5496810177/100000000000000 : ℝ)*(sp4) + (9723185589/25000000000000 : ℝ)*(sp5) + (171561292379/100000000000000 : ℝ)*(sp6) + (4726755181/12500000000000 : ℝ)*(sp7) + (122086411923961/6250000000000 : ℝ)*(sp12) + (488337298712799/25000000000000 : ℝ)*(sp13) + (976608263150587/50000000000000 : ℝ)*(sp14) + (551196047799763/100000000000000 : ℝ)*(sp15) + (551233861841211/100000000000000 : ℝ)*(f.failure) + (1953388087593553/100000000000000 : ℝ)*(f.sum) + (5709565796527/4240500000000000000000000000 : ℝ)*base65 + (4470870853456939981/1696200000000000000000000000000000 : ℝ)*base67 + (6141628362316939981/1696200000000000000000000000000000 : ℝ)*base69 + (14785427127940939981/1696200000000000000000000000000000 : ℝ)*base71 + (45903243492427/8481000000000000000000000000 : ℝ)*base74 + (15736385437180339981/1696200000000000000000000000000000 : ℝ)*base75 + (6040630960882339981/1696200000000000000000000000000000 : ℝ)*base77 + (5818537146366139981/1696200000000000000000000000000000 : ℝ)*base79 + (3810489487921/2120250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (29055409/2500000000000000000000 : ℝ)*base90 + (29055409/2500000000000000000000 : ℝ)*base92 + (29055409/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1765_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (56091581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8843/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1841/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6921/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58843/100000 : ℝ) else (16479/20000 : ℝ) ≤ X j i ∧ X j i ≤ (93169/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1765_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1765_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (56091581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1841/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6921/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58843/100000 : ℝ) else (16479/20000 : ℝ) ≤ X j i ∧ X j i ≤ (93169/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1765_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1765_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (56091581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1841/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6921/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58843/100000 : ℝ) else (16479/20000 : ℝ) ≤ X j i ∧ X j i ≤ (93169/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1765_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

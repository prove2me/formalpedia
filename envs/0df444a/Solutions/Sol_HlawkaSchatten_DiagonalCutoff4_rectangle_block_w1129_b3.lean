-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1129_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:26:00.948553+00:00
-- url     : https://prove2.me/submissions/4990109e-d9a8-40c2-9ad2-2097097ea468

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
theorem support_rectangle_w1129_box_0 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-127862073/625000000 : ℝ)*x 0 + (5376496049/10000000000 : ℝ)*x 1 + (2688248043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127862073/625000000 : ℝ)^4161 ≤ (12187333995503/100000000000000 : ℝ)^3137 := by
    have hnat : (127862073 : ℕ)^4161*100000000000000^3137 ≤ 12187333995503^3137*625000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127862073 625000000 12187333995503 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376496049/10000000000 : ℝ)^4161 ≤ (43906332795967/100000000000000 : ℝ)^3137 := by
    have hnat : (5376496049 : ℕ)^4161*100000000000000^3137 ≤ 43906332795967^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376496049 10000000000 43906332795967 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688248043/5000000000 : ℝ)^4161 ≤ (43906333196753/100000000000000 : ℝ)^3137 := by
    have hnat : (2688248043 : ℕ)^4161*100000000000000^3137 ≤ 43906333196753^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688248043 5000000000 43906333196753 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-127862073/625000000 : ℝ), (5376496049/10000000000 : ℝ), (2688248043/5000000000 : ℝ)] ![(12187333995503/100000000000000 : ℝ), (43906332795967/100000000000000 : ℝ), (43906333196753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-127862073/625000000 : ℝ)|^4161 ≤ (12187333995503/100000000000000 : ℝ)^3137
        have hw : |(-127862073/625000000 : ℝ)|=(127862073/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376496049/10000000000 : ℝ)|^4161 ≤ (43906332795967/100000000000000 : ℝ)^3137
        have hw : |(5376496049/10000000000 : ℝ)|=(5376496049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688248043/5000000000 : ℝ)|^4161 ≤ (43906333196753/100000000000000 : ℝ)^3137
        have hw : |(2688248043/5000000000 : ℝ)|=(2688248043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_box_1 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295861337/10000000000 : ℝ)*x 0 + (-2155115459/10000000000 : ℝ)*x 1 + (5376495877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295861337/10000000000 : ℝ)^4161 ≤ (10758759518001/25000000000000 : ℝ)^3137 := by
    have hnat : (5295861337 : ℕ)^4161*25000000000000^3137 ≤ 10758759518001^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295861337 10000000000 10758759518001 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2155115459/10000000000 : ℝ)^4161 ≤ (13058630977079/100000000000000 : ℝ)^3137 := by
    have hnat : (2155115459 : ℕ)^4161*100000000000000^3137 ≤ 13058630977079^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155115459 10000000000 13058630977079 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376495877/10000000000 : ℝ)^4161 ≤ (43906330932853/100000000000000 : ℝ)^3137 := by
    have hnat : (5376495877 : ℕ)^4161*100000000000000^3137 ≤ 43906330932853^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376495877 10000000000 43906330932853 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295861337/10000000000 : ℝ), (-2155115459/10000000000 : ℝ), (5376495877/10000000000 : ℝ)] ![(10758759518001/25000000000000 : ℝ), (13058630977079/100000000000000 : ℝ), (43906330932853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295861337/10000000000 : ℝ)|^4161 ≤ (10758759518001/25000000000000 : ℝ)^3137
        have hw : |(5295861337/10000000000 : ℝ)|=(5295861337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2155115459/10000000000 : ℝ)|^4161 ≤ (13058630977079/100000000000000 : ℝ)^3137
        have hw : |(-2155115459/10000000000 : ℝ)|=(2155115459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376495877/10000000000 : ℝ)|^4161 ≤ (43906330932853/100000000000000 : ℝ)^3137
        have hw : |(5376495877/10000000000 : ℝ)|=(5376495877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_box_2 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295861061/10000000000 : ℝ)*x 0 + (5376496207/10000000000 : ℝ)*x 1 + (-269389423/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295861061/10000000000 : ℝ)^4161 ≤ (21517517548533/50000000000000 : ℝ)^3137 := by
    have hnat : (5295861061 : ℕ)^4161*50000000000000^3137 ≤ 21517517548533^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295861061 10000000000 21517517548533 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376496207/10000000000 : ℝ)^4161 ≤ (5488291813429/12500000000000 : ℝ)^3137 := by
    have hnat : (5376496207 : ℕ)^4161*12500000000000^3137 ≤ 5488291813429^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376496207 10000000000 5488291813429 12500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269389423/1250000000 : ℝ)^4161 ≤ (6529315187141/50000000000000 : ℝ)^3137 := by
    have hnat : (269389423 : ℕ)^4161*50000000000000^3137 ≤ 6529315187141^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269389423 1250000000 6529315187141 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295861061/10000000000 : ℝ), (5376496207/10000000000 : ℝ), (-269389423/1250000000 : ℝ)] ![(21517517548533/50000000000000 : ℝ), (5488291813429/12500000000000 : ℝ), (6529315187141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295861061/10000000000 : ℝ)|^4161 ≤ (21517517548533/50000000000000 : ℝ)^3137
        have hw : |(5295861061/10000000000 : ℝ)|=(5295861061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376496207/10000000000 : ℝ)|^4161 ≤ (5488291813429/12500000000000 : ℝ)^3137
        have hw : |(5376496207/10000000000 : ℝ)|=(5376496207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-269389423/1250000000 : ℝ)|^4161 ≤ (6529315187141/50000000000000 : ℝ)^3137
        have hw : |(-269389423/1250000000 : ℝ)|=(269389423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_box_3 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4474197587/10000000000 : ℝ)*x 0 + (431478359/1000000000 : ℝ)*x 1 + (2157391709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4474197587/10000000000 : ℝ)^4161 ≤ (34411160833107/100000000000000 : ℝ)^3137 := by
    have hnat : (4474197587 : ℕ)^4161*100000000000000^3137 ≤ 34411160833107^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474197587 10000000000 34411160833107 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431478359/1000000000 : ℝ)^4161 ≤ (3279442044317/10000000000000 : ℝ)^3137 := by
    have hnat : (431478359 : ℕ)^4161*10000000000000^3137 ≤ 3279442044317^3137*1000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431478359 1000000000 3279442044317 10000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2157391709/5000000000 : ℝ)^4161 ≤ (8198604677289/25000000000000 : ℝ)^3137 := by
    have hnat : (2157391709 : ℕ)^4161*25000000000000^3137 ≤ 8198604677289^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157391709 5000000000 8198604677289 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4474197587/10000000000 : ℝ), (431478359/1000000000 : ℝ), (2157391709/5000000000 : ℝ)] ![(34411160833107/100000000000000 : ℝ), (3279442044317/10000000000000 : ℝ), (8198604677289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4474197587/10000000000 : ℝ)|^4161 ≤ (34411160833107/100000000000000 : ℝ)^3137
        have hw : |(4474197587/10000000000 : ℝ)|=(4474197587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(431478359/1000000000 : ℝ)|^4161 ≤ (3279442044317/10000000000000 : ℝ)^3137
        have hw : |(431478359/1000000000 : ℝ)|=(431478359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2157391709/5000000000 : ℝ)|^4161 ≤ (8198604677289/25000000000000 : ℝ)^3137
        have hw : |(2157391709/5000000000 : ℝ)|=(2157391709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_box_4 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-575458449/2500000000 : ℝ)*x 0 + (1320242829/2500000000 : ℝ)*x 1 + (264048611/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (575458449/2500000000 : ℝ)^4161 ≤ (890672414187/6250000000000 : ℝ)^3137 := by
    have hnat : (575458449 : ℕ)^4161*6250000000000^3137 ≤ 890672414187^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575458449 2500000000 890672414187 6250000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320242829/2500000000 : ℝ)^4161 ≤ (21437307906829/50000000000000 : ℝ)^3137 := by
    have hnat : (1320242829 : ℕ)^4161*50000000000000^3137 ≤ 21437307906829^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320242829 2500000000 21437307906829 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264048611/500000000 : ℝ)^4161 ≤ (21437312774353/50000000000000 : ℝ)^3137 := by
    have hnat : (264048611 : ℕ)^4161*50000000000000^3137 ≤ 21437312774353^3137*500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264048611 500000000 21437312774353 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-575458449/2500000000 : ℝ), (1320242829/2500000000 : ℝ), (264048611/500000000 : ℝ)] ![(890672414187/6250000000000 : ℝ), (21437307906829/50000000000000 : ℝ), (21437312774353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-575458449/2500000000 : ℝ)|^4161 ≤ (890672414187/6250000000000 : ℝ)^3137
        have hw : |(-575458449/2500000000 : ℝ)|=(575458449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320242829/2500000000 : ℝ)|^4161 ≤ (21437307906829/50000000000000 : ℝ)^3137
        have hw : |(1320242829/2500000000 : ℝ)|=(1320242829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264048611/500000000 : ℝ)|^4161 ≤ (21437312774353/50000000000000 : ℝ)^3137
        have hw : |(264048611/500000000 : ℝ)|=(264048611/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_box_5 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681684457/5000000000 : ℝ)*x 0 + (-438530571/2000000000 : ℝ)*x 1 + (211238867/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681684457/5000000000 : ℝ)^4161 ≤ (4376419558559/10000000000000 : ℝ)^3137 := by
    have hnat : (2681684457 : ℕ)^4161*10000000000000^3137 ≤ 4376419558559^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681684457 5000000000 4376419558559 10000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438530571/2000000000 : ℝ)^4161 ≤ (13361184723443/100000000000000 : ℝ)^3137 := by
    have hnat : (438530571 : ℕ)^4161*100000000000000^3137 ≤ 13361184723443^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438530571 2000000000 13361184723443 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211238867/400000000 : ℝ)^4161 ≤ (21437309839839/50000000000000 : ℝ)^3137 := by
    have hnat : (211238867 : ℕ)^4161*50000000000000^3137 ≤ 21437309839839^3137*400000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211238867 400000000 21437309839839 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681684457/5000000000 : ℝ), (-438530571/2000000000 : ℝ), (211238867/400000000 : ℝ)] ![(4376419558559/10000000000000 : ℝ), (13361184723443/100000000000000 : ℝ), (21437309839839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681684457/5000000000 : ℝ)|^4161 ≤ (4376419558559/10000000000000 : ℝ)^3137
        have hw : |(2681684457/5000000000 : ℝ)|=(2681684457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438530571/2000000000 : ℝ)|^4161 ≤ (13361184723443/100000000000000 : ℝ)^3137
        have hw : |(-438530571/2000000000 : ℝ)|=(438530571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211238867/400000000 : ℝ)|^4161 ≤ (21437309839839/50000000000000 : ℝ)^3137
        have hw : |(211238867/400000000 : ℝ)|=(211238867/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_box_6 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363369021/10000000000 : ℝ)*x 0 + (2640485801/5000000000 : ℝ)*x 1 + (-2192652809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363369021/10000000000 : ℝ)^4161 ≤ (2735262296481/6250000000000 : ℝ)^3137 := by
    have hnat : (5363369021 : ℕ)^4161*6250000000000^3137 ≤ 2735262296481^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363369021 10000000000 2735262296481 6250000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640485801/5000000000 : ℝ)^4161 ≤ (2679663680847/6250000000000 : ℝ)^3137 := by
    have hnat : (2640485801 : ℕ)^4161*6250000000000^3137 ≤ 2679663680847^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640485801 5000000000 2679663680847 6250000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2192652809/10000000000 : ℝ)^4161 ≤ (6680592175819/50000000000000 : ℝ)^3137 := by
    have hnat : (2192652809 : ℕ)^4161*50000000000000^3137 ≤ 6680592175819^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192652809 10000000000 6680592175819 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363369021/10000000000 : ℝ), (2640485801/5000000000 : ℝ), (-2192652809/10000000000 : ℝ)] ![(2735262296481/6250000000000 : ℝ), (2679663680847/6250000000000 : ℝ), (6680592175819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363369021/10000000000 : ℝ)|^4161 ≤ (2735262296481/6250000000000 : ℝ)^3137
        have hw : |(5363369021/10000000000 : ℝ)|=(5363369021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640485801/5000000000 : ℝ)|^4161 ≤ (2679663680847/6250000000000 : ℝ)^3137
        have hw : |(2640485801/5000000000 : ℝ)|=(2640485801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2192652809/10000000000 : ℝ)|^4161 ≤ (6680592175819/50000000000000 : ℝ)^3137
        have hw : |(-2192652809/10000000000 : ℝ)|=(2192652809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_box_7 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2129233847/5000000000 : ℝ)*x 0 + (27641421/62500000 : ℝ)*x 1 + (884525533/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129233847/5000000000 : ℝ)^4161 ≤ (32227886063889/100000000000000 : ℝ)^3137 := by
    have hnat : (2129233847 : ℕ)^4161*100000000000000^3137 ≤ 32227886063889^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129233847 5000000000 32227886063889 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27641421/62500000 : ℝ)^4161 ≤ (16943027705123/50000000000000 : ℝ)^3137 := by
    have hnat : (27641421 : ℕ)^4161*50000000000000^3137 ≤ 16943027705123^3137*62500000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27641421 62500000 16943027705123 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (884525533/2000000000 : ℝ)^4161 ≤ (16943029254987/50000000000000 : ℝ)^3137 := by
    have hnat : (884525533 : ℕ)^4161*50000000000000^3137 ≤ 16943029254987^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884525533 2000000000 16943029254987 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2129233847/5000000000 : ℝ), (27641421/62500000 : ℝ), (884525533/2000000000 : ℝ)] ![(32227886063889/100000000000000 : ℝ), (16943027705123/50000000000000 : ℝ), (16943029254987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2129233847/5000000000 : ℝ)|^4161 ≤ (32227886063889/100000000000000 : ℝ)^3137
        have hw : |(2129233847/5000000000 : ℝ)|=(2129233847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27641421/62500000 : ℝ)|^4161 ≤ (16943027705123/50000000000000 : ℝ)^3137
        have hw : |(27641421/62500000 : ℝ)|=(27641421/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(884525533/2000000000 : ℝ)|^4161 ≤ (16943029254987/50000000000000 : ℝ)^3137
        have hw : |(884525533/2000000000 : ℝ)|=(884525533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_box_8 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-562076649/2500000000 : ℝ)*x 0 + (5216030981/10000000000 : ℝ)*x 1 + (538610407/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (562076649/2500000000 : ℝ)^4161 ≤ (2762574422627/20000000000000 : ℝ)^3137 := by
    have hnat : (562076649 : ℕ)^4161*20000000000000^3137 ≤ 2762574422627^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562076649 2500000000 2762574422627 20000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216030981/10000000000 : ℝ)^4161 ≤ (2108834504291/5000000000000 : ℝ)^3137 := by
    have hnat : (5216030981 : ℕ)^4161*5000000000000^3137 ≤ 2108834504291^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216030981 10000000000 2108834504291 5000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538610407/1000000000 : ℝ)^4161 ≤ (44010437792863/100000000000000 : ℝ)^3137 := by
    have hnat : (538610407 : ℕ)^4161*100000000000000^3137 ≤ 44010437792863^3137*1000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538610407 1000000000 44010437792863 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-562076649/2500000000 : ℝ), (5216030981/10000000000 : ℝ), (538610407/1000000000 : ℝ)] ![(2762574422627/20000000000000 : ℝ), (2108834504291/5000000000000 : ℝ), (44010437792863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-562076649/2500000000 : ℝ)|^4161 ≤ (2762574422627/20000000000000 : ℝ)^3137
        have hw : |(-562076649/2500000000 : ℝ)|=(562076649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216030981/10000000000 : ℝ)|^4161 ≤ (2108834504291/5000000000000 : ℝ)^3137
        have hw : |(5216030981/10000000000 : ℝ)|=(5216030981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538610407/1000000000 : ℝ)|^4161 ≤ (44010437792863/100000000000000 : ℝ)^3137
        have hw : |(538610407/1000000000 : ℝ)|=(538610407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_box_9 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644533831/5000000000 : ℝ)*x 0 + (-537817627/2500000000 : ℝ)*x 1 + (5386103999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644533831/5000000000 : ℝ)^4161 ≤ (21480913009591/50000000000000 : ℝ)^3137 := by
    have hnat : (2644533831 : ℕ)^4161*50000000000000^3137 ≤ 21480913009591^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644533831 5000000000 21480913009591 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537817627/2500000000 : ℝ)^4161 ≤ (6513868472873/50000000000000 : ℝ)^3137 := by
    have hnat : (537817627 : ℕ)^4161*50000000000000^3137 ≤ 6513868472873^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537817627 2500000000 6513868472873 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386103999/10000000000 : ℝ)^4161 ≤ (44010437023339/100000000000000 : ℝ)^3137 := by
    have hnat : (5386103999 : ℕ)^4161*100000000000000^3137 ≤ 44010437023339^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386103999 10000000000 44010437023339 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644533831/5000000000 : ℝ), (-537817627/2500000000 : ℝ), (5386103999/10000000000 : ℝ)] ![(21480913009591/50000000000000 : ℝ), (6513868472873/50000000000000 : ℝ), (44010437023339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644533831/5000000000 : ℝ)|^4161 ≤ (21480913009591/50000000000000 : ℝ)^3137
        have hw : |(2644533831/5000000000 : ℝ)|=(2644533831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-537817627/2500000000 : ℝ)|^4161 ≤ (6513868472873/50000000000000 : ℝ)^3137
        have hw : |(-537817627/2500000000 : ℝ)|=(537817627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386103999/10000000000 : ℝ)|^4161 ≤ (44010437023339/100000000000000 : ℝ)^3137
        have hw : |(5386103999/10000000000 : ℝ)|=(5386103999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_box_10 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057813543/2000000000 : ℝ)*x 0 + (5386104139/10000000000 : ℝ)*x 1 + (-2151270247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057813543/2000000000 : ℝ)^4161 ≤ (42961826590217/100000000000000 : ℝ)^3137 := by
    have hnat : (1057813543 : ℕ)^4161*100000000000000^3137 ≤ 42961826590217^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057813543 2000000000 42961826590217 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386104139/10000000000 : ℝ)^4161 ≤ (44010438540711/100000000000000 : ℝ)^3137 := by
    have hnat : (5386104139 : ℕ)^4161*100000000000000^3137 ≤ 44010438540711^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386104139 10000000000 44010438540711 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2151270247/10000000000 : ℝ)^4161 ≤ (13027734849233/100000000000000 : ℝ)^3137 := by
    have hnat : (2151270247 : ℕ)^4161*100000000000000^3137 ≤ 13027734849233^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151270247 10000000000 13027734849233 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057813543/2000000000 : ℝ), (5386104139/10000000000 : ℝ), (-2151270247/10000000000 : ℝ)] ![(42961826590217/100000000000000 : ℝ), (44010438540711/100000000000000 : ℝ), (13027734849233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057813543/2000000000 : ℝ)|^4161 ≤ (42961826590217/100000000000000 : ℝ)^3137
        have hw : |(1057813543/2000000000 : ℝ)|=(1057813543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386104139/10000000000 : ℝ)|^4161 ≤ (44010438540711/100000000000000 : ℝ)^3137
        have hw : |(5386104139/10000000000 : ℝ)|=(5386104139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2151270247/10000000000 : ℝ)|^4161 ≤ (13027734849233/100000000000000 : ℝ)^3137
        have hw : |(-2151270247/10000000000 : ℝ)|=(2151270247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_box_11 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (44956227/100000000 : ℝ)*x 0 + (4303930251/10000000000 : ℝ)*x 1 + (2151965281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44956227/100000000 : ℝ)^4161 ≤ (34629901440633/100000000000000 : ℝ)^3137 := by
    have hnat : (44956227 : ℕ)^4161*100000000000000^3137 ≤ 34629901440633^3137*100000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44956227 100000000 34629901440633 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4303930251/10000000000 : ℝ)^4161 ≤ (16342523854027/50000000000000 : ℝ)^3137 := by
    have hnat : (4303930251 : ℕ)^4161*50000000000000^3137 ≤ 16342523854027^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303930251 10000000000 16342523854027 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2151965281/5000000000 : ℝ)^4161 ≤ (2042815677551/6250000000000 : ℝ)^3137 := by
    have hnat : (2151965281 : ℕ)^4161*6250000000000^3137 ≤ 2042815677551^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151965281 5000000000 2042815677551 6250000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44956227/100000000 : ℝ), (4303930251/10000000000 : ℝ), (2151965281/5000000000 : ℝ)] ![(34629901440633/100000000000000 : ℝ), (16342523854027/50000000000000 : ℝ), (2042815677551/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44956227/100000000 : ℝ)|^4161 ≤ (34629901440633/100000000000000 : ℝ)^3137
        have hw : |(44956227/100000000 : ℝ)|=(44956227/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4303930251/10000000000 : ℝ)|^4161 ≤ (16342523854027/50000000000000 : ℝ)^3137
        have hw : |(4303930251/10000000000 : ℝ)|=(4303930251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2151965281/5000000000 : ℝ)|^4161 ≤ (2042815677551/6250000000000 : ℝ)^3137
        have hw : |(2151965281/5000000000 : ℝ)|=(2151965281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_box_12 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2099646989/10000000000 : ℝ)*x 0 + (680018711/1250000000 : ℝ)*x 1 + (1318234799/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099646989/10000000000 : ℝ)^4161 ≤ (6307348919413/50000000000000 : ℝ)^3137 := by
    have hnat : (2099646989 : ℕ)^4161*50000000000000^3137 ≤ 6307348919413^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099646989 10000000000 6307348919413 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680018711/1250000000 : ℝ)^4161 ≤ (5574645200373/12500000000000 : ℝ)^3137 := by
    have hnat : (680018711 : ℕ)^4161*12500000000000^3137 ≤ 5574645200373^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680018711 1250000000 5574645200373 12500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318234799/2500000000 : ℝ)^4161 ≤ (21394070268641/50000000000000 : ℝ)^3137 := by
    have hnat : (1318234799 : ℕ)^4161*50000000000000^3137 ≤ 21394070268641^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318234799 2500000000 21394070268641 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2099646989/10000000000 : ℝ), (680018711/1250000000 : ℝ), (1318234799/2500000000 : ℝ)] ![(6307348919413/50000000000000 : ℝ), (5574645200373/12500000000000 : ℝ), (21394070268641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2099646989/10000000000 : ℝ)|^4161 ≤ (6307348919413/50000000000000 : ℝ)^3137
        have hw : |(-2099646989/10000000000 : ℝ)|=(2099646989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680018711/1250000000 : ℝ)|^4161 ≤ (5574645200373/12500000000000 : ℝ)^3137
        have hw : |(680018711/1250000000 : ℝ)|=(680018711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318234799/2500000000 : ℝ)|^4161 ≤ (21394070268641/50000000000000 : ℝ)^3137
        have hw : |(1318234799/2500000000 : ℝ)|=(1318234799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_box_13 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369043129/10000000000 : ℝ)*x 0 + (-17154307/78125000 : ℝ)*x 1 + (5272939613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369043129/10000000000 : ℝ)^4161 ≤ (21912810297441/50000000000000 : ℝ)^3137 := by
    have hnat : (5369043129 : ℕ)^4161*50000000000000^3137 ≤ 21912810297441^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369043129 10000000000 21912810297441 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17154307/78125000 : ℝ)^4161 ≤ (3346558593019/25000000000000 : ℝ)^3137 := by
    have hnat : (17154307 : ℕ)^4161*25000000000000^3137 ≤ 3346558593019^3137*78125000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17154307 78125000 3346558593019 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272939613/10000000000 : ℝ)^4161 ≤ (8557629005133/20000000000000 : ℝ)^3137 := by
    have hnat : (5272939613 : ℕ)^4161*20000000000000^3137 ≤ 8557629005133^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272939613 10000000000 8557629005133 20000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369043129/10000000000 : ℝ), (-17154307/78125000 : ℝ), (5272939613/10000000000 : ℝ)] ![(21912810297441/50000000000000 : ℝ), (3346558593019/25000000000000 : ℝ), (8557629005133/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369043129/10000000000 : ℝ)|^4161 ≤ (21912810297441/50000000000000 : ℝ)^3137
        have hw : |(5369043129/10000000000 : ℝ)|=(5369043129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17154307/78125000 : ℝ)|^4161 ≤ (3346558593019/25000000000000 : ℝ)^3137
        have hw : |(-17154307/78125000 : ℝ)|=(17154307/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272939613/10000000000 : ℝ)|^4161 ≤ (8557629005133/20000000000000 : ℝ)^3137
        have hw : |(5272939613/10000000000 : ℝ)|=(5272939613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_box_14 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134226081/250000000 : ℝ)*x 0 + (210917569/400000000 : ℝ)*x 1 + (-1097875831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134226081/250000000 : ℝ)^4161 ≤ (5478202724587/12500000000000 : ℝ)^3137 := by
    have hnat : (134226081 : ℕ)^4161*12500000000000^3137 ≤ 5478202724587^3137*250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134226081 250000000 5478202724587 12500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210917569/400000000 : ℝ)^4161 ≤ (2674258803089/6250000000000 : ℝ)^3137 := by
    have hnat : (210917569 : ℕ)^4161*6250000000000^3137 ≤ 2674258803089^3137*400000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210917569 400000000 2674258803089 6250000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097875831/5000000000 : ℝ)^4161 ≤ (13386237331721/100000000000000 : ℝ)^3137 := by
    have hnat : (1097875831 : ℕ)^4161*100000000000000^3137 ≤ 13386237331721^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097875831 5000000000 13386237331721 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134226081/250000000 : ℝ), (210917569/400000000 : ℝ), (-1097875831/5000000000 : ℝ)] ![(5478202724587/12500000000000 : ℝ), (2674258803089/6250000000000 : ℝ), (13386237331721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134226081/250000000 : ℝ)|^4161 ≤ (5478202724587/12500000000000 : ℝ)^3137
        have hw : |(134226081/250000000 : ℝ)|=(134226081/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210917569/400000000 : ℝ)|^4161 ≤ (2674258803089/6250000000000 : ℝ)^3137
        have hw : |(210917569/400000000 : ℝ)|=(210917569/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1097875831/5000000000 : ℝ)|^4161 ≤ (13386237331721/100000000000000 : ℝ)^3137
        have hw : |(-1097875831/5000000000 : ℝ)|=(1097875831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_box_15 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2120047393/5000000000 : ℝ)*x 0 + (4431691479/10000000000 : ℝ)*x 1 + (4431692147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120047393/5000000000 : ℝ)^4161 ≤ (32043582668359/100000000000000 : ℝ)^3137 := by
    have hnat : (2120047393 : ℕ)^4161*100000000000000^3137 ≤ 32043582668359^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120047393 5000000000 32043582668359 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4431691479/10000000000 : ℝ)^4161 ≤ (16989102631547/50000000000000 : ℝ)^3137 := by
    have hnat : (4431691479 : ℕ)^4161*50000000000000^3137 ≤ 16989102631547^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4431691479 10000000000 16989102631547 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4431692147/10000000000 : ℝ)^4161 ≤ (33978212056547/100000000000000 : ℝ)^3137 := by
    have hnat : (4431692147 : ℕ)^4161*100000000000000^3137 ≤ 33978212056547^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4431692147 10000000000 33978212056547 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120047393/5000000000 : ℝ), (4431691479/10000000000 : ℝ), (4431692147/10000000000 : ℝ)] ![(32043582668359/100000000000000 : ℝ), (16989102631547/50000000000000 : ℝ), (33978212056547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120047393/5000000000 : ℝ)|^4161 ≤ (32043582668359/100000000000000 : ℝ)^3137
        have hw : |(2120047393/5000000000 : ℝ)|=(2120047393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4431691479/10000000000 : ℝ)|^4161 ≤ (16989102631547/50000000000000 : ℝ)^3137
        have hw : |(4431691479/10000000000 : ℝ)|=(4431691479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4431692147/10000000000 : ℝ)|^4161 ≤ (33978212056547/100000000000000 : ℝ)^3137
        have hw : |(4431692147/10000000000 : ℝ)|=(4431692147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1129_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6223/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7411/12500 : ℝ) ∧ (9971/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16619/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14041/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14041/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14041/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14041/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14041/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14041/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11337/100000 : ℝ) ^ (8321/2048 : ℝ) ≤ (1800309042704839/12500000000000000000 : ℝ) := by
    have hpowers : (11337/100000 : ℝ)^8321 ≤ (1800309042704839/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11337 : ℕ)^8321*12500000000000000000^2048 ≤ 1800309042704839^2048*100000^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11337 100000 1800309042704839 12500000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11337/100000 : ℝ)) (X := (1800309042704839/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14041/100000 : ℝ) ^ (8321/2048 : ℝ) ≤ (343469537507031/1000000000000000000 : ℝ) := by
    have hpowers : (14041/100000 : ℝ)^8321 ≤ (343469537507031/1000000000000000000 : ℝ)^2048 := by
      have hnat : (14041 : ℕ)^8321*1000000000000000000^2048 ≤ 343469537507031^2048*100000^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14041 100000 343469537507031 1000000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14041/100000 : ℝ)) (X := (343469537507031/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251800309042704839/6250000000000000000 : ℝ) ≤ (10000708882617153/10000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (6251800309042704839/6250000000000000000 : ℝ)^2048 ≤ (10000708882617153/10000000000000000 : ℝ)^8321 := by
      have hnat : (6251800309042704839 : ℕ)^2048*10000000000000000^8321 ≤ 10000708882617153^8321*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251800309042704839 6250000000000000000 10000708882617153 10000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000708882617153/10000000000000000 : ℝ)) (X := (6251800309042704839/6250000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012187356523085453/25000000000000000000 : ℝ) ≤ (5000599810623579/5000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (25012187356523085453/25000000000000000000 : ℝ)^2048 ≤ (5000599810623579/5000000000000000 : ℝ)^8321 := by
      have hnat : (25012187356523085453 : ℕ)^2048*5000000000000000^8321 ≤ 5000599810623579^8321*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012187356523085453 25000000000000000000 5000599810623579 5000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000599810623579/5000000000000000 : ℝ)) (X := (25012187356523085453/25000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (500343469537507031/500000000000000000 : ℝ) ≤ (10001690359877163/10000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (500343469537507031/500000000000000000 : ℝ)^2048 ≤ (10001690359877163/10000000000000000 : ℝ)^8321 := by
      have hnat : (500343469537507031 : ℕ)^2048*10000000000000000^8321 ≤ 10001690359877163^8321*500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500343469537507031 500000000000000000 10001690359877163 10000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001690359877163/10000000000000000 : ℝ)) (X := (500343469537507031/500000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1800309042704839/12500000000000000000 : ℝ) ≤ ((1039645761957694167/1040000000000000000 : ℝ)+2*(7549825077/4160000000000 : ℝ)*(11337/100000 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (1039645761957694167/1040000000000000000 : ℝ)+2*(7549825077/4160000000000 : ℝ)*(11337/100000 : ℝ)=(10000708882617153/10000000000000000 : ℝ) by norm_num, show 1+2*(1800309042704839/12500000000000000000 : ℝ)=(6251800309042704839/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(343469537507031/1000000000000000000 : ℝ)+(1800309042704839/12500000000000000000 : ℝ) ≤ ((1039645761957694167/1040000000000000000 : ℝ)+(7549825077/4160000000000 : ℝ)*((14041/100000 : ℝ)+(11337/100000 : ℝ)))^(8321/2048 : ℝ) := by
    rw [show (1039645761957694167/1040000000000000000 : ℝ)+(7549825077/4160000000000 : ℝ)*((14041/100000 : ℝ)+(11337/100000 : ℝ))=(5000599810623579/5000000000000000 : ℝ) by norm_num, show 1+(343469537507031/1000000000000000000 : ℝ)+(1800309042704839/12500000000000000000 : ℝ)=(25012187356523085453/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(343469537507031/1000000000000000000 : ℝ) ≤ ((1039645761957694167/1040000000000000000 : ℝ)+2*(7549825077/4160000000000 : ℝ)*(14041/100000 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (1039645761957694167/1040000000000000000 : ℝ)+2*(7549825077/4160000000000 : ℝ)*(14041/100000 : ℝ)=(10001690359877163/10000000000000000 : ℝ) by norm_num, show 1+2*(343469537507031/1000000000000000000 : ℝ)=(500343469537507031/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1039645761957694167/1040000000000000000 : ℝ)*(X 1 0+X 2 0)+(7549825077/4160000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (14041/100000 : ℝ)) (c := (1039645761957694167/1040000000000000000 : ℝ)) (alpha := (7549825077/4160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1039645761957694167/1040000000000000000 : ℝ)*(X 0 1+X 2 1)+(7549825077/4160000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (14041/100000 : ℝ)) (c := (1039645761957694167/1040000000000000000 : ℝ)) (alpha := (7549825077/4160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1039645761957694167/1040000000000000000 : ℝ)*(X 0 2+X 1 2)+(7549825077/4160000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (14041/100000 : ℝ)) (c := (1039645761957694167/1040000000000000000 : ℝ)) (alpha := (7549825077/4160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-127862073/625000000 : ℝ)*X 0 0+(5376496049/10000000000 : ℝ)*X 0 1+(2688248043/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295861337/10000000000 : ℝ)*X 1 0+(-2155115459/10000000000 : ℝ)*X 1 1+(5376495877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295861061/10000000000 : ℝ)*X 2 0+(5376496207/10000000000 : ℝ)*X 2 1+(-269389423/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4474197587/10000000000 : ℝ)*X 0 0+(431478359/1000000000 : ℝ)*X 0 1+(2157391709/5000000000 : ℝ)*X 0 2+(4474197587/10000000000 : ℝ)*X 1 0+(431478359/1000000000 : ℝ)*X 1 1+(2157391709/5000000000 : ℝ)*X 1 2+(4474197587/10000000000 : ℝ)*X 2 0+(431478359/1000000000 : ℝ)*X 2 1+(2157391709/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-575458449/2500000000 : ℝ)*X 0 0+(1320242829/2500000000 : ℝ)*X 0 1+(264048611/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681684457/5000000000 : ℝ)*X 1 0+(-438530571/2000000000 : ℝ)*X 1 1+(211238867/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363369021/10000000000 : ℝ)*X 2 0+(2640485801/5000000000 : ℝ)*X 2 1+(-2192652809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2129233847/5000000000 : ℝ)*X 0 0+(27641421/62500000 : ℝ)*X 0 1+(884525533/2000000000 : ℝ)*X 0 2+(2129233847/5000000000 : ℝ)*X 1 0+(27641421/62500000 : ℝ)*X 1 1+(884525533/2000000000 : ℝ)*X 1 2+(2129233847/5000000000 : ℝ)*X 2 0+(27641421/62500000 : ℝ)*X 2 1+(884525533/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-562076649/2500000000 : ℝ)*X 0 0+(5216030981/10000000000 : ℝ)*X 0 1+(538610407/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644533831/5000000000 : ℝ)*X 1 0+(-537817627/2500000000 : ℝ)*X 1 1+(5386103999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1057813543/2000000000 : ℝ)*X 2 0+(5386104139/10000000000 : ℝ)*X 2 1+(-2151270247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((44956227/100000000 : ℝ)*X 0 0+(4303930251/10000000000 : ℝ)*X 0 1+(2151965281/5000000000 : ℝ)*X 0 2+(44956227/100000000 : ℝ)*X 1 0+(4303930251/10000000000 : ℝ)*X 1 1+(2151965281/5000000000 : ℝ)*X 1 2+(44956227/100000000 : ℝ)*X 2 0+(4303930251/10000000000 : ℝ)*X 2 1+(2151965281/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2099646989/10000000000 : ℝ)*X 0 0+(680018711/1250000000 : ℝ)*X 0 1+(1318234799/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369043129/10000000000 : ℝ)*X 1 0+(-17154307/78125000 : ℝ)*X 1 1+(5272939613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((134226081/250000000 : ℝ)*X 2 0+(210917569/400000000 : ℝ)*X 2 1+(-1097875831/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2120047393/5000000000 : ℝ)*X 0 0+(4431691479/10000000000 : ℝ)*X 0 1+(4431692147/10000000000 : ℝ)*X 0 2+(2120047393/5000000000 : ℝ)*X 1 0+(4431691479/10000000000 : ℝ)*X 1 1+(4431692147/10000000000 : ℝ)*X 1 2+(2120047393/5000000000 : ℝ)*X 2 0+(4431691479/10000000000 : ℝ)*X 2 1+(4431692147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6223/10000 : ℝ) ≤ (-4044765526116379340721189285621/6500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (139346479/100000000000000 : ℝ)*(lower3) + (3450109/20000000000000 : ℝ)*(lower4) + (209/4000000000 : ℝ)*(upper5) + (977384598678121/25000000000000 : ℝ)*(major0) + (977384598678121/25000000000000 : ℝ)*(major1) + (977384598678121/25000000000000 : ℝ)*(major2) + (6609421009/50000000000000 : ℝ)*(sp1) + (24047537007/100000000000000 : ℝ)*(sp2) + (5219815049336403/100000000000000 : ℝ)*(sp4) + (5219825312046827/100000000000000 : ℝ)*(sp5) + (2609907241675919/50000000000000 : ℝ)*(sp6) + (523981577417473/20000000000000 : ℝ)*(sp7) + (23481552443/100000000000000 : ℝ)*(sp12) + (72758762171/100000000000000 : ℝ)*(sp15) + (40937197591399/1562500000000 : ℝ)*(f.failure) + (1043967706177769/20000000000000 : ℝ)*(f.sum) + (11862742667/10400000000000000000000000 : ℝ)*base66 + (73340676005470207/26000000000000000000000000000000 : ℝ)*base67 + (10411899628529793/26000000000000000000000000000000 : ℝ)*base70 + (85532876311470207/26000000000000000000000000000000 : ℝ)*base71 + (154326042293/52000000000000000000000000 : ℝ)*base73 + (123487982773470207/26000000000000000000000000000000 : ℝ)*base75 + (38238848205470207/26000000000000000000000000000000 : ℝ)*base77 + (113369423387470207/26000000000000000000000000000000 : ℝ)*base79 + (144989688253/52000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (11639/1250000000000000000 : ℝ)*base89 + (11639/1250000000000000000 : ℝ)*base91 + (11639/1250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (7411/12500 : ℝ) ≤ (24665009623950422365973817363/41600000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216167/12500000000000 : ℝ)*(lower0) + (9868003/20000000000000 : ℝ)*(upper1) + (31225841/100000000000000 : ℝ)*(upper2) + (9618391/50000000000000 : ℝ)*(upper3) + (6357545150737/160000000000 : ℝ)*(major0) + (6357545150737/160000000000 : ℝ)*(major1) + (6357545150737/160000000000 : ℝ)*(major2) + (526434620947537/10000000000000 : ℝ)*(sp0) + (2632131514090459/50000000000000 : ℝ)*(sp1) + (2632168841577751/50000000000000 : ℝ)*(sp2) + (1331408586274197/50000000000000 : ℝ)*(sp3) + (2131579967/25000000000000 : ℝ)*(sp6) + (1106722777/25000000000000 : ℝ)*(sp7) + (20795323613/25000000000000 : ℝ)*(sp9) + (2662821599439503/100000000000000 : ℝ)*(f.failure) + (526434620947537/10000000000000 : ℝ)*(f.sum) + (251426656913/41600000000000000000000000 : ℝ)*base65 + (519446374893079/166400000000000000000000000000 : ℝ)*base67 + (1313448458656279/166400000000000000000000000000 : ℝ)*base69 + (1209243206253079/166400000000000000000000000000 : ℝ)*base71 + (118911879829/208000000000000000000000000 : ℝ)*base73 + (1740699292806679/166400000000000000000000000000 : ℝ)*base75 + (1647351399789079/166400000000000000000000000000 : ℝ)*base77 + (80052276754921/166400000000000000000000000000 : ℝ)*base80 + (456174484469/208000000000000000000000000 : ℝ)*base81 + (540783/80000000000000000000 : ℝ)*base89 + (540783/80000000000000000000 : ℝ)*base91 + (540783/80000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (9971/12500 : ℝ) ≤ (2592549459532656514715208840711/3250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93603123/100000000000000 : ℝ)*(upper0) + (53999859/50000000000000 : ℝ)*(lower3) + (438567/400000000000 : ℝ)*(upper4) + (555177718058211/12500000000000 : ℝ)*(major0) + (555177718058211/12500000000000 : ℝ)*(major1) + (555177718058211/12500000000000 : ℝ)*(major2) + (101352802579/100000000000000 : ℝ)*(sp1) + (108440265059/50000000000000 : ℝ)*(sp2) + (74614453983/100000000000000 : ℝ)*(sp3) + (9252693/312500000000 : ℝ)*(sp4) + (2939913764811847/50000000000000 : ℝ)*(sp8) + (47037833101463/800000000000 : ℝ)*(sp9) + (1175922721991067/20000000000000 : ℝ)*(sp10) + (297634813312493/10000000000000 : ℝ)*(sp11) + (2976422747578913/100000000000000 : ℝ)*(f.failure) + (5879830490485453/100000000000000 : ℝ)*(f.sum) + (12190890423/5200000000000000000000000 : ℝ)*base66 + (113537306690905237/13000000000000000000000000000000 : ℝ)*base67 + (36084502789094763/13000000000000000000000000000000 : ℝ)*base70 + (147412863569094763/13000000000000000000000000000000 : ℝ)*base72 + (71114048367/26000000000000000000000000 : ℝ)*base74 + (1993850453094763/13000000000000000000000000000000 : ℝ)*base76 + (35622852119094763/13000000000000000000000000000000 : ℝ)*base78 + (336886095530094763/13000000000000000000000000000000 : ℝ)*base80 + (2796050333/1040000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (361793/80000000000000000000 : ℝ)*base89 + (361793/80000000000000000000 : ℝ)*base91 + (361793/80000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-16619/20000 : ℝ) ≤ (-10802069500032383338845428470893/13000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (563509/10000000000000 : ℝ)*(lower0) + (59069487/50000000000000 : ℝ)*(lower1) + (6940371/4000000000000 : ℝ)*(lower4) + (1119082325451607/25000000000000 : ℝ)*(major0) + (1119082325451607/25000000000000 : ℝ)*(major1) + (1119082325451607/25000000000000 : ℝ)*(major2) + (2056823937/10000000000000 : ℝ)*(sp4) + (52847200243/12500000000000 : ℝ)*(sp6) + (59400674851/25000000000000 : ℝ)*(sp7) + (5069021381/50000000000000 : ℝ)*(sp8) + (598050943313533/10000000000000 : ℝ)*(sp12) + (2990270069708731/50000000000000 : ℝ)*(sp13) + (2990058680907759/50000000000000 : ℝ)*(sp14) + (2999578475598633/100000000000000 : ℝ)*(sp15) + (2999816078298037/100000000000000 : ℝ)*(f.failure) + (2990270069708731/50000000000000 : ℝ)*(f.sum) + (40906509479/10400000000000000000000000 : ℝ)*base65 + (69494853504573631/26000000000000000000000000000000 : ℝ)*base68 + (32955623556573631/26000000000000000000000000000000 : ℝ)*base70 + (206485750537426369/26000000000000000000000000000000 : ℝ)*base71 + (92833582199/52000000000000000000000000 : ℝ)*base73 + (185622027992573631/26000000000000000000000000000000 : ℝ)*base76 + (108979080341426369/26000000000000000000000000000000 : ℝ)*base77 + (89044002760573631/26000000000000000000000000000000 : ℝ)*base80 + (112937603591/52000000000000000000000000 : ℝ)*base81 + (547157/80000000000000000000 : ℝ)*base89 + (547157/80000000000000000000 : ℝ)*base91 + (547157/80000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1129_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(7411/12500 : ℝ) else (9971/12500 : ℝ) ≤ X j i ∧ X j i ≤ (16619/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1129_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1129_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(7411/12500 : ℝ) else (9971/12500 : ℝ) ≤ X j i ∧ X j i ≤ (16619/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1129_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(7411/12500 : ℝ) else (9971/12500 : ℝ) ≤ X j i ∧ X j i ≤ (16619/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1129_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

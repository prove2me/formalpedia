-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1430_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:54:18.092967+00:00
-- url     : https://prove2.me/submissions/c709273a-f3de-4ebc-8908-6dd198e1c7a5

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
theorem support_rectangle_w1430_s0_0 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1758247853/10000000000 : ℝ)*x 0 + (5959768341/10000000000 : ℝ)*x 1 + (483146677/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1758247853/10000000000 : ℝ)^2195 ≤ (2072284467901/20000000000000 : ℝ)^1683 := by
    have hnat : (1758247853 : ℕ)^2195*20000000000000^1683 ≤ 2072284467901^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1758247853 10000000000 2072284467901 20000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5959768341/10000000000 : ℝ)^2195 ≤ (25457747029121/50000000000000 : ℝ)^1683 := by
    have hnat : (5959768341 : ℕ)^2195*50000000000000^1683 ≤ 25457747029121^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5959768341 10000000000 25457747029121 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (483146677/1000000000 : ℝ)^2195 ≤ (38723083578237/100000000000000 : ℝ)^1683 := by
    have hnat : (483146677 : ℕ)^2195*100000000000000^1683 ≤ 38723083578237^1683*1000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483146677 1000000000 38723083578237 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1758247853/10000000000 : ℝ), (5959768341/10000000000 : ℝ), (483146677/1000000000 : ℝ)] ![(2072284467901/20000000000000 : ℝ), (25457747029121/50000000000000 : ℝ), (38723083578237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1758247853/10000000000 : ℝ)|^2195 ≤ (2072284467901/20000000000000 : ℝ)^1683
        have hw : |(-1758247853/10000000000 : ℝ)|=(1758247853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5959768341/10000000000 : ℝ)|^2195 ≤ (25457747029121/50000000000000 : ℝ)^1683
        have hw : |(5959768341/10000000000 : ℝ)|=(5959768341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(483146677/1000000000 : ℝ)|^2195 ≤ (38723083578237/100000000000000 : ℝ)^1683
        have hw : |(483146677/1000000000 : ℝ)|=(483146677/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s0_1 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1098397577/2000000000 : ℝ)*x 0 + (-37430897/156250000 : ℝ)*x 1 + (2415733607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098397577/2000000000 : ℝ)^2195 ≤ (5720848712111/12500000000000 : ℝ)^1683 := by
    have hnat : (1098397577 : ℕ)^2195*12500000000000^1683 ≤ 5720848712111^1683*2000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098397577 2000000000 5720848712111 12500000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37430897/156250000 : ℝ)^2195 ≤ (15510122066523/100000000000000 : ℝ)^1683 := by
    have hnat : (37430897 : ℕ)^2195*100000000000000^1683 ≤ 15510122066523^1683*156250000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37430897 156250000 15510122066523 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2415733607/5000000000 : ℝ)^2195 ≤ (38723088219373/100000000000000 : ℝ)^1683 := by
    have hnat : (2415733607 : ℕ)^2195*100000000000000^1683 ≤ 38723088219373^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2415733607 5000000000 38723088219373 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1098397577/2000000000 : ℝ), (-37430897/156250000 : ℝ), (2415733607/5000000000 : ℝ)] ![(5720848712111/12500000000000 : ℝ), (15510122066523/100000000000000 : ℝ), (38723088219373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1098397577/2000000000 : ℝ)|^2195 ≤ (5720848712111/12500000000000 : ℝ)^1683
        have hw : |(1098397577/2000000000 : ℝ)|=(1098397577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37430897/156250000 : ℝ)|^2195 ≤ (15510122066523/100000000000000 : ℝ)^1683
        have hw : |(-37430897/156250000 : ℝ)|=(37430897/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2415733607/5000000000 : ℝ)|^2195 ≤ (38723088219373/100000000000000 : ℝ)^1683
        have hw : |(2415733607/5000000000 : ℝ)|=(2415733607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s0_2 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5491988453/10000000000 : ℝ)*x 0 + (241573351/500000000 : ℝ)*x 1 + (-2395576917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5491988453/10000000000 : ℝ)^2195 ≤ (2288339793511/5000000000000 : ℝ)^1683 := by
    have hnat : (5491988453 : ℕ)^2195*5000000000000^1683 ≤ 2288339793511^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491988453 10000000000 2288339793511 5000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241573351/500000000 : ℝ)^2195 ≤ (38723086191489/100000000000000 : ℝ)^1683 := by
    have hnat : (241573351 : ℕ)^2195*100000000000000^1683 ≤ 38723086191489^1683*500000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241573351 500000000 38723086191489 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2395576917/10000000000 : ℝ)^2195 ≤ (310202358409/2000000000000 : ℝ)^1683 := by
    have hnat : (2395576917 : ℕ)^2195*2000000000000^1683 ≤ 310202358409^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395576917 10000000000 310202358409 2000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5491988453/10000000000 : ℝ), (241573351/500000000 : ℝ), (-2395576917/10000000000 : ℝ)] ![(2288339793511/5000000000000 : ℝ), (38723086191489/100000000000000 : ℝ), (310202358409/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5491988453/10000000000 : ℝ)|^2195 ≤ (2288339793511/5000000000000 : ℝ)^1683
        have hw : |(5491988453/10000000000 : ℝ)|=(5491988453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(241573351/500000000 : ℝ)|^2195 ≤ (38723086191489/100000000000000 : ℝ)^1683
        have hw : |(241573351/500000000 : ℝ)|=(241573351/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2395576917/10000000000 : ℝ)|^2195 ≤ (310202358409/2000000000000 : ℝ)^1683
        have hw : |(-2395576917/10000000000 : ℝ)|=(2395576917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s0_3 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2082928551/5000000000 : ℝ)*x 0 + (3103332249/10000000000 : ℝ)*x 1 + (2772560571/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082928551/5000000000 : ℝ)^2195 ≤ (15958106042251/50000000000000 : ℝ)^1683 := by
    have hnat : (2082928551 : ℕ)^2195*50000000000000^1683 ≤ 15958106042251^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082928551 5000000000 15958106042251 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3103332249/10000000000 : ℝ)^2195 ≤ (21738669235041/100000000000000 : ℝ)^1683 := by
    have hnat : (3103332249 : ℕ)^2195*100000000000000^1683 ≤ 21738669235041^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3103332249 10000000000 21738669235041 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2772560571/5000000000 : ℝ)^2195 ≤ (46345118660041/100000000000000 : ℝ)^1683 := by
    have hnat : (2772560571 : ℕ)^2195*100000000000000^1683 ≤ 46345118660041^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2772560571 5000000000 46345118660041 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2082928551/5000000000 : ℝ), (3103332249/10000000000 : ℝ), (2772560571/5000000000 : ℝ)] ![(15958106042251/50000000000000 : ℝ), (21738669235041/100000000000000 : ℝ), (46345118660041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2082928551/5000000000 : ℝ)|^2195 ≤ (15958106042251/50000000000000 : ℝ)^1683
        have hw : |(2082928551/5000000000 : ℝ)|=(2082928551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3103332249/10000000000 : ℝ)|^2195 ≤ (21738669235041/100000000000000 : ℝ)^1683
        have hw : |(3103332249/10000000000 : ℝ)|=(3103332249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2772560571/5000000000 : ℝ)|^2195 ≤ (46345118660041/100000000000000 : ℝ)^1683
        have hw : |(2772560571/5000000000 : ℝ)|=(2772560571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s0_4 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1762260151/10000000000 : ℝ)*x 0 + (151885413/312500000 : ℝ)*x 1 + (2964935687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1762260151/10000000000 : ℝ)^2195 ≤ (10392270801269/100000000000000 : ℝ)^1683 := by
    have hnat : (1762260151 : ℕ)^2195*100000000000000^1683 ≤ 10392270801269^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1762260151 10000000000 10392270801269 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151885413/312500000 : ℝ)^2195 ≤ (19512549328599/50000000000000 : ℝ)^1683 := by
    have hnat : (151885413 : ℕ)^2195*50000000000000^1683 ≤ 19512549328599^1683*312500000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151885413 312500000 19512549328599 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2964935687/5000000000 : ℝ)^2195 ≤ (1011652610449/2000000000000 : ℝ)^1683 := by
    have hnat : (2964935687 : ℕ)^2195*2000000000000^1683 ≤ 1011652610449^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2964935687 5000000000 1011652610449 2000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1762260151/10000000000 : ℝ), (151885413/312500000 : ℝ), (2964935687/5000000000 : ℝ)] ![(10392270801269/100000000000000 : ℝ), (19512549328599/50000000000000 : ℝ), (1011652610449/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1762260151/10000000000 : ℝ)|^2195 ≤ (10392270801269/100000000000000 : ℝ)^1683
        have hw : |(-1762260151/10000000000 : ℝ)|=(1762260151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(151885413/312500000 : ℝ)|^2195 ≤ (19512549328599/50000000000000 : ℝ)^1683
        have hw : |(151885413/312500000 : ℝ)|=(151885413/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2964935687/5000000000 : ℝ)|^2195 ≤ (1011652610449/2000000000000 : ℝ)^1683
        have hw : |(2964935687/5000000000 : ℝ)|=(2964935687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s0_5 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5184025307/10000000000 : ℝ)*x 0 + (-1297172533/10000000000 : ℝ)*x 1 + (5929871447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184025307/10000000000 : ℝ)^2195 ≤ (42448615044267/100000000000000 : ℝ)^1683 := by
    have hnat : (5184025307 : ℕ)^2195*100000000000000^1683 ≤ 42448615044267^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184025307 10000000000 42448615044267 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1297172533/10000000000 : ℝ)^2195 ≤ (6968753597773/100000000000000 : ℝ)^1683 := by
    have hnat : (1297172533 : ℕ)^2195*100000000000000^1683 ≤ 6968753597773^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297172533 10000000000 6968753597773 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5929871447/10000000000 : ℝ)^2195 ≤ (50582631334587/100000000000000 : ℝ)^1683 := by
    have hnat : (5929871447 : ℕ)^2195*100000000000000^1683 ≤ 50582631334587^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5929871447 10000000000 50582631334587 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184025307/10000000000 : ℝ), (-1297172533/10000000000 : ℝ), (5929871447/10000000000 : ℝ)] ![(42448615044267/100000000000000 : ℝ), (6968753597773/100000000000000 : ℝ), (50582631334587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184025307/10000000000 : ℝ)|^2195 ≤ (42448615044267/100000000000000 : ℝ)^1683
        have hw : |(5184025307/10000000000 : ℝ)|=(5184025307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1297172533/10000000000 : ℝ)|^2195 ≤ (6968753597773/100000000000000 : ℝ)^1683
        have hw : |(-1297172533/10000000000 : ℝ)|=(1297172533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5929871447/10000000000 : ℝ)|^2195 ≤ (50582631334587/100000000000000 : ℝ)^1683
        have hw : |(5929871447/10000000000 : ℝ)|=(5929871447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s0_6 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5184025329/10000000000 : ℝ)*x 0 + (5929871287/10000000000 : ℝ)*x 1 + (-259434551/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184025329/10000000000 : ℝ)^2195 ≤ (21224307639607/50000000000000 : ℝ)^1683 := by
    have hnat : (5184025329 : ℕ)^2195*50000000000000^1683 ≤ 21224307639607^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184025329 10000000000 21224307639607 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5929871287/10000000000 : ℝ)^2195 ≤ (79035358679/156250000000 : ℝ)^1683 := by
    have hnat : (5929871287 : ℕ)^2195*156250000000^1683 ≤ 79035358679^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5929871287 10000000000 79035358679 156250000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259434551/2000000000 : ℝ)^2195 ≤ (174218878831/2500000000000 : ℝ)^1683 := by
    have hnat : (259434551 : ℕ)^2195*2500000000000^1683 ≤ 174218878831^1683*2000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259434551 2000000000 174218878831 2500000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184025329/10000000000 : ℝ), (5929871287/10000000000 : ℝ), (-259434551/2000000000 : ℝ)] ![(21224307639607/50000000000000 : ℝ), (79035358679/156250000000 : ℝ), (174218878831/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184025329/10000000000 : ℝ)|^2195 ≤ (21224307639607/50000000000000 : ℝ)^1683
        have hw : |(5184025329/10000000000 : ℝ)|=(5184025329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5929871287/10000000000 : ℝ)|^2195 ≤ (79035358679/156250000000 : ℝ)^1683
        have hw : |(5929871287/10000000000 : ℝ)|=(5929871287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-259434551/2000000000 : ℝ)|^2195 ≤ (174218878831/2500000000000 : ℝ)^1683
        have hw : |(-259434551/2000000000 : ℝ)|=(259434551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s0_7 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (26090891/62500000 : ℝ)*x 0 + (5482650121/10000000000 : ℝ)*x 1 + (3168033731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26090891/62500000 : ℝ)^2195 ≤ (32003025680999/100000000000000 : ℝ)^1683 := by
    have hnat : (26090891 : ℕ)^2195*100000000000000^1683 ≤ 32003025680999^1683*62500000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26090891 62500000 32003025680999 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5482650121/10000000000 : ℝ)^2195 ≤ (5708166009279/12500000000000 : ℝ)^1683 := by
    have hnat : (5482650121 : ℕ)^2195*12500000000000^1683 ≤ 5708166009279^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482650121 10000000000 5708166009279 12500000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3168033731/10000000000 : ℝ)^2195 ≤ (5582911558981/25000000000000 : ℝ)^1683 := by
    have hnat : (3168033731 : ℕ)^2195*25000000000000^1683 ≤ 5582911558981^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3168033731 10000000000 5582911558981 25000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26090891/62500000 : ℝ), (5482650121/10000000000 : ℝ), (3168033731/10000000000 : ℝ)] ![(32003025680999/100000000000000 : ℝ), (5708166009279/12500000000000 : ℝ), (5582911558981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26090891/62500000 : ℝ)|^2195 ≤ (32003025680999/100000000000000 : ℝ)^1683
        have hw : |(26090891/62500000 : ℝ)|=(26090891/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5482650121/10000000000 : ℝ)|^2195 ≤ (5708166009279/12500000000000 : ℝ)^1683
        have hw : |(5482650121/10000000000 : ℝ)|=(5482650121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3168033731/10000000000 : ℝ)|^2195 ≤ (5582911558981/25000000000000 : ℝ)^1683
        have hw : |(3168033731/10000000000 : ℝ)|=(3168033731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1430_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (411/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26251/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4389/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4389 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4389*1^1024 ≤ 0^1024*1^4389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4389 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4389/1024 : ℝ) ≤ (246198999904291773/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4389 ≤ (246198999904291773/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4389*12500000000000000000^1024 ≤ 246198999904291773^1024*5^4389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 246198999904291773 12500000000000000000 4389 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (246198999904291773/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4389 := by
      have hnat : (1 : ℕ)^1024*1^4389 ≤ 1^4389*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12746198999904291773/12500000000000000000 : ℝ) ≤ (10045609671769131/10000000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (12746198999904291773/12500000000000000000 : ℝ)^1024 ≤ (10045609671769131/10000000000000000 : ℝ)^4389 := by
      have hnat : (12746198999904291773 : ℕ)^1024*10000000000000000^4389 ≤ 10045609671769131^4389*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12746198999904291773 12500000000000000000 10045609671769131 10000000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10045609671769131/10000000000000000 : ℝ)) (X := (12746198999904291773/12500000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6496198999904291773/6250000000000000000 : ℝ) ≤ (5045609671769131/5000000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (6496198999904291773/6250000000000000000 : ℝ)^1024 ≤ (5045609671769131/5000000000000000 : ℝ)^4389 := by
      have hnat : (6496198999904291773 : ℕ)^1024*5000000000000000^4389 ≤ 5045609671769131^4389*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6496198999904291773 6250000000000000000 5045609671769131 5000000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5045609671769131/5000000000000000 : ℝ)) (X := (6496198999904291773/6250000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(45609671769131/4000000000000000 : ℝ)*(0 : ℝ))^(4389/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(45609671769131/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(246198999904291773/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(45609671769131/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4389/1024 : ℝ) := by
    rw [show (1 : ℝ)+(45609671769131/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10045609671769131/10000000000000000 : ℝ) by norm_num, show 1+(246198999904291773/12500000000000000000 : ℝ)+(0 : ℝ)=(12746198999904291773/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(246198999904291773/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(45609671769131/4000000000000000 : ℝ)*(2/5 : ℝ))^(4389/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(45609671769131/4000000000000000 : ℝ)*(2/5 : ℝ)=(5045609671769131/5000000000000000 : ℝ) by norm_num, show 1+2*(246198999904291773/12500000000000000000 : ℝ)=(6496198999904291773/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(45609671769131/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45609671769131/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(45609671769131/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45609671769131/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(45609671769131/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45609671769131/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1758247853/10000000000 : ℝ)*X 0 0+(5959768341/10000000000 : ℝ)*X 0 1+(483146677/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1098397577/2000000000 : ℝ)*X 1 0+(-37430897/156250000 : ℝ)*X 1 1+(2415733607/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5491988453/10000000000 : ℝ)*X 2 0+(241573351/500000000 : ℝ)*X 2 1+(-2395576917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2082928551/5000000000 : ℝ)*X 0 0+(3103332249/10000000000 : ℝ)*X 0 1+(2772560571/5000000000 : ℝ)*X 0 2+(2082928551/5000000000 : ℝ)*X 1 0+(3103332249/10000000000 : ℝ)*X 1 1+(2772560571/5000000000 : ℝ)*X 1 2+(2082928551/5000000000 : ℝ)*X 2 0+(3103332249/10000000000 : ℝ)*X 2 1+(2772560571/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1762260151/10000000000 : ℝ)*X 0 0+(151885413/312500000 : ℝ)*X 0 1+(2964935687/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5184025307/10000000000 : ℝ)*X 1 0+(-1297172533/10000000000 : ℝ)*X 1 1+(5929871447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5184025329/10000000000 : ℝ)*X 2 0+(5929871287/10000000000 : ℝ)*X 2 1+(-259434551/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((26090891/62500000 : ℝ)*X 0 0+(5482650121/10000000000 : ℝ)*X 0 1+(3168033731/10000000000 : ℝ)*X 0 2+(26090891/62500000 : ℝ)*X 1 0+(5482650121/10000000000 : ℝ)*X 1 1+(3168033731/10000000000 : ℝ)*X 1 2+(26090891/62500000 : ℝ)*X 2 0+(5482650121/10000000000 : ℝ)*X 2 1+(3168033731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12563012769776979367353/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (145439923/20000000000000 : ℝ)*(base19) + (717074359/100000000000000 : ℝ)*(base23) + (857879/1250000000000 : ℝ)*(upper3) + (3493887/6250000000000 : ℝ)*(upper4) + (8562823/6250000000000 : ℝ)*(upper5) + (64791588370279/10000000000000 : ℝ)*(major0) + (64791588370279/10000000000000 : ℝ)*(major1) + (64791588370279/10000000000000 : ℝ)*(major2) + (443145029824029/50000000000000 : ℝ)*(sp0) + (221573121930281/25000000000000 : ℝ)*(sp1) + (44314624892319/5000000000000 : ℝ)*(sp2) + (40953716283557/10000000000000 : ℝ)*(sp3) + (78881817/2500000000000 : ℝ)*(sp4) + (1305895847/100000000000000 : ℝ)*(sp7) + (409538468731417/100000000000000 : ℝ)*(f.failure) + (886293214920739/100000000000000 : ℝ)*(f.sum) + (19435583937549/20000000000000000000000000000 : ℝ)*base65 + (188718427057549/40000000000000000000000000000 : ℝ)*base67 + (239973786977549/40000000000000000000000000000 : ℝ)*base69 + (21001062057549/40000000000000000000000000000 : ℝ)*base71 + (67033473557549/20000000000000000000000000000 : ℝ)*base73 + (9456444737549/40000000000000000000000000000 : ℝ)*base75 + (61449633942451/40000000000000000000000000000 : ℝ)*base78 + (58662250622451/40000000000000000000000000000 : ℝ)*base80 + (106414517317549/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (8488993/2000000000000000000000 : ℝ)*base90 + (8488993/2000000000000000000000 : ℝ)*base92 + (8488993/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222656827180495090708959/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (253190817/25000000000000 : ℝ)*(base19) + (1020691083/100000000000000 : ℝ)*(base23) + (126186763/100000000000000 : ℝ)*(base32) + (156854343/100000000000000 : ℝ)*(upper3) + (40007399/50000000000000 : ℝ)*(upper5) + (170877430302463/25000000000000 : ℝ)*(major0) + (170877430302463/25000000000000 : ℝ)*(major1) + (170877430302463/25000000000000 : ℝ)*(major2) + (149181587/6250000000000 : ℝ)*(sp1) + (2453559791/100000000000000 : ℝ)*(sp2) + (934982463849517/100000000000000 : ℝ)*(sp4) + (934979064180857/100000000000000 : ℝ)*(sp5) + (233744747399661/25000000000000 : ℝ)*(sp6) + (6750573499149/1562500000000 : ℝ)*(sp7) + (432036830132299/100000000000000 : ℝ)*(f.failure) + (934982463849517/100000000000000 : ℝ)*(f.sum) + (7450117980347/50000000000000000000000000000 : ℝ)*base66 + (13918983869653/100000000000000000000000000000 : ℝ)*base67 + (143075519269653/100000000000000000000000000000 : ℝ)*base69 + (359552018769653/100000000000000000000000000000 : ℝ)*base71 + (111955620280347/50000000000000000000000000000 : ℝ)*base74 + (339667358369653/100000000000000000000000000000 : ℝ)*base75 + (5649700769653/100000000000000000000000000000 : ℝ)*base77 + (568448113730347/100000000000000000000000000000 : ℝ)*base80 + (85943675780347/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1487971/2000000000000000000000 : ℝ)*base90 + (1487971/2000000000000000000000 : ℝ)*base92 + (1487971/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1430_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (411/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26251/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1430_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1430_s1_0 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1930462793/10000000000 : ℝ)*x 0 + (1120964079/2000000000 : ℝ)*x 1 + (5076009753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1930462793/10000000000 : ℝ)^2195 ≤ (1170432349721/10000000000000 : ℝ)^1683 := by
    have hnat : (1930462793 : ℕ)^2195*10000000000000^1683 ≤ 1170432349721^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930462793 10000000000 1170432349721 10000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120964079/2000000000 : ℝ)^2195 ≤ (46996928825331/100000000000000 : ℝ)^1683 := by
    have hnat : (1120964079 : ℕ)^2195*100000000000000^1683 ≤ 46996928825331^1683*2000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120964079 2000000000 46996928825331 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5076009753/10000000000 : ℝ)^2195 ≤ (20649373832717/50000000000000 : ℝ)^1683 := by
    have hnat : (5076009753 : ℕ)^2195*50000000000000^1683 ≤ 20649373832717^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076009753 10000000000 20649373832717 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1930462793/10000000000 : ℝ), (1120964079/2000000000 : ℝ), (5076009753/10000000000 : ℝ)] ![(1170432349721/10000000000000 : ℝ), (46996928825331/100000000000000 : ℝ), (20649373832717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1930462793/10000000000 : ℝ)|^2195 ≤ (1170432349721/10000000000000 : ℝ)^1683
        have hw : |(-1930462793/10000000000 : ℝ)|=(1930462793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120964079/2000000000 : ℝ)|^2195 ≤ (46996928825331/100000000000000 : ℝ)^1683
        have hw : |(1120964079/2000000000 : ℝ)|=(1120964079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5076009753/10000000000 : ℝ)|^2195 ≤ (20649373832717/50000000000000 : ℝ)^1683
        have hw : |(5076009753/10000000000 : ℝ)|=(5076009753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s1_1 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (337294277/625000000 : ℝ)*x 0 + (-2210650937/10000000000 : ℝ)*x 1 + (2538005593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337294277/625000000 : ℝ)^2195 ≤ (44733984763179/100000000000000 : ℝ)^1683 := by
    have hnat : (337294277 : ℕ)^2195*100000000000000^1683 ≤ 44733984763179^1683*625000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337294277 625000000 44733984763179 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2210650937/10000000000 : ℝ)^2195 ≤ (13967252351761/100000000000000 : ℝ)^1683 := by
    have hnat : (2210650937 : ℕ)^2195*100000000000000^1683 ≤ 13967252351761^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210650937 10000000000 13967252351761 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2538005593/5000000000 : ℝ)^2195 ≤ (80661646233/195312500000 : ℝ)^1683 := by
    have hnat : (2538005593 : ℕ)^2195*195312500000^1683 ≤ 80661646233^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538005593 5000000000 80661646233 195312500000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337294277/625000000 : ℝ), (-2210650937/10000000000 : ℝ), (2538005593/5000000000 : ℝ)] ![(44733984763179/100000000000000 : ℝ), (13967252351761/100000000000000 : ℝ), (80661646233/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337294277/625000000 : ℝ)|^2195 ≤ (44733984763179/100000000000000 : ℝ)^1683
        have hw : |(337294277/625000000 : ℝ)|=(337294277/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2210650937/10000000000 : ℝ)|^2195 ≤ (13967252351761/100000000000000 : ℝ)^1683
        have hw : |(-2210650937/10000000000 : ℝ)|=(2210650937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2538005593/5000000000 : ℝ)|^2195 ≤ (80661646233/195312500000 : ℝ)^1683
        have hw : |(2538005593/5000000000 : ℝ)|=(2538005593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s1_2 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (539670953/1000000000 : ℝ)*x 0 + (5076009959/10000000000 : ℝ)*x 1 + (-2210651077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539670953/1000000000 : ℝ)^2195 ≤ (44733996633471/100000000000000 : ℝ)^1683 := by
    have hnat : (539670953 : ℕ)^2195*100000000000000^1683 ≤ 44733996633471^1683*1000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539670953 1000000000 44733996633471 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5076009959/10000000000 : ℝ)^2195 ≤ (41298749851343/100000000000000 : ℝ)^1683 := by
    have hnat : (5076009959 : ℕ)^2195*100000000000000^1683 ≤ 41298749851343^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076009959 10000000000 41298749851343 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210651077/10000000000 : ℝ)^2195 ≤ (6983626752699/50000000000000 : ℝ)^1683 := by
    have hnat : (2210651077 : ℕ)^2195*50000000000000^1683 ≤ 6983626752699^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210651077 10000000000 6983626752699 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539670953/1000000000 : ℝ), (5076009959/10000000000 : ℝ), (-2210651077/10000000000 : ℝ)] ![(44733996633471/100000000000000 : ℝ), (41298749851343/100000000000000 : ℝ), (6983626752699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539670953/1000000000 : ℝ)|^2195 ≤ (44733996633471/100000000000000 : ℝ)^1683
        have hw : |(539670953/1000000000 : ℝ)|=(539670953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5076009959/10000000000 : ℝ)|^2195 ≤ (41298749851343/100000000000000 : ℝ)^1683
        have hw : |(5076009959/10000000000 : ℝ)|=(5076009959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2210651077/10000000000 : ℝ)|^2195 ≤ (6983626752699/50000000000000 : ℝ)^1683
        have hw : |(-2210651077/10000000000 : ℝ)|=(2210651077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s1_3 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4276457777/10000000000 : ℝ)*x 0 + (1460317/3906250 : ℝ)*x 1 + (976564479/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4276457777/10000000000 : ℝ)^2195 ≤ (6605156488311/20000000000000 : ℝ)^1683 := by
    have hnat : (4276457777 : ℕ)^2195*20000000000000^1683 ≤ 6605156488311^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4276457777 10000000000 6605156488311 20000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1460317/3906250 : ℝ)^2195 ≤ (13856723655949/50000000000000 : ℝ)^1683 := by
    have hnat : (1460317 : ℕ)^2195*50000000000000^1683 ≤ 13856723655949^1683*3906250^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460317 3906250 13856723655949 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (976564479/2000000000 : ℝ)^2195 ≤ (7852154046677/20000000000000 : ℝ)^1683 := by
    have hnat : (976564479 : ℕ)^2195*20000000000000^1683 ≤ 7852154046677^1683*2000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976564479 2000000000 7852154046677 20000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4276457777/10000000000 : ℝ), (1460317/3906250 : ℝ), (976564479/2000000000 : ℝ)] ![(6605156488311/20000000000000 : ℝ), (13856723655949/50000000000000 : ℝ), (7852154046677/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4276457777/10000000000 : ℝ)|^2195 ≤ (6605156488311/20000000000000 : ℝ)^1683
        have hw : |(4276457777/10000000000 : ℝ)|=(4276457777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1460317/3906250 : ℝ)|^2195 ≤ (13856723655949/50000000000000 : ℝ)^1683
        have hw : |(1460317/3906250 : ℝ)|=(1460317/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(976564479/2000000000 : ℝ)|^2195 ≤ (7852154046677/20000000000000 : ℝ)^1683
        have hw : |(976564479/2000000000 : ℝ)|=(976564479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s1_4 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1930859359/10000000000 : ℝ)*x 0 + (635275729/1250000000 : ℝ)*x 1 + (1119703877/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1930859359/10000000000 : ℝ)^2195 ≤ (5853729706299/50000000000000 : ℝ)^1683 := by
    have hnat : (1930859359 : ℕ)^2195*50000000000000^1683 ≤ 5853729706299^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930859359 10000000000 5853729706299 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635275729/1250000000 : ℝ)^2195 ≤ (41364507755033/100000000000000 : ℝ)^1683 := by
    have hnat : (635275729 : ℕ)^2195*100000000000000^1683 ≤ 41364507755033^1683*1250000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635275729 1250000000 41364507755033 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119703877/2000000000 : ℝ)^2195 ≤ (5866004102057/12500000000000 : ℝ)^1683 := by
    have hnat : (1119703877 : ℕ)^2195*12500000000000^1683 ≤ 5866004102057^1683*2000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119703877 2000000000 5866004102057 12500000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1930859359/10000000000 : ℝ), (635275729/1250000000 : ℝ), (1119703877/2000000000 : ℝ)] ![(5853729706299/50000000000000 : ℝ), (41364507755033/100000000000000 : ℝ), (5866004102057/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1930859359/10000000000 : ℝ)|^2195 ≤ (5853729706299/50000000000000 : ℝ)^1683
        have hw : |(-1930859359/10000000000 : ℝ)|=(1930859359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635275729/1250000000 : ℝ)|^2195 ≤ (41364507755033/100000000000000 : ℝ)^1683
        have hw : |(635275729/1250000000 : ℝ)|=(635275729/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119703877/2000000000 : ℝ)|^2195 ≤ (5866004102057/12500000000000 : ℝ)^1683
        have hw : |(1119703877/2000000000 : ℝ)|=(1119703877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s1_5 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5258534797/10000000000 : ℝ)*x 0 + (-211017763/1250000000 : ℝ)*x 1 + (5598519401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258534797/10000000000 : ℝ)^2195 ≤ (43246065505547/100000000000000 : ℝ)^1683 := by
    have hnat : (5258534797 : ℕ)^2195*100000000000000^1683 ≤ 43246065505547^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258534797 10000000000 43246065505547 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211017763/1250000000 : ℝ)^2195 ≤ (9825901489067/100000000000000 : ℝ)^1683 := by
    have hnat : (211017763 : ℕ)^2195*100000000000000^1683 ≤ 9825901489067^1683*1250000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211017763 1250000000 9825901489067 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5598519401/10000000000 : ℝ)^2195 ≤ (11732008247843/25000000000000 : ℝ)^1683 := by
    have hnat : (5598519401 : ℕ)^2195*25000000000000^1683 ≤ 11732008247843^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5598519401 10000000000 11732008247843 25000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258534797/10000000000 : ℝ), (-211017763/1250000000 : ℝ), (5598519401/10000000000 : ℝ)] ![(43246065505547/100000000000000 : ℝ), (9825901489067/100000000000000 : ℝ), (11732008247843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258534797/10000000000 : ℝ)|^2195 ≤ (43246065505547/100000000000000 : ℝ)^1683
        have hw : |(5258534797/10000000000 : ℝ)|=(5258534797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211017763/1250000000 : ℝ)|^2195 ≤ (9825901489067/100000000000000 : ℝ)^1683
        have hw : |(-211017763/1250000000 : ℝ)|=(211017763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5598519401/10000000000 : ℝ)|^2195 ≤ (11732008247843/25000000000000 : ℝ)^1683
        have hw : |(5598519401/10000000000 : ℝ)|=(5598519401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s1_6 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5258534747/10000000000 : ℝ)*x 0 + (5598519363/10000000000 : ℝ)*x 1 + (-168814223/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258534747/10000000000 : ℝ)^2195 ≤ (21623032484627/50000000000000 : ℝ)^1683 := by
    have hnat : (5258534747 : ℕ)^2195*50000000000000^1683 ≤ 21623032484627^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258534747 10000000000 21623032484627 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5598519363/10000000000 : ℝ)^2195 ≤ (46928032575947/100000000000000 : ℝ)^1683 := by
    have hnat : (5598519363 : ℕ)^2195*100000000000000^1683 ≤ 46928032575947^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5598519363 10000000000 46928032575947 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168814223/1000000000 : ℝ)^2195 ≤ (1965180489113/20000000000000 : ℝ)^1683 := by
    have hnat : (168814223 : ℕ)^2195*20000000000000^1683 ≤ 1965180489113^1683*1000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168814223 1000000000 1965180489113 20000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258534747/10000000000 : ℝ), (5598519363/10000000000 : ℝ), (-168814223/1000000000 : ℝ)] ![(21623032484627/50000000000000 : ℝ), (46928032575947/100000000000000 : ℝ), (1965180489113/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258534747/10000000000 : ℝ)|^2195 ≤ (21623032484627/50000000000000 : ℝ)^1683
        have hw : |(5258534747/10000000000 : ℝ)|=(5258534747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5598519363/10000000000 : ℝ)|^2195 ≤ (46928032575947/100000000000000 : ℝ)^1683
        have hw : |(5598519363/10000000000 : ℝ)|=(5598519363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-168814223/1000000000 : ℝ)|^2195 ≤ (1965180489113/20000000000000 : ℝ)^1683
        have hw : |(-168814223/1000000000 : ℝ)|=(168814223/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s1_7 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (855463317/2000000000 : ℝ)*x 0 + (486941441/1000000000 : ℝ)*x 1 + (938011497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855463317/2000000000 : ℝ)^2195 ≤ (4129304086503/12500000000000 : ℝ)^1683 := by
    have hnat : (855463317 : ℕ)^2195*12500000000000^1683 ≤ 4129304086503^1683*2000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855463317 2000000000 4129304086503 12500000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486941441/1000000000 : ℝ)^2195 ≤ (39120223660537/100000000000000 : ℝ)^1683 := by
    have hnat : (486941441 : ℕ)^2195*100000000000000^1683 ≤ 39120223660537^1683*1000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486941441 1000000000 39120223660537 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (938011497/2500000000 : ℝ)^2195 ≤ (27845343641711/100000000000000 : ℝ)^1683 := by
    have hnat : (938011497 : ℕ)^2195*100000000000000^1683 ≤ 27845343641711^1683*2500000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938011497 2500000000 27845343641711 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855463317/2000000000 : ℝ), (486941441/1000000000 : ℝ), (938011497/2500000000 : ℝ)] ![(4129304086503/12500000000000 : ℝ), (39120223660537/100000000000000 : ℝ), (27845343641711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855463317/2000000000 : ℝ)|^2195 ≤ (4129304086503/12500000000000 : ℝ)^1683
        have hw : |(855463317/2000000000 : ℝ)|=(855463317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(486941441/1000000000 : ℝ)|^2195 ≤ (39120223660537/100000000000000 : ℝ)^1683
        have hw : |(486941441/1000000000 : ℝ)|=(486941441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(938011497/2500000000 : ℝ)|^2195 ≤ (27845343641711/100000000000000 : ℝ)^1683
        have hw : |(938011497/2500000000 : ℝ)|=(938011497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1430_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26251/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (411/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (383/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (471/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26251/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (411/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26251/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (411/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26251/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (411/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26251/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (411/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26251/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (411/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26251/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (411/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (411/20000 : ℝ) ^ (4389/1024 : ℝ) ≤ (2933981774939/50000000000000000000 : ℝ) := by
    have hpowers : (411/20000 : ℝ)^4389 ≤ (2933981774939/50000000000000000000 : ℝ)^1024 := by
      have hnat : (411 : ℕ)^4389*50000000000000000000^1024 ≤ 2933981774939^1024*20000^4389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        411 20000 2933981774939 50000000000000000000 4389 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (411/20000 : ℝ)) (X := (2933981774939/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26251/100000 : ℝ) ^ (4389/1024 : ℝ) ≤ (161939196923143257/50000000000000000000 : ℝ) := by
    have hpowers : (26251/100000 : ℝ)^4389 ≤ (161939196923143257/50000000000000000000 : ℝ)^1024 := by
      have hnat : (26251 : ℕ)^4389*50000000000000000000^1024 ≤ 161939196923143257^1024*100000^4389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26251 100000 161939196923143257 50000000000000000000 4389 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26251/100000 : ℝ)) (X := (161939196923143257/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000002933981774939/25000000000000000000 : ℝ) ≤ (2500000068452887/2500000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (25000002933981774939/25000000000000000000 : ℝ)^1024 ≤ (2500000068452887/2500000000000000 : ℝ)^4389 := by
      have hnat : (25000002933981774939 : ℕ)^1024*2500000000000000^4389 ≤ 2500000068452887^4389*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000002933981774939 25000000000000000000 2500000068452887 2500000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000068452887/2500000000000000 : ℝ)) (X := (25000002933981774939/25000000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12540485532726229549/12500000000000000000 : ℝ) ≤ (10007547197176179/10000000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (12540485532726229549/12500000000000000000 : ℝ)^1024 ≤ (10007547197176179/10000000000000000 : ℝ)^4389 := by
      have hnat : (12540485532726229549 : ℕ)^1024*10000000000000000^4389 ≤ 10007547197176179^4389*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12540485532726229549 12500000000000000000 10007547197176179 10000000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007547197176179/10000000000000000 : ℝ)) (X := (12540485532726229549/12500000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25161939196923143257/25000000000000000000 : ℝ) ≤ (1001509412054081/1000000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (25161939196923143257/25000000000000000000 : ℝ)^1024 ≤ (1001509412054081/1000000000000000 : ℝ)^4389 := by
      have hnat : (25161939196923143257 : ℕ)^1024*1000000000000000^4389 ≤ 1001509412054081^4389*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25161939196923143257 25000000000000000000 1001509412054081 1000000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001509412054081/1000000000000000 : ℝ)) (X := (25161939196923143257/25000000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2933981774939/50000000000000000000 : ℝ) ≤ ((120964494385057790999/120980000000000000000 : ℝ)+2*(7546923364631/2419600000000000 : ℝ)*(411/20000 : ℝ))^(4389/1024 : ℝ) := by
    rw [show (120964494385057790999/120980000000000000000 : ℝ)+2*(7546923364631/2419600000000000 : ℝ)*(411/20000 : ℝ)=(2500000068452887/2500000000000000 : ℝ) by norm_num, show 1+2*(2933981774939/50000000000000000000 : ℝ)=(25000002933981774939/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(161939196923143257/50000000000000000000 : ℝ)+(2933981774939/50000000000000000000 : ℝ) ≤ ((120964494385057790999/120980000000000000000 : ℝ)+(7546923364631/2419600000000000 : ℝ)*((26251/100000 : ℝ)+(411/20000 : ℝ)))^(4389/1024 : ℝ) := by
    rw [show (120964494385057790999/120980000000000000000 : ℝ)+(7546923364631/2419600000000000 : ℝ)*((26251/100000 : ℝ)+(411/20000 : ℝ))=(10007547197176179/10000000000000000 : ℝ) by norm_num, show 1+(161939196923143257/50000000000000000000 : ℝ)+(2933981774939/50000000000000000000 : ℝ)=(12540485532726229549/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(161939196923143257/50000000000000000000 : ℝ) ≤ ((120964494385057790999/120980000000000000000 : ℝ)+2*(7546923364631/2419600000000000 : ℝ)*(26251/100000 : ℝ))^(4389/1024 : ℝ) := by
    rw [show (120964494385057790999/120980000000000000000 : ℝ)+2*(7546923364631/2419600000000000 : ℝ)*(26251/100000 : ℝ)=(1001509412054081/1000000000000000 : ℝ) by norm_num, show 1+2*(161939196923143257/50000000000000000000 : ℝ)=(25161939196923143257/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (120964494385057790999/120980000000000000000 : ℝ)*(X 1 0+X 2 0)+(7546923364631/2419600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (411/20000 : ℝ)) (hi := (26251/100000 : ℝ)) (c := (120964494385057790999/120980000000000000000 : ℝ)) (alpha := (7546923364631/2419600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (120964494385057790999/120980000000000000000 : ℝ)*(X 0 1+X 2 1)+(7546923364631/2419600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (411/20000 : ℝ)) (hi := (26251/100000 : ℝ)) (c := (120964494385057790999/120980000000000000000 : ℝ)) (alpha := (7546923364631/2419600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (120964494385057790999/120980000000000000000 : ℝ)*(X 0 2+X 1 2)+(7546923364631/2419600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (411/20000 : ℝ)) (hi := (26251/100000 : ℝ)) (c := (120964494385057790999/120980000000000000000 : ℝ)) (alpha := (7546923364631/2419600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1930462793/10000000000 : ℝ)*X 0 0+(1120964079/2000000000 : ℝ)*X 0 1+(5076009753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((337294277/625000000 : ℝ)*X 1 0+(-2210650937/10000000000 : ℝ)*X 1 1+(2538005593/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((539670953/1000000000 : ℝ)*X 2 0+(5076009959/10000000000 : ℝ)*X 2 1+(-2210651077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4276457777/10000000000 : ℝ)*X 0 0+(1460317/3906250 : ℝ)*X 0 1+(976564479/2000000000 : ℝ)*X 0 2+(4276457777/10000000000 : ℝ)*X 1 0+(1460317/3906250 : ℝ)*X 1 1+(976564479/2000000000 : ℝ)*X 1 2+(4276457777/10000000000 : ℝ)*X 2 0+(1460317/3906250 : ℝ)*X 2 1+(976564479/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1930859359/10000000000 : ℝ)*X 0 0+(635275729/1250000000 : ℝ)*X 0 1+(1119703877/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258534797/10000000000 : ℝ)*X 1 0+(-211017763/1250000000 : ℝ)*X 1 1+(5598519401/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5258534747/10000000000 : ℝ)*X 2 0+(5598519363/10000000000 : ℝ)*X 2 1+(-168814223/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((855463317/2000000000 : ℝ)*X 0 0+(486941441/1000000000 : ℝ)*X 0 1+(938011497/2500000000 : ℝ)*X 0 2+(855463317/2000000000 : ℝ)*X 1 0+(486941441/1000000000 : ℝ)*X 1 1+(938011497/2500000000 : ℝ)*X 1 2+(855463317/2000000000 : ℝ)*X 2 0+(486941441/1000000000 : ℝ)*X 2 1+(938011497/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2029405008904230628780892229/378062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (846113857/100000000000000 : ℝ)*(base19) + (1182942601/100000000000000 : ℝ)*(base23) + (13099857/12500000000000 : ℝ)*(upper3) + (12930647/50000000000000 : ℝ)*(upper4) + (11167063/12500000000000 : ℝ)*(upper5) + (86402413856257/6250000000000 : ℝ)*(major0) + (86402413856257/6250000000000 : ℝ)*(major1) + (86402413856257/6250000000000 : ℝ)*(major2) + (472761501213471/25000000000000 : ℝ)*(sp0) + (472764078222847/25000000000000 : ℝ)*(sp1) + (378211195212529/20000000000000 : ℝ)*(sp2) + (87381564461937/10000000000000 : ℝ)*(sp3) + (5577075681/50000000000000 : ℝ)*(sp4) + (1065211327/25000000000000 : ℝ)*(sp7) + (873819905464677/100000000000000 : ℝ)*(f.failure) + (945528579502623/50000000000000 : ℝ)*(f.sum) + (1019611200099/945156250000000000000000000 : ℝ)*base65 + (2410628226676719257/756125000000000000000000000000000 : ℝ)*base68 + (5687039158322719257/756125000000000000000000000000000 : ℝ)*base70 + (1755605973966030743/756125000000000000000000000000000 : ℝ)*base71 + (3125983585357/1890312500000000000000000000 : ℝ)*base74 + (3699509335408030743/756125000000000000000000000000000 : ℝ)*base75 + (1441837381342219257/756125000000000000000000000000000 : ℝ)*base78 + (2881372136846594257/756125000000000000000000000000000 : ℝ)*base80 + (163443459998637/30245000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (14115533/2000000000000000000000 : ℝ)*base90 + (14115533/2000000000000000000000 : ℝ)*base92 + (14115533/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61165744068672861191126850453/6049000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45091809/50000000000000 : ℝ)*(base1) + (520401321/25000000000000 : ℝ)*(base19) + (2055083339/100000000000000 : ℝ)*(base23) + (120277163/50000000000000 : ℝ)*(upper3) + (109655243/50000000000000 : ℝ)*(upper5) + (1415883796736283/100000000000000 : ℝ)*(major0) + (1415883796736283/100000000000000 : ℝ)*(major1) + (1415883796736283/100000000000000 : ℝ)*(major2) + (12024109873/100000000000000 : ℝ)*(sp1) + (2343102873/20000000000000 : ℝ)*(sp2) + (19368072188999/1000000000000 : ℝ)*(sp4) + (15494344184009/800000000000 : ℝ)*(sp5) + (968396679059289/50000000000000 : ℝ)*(sp6) + (894960037515603/100000000000000 : ℝ)*(sp7) + (894960127699221/100000000000000 : ℝ)*(f.failure) + (968403564358141/50000000000000 : ℝ)*(f.sum) + (129049273415327/120980000000000000000000000000 : ℝ)*base66 + (128756598562877233283/12098000000000000000000000000000000 : ℝ)*base68 + (12372099281809233283/12098000000000000000000000000000000 : ℝ)*base70 + (103770786512505233283/12098000000000000000000000000000000 : ℝ)*base72 + (570476206677847/120980000000000000000000000000 : ℝ)*base74 + (85852980110103233283/12098000000000000000000000000000000 : ℝ)*base76 + (143820398353095233283/12098000000000000000000000000000000 : ℝ)*base78 + (144803023415679233283/12098000000000000000000000000000000 : ℝ)*base80 + (240064449221953/120980000000000000000000000000 : ℝ)*base81 + (1850109/2000000000000000000000 : ℝ)*base90 + (1850109/2000000000000000000000 : ℝ)*base92 + (1850109/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1430_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26251/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (411/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (383/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (471/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1430_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1430_s2_0 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-49087927/250000000 : ℝ)*x 0 + (5457953/10000000 : ℝ)*x 1 + (1300399901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49087927/250000000 : ℝ)^2195 ≤ (11966375980379/100000000000000 : ℝ)^1683 := by
    have hnat : (49087927 : ℕ)^2195*100000000000000^1683 ≤ 11966375980379^1683*250000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49087927 250000000 11966375980379 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457953/10000000 : ℝ)^2195 ≤ (2269861465879/5000000000000 : ℝ)^1683 := by
    have hnat : (5457953 : ℕ)^2195*5000000000000^1683 ≤ 2269861465879^1683*10000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457953 10000000 2269861465879 5000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1300399901/2500000000 : ℝ)^2195 ≤ (42636394682893/100000000000000 : ℝ)^1683 := by
    have hnat : (1300399901 : ℕ)^2195*100000000000000^1683 ≤ 42636394682893^1683*2500000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300399901 2500000000 42636394682893 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-49087927/250000000 : ℝ), (5457953/10000000 : ℝ), (1300399901/2500000000 : ℝ)] ![(11966375980379/100000000000000 : ℝ), (2269861465879/5000000000000 : ℝ), (42636394682893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-49087927/250000000 : ℝ)|^2195 ≤ (11966375980379/100000000000000 : ℝ)^1683
        have hw : |(-49087927/250000000 : ℝ)|=(49087927/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457953/10000000 : ℝ)|^2195 ≤ (2269861465879/5000000000000 : ℝ)^1683
        have hw : |(5457953/10000000 : ℝ)|=(5457953/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1300399901/2500000000 : ℝ)|^2195 ≤ (42636394682893/100000000000000 : ℝ)^1683
        have hw : |(1300399901/2500000000 : ℝ)|=(1300399901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s2_1 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5360078601/10000000000 : ℝ)*x 0 + (-2095404033/10000000000 : ℝ)*x 1 + (5201599497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360078601/10000000000 : ℝ)^2195 ≤ (22169197687099/50000000000000 : ℝ)^1683 := by
    have hnat : (5360078601 : ℕ)^2195*50000000000000^1683 ≤ 22169197687099^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360078601 10000000000 22169197687099 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2095404033/10000000000 : ℝ)^2195 ≤ (6512605533249/50000000000000 : ℝ)^1683 := by
    have hnat : (2095404033 : ℕ)^2195*50000000000000^1683 ≤ 6512605533249^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095404033 10000000000 6512605533249 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5201599497/10000000000 : ℝ)^2195 ≤ (2131819676951/5000000000000 : ℝ)^1683 := by
    have hnat : (5201599497 : ℕ)^2195*5000000000000^1683 ≤ 2131819676951^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201599497 10000000000 2131819676951 5000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360078601/10000000000 : ℝ), (-2095404033/10000000000 : ℝ), (5201599497/10000000000 : ℝ)] ![(22169197687099/50000000000000 : ℝ), (6512605533249/50000000000000 : ℝ), (2131819676951/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360078601/10000000000 : ℝ)|^2195 ≤ (22169197687099/50000000000000 : ℝ)^1683
        have hw : |(5360078601/10000000000 : ℝ)|=(5360078601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2095404033/10000000000 : ℝ)|^2195 ≤ (6512605533249/50000000000000 : ℝ)^1683
        have hw : |(-2095404033/10000000000 : ℝ)|=(2095404033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5201599497/10000000000 : ℝ)|^2195 ≤ (2131819676951/5000000000000 : ℝ)^1683
        have hw : |(5201599497/10000000000 : ℝ)|=(5201599497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s2_2 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2680039107/5000000000 : ℝ)*x 0 + (1040319987/2000000000 : ℝ)*x 1 + (-209540397/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680039107/5000000000 : ℝ)^2195 ≤ (44338391199067/100000000000000 : ℝ)^1683 := by
    have hnat : (2680039107 : ℕ)^2195*100000000000000^1683 ≤ 44338391199067^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680039107 5000000000 44338391199067 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040319987/2000000000 : ℝ)^2195 ≤ (5329549777677/12500000000000 : ℝ)^1683 := by
    have hnat : (1040319987 : ℕ)^2195*12500000000000^1683 ≤ 5329549777677^1683*2000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040319987 2000000000 5329549777677 12500000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209540397/1000000000 : ℝ)^2195 ≤ (3256302638937/25000000000000 : ℝ)^1683 := by
    have hnat : (209540397 : ℕ)^2195*25000000000000^1683 ≤ 3256302638937^1683*1000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209540397 1000000000 3256302638937 25000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680039107/5000000000 : ℝ), (1040319987/2000000000 : ℝ), (-209540397/1000000000 : ℝ)] ![(44338391199067/100000000000000 : ℝ), (5329549777677/12500000000000 : ℝ), (3256302638937/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680039107/5000000000 : ℝ)|^2195 ≤ (44338391199067/100000000000000 : ℝ)^1683
        have hw : |(2680039107/5000000000 : ℝ)|=(2680039107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040319987/2000000000 : ℝ)|^2195 ≤ (5329549777677/12500000000000 : ℝ)^1683
        have hw : |(1040319987/2000000000 : ℝ)|=(1040319987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209540397/1000000000 : ℝ)|^2195 ≤ (3256302638937/25000000000000 : ℝ)^1683
        have hw : |(-209540397/1000000000 : ℝ)|=(209540397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s2_3 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2149897311/5000000000 : ℝ)*x 0 + (4030432357/10000000000 : ℝ)*x 1 + (229260693/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149897311/5000000000 : ℝ)^2195 ≤ (16630513982321/50000000000000 : ℝ)^1683 := by
    have hnat : (2149897311 : ℕ)^2195*50000000000000^1683 ≤ 16630513982321^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149897311 5000000000 16630513982321 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4030432357/10000000000 : ℝ)^2195 ≤ (7642443739511/25000000000000 : ℝ)^1683 := by
    have hnat : (4030432357 : ℕ)^2195*25000000000000^1683 ≤ 7642443739511^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030432357 10000000000 7642443739511 25000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229260693/500000000 : ℝ)^2195 ≤ (18084598528731/50000000000000 : ℝ)^1683 := by
    have hnat : (229260693 : ℕ)^2195*50000000000000^1683 ≤ 18084598528731^1683*500000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229260693 500000000 18084598528731 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149897311/5000000000 : ℝ), (4030432357/10000000000 : ℝ), (229260693/500000000 : ℝ)] ![(16630513982321/50000000000000 : ℝ), (7642443739511/25000000000000 : ℝ), (18084598528731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149897311/5000000000 : ℝ)|^2195 ≤ (16630513982321/50000000000000 : ℝ)^1683
        have hw : |(2149897311/5000000000 : ℝ)|=(2149897311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4030432357/10000000000 : ℝ)|^2195 ≤ (7642443739511/25000000000000 : ℝ)^1683
        have hw : |(4030432357/10000000000 : ℝ)|=(4030432357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(229260693/500000000 : ℝ)|^2195 ≤ (18084598528731/50000000000000 : ℝ)^1683
        have hw : |(229260693/500000000 : ℝ)|=(229260693/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s2_4 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-490890617/2500000000 : ℝ)*x 0 + (1300766181/2500000000 : ℝ)*x 1 + (5456475787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490890617/2500000000 : ℝ)^2195 ≤ (1196673674251/10000000000000 : ℝ)^1683 := by
    have hnat : (490890617 : ℕ)^2195*10000000000000^1683 ≤ 1196673674251^1683*2500000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490890617 2500000000 1196673674251 10000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1300766181/2500000000 : ℝ)^2195 ≤ (42652058073039/100000000000000 : ℝ)^1683 := by
    have hnat : (1300766181 : ℕ)^2195*100000000000000^1683 ≤ 42652058073039^1683*2500000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300766181 2500000000 42652058073039 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456475787/10000000000 : ℝ)^2195 ≤ (45381205160081/100000000000000 : ℝ)^1683 := by
    have hnat : (5456475787 : ℕ)^2195*100000000000000^1683 ≤ 45381205160081^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456475787 10000000000 45381205160081 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-490890617/2500000000 : ℝ), (1300766181/2500000000 : ℝ), (5456475787/10000000000 : ℝ)] ![(1196673674251/10000000000000 : ℝ), (42652058073039/100000000000000 : ℝ), (45381205160081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-490890617/2500000000 : ℝ)|^2195 ≤ (1196673674251/10000000000000 : ℝ)^1683
        have hw : |(-490890617/2500000000 : ℝ)|=(490890617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1300766181/2500000000 : ℝ)|^2195 ≤ (42652058073039/100000000000000 : ℝ)^1683
        have hw : |(1300766181/2500000000 : ℝ)|=(1300766181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456475787/10000000000 : ℝ)|^2195 ≤ (45381205160081/100000000000000 : ℝ)^1683
        have hw : |(5456475787/10000000000 : ℝ)|=(5456475787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s2_5 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5293411837/10000000000 : ℝ)*x 0 + (-1840527449/10000000000 : ℝ)*x 1 + (5456476237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293411837/10000000000 : ℝ)^2195 ≤ (43620528691191/100000000000000 : ℝ)^1683 := by
    have hnat : (5293411837 : ℕ)^2195*100000000000000^1683 ≤ 43620528691191^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293411837 10000000000 43620528691191 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1840527449/10000000000 : ℝ)^2195 ≤ (10998261258843/100000000000000 : ℝ)^1683 := by
    have hnat : (1840527449 : ℕ)^2195*100000000000000^1683 ≤ 10998261258843^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840527449 10000000000 10998261258843 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456476237/10000000000 : ℝ)^2195 ≤ (22690605020641/50000000000000 : ℝ)^1683 := by
    have hnat : (5456476237 : ℕ)^2195*50000000000000^1683 ≤ 22690605020641^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456476237 10000000000 22690605020641 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293411837/10000000000 : ℝ), (-1840527449/10000000000 : ℝ), (5456476237/10000000000 : ℝ)] ![(43620528691191/100000000000000 : ℝ), (10998261258843/100000000000000 : ℝ), (22690605020641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293411837/10000000000 : ℝ)|^2195 ≤ (43620528691191/100000000000000 : ℝ)^1683
        have hw : |(5293411837/10000000000 : ℝ)|=(5293411837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1840527449/10000000000 : ℝ)|^2195 ≤ (10998261258843/100000000000000 : ℝ)^1683
        have hw : |(-1840527449/10000000000 : ℝ)|=(1840527449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456476237/10000000000 : ℝ)|^2195 ≤ (22690605020641/50000000000000 : ℝ)^1683
        have hw : |(5456476237/10000000000 : ℝ)|=(5456476237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s2_6 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5293411719/10000000000 : ℝ)*x 0 + (2728238103/5000000000 : ℝ)*x 1 + (-368105531/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293411719/10000000000 : ℝ)^2195 ≤ (2726282963937/6250000000000 : ℝ)^1683 := by
    have hnat : (5293411719 : ℕ)^2195*6250000000000^1683 ≤ 2726282963937^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293411719 10000000000 2726282963937 6250000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728238103/5000000000 : ℝ)^2195 ≤ (22690604852511/50000000000000 : ℝ)^1683 := by
    have hnat : (2728238103 : ℕ)^2195*50000000000000^1683 ≤ 22690604852511^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728238103 5000000000 22690604852511 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (368105531/2000000000 : ℝ)^2195 ≤ (5499131432151/50000000000000 : ℝ)^1683 := by
    have hnat : (368105531 : ℕ)^2195*50000000000000^1683 ≤ 5499131432151^1683*2000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368105531 2000000000 5499131432151 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293411719/10000000000 : ℝ), (2728238103/5000000000 : ℝ), (-368105531/2000000000 : ℝ)] ![(2726282963937/6250000000000 : ℝ), (22690604852511/50000000000000 : ℝ), (5499131432151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293411719/10000000000 : ℝ)|^2195 ≤ (2726282963937/6250000000000 : ℝ)^1683
        have hw : |(5293411719/10000000000 : ℝ)|=(5293411719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728238103/5000000000 : ℝ)|^2195 ≤ (22690604852511/50000000000000 : ℝ)^1683
        have hw : |(2728238103/5000000000 : ℝ)|=(2728238103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-368105531/2000000000 : ℝ)|^2195 ≤ (5499131432151/50000000000000 : ℝ)^1683
        have hw : |(-368105531/2000000000 : ℝ)|=(368105531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s2_7 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074973169/2500000000 : ℝ)*x 0 + (4582043479/10000000000 : ℝ)*x 1 + (4033628859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074973169/2500000000 : ℝ)^2195 ≤ (8315504303163/25000000000000 : ℝ)^1683 := by
    have hnat : (1074973169 : ℕ)^2195*25000000000000^1683 ≤ 8315504303163^1683*2500000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074973169 2500000000 8315504303163 25000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4582043479/10000000000 : ℝ)^2195 ≤ (9034145926133/25000000000000 : ℝ)^1683 := by
    have hnat : (4582043479 : ℕ)^2195*25000000000000^1683 ≤ 9034145926133^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582043479 10000000000 9034145926133 25000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033628859/10000000000 : ℝ)^2195 ≤ (3060139907249/10000000000000 : ℝ)^1683 := by
    have hnat : (4033628859 : ℕ)^2195*10000000000000^1683 ≤ 3060139907249^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033628859 10000000000 3060139907249 10000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074973169/2500000000 : ℝ), (4582043479/10000000000 : ℝ), (4033628859/10000000000 : ℝ)] ![(8315504303163/25000000000000 : ℝ), (9034145926133/25000000000000 : ℝ), (3060139907249/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074973169/2500000000 : ℝ)|^2195 ≤ (8315504303163/25000000000000 : ℝ)^1683
        have hw : |(1074973169/2500000000 : ℝ)|=(1074973169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4582043479/10000000000 : ℝ)|^2195 ≤ (9034145926133/25000000000000 : ℝ)^1683
        have hw : |(4582043479/10000000000 : ℝ)|=(4582043479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033628859/10000000000 : ℝ)|^2195 ≤ (3060139907249/10000000000000 : ℝ)^1683
        have hw : |(4033628859/10000000000 : ℝ)|=(4033628859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1430_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (471/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (383/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (10373/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15797/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (471/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (383/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (471/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (383/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (471/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (383/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (471/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (383/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (471/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (383/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (471/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (383/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (383/5000 : ℝ) ^ (4389/1024 : ℝ) ≤ (412663756201063/25000000000000000000 : ℝ) := by
    have hpowers : (383/5000 : ℝ)^4389 ≤ (412663756201063/25000000000000000000 : ℝ)^1024 := by
      have hnat : (383 : ℕ)^4389*25000000000000000000^1024 ≤ 412663756201063^1024*5000^4389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        383 5000 412663756201063 25000000000000000000 4389 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (383/5000 : ℝ)) (X := (412663756201063/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (471/2500 : ℝ) ^ (4389/1024 : ℝ) ≤ (19536216575070961/25000000000000000000 : ℝ) := by
    have hpowers : (471/2500 : ℝ)^4389 ≤ (19536216575070961/25000000000000000000 : ℝ)^1024 := by
      have hnat : (471 : ℕ)^4389*25000000000000000000^1024 ≤ 19536216575070961^1024*2500^4389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        471 2500 19536216575070961 25000000000000000000 4389 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (471/2500 : ℝ)) (X := (19536216575070961/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500412663756201063/12500000000000000000 : ℝ) ≤ (2000015404414261/2000000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (12500412663756201063/12500000000000000000 : ℝ)^1024 ≤ (2000015404414261/2000000000000000 : ℝ)^4389 := by
      have hnat : (12500412663756201063 : ℕ)^1024*2000000000000000^4389 ≤ 2000015404414261^4389*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500412663756201063 12500000000000000000 2000015404414261 2000000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000015404414261/2000000000000000 : ℝ)) (X := (12500412663756201063/12500000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3127493610041409003/3125000000000000000 : ℝ) ≤ (10001861144473889/10000000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (3127493610041409003/3125000000000000000 : ℝ)^1024 ≤ (10001861144473889/10000000000000000 : ℝ)^4389 := by
      have hnat : (3127493610041409003 : ℕ)^1024*10000000000000000^4389 ≤ 10001861144473889^4389*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127493610041409003 3125000000000000000 10001861144473889 10000000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001861144473889/10000000000000000 : ℝ)) (X := (3127493610041409003/3125000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12519536216575070961/12500000000000000000 : ℝ) ≤ (10003645266876473/10000000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (12519536216575070961/12500000000000000000 : ℝ)^1024 ≤ (10003645266876473/10000000000000000 : ℝ)^4389 := by
      have hnat : (12519536216575070961 : ℕ)^1024*10000000000000000^4389 ≤ 10003645266876473^4389*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12519536216575070961 12500000000000000000 10003645266876473 10000000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003645266876473/10000000000000000 : ℝ)) (X := (12519536216575070961/12500000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(412663756201063/25000000000000000000 : ℝ) ≤ ((5588676417577480151/5590000000000000000 : ℝ)+2*(223015300323/139750000000000 : ℝ)*(383/5000 : ℝ))^(4389/1024 : ℝ) := by
    rw [show (5588676417577480151/5590000000000000000 : ℝ)+2*(223015300323/139750000000000 : ℝ)*(383/5000 : ℝ)=(2000015404414261/2000000000000000 : ℝ) by norm_num, show 1+2*(412663756201063/25000000000000000000 : ℝ)=(12500412663756201063/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19536216575070961/25000000000000000000 : ℝ)+(412663756201063/25000000000000000000 : ℝ) ≤ ((5588676417577480151/5590000000000000000 : ℝ)+(223015300323/139750000000000 : ℝ)*((471/2500 : ℝ)+(383/5000 : ℝ)))^(4389/1024 : ℝ) := by
    rw [show (5588676417577480151/5590000000000000000 : ℝ)+(223015300323/139750000000000 : ℝ)*((471/2500 : ℝ)+(383/5000 : ℝ))=(10001861144473889/10000000000000000 : ℝ) by norm_num, show 1+(19536216575070961/25000000000000000000 : ℝ)+(412663756201063/25000000000000000000 : ℝ)=(3127493610041409003/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19536216575070961/25000000000000000000 : ℝ) ≤ ((5588676417577480151/5590000000000000000 : ℝ)+2*(223015300323/139750000000000 : ℝ)*(471/2500 : ℝ))^(4389/1024 : ℝ) := by
    rw [show (5588676417577480151/5590000000000000000 : ℝ)+2*(223015300323/139750000000000 : ℝ)*(471/2500 : ℝ)=(10003645266876473/10000000000000000 : ℝ) by norm_num, show 1+2*(19536216575070961/25000000000000000000 : ℝ)=(12519536216575070961/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5588676417577480151/5590000000000000000 : ℝ)*(X 1 0+X 2 0)+(223015300323/139750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (383/5000 : ℝ)) (hi := (471/2500 : ℝ)) (c := (5588676417577480151/5590000000000000000 : ℝ)) (alpha := (223015300323/139750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5588676417577480151/5590000000000000000 : ℝ)*(X 0 1+X 2 1)+(223015300323/139750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (383/5000 : ℝ)) (hi := (471/2500 : ℝ)) (c := (5588676417577480151/5590000000000000000 : ℝ)) (alpha := (223015300323/139750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5588676417577480151/5590000000000000000 : ℝ)*(X 0 2+X 1 2)+(223015300323/139750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (383/5000 : ℝ)) (hi := (471/2500 : ℝ)) (c := (5588676417577480151/5590000000000000000 : ℝ)) (alpha := (223015300323/139750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-49087927/250000000 : ℝ)*X 0 0+(5457953/10000000 : ℝ)*X 0 1+(1300399901/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5360078601/10000000000 : ℝ)*X 1 0+(-2095404033/10000000000 : ℝ)*X 1 1+(5201599497/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2680039107/5000000000 : ℝ)*X 2 0+(1040319987/2000000000 : ℝ)*X 2 1+(-209540397/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2149897311/5000000000 : ℝ)*X 0 0+(4030432357/10000000000 : ℝ)*X 0 1+(229260693/500000000 : ℝ)*X 0 2+(2149897311/5000000000 : ℝ)*X 1 0+(4030432357/10000000000 : ℝ)*X 1 1+(229260693/500000000 : ℝ)*X 1 2+(2149897311/5000000000 : ℝ)*X 2 0+(4030432357/10000000000 : ℝ)*X 2 1+(229260693/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-490890617/2500000000 : ℝ)*X 0 0+(1300766181/2500000000 : ℝ)*X 0 1+(5456475787/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293411837/10000000000 : ℝ)*X 1 0+(-1840527449/10000000000 : ℝ)*X 1 1+(5456476237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293411719/10000000000 : ℝ)*X 2 0+(2728238103/5000000000 : ℝ)*X 2 1+(-368105531/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1074973169/2500000000 : ℝ)*X 0 0+(4582043479/10000000000 : ℝ)*X 0 1+(4033628859/10000000000 : ℝ)*X 0 2+(1074973169/2500000000 : ℝ)*X 1 0+(4582043479/10000000000 : ℝ)*X 1 1+(4033628859/10000000000 : ℝ)*X 1 2+(1074973169/2500000000 : ℝ)*X 2 0+(4582043479/10000000000 : ℝ)*X 2 1+(4033628859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1467932515656476498833379571/279500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118651219/20000000000000 : ℝ)*(base19) + (24188781/25000000000000 : ℝ)*(base23) + (57582299/50000000000000 : ℝ)*(lower2) + (88898509/50000000000000 : ℝ)*(upper3) + (7734587/100000000000000 : ℝ)*(upper5) + (2851695283601193/100000000000000 : ℝ)*(major0) + (2851695283601193/100000000000000 : ℝ)*(major1) + (2851695283601193/100000000000000 : ℝ)*(major2) + (1950435785077821/50000000000000 : ℝ)*(sp0) + (243804595770203/6250000000000 : ℝ)*(sp1) + (195043701441211/5000000000000 : ℝ)*(sp2) + (1802513012782037/100000000000000 : ℝ)*(sp3) + (2555423701/100000000000000 : ℝ)*(sp4) + (3253774507/100000000000000 : ℝ)*(sp7) + (14082158332473/781250000000 : ℝ)*(f.failure) + (243804632848709/6250000000000 : ℝ)*(f.sum) + (3165127843343/3493750000000000000000000000 : ℝ)*base66 + (634022211596980143/559000000000000000000000000000000 : ℝ)*base67 + (509525531678980143/559000000000000000000000000000000 : ℝ)*base69 + (2588945156324980143/559000000000000000000000000000000 : ℝ)*base71 + (6543634606407/3493750000000000000000000000 : ℝ)*base73 + (3662166575919980143/559000000000000000000000000000000 : ℝ)*base75 + (898056054563019857/559000000000000000000000000000000 : ℝ)*base78 + (5297513470787019857/559000000000000000000000000000000 : ℝ)*base80 + (4165659532003/13975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (113067/15625000000000000000 : ℝ)*base90 + (113067/15625000000000000000 : ℝ)*base92 + (113067/15625000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (105627861931082145007292409/8734375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (728045091/50000000000000 : ℝ)*(base19) + (821939119/50000000000000 : ℝ)*(base23) + (314194929/100000000000000 : ℝ)*(upper3) + (32401703/25000000000000 : ℝ)*(lower4) + (9014563/5000000000000 : ℝ)*(upper5) + (90149854338261/3125000000000 : ℝ)*(major0) + (90149854338261/3125000000000 : ℝ)*(major1) + (90149854338261/3125000000000 : ℝ)*(major2) + (10298310119/50000000000000 : ℝ)*(sp1) + (11525483407/50000000000000 : ℝ)*(sp2) + (1973075965549907/50000000000000 : ℝ)*(sp4) + (3946129878389393/100000000000000 : ℝ)*(sp5) + (1973063618127381/50000000000000 : ℝ)*(sp6) + (364687668687437/20000000000000 : ℝ)*(sp7) + (364687668687437/20000000000000 : ℝ)*(f.failure) + (1973075965549907/50000000000000 : ℝ)*(f.sum) + (5245917655523/3493750000000000000000000000 : ℝ)*base65 + (69692946155446161/17468750000000000000000000000000 : ℝ)*base67 + (179620338394883661/17468750000000000000000000000000 : ℝ)*base69 + (279482133399446161/17468750000000000000000000000000 : ℝ)*base71 + (1815399361469/436718750000000000000000000 : ℝ)*base74 + (262649817075164911/17468750000000000000000000000000 : ℝ)*base75 + (2987101572585089/17468750000000000000000000000000 : ℝ)*base78 + (243500218098133661/17468750000000000000000000000000 : ℝ)*base79 + (13591193737983/13975000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (412427/400000000000000000000 : ℝ)*base89 + (412427/400000000000000000000 : ℝ)*base91 + (412427/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1430_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (471/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (383/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15797/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1430_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1430_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15797/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1430_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1430_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1430_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15797/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1430_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

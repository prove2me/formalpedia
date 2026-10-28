-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1122_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:09:43.318959+00:00
-- url     : https://prove2.me/submissions/68f47b73-1e39-4401-ae81-9b112e283a12

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
theorem support_rectangle_w1122_s6_0 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2176450347/10000000000 : ℝ)*x 0 + (337111483/625000000 : ℝ)*x 1 + (5265044791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176450347/10000000000 : ℝ)^8315 ≤ (13223028534211/100000000000000 : ℝ)^6267 := by
    have hnat : (2176450347 : ℕ)^8315*100000000000000^6267 ≤ 13223028534211^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176450347 10000000000 13223028534211 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337111483/625000000 : ℝ)^8315 ≤ (44083768447813/100000000000000 : ℝ)^6267 := by
    have hnat : (337111483 : ℕ)^8315*100000000000000^6267 ≤ 44083768447813^6267*625000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337111483 625000000 44083768447813 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265044791/10000000000 : ℝ)^8315 ≤ (42693203002057/100000000000000 : ℝ)^6267 := by
    have hnat : (5265044791 : ℕ)^8315*100000000000000^6267 ≤ 42693203002057^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265044791 10000000000 42693203002057 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2176450347/10000000000 : ℝ), (337111483/625000000 : ℝ), (5265044791/10000000000 : ℝ)] ![(13223028534211/100000000000000 : ℝ), (44083768447813/100000000000000 : ℝ), (42693203002057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2176450347/10000000000 : ℝ)|^8315 ≤ (13223028534211/100000000000000 : ℝ)^6267
        have hw : |(-2176450347/10000000000 : ℝ)|=(2176450347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337111483/625000000 : ℝ)|^8315 ≤ (44083768447813/100000000000000 : ℝ)^6267
        have hw : |(337111483/625000000 : ℝ)|=(337111483/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265044791/10000000000 : ℝ)|^8315 ≤ (42693203002057/100000000000000 : ℝ)^6267
        have hw : |(5265044791/10000000000 : ℝ)|=(5265044791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s6_1 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (83514481/156250000 : ℝ)*x 0 + (-448351919/2000000000 : ℝ)*x 1 + (5265044791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83514481/156250000 : ℝ)^8315 ≤ (348438013039/800000000000 : ℝ)^6267 := by
    have hnat : (83514481 : ℕ)^8315*800000000000^6267 ≤ 348438013039^6267*156250000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83514481 156250000 348438013039 800000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448351919/2000000000 : ℝ)^8315 ≤ (6876022679507/50000000000000 : ℝ)^6267 := by
    have hnat : (448351919 : ℕ)^8315*50000000000000^6267 ≤ 6876022679507^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448351919 2000000000 6876022679507 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265044791/10000000000 : ℝ)^8315 ≤ (42693203002057/100000000000000 : ℝ)^6267 := by
    have hnat : (5265044791 : ℕ)^8315*100000000000000^6267 ≤ 42693203002057^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265044791 10000000000 42693203002057 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83514481/156250000 : ℝ), (-448351919/2000000000 : ℝ), (5265044791/10000000000 : ℝ)] ![(348438013039/800000000000 : ℝ), (6876022679507/50000000000000 : ℝ), (42693203002057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83514481/156250000 : ℝ)|^8315 ≤ (348438013039/800000000000 : ℝ)^6267
        have hw : |(83514481/156250000 : ℝ)|=(83514481/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-448351919/2000000000 : ℝ)|^8315 ≤ (6876022679507/50000000000000 : ℝ)^6267
        have hw : |(-448351919/2000000000 : ℝ)|=(448351919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265044791/10000000000 : ℝ)|^8315 ≤ (42693203002057/100000000000000 : ℝ)^6267
        have hw : |(5265044791/10000000000 : ℝ)|=(5265044791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s6_2 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672463389/5000000000 : ℝ)*x 0 + (5265044797/10000000000 : ℝ)*x 1 + (-1120879797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672463389/5000000000 : ℝ)^8315 ≤ (10888687891251/25000000000000 : ℝ)^6267 := by
    have hnat : (2672463389 : ℕ)^8315*25000000000000^6267 ≤ 10888687891251^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672463389 5000000000 10888687891251 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265044797/10000000000 : ℝ)^8315 ≤ (42693203066609/100000000000000 : ℝ)^6267 := by
    have hnat : (5265044797 : ℕ)^8315*100000000000000^6267 ≤ 42693203066609^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265044797 10000000000 42693203066609 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120879797/5000000000 : ℝ)^8315 ≤ (6876022675437/50000000000000 : ℝ)^6267 := by
    have hnat : (1120879797 : ℕ)^8315*50000000000000^6267 ≤ 6876022675437^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120879797 5000000000 6876022675437 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672463389/5000000000 : ℝ), (5265044797/10000000000 : ℝ), (-1120879797/5000000000 : ℝ)] ![(10888687891251/25000000000000 : ℝ), (42693203066609/100000000000000 : ℝ), (6876022675437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672463389/5000000000 : ℝ)|^8315 ≤ (10888687891251/25000000000000 : ℝ)^6267
        have hw : |(2672463389/5000000000 : ℝ)|=(2672463389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265044797/10000000000 : ℝ)|^8315 ≤ (42693203066609/100000000000000 : ℝ)^6267
        have hw : |(5265044797/10000000000 : ℝ)|=(5265044797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1120879797/5000000000 : ℝ)|^8315 ≤ (6876022675437/50000000000000 : ℝ)^6267
        have hw : |(-1120879797/5000000000 : ℝ)|=(1120879797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s6_3 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873495803/2000000000 : ℝ)*x 0 + (2120891073/5000000000 : ℝ)*x 1 + (2248450283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873495803/2000000000 : ℝ)^8315 ≤ (2082291231721/6250000000000 : ℝ)^6267 := by
    have hnat : (873495803 : ℕ)^8315*6250000000000^6267 ≤ 2082291231721^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873495803 2000000000 2082291231721 6250000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2120891073/5000000000 : ℝ)^8315 ≤ (16025237418973/50000000000000 : ℝ)^6267 := by
    have hnat : (2120891073 : ℕ)^8315*50000000000000^6267 ≤ 16025237418973^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120891073 5000000000 16025237418973 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248450283/5000000000 : ℝ)^8315 ≤ (541138522407/1562500000000 : ℝ)^6267 := by
    have hnat : (2248450283 : ℕ)^8315*1562500000000^6267 ≤ 541138522407^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248450283 5000000000 541138522407 1562500000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873495803/2000000000 : ℝ), (2120891073/5000000000 : ℝ), (2248450283/5000000000 : ℝ)] ![(2082291231721/6250000000000 : ℝ), (16025237418973/50000000000000 : ℝ), (541138522407/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873495803/2000000000 : ℝ)|^8315 ≤ (2082291231721/6250000000000 : ℝ)^6267
        have hw : |(873495803/2000000000 : ℝ)|=(873495803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2120891073/5000000000 : ℝ)|^8315 ≤ (16025237418973/50000000000000 : ℝ)^6267
        have hw : |(2120891073/5000000000 : ℝ)|=(2120891073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248450283/5000000000 : ℝ)|^8315 ≤ (541138522407/1562500000000 : ℝ)^6267
        have hw : |(2248450283/5000000000 : ℝ)|=(2248450283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s6_4 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-435291087/2000000000 : ℝ)*x 0 + (2632684919/5000000000 : ℝ)*x 1 + (5393457449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435291087/2000000000 : ℝ)^8315 ≤ (13223069548199/100000000000000 : ℝ)^6267 := by
    have hnat : (435291087 : ℕ)^8315*100000000000000^6267 ≤ 13223069548199^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435291087 2000000000 13223069548199 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632684919/5000000000 : ℝ)^8315 ≤ (21348350057949/50000000000000 : ℝ)^6267 := by
    have hnat : (2632684919 : ℕ)^8315*50000000000000^6267 ≤ 21348350057949^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632684919 5000000000 21348350057949 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393457449/10000000000 : ℝ)^8315 ≤ (22040115163849/50000000000000 : ℝ)^6267 := by
    have hnat : (5393457449 : ℕ)^8315*50000000000000^6267 ≤ 22040115163849^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393457449 10000000000 22040115163849 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435291087/2000000000 : ℝ), (2632684919/5000000000 : ℝ), (5393457449/10000000000 : ℝ)] ![(13223069548199/100000000000000 : ℝ), (21348350057949/50000000000000 : ℝ), (22040115163849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435291087/2000000000 : ℝ)|^8315 ≤ (13223069548199/100000000000000 : ℝ)^6267
        have hw : |(-435291087/2000000000 : ℝ)|=(435291087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632684919/5000000000 : ℝ)|^8315 ≤ (21348350057949/50000000000000 : ℝ)^6267
        have hw : |(2632684919/5000000000 : ℝ)|=(2632684919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393457449/10000000000 : ℝ)|^8315 ≤ (22040115163849/50000000000000 : ℝ)^6267
        have hw : |(5393457449/10000000000 : ℝ)|=(5393457449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s6_5 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664044871/1250000000 : ℝ)*x 0 + (-2113346947/10000000000 : ℝ)*x 1 + (337091089/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664044871/1250000000 : ℝ)^8315 ≤ (1080074682851/2500000000000 : ℝ)^6267 := by
    have hnat : (664044871 : ℕ)^8315*2500000000000^6267 ≤ 1080074682851^6267*1250000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664044871 1250000000 1080074682851 2500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113346947/10000000000 : ℝ)^8315 ≤ (6358391305817/50000000000000 : ℝ)^6267 := by
    have hnat : (2113346947 : ℕ)^8315*50000000000000^6267 ≤ 6358391305817^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113346947 10000000000 6358391305817 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337091089/625000000 : ℝ)^8315 ≤ (8816046011321/20000000000000 : ℝ)^6267 := by
    have hnat : (337091089 : ℕ)^8315*20000000000000^6267 ≤ 8816046011321^6267*625000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337091089 625000000 8816046011321 20000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664044871/1250000000 : ℝ), (-2113346947/10000000000 : ℝ), (337091089/625000000 : ℝ)] ![(1080074682851/2500000000000 : ℝ), (6358391305817/50000000000000 : ℝ), (8816046011321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664044871/1250000000 : ℝ)|^8315 ≤ (1080074682851/2500000000000 : ℝ)^6267
        have hw : |(664044871/1250000000 : ℝ)|=(664044871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2113346947/10000000000 : ℝ)|^8315 ≤ (6358391305817/50000000000000 : ℝ)^6267
        have hw : |(-2113346947/10000000000 : ℝ)|=(2113346947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337091089/625000000 : ℝ)|^8315 ≤ (8816046011321/20000000000000 : ℝ)^6267
        have hw : |(337091089/625000000 : ℝ)|=(337091089/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s6_6 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328089753/2500000000 : ℝ)*x 0 + (1078691467/2000000000 : ℝ)*x 1 + (-2113347009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328089753/2500000000 : ℝ)^8315 ≤ (5400373473601/12500000000000 : ℝ)^6267 := by
    have hnat : (1328089753 : ℕ)^8315*12500000000000^6267 ≤ 5400373473601^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328089753 2500000000 5400373473601 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078691467/2000000000 : ℝ)^8315 ≤ (5510028636439/12500000000000 : ℝ)^6267 := by
    have hnat : (1078691467 : ℕ)^8315*12500000000000^6267 ≤ 5510028636439^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078691467 2000000000 5510028636439 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113347009/10000000000 : ℝ)^8315 ≤ (12716783106629/100000000000000 : ℝ)^6267 := by
    have hnat : (2113347009 : ℕ)^8315*100000000000000^6267 ≤ 12716783106629^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113347009 10000000000 12716783106629 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328089753/2500000000 : ℝ), (1078691467/2000000000 : ℝ), (-2113347009/10000000000 : ℝ)] ![(5400373473601/12500000000000 : ℝ), (5510028636439/12500000000000 : ℝ), (12716783106629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328089753/2500000000 : ℝ)|^8315 ≤ (5400373473601/12500000000000 : ℝ)^6267
        have hw : |(1328089753/2500000000 : ℝ)|=(1328089753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078691467/2000000000 : ℝ)|^8315 ≤ (5510028636439/12500000000000 : ℝ)^6267
        have hw : |(1078691467/2000000000 : ℝ)|=(1078691467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2113347009/10000000000 : ℝ)|^8315 ≤ (12716783106629/100000000000000 : ℝ)^6267
        have hw : |(-2113347009/10000000000 : ℝ)|=(2113347009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s6_7 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4367488957/10000000000 : ℝ)*x 0 + (4496256287/10000000000 : ℝ)*x 1 + (4242428771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367488957/10000000000 : ℝ)^8315 ≤ (33316760332817/100000000000000 : ℝ)^6267 := by
    have hnat : (4367488957 : ℕ)^8315*100000000000000^6267 ≤ 33316760332817^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367488957 10000000000 33316760332817 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496256287/10000000000 : ℝ)^8315 ≤ (34626282166457/100000000000000 : ℝ)^6267 := by
    have hnat : (4496256287 : ℕ)^8315*100000000000000^6267 ≤ 34626282166457^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496256287 10000000000 34626282166457 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242428771/10000000000 : ℝ)^8315 ≤ (16028478739503/50000000000000 : ℝ)^6267 := by
    have hnat : (4242428771 : ℕ)^8315*50000000000000^6267 ≤ 16028478739503^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242428771 10000000000 16028478739503 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367488957/10000000000 : ℝ), (4496256287/10000000000 : ℝ), (4242428771/10000000000 : ℝ)] ![(33316760332817/100000000000000 : ℝ), (34626282166457/100000000000000 : ℝ), (16028478739503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367488957/10000000000 : ℝ)|^8315 ≤ (33316760332817/100000000000000 : ℝ)^6267
        have hw : |(4367488957/10000000000 : ℝ)|=(4367488957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496256287/10000000000 : ℝ)|^8315 ≤ (34626282166457/100000000000000 : ℝ)^6267
        have hw : |(4496256287/10000000000 : ℝ)|=(4496256287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4242428771/10000000000 : ℝ)|^8315 ≤ (16028478739503/50000000000000 : ℝ)^6267
        have hw : |(4242428771/10000000000 : ℝ)|=(4242428771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1122_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11319/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7023/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5643/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5643/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5643/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5643/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5643/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5643/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5643/50000 : ℝ) ^ (4157/1024 : ℝ) ≤ (1424687776572971/10000000000000000000 : ℝ) := by
    have hpowers : (5643/50000 : ℝ)^4157 ≤ (1424687776572971/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5643 : ℕ)^4157*10000000000000000000^1024 ≤ 1424687776572971^1024*50000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5643 50000 1424687776572971 10000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5643/50000 : ℝ)) (X := (1424687776572971/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14081/100000 : ℝ) ^ (4157/1024 : ℝ) ≤ (34979840543962111/100000000000000000000 : ℝ) := by
    have hpowers : (14081/100000 : ℝ)^4157 ≤ (34979840543962111/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14081 : ℕ)^4157*100000000000000000000^1024 ≤ 34979840543962111^1024*100000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14081 100000 34979840543962111 100000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14081/100000 : ℝ)) (X := (34979840543962111/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001424687776572971/5000000000000000000 : ℝ) ≤ (2000140363114087/2000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (5001424687776572971/5000000000000000000 : ℝ)^1024 ≤ (2000140363114087/2000000000000000 : ℝ)^4157 := by
      have hnat : (5001424687776572971 : ℕ)^1024*2000000000000000^4157 ≤ 2000140363114087^4157*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001424687776572971 5000000000000000000 2000140363114087 2000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000140363114087/2000000000000000 : ℝ)) (X := (5001424687776572971/5000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049226718309691821/100000000000000000000 : ℝ) ≤ (1250151548025521/1250000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (100049226718309691821/100000000000000000000 : ℝ)^1024 ≤ (1250151548025521/1250000000000000 : ℝ)^4157 := by
      have hnat : (100049226718309691821 : ℕ)^1024*1250000000000000^4157 ≤ 1250151548025521^4157*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049226718309691821 100000000000000000000 1250151548025521 1250000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250151548025521/1250000000000000 : ℝ)) (X := (100049226718309691821/100000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034979840543962111/50000000000000000000 : ℝ) ≤ (10001722952837901/10000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (50034979840543962111/50000000000000000000 : ℝ)^1024 ≤ (10001722952837901/10000000000000000 : ℝ)^4157 := by
      have hnat : (50034979840543962111 : ℕ)^1024*10000000000000000^4157 ≤ 10001722952837901^4157*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034979840543962111 50000000000000000000 10001722952837901 10000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001722952837901/10000000000000000 : ℝ)) (X := (50034979840543962111/50000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1424687776572971/10000000000000000000 : ℝ) ≤ ((27940437019318744549/27950000000000000000 : ℝ)+2*(510568633733/279500000000000 : ℝ)*(5643/50000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (27940437019318744549/27950000000000000000 : ℝ)+2*(510568633733/279500000000000 : ℝ)*(5643/50000 : ℝ)=(2000140363114087/2000000000000000 : ℝ) by norm_num, show 1+2*(1424687776572971/10000000000000000000 : ℝ)=(5001424687776572971/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34979840543962111/100000000000000000000 : ℝ)+(1424687776572971/10000000000000000000 : ℝ) ≤ ((27940437019318744549/27950000000000000000 : ℝ)+(510568633733/279500000000000 : ℝ)*((14081/100000 : ℝ)+(5643/50000 : ℝ)))^(4157/1024 : ℝ) := by
    rw [show (27940437019318744549/27950000000000000000 : ℝ)+(510568633733/279500000000000 : ℝ)*((14081/100000 : ℝ)+(5643/50000 : ℝ))=(1250151548025521/1250000000000000 : ℝ) by norm_num, show 1+(34979840543962111/100000000000000000000 : ℝ)+(1424687776572971/10000000000000000000 : ℝ)=(100049226718309691821/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34979840543962111/100000000000000000000 : ℝ) ≤ ((27940437019318744549/27950000000000000000 : ℝ)+2*(510568633733/279500000000000 : ℝ)*(14081/100000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (27940437019318744549/27950000000000000000 : ℝ)+2*(510568633733/279500000000000 : ℝ)*(14081/100000 : ℝ)=(10001722952837901/10000000000000000 : ℝ) by norm_num, show 1+2*(34979840543962111/100000000000000000000 : ℝ)=(50034979840543962111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27940437019318744549/27950000000000000000 : ℝ)*(X 1 0+X 2 0)+(510568633733/279500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (27940437019318744549/27950000000000000000 : ℝ)) (alpha := (510568633733/279500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27940437019318744549/27950000000000000000 : ℝ)*(X 0 1+X 2 1)+(510568633733/279500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (27940437019318744549/27950000000000000000 : ℝ)) (alpha := (510568633733/279500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27940437019318744549/27950000000000000000 : ℝ)*(X 0 2+X 1 2)+(510568633733/279500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (27940437019318744549/27950000000000000000 : ℝ)) (alpha := (510568633733/279500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2176450347/10000000000 : ℝ)*X 0 0+(337111483/625000000 : ℝ)*X 0 1+(5265044791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83514481/156250000 : ℝ)*X 1 0+(-448351919/2000000000 : ℝ)*X 1 1+(5265044791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672463389/5000000000 : ℝ)*X 2 0+(5265044797/10000000000 : ℝ)*X 2 1+(-1120879797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873495803/2000000000 : ℝ)*X 0 0+(2120891073/5000000000 : ℝ)*X 0 1+(2248450283/5000000000 : ℝ)*X 0 2+(873495803/2000000000 : ℝ)*X 1 0+(2120891073/5000000000 : ℝ)*X 1 1+(2248450283/5000000000 : ℝ)*X 1 2+(873495803/2000000000 : ℝ)*X 2 0+(2120891073/5000000000 : ℝ)*X 2 1+(2248450283/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-435291087/2000000000 : ℝ)*X 0 0+(2632684919/5000000000 : ℝ)*X 0 1+(5393457449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664044871/1250000000 : ℝ)*X 1 0+(-2113346947/10000000000 : ℝ)*X 1 1+(337091089/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328089753/2500000000 : ℝ)*X 2 0+(1078691467/2000000000 : ℝ)*X 2 1+(-2113347009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367488957/10000000000 : ℝ)*X 0 0+(4496256287/10000000000 : ℝ)*X 0 1+(4242428771/10000000000 : ℝ)*X 0 2+(4367488957/10000000000 : ℝ)*X 1 0+(4496256287/10000000000 : ℝ)*X 1 1+(4242428771/10000000000 : ℝ)*X 1 2+(4367488957/10000000000 : ℝ)*X 2 0+(4496256287/10000000000 : ℝ)*X 2 1+(4242428771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (959093738879953410549209883/174687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (561036007/50000000000000 : ℝ)*(base19) + (32149757/3125000000000 : ℝ)*(base23) + (11299183/25000000000000 : ℝ)*(lower2) + (143058029/100000000000000 : ℝ)*(upper3) + (79579237/100000000000000 : ℝ)*(upper5) + (1460937463864989/25000000000000 : ℝ)*(major0) + (1460937463864989/25000000000000 : ℝ)*(major1) + (1460937463864989/25000000000000 : ℝ)*(major2) + (7767689679398899/100000000000000 : ℝ)*(sp0) + (31070875163817/400000000000 : ℝ)*(sp1) + (194192972105851/2500000000000 : ℝ)*(sp2) + (783952615929029/20000000000000 : ℝ)*(sp3) + (7558406841/25000000000000 : ℝ)*(sp4) + (3307047433/20000000000000 : ℝ)*(sp7) + (391977961488231/10000000000000 : ℝ)*(f.failure) + (970964989128283/12500000000000 : ℝ)*(f.sum) + (86203448527577/13975000000000000000000000000 : ℝ)*base66 + (210194568050335003/53750000000000000000000000000000 : ℝ)*base68 + (1211718092354085003/53750000000000000000000000000000 : ℝ)*base70 + (92810250458414997/53750000000000000000000000000000 : ℝ)*base71 + (55112301584877/13975000000000000000000000000 : ℝ)*base74 + (783582798372835003/53750000000000000000000000000000 : ℝ)*base76 + (695782397241585003/53750000000000000000000000000000 : ℝ)*base78 + (943770664510335003/53750000000000000000000000000000 : ℝ)*base80 + (84772670391127/13975000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4223223/1000000000000000000000 : ℝ)*base89 + (4223223/1000000000000000000000 : ℝ)*base91 + (4223223/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52696105989587495326107/6987500000000000000000000000 : ℝ) := by norm_num
    linear_combination (837659141/50000000000000 : ℝ)*(base19) + (1712737891/100000000000000 : ℝ)*(base23) + (14478027/10000000000000 : ℝ)*(upper3) + (4652519/100000000000000 : ℝ)*(lower4) + (211763677/100000000000000 : ℝ)*(upper5) + (5873420956792889/100000000000000 : ℝ)*(major0) + (5873420956792889/100000000000000 : ℝ)*(major1) + (5873420956792889/100000000000000 : ℝ)*(major2) + (23652047093/50000000000000 : ℝ)*(sp1) + (20715840377/50000000000000 : ℝ)*(sp2) + (7807159727571823/100000000000000 : ℝ)*(sp4) + (1951777687039839/25000000000000 : ℝ)*(sp5) + (7807116583153179/100000000000000 : ℝ)*(sp6) + (3939681934631207/100000000000000 : ℝ)*(sp7) + (3939681934631207/100000000000000 : ℝ)*(f.failure) + (7807159727571823/100000000000000 : ℝ)*(f.sum) + (75179071564013/13975000000000000000000000000 : ℝ)*base66 + (2129419343413031697/215000000000000000000000000000000 : ℝ)*base67 + (2229008839598031697/215000000000000000000000000000000 : ℝ)*base69 + (2444456352906968303/215000000000000000000000000000000 : ℝ)*base72 + (38991946154203/3493750000000000000000000000 : ℝ)*base73 + (2175069337146968303/215000000000000000000000000000000 : ℝ)*base76 + (1474623028426968303/215000000000000000000000000000000 : ℝ)*base78 + (1760483594178031697/215000000000000000000000000000000 : ℝ)*base79 + (85823577162387/13975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (45264969/10000000000000000000000 : ℝ)*base90 + (45264969/10000000000000000000000 : ℝ)*base92 + (45264969/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1122_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11319/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1122_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1122_s7_0 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2176482407/10000000000 : ℝ)*x 0 + (2696715179/5000000000 : ℝ)*x 1 + (2632688467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176482407/10000000000 : ℝ)^8315 ≤ (13223286967999/100000000000000 : ℝ)^6267 := by
    have hnat : (2176482407 : ℕ)^8315*100000000000000^6267 ≤ 13223286967999^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176482407 10000000000 13223286967999 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696715179/5000000000 : ℝ)^8315 ≤ (22039968280069/50000000000000 : ℝ)^6267 := by
    have hnat : (2696715179 : ℕ)^8315*50000000000000^6267 ≤ 22039968280069^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696715179 5000000000 22039968280069 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632688467/5000000000 : ℝ)^8315 ≤ (4269677646109/10000000000000 : ℝ)^6267 := by
    have hnat : (2632688467 : ℕ)^8315*10000000000000^6267 ≤ 4269677646109^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632688467 5000000000 4269677646109 10000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2176482407/10000000000 : ℝ), (2696715179/5000000000 : ℝ), (2632688467/5000000000 : ℝ)] ![(13223286967999/100000000000000 : ℝ), (22039968280069/50000000000000 : ℝ), (4269677646109/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2176482407/10000000000 : ℝ)|^8315 ≤ (13223286967999/100000000000000 : ℝ)^6267
        have hw : |(-2176482407/10000000000 : ℝ)|=(2176482407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696715179/5000000000 : ℝ)|^8315 ≤ (22039968280069/50000000000000 : ℝ)^6267
        have hw : |(2696715179/5000000000 : ℝ)|=(2696715179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632688467/5000000000 : ℝ)|^8315 ≤ (4269677646109/10000000000000 : ℝ)^6267
        have hw : |(2632688467/5000000000 : ℝ)|=(2632688467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s7_1 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344837659/10000000000 : ℝ)*x 0 + (-2241438921/10000000000 : ℝ)*x 1 + (5265376943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344837659/10000000000 : ℝ)^8315 ≤ (10888447008629/25000000000000 : ℝ)^6267 := by
    have hnat : (5344837659 : ℕ)^8315*25000000000000^6267 ≤ 10888447008629^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344837659 10000000000 10888447008629 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241438921/10000000000 : ℝ)^8315 ≤ (13749435395623/100000000000000 : ℝ)^6267 := by
    have hnat : (2241438921 : ℕ)^8315*100000000000000^6267 ≤ 13749435395623^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241438921 10000000000 13749435395623 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265376943/10000000000 : ℝ)^8315 ≤ (266854853487/625000000000 : ℝ)^6267 := by
    have hnat : (5265376943 : ℕ)^8315*625000000000^6267 ≤ 266854853487^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265376943 10000000000 266854853487 625000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344837659/10000000000 : ℝ), (-2241438921/10000000000 : ℝ), (5265376943/10000000000 : ℝ)] ![(10888447008629/25000000000000 : ℝ), (13749435395623/100000000000000 : ℝ), (266854853487/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344837659/10000000000 : ℝ)|^8315 ≤ (10888447008629/25000000000000 : ℝ)^6267
        have hw : |(5344837659/10000000000 : ℝ)|=(5344837659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2241438921/10000000000 : ℝ)|^8315 ≤ (13749435395623/100000000000000 : ℝ)^6267
        have hw : |(-2241438921/10000000000 : ℝ)|=(2241438921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265376943/10000000000 : ℝ)|^8315 ≤ (266854853487/625000000000 : ℝ)^6267
        have hw : |(5265376943/10000000000 : ℝ)|=(5265376943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s7_2 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344837663/10000000000 : ℝ)*x 0 + (1053075389/2000000000 : ℝ)*x 1 + (-2241438913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344837663/10000000000 : ℝ)^8315 ≤ (43553788077763/100000000000000 : ℝ)^6267 := by
    have hnat : (5344837663 : ℕ)^8315*100000000000000^6267 ≤ 43553788077763^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344837663 10000000000 43553788077763 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053075389/2000000000 : ℝ)^8315 ≤ (21348388289719/50000000000000 : ℝ)^6267 := by
    have hnat : (1053075389 : ℕ)^8315*50000000000000^6267 ≤ 21348388289719^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053075389 2000000000 21348388289719 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241438913/10000000000 : ℝ)^8315 ≤ (13749435330513/100000000000000 : ℝ)^6267 := by
    have hnat : (2241438913 : ℕ)^8315*100000000000000^6267 ≤ 13749435330513^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241438913 10000000000 13749435330513 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344837663/10000000000 : ℝ), (1053075389/2000000000 : ℝ), (-2241438913/10000000000 : ℝ)] ![(43553788077763/100000000000000 : ℝ), (21348388289719/50000000000000 : ℝ), (13749435330513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344837663/10000000000 : ℝ)|^8315 ≤ (43553788077763/100000000000000 : ℝ)^6267
        have hw : |(5344837663/10000000000 : ℝ)|=(5344837663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053075389/2000000000 : ℝ)|^8315 ≤ (21348388289719/50000000000000 : ℝ)^6267
        have hw : |(1053075389/2000000000 : ℝ)|=(1053075389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2241438913/10000000000 : ℝ)|^8315 ≤ (13749435330513/100000000000000 : ℝ)^6267
        have hw : |(-2241438913/10000000000 : ℝ)|=(2241438913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s7_3 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4367496497/10000000000 : ℝ)*x 0 + (33939673/80000000 : ℝ)*x 1 + (899243807/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367496497/10000000000 : ℝ)^8315 ≤ (666336732939/2000000000000 : ℝ)^6267 := by
    have hnat : (4367496497 : ℕ)^8315*2000000000000^6267 ≤ 666336732939^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367496497 10000000000 666336732939 2000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33939673/80000000 : ℝ)^8315 ≤ (32057261796373/100000000000000 : ℝ)^6267 := by
    have hnat : (33939673 : ℕ)^8315*100000000000000^6267 ≤ 32057261796373^6267*80000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33939673 80000000 32057261796373 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899243807/2000000000 : ℝ)^8315 ≤ (8656475383379/25000000000000 : ℝ)^6267 := by
    have hnat : (899243807 : ℕ)^8315*25000000000000^6267 ≤ 8656475383379^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899243807 2000000000 8656475383379 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367496497/10000000000 : ℝ), (33939673/80000000 : ℝ), (899243807/2000000000 : ℝ)] ![(666336732939/2000000000000 : ℝ), (32057261796373/100000000000000 : ℝ), (8656475383379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367496497/10000000000 : ℝ)|^8315 ≤ (666336732939/2000000000000 : ℝ)^6267
        have hw : |(4367496497/10000000000 : ℝ)|=(4367496497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33939673/80000000 : ℝ)|^8315 ≤ (32057261796373/100000000000000 : ℝ)^6267
        have hw : |(33939673/80000000 : ℝ)|=(33939673/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899243807/2000000000 : ℝ)|^8315 ≤ (8656475383379/25000000000000 : ℝ)^6267
        have hw : |(899243807/2000000000 : ℝ)|=(899243807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s7_4 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-136030459/625000000 : ℝ)*x 0 + (2632849287/5000000000 : ℝ)*x 1 + (5393107557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136030459/625000000 : ℝ)^8315 ≤ (6611663382489/50000000000000 : ℝ)^6267 := by
    have hnat : (136030459 : ℕ)^8315*50000000000000^6267 ≤ 6611663382489^6267*625000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136030459 625000000 6611663382489 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632849287/5000000000 : ℝ)^8315 ≤ (1334382405959/3125000000000 : ℝ)^6267 := by
    have hnat : (2632849287 : ℕ)^8315*3125000000000^6267 ≤ 1334382405959^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632849287 5000000000 1334382405959 3125000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393107557/10000000000 : ℝ)^8315 ≤ (22038218114753/50000000000000 : ℝ)^6267 := by
    have hnat : (5393107557 : ℕ)^8315*50000000000000^6267 ≤ 22038218114753^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393107557 10000000000 22038218114753 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136030459/625000000 : ℝ), (2632849287/5000000000 : ℝ), (5393107557/10000000000 : ℝ)] ![(6611663382489/50000000000000 : ℝ), (1334382405959/3125000000000 : ℝ), (22038218114753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136030459/625000000 : ℝ)|^8315 ≤ (6611663382489/50000000000000 : ℝ)^6267
        have hw : |(-136030459/625000000 : ℝ)|=(136030459/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632849287/5000000000 : ℝ)|^8315 ≤ (1334382405959/3125000000000 : ℝ)^6267
        have hw : |(2632849287/5000000000 : ℝ)|=(2632849287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393107557/10000000000 : ℝ)|^8315 ≤ (22038218114753/50000000000000 : ℝ)^6267
        have hw : |(5393107557/10000000000 : ℝ)|=(5393107557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s7_5 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312443193/10000000000 : ℝ)*x 0 + (-1056854153/5000000000 : ℝ)*x 1 + (107862151/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312443193/10000000000 : ℝ)^8315 ≤ (43203896119793/100000000000000 : ℝ)^6267 := by
    have hnat : (5312443193 : ℕ)^8315*100000000000000^6267 ≤ 43203896119793^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312443193 10000000000 43203896119793 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056854153/5000000000 : ℝ)^8315 ≤ (12719667705943/100000000000000 : ℝ)^6267 := by
    have hnat : (1056854153 : ℕ)^8315*100000000000000^6267 ≤ 12719667705943^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056854153 5000000000 12719667705943 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107862151/200000000 : ℝ)^8315 ≤ (44076436153601/100000000000000 : ℝ)^6267 := by
    have hnat : (107862151 : ℕ)^8315*100000000000000^6267 ≤ 44076436153601^6267*200000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107862151 200000000 44076436153601 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312443193/10000000000 : ℝ), (-1056854153/5000000000 : ℝ), (107862151/200000000 : ℝ)] ![(43203896119793/100000000000000 : ℝ), (12719667705943/100000000000000 : ℝ), (44076436153601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312443193/10000000000 : ℝ)|^8315 ≤ (43203896119793/100000000000000 : ℝ)^6267
        have hw : |(5312443193/10000000000 : ℝ)|=(5312443193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1056854153/5000000000 : ℝ)|^8315 ≤ (12719667705943/100000000000000 : ℝ)^6267
        have hw : |(-1056854153/5000000000 : ℝ)|=(1056854153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107862151/200000000 : ℝ)|^8315 ≤ (44076436153601/100000000000000 : ℝ)^6267
        have hw : |(107862151/200000000 : ℝ)|=(107862151/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s7_6 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328110799/2500000000 : ℝ)*x 0 + (2696553773/5000000000 : ℝ)*x 1 + (-528427077/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328110799/2500000000 : ℝ)^8315 ≤ (43203896152163/100000000000000 : ℝ)^6267 := by
    have hnat : (1328110799 : ℕ)^8315*100000000000000^6267 ≤ 43203896152163^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328110799 2500000000 43203896152163 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696553773/5000000000 : ℝ)^8315 ≤ (44076436110227/100000000000000 : ℝ)^6267 := by
    have hnat : (2696553773 : ℕ)^8315*100000000000000^6267 ≤ 44076436110227^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696553773 5000000000 44076436110227 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528427077/2500000000 : ℝ)^8315 ≤ (1589958465239/12500000000000 : ℝ)^6267 := by
    have hnat : (528427077 : ℕ)^8315*12500000000000^6267 ≤ 1589958465239^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528427077 2500000000 1589958465239 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328110799/2500000000 : ℝ), (2696553773/5000000000 : ℝ), (-528427077/2500000000 : ℝ)] ![(43203896152163/100000000000000 : ℝ), (44076436110227/100000000000000 : ℝ), (1589958465239/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328110799/2500000000 : ℝ)|^8315 ≤ (43203896152163/100000000000000 : ℝ)^6267
        have hw : |(1328110799/2500000000 : ℝ)|=(1328110799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696553773/5000000000 : ℝ)|^8315 ≤ (44076436110227/100000000000000 : ℝ)^6267
        have hw : |(2696553773/5000000000 : ℝ)|=(2696553773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-528427077/2500000000 : ℝ)|^8315 ≤ (1589958465239/12500000000000 : ℝ)^6267
        have hw : |(-528427077/2500000000 : ℝ)|=(528427077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s7_7 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873501257/2000000000 : ℝ)*x 0 + (899116333/2000000000 : ℝ)*x 1 + (10607747/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873501257/2000000000 : ℝ)^8315 ≤ (3331693571369/10000000000000 : ℝ)^6267 := by
    have hnat : (873501257 : ℕ)^8315*10000000000000^6267 ≤ 3331693571369^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873501257 2000000000 3331693571369 10000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899116333/2000000000 : ℝ)^8315 ≤ (34619389183311/100000000000000 : ℝ)^6267 := by
    have hnat : (899116333 : ℕ)^8315*100000000000000^6267 ≤ 34619389183311^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899116333 2000000000 34619389183311 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10607747/25000000 : ℝ)^8315 ≤ (32063675093969/100000000000000 : ℝ)^6267 := by
    have hnat : (10607747 : ℕ)^8315*100000000000000^6267 ≤ 32063675093969^6267*25000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10607747 25000000 32063675093969 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873501257/2000000000 : ℝ), (899116333/2000000000 : ℝ), (10607747/25000000 : ℝ)] ![(3331693571369/10000000000000 : ℝ), (34619389183311/100000000000000 : ℝ), (32063675093969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873501257/2000000000 : ℝ)|^8315 ≤ (3331693571369/10000000000000 : ℝ)^6267
        have hw : |(873501257/2000000000 : ℝ)|=(873501257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899116333/2000000000 : ℝ)|^8315 ≤ (34619389183311/100000000000000 : ℝ)^6267
        have hw : |(899116333/2000000000 : ℝ)|=(899116333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10607747/25000000 : ℝ)|^8315 ≤ (32063675093969/100000000000000 : ℝ)^6267
        have hw : |(10607747/25000000 : ℝ)|=(10607747/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1122_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11319/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5663/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7019/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7023/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11319/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7023/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11319/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7023/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11319/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7023/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11319/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7023/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11319/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7023/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11319/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11319/100000 : ℝ) ^ (4157/1024 : ℝ) ≤ (45052335729117/312500000000000000 : ℝ) := by
    have hpowers : (11319/100000 : ℝ)^4157 ≤ (45052335729117/312500000000000000 : ℝ)^1024 := by
      have hnat : (11319 : ℕ)^4157*312500000000000000^1024 ≤ 45052335729117^1024*100000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11319 100000 45052335729117 312500000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11319/100000 : ℝ)) (X := (45052335729117/312500000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7023/50000 : ℝ) ^ (4157/1024 : ℝ) ≤ (34628214746850493/100000000000000000000 : ℝ) := by
    have hpowers : (7023/50000 : ℝ)^4157 ≤ (34628214746850493/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7023 : ℕ)^4157*100000000000000000000^1024 ≤ 34628214746850493^1024*50000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7023 50000 34628214746850493 100000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7023/50000 : ℝ)) (X := (34628214746850493/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (156295052335729117/156250000000000000 : ℝ) ≤ (1000071018261261/1000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (156295052335729117/156250000000000000 : ℝ)^1024 ≤ (1000071018261261/1000000000000000 : ℝ)^4157 := by
      have hnat : (156295052335729117 : ℕ)^1024*1000000000000000^4157 ≤ 1000071018261261^4157*156250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        156295052335729117 156250000000000000 1000071018261261 1000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000071018261261/1000000000000000 : ℝ)) (X := (156295052335729117/156250000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049044962180167933/100000000000000000000 : ℝ) ≤ (10001207908635663/10000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (100049044962180167933/100000000000000000000 : ℝ)^1024 ≤ (10001207908635663/10000000000000000 : ℝ)^4157 := by
      have hnat : (100049044962180167933 : ℕ)^1024*10000000000000000^4157 ≤ 10001207908635663^4157*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049044962180167933 100000000000000000000 10001207908635663 10000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001207908635663/10000000000000000 : ℝ)) (X := (100049044962180167933/100000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034628214746850493/50000000000000000000 : ℝ) ≤ (2500426408664679/2500000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (50034628214746850493/50000000000000000000 : ℝ)^1024 ≤ (2500426408664679/2500000000000000 : ℝ)^4157 := by
      have hnat : (50034628214746850493 : ℕ)^1024*2500000000000000^4157 ≤ 2500426408664679^4157*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034628214746850493 50000000000000000000 2500426408664679 2500000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500426408664679/2500000000000000 : ℝ)) (X := (50034628214746850493/50000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(45052335729117/312500000000000000 : ℝ) ≤ ((378620404809371023/378750000000000000 : ℝ)+2*(165908674351/90900000000000 : ℝ)*(11319/100000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (378620404809371023/378750000000000000 : ℝ)+2*(165908674351/90900000000000 : ℝ)*(11319/100000 : ℝ)=(1000071018261261/1000000000000000 : ℝ) by norm_num, show 1+2*(45052335729117/312500000000000000 : ℝ)=(156295052335729117/156250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34628214746850493/100000000000000000000 : ℝ)+(45052335729117/312500000000000000 : ℝ) ≤ ((378620404809371023/378750000000000000 : ℝ)+(165908674351/90900000000000 : ℝ)*((7023/50000 : ℝ)+(11319/100000 : ℝ)))^(4157/1024 : ℝ) := by
    rw [show (378620404809371023/378750000000000000 : ℝ)+(165908674351/90900000000000 : ℝ)*((7023/50000 : ℝ)+(11319/100000 : ℝ))=(10001207908635663/10000000000000000 : ℝ) by norm_num, show 1+(34628214746850493/100000000000000000000 : ℝ)+(45052335729117/312500000000000000 : ℝ)=(100049044962180167933/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34628214746850493/100000000000000000000 : ℝ) ≤ ((378620404809371023/378750000000000000 : ℝ)+2*(165908674351/90900000000000 : ℝ)*(7023/50000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (378620404809371023/378750000000000000 : ℝ)+2*(165908674351/90900000000000 : ℝ)*(7023/50000 : ℝ)=(2500426408664679/2500000000000000 : ℝ) by norm_num, show 1+2*(34628214746850493/100000000000000000000 : ℝ)=(50034628214746850493/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (378620404809371023/378750000000000000 : ℝ)*(X 1 0+X 2 0)+(165908674351/90900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (11319/100000 : ℝ)) (hi := (7023/50000 : ℝ)) (c := (378620404809371023/378750000000000000 : ℝ)) (alpha := (165908674351/90900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (378620404809371023/378750000000000000 : ℝ)*(X 0 1+X 2 1)+(165908674351/90900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (11319/100000 : ℝ)) (hi := (7023/50000 : ℝ)) (c := (378620404809371023/378750000000000000 : ℝ)) (alpha := (165908674351/90900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (378620404809371023/378750000000000000 : ℝ)*(X 0 2+X 1 2)+(165908674351/90900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (11319/100000 : ℝ)) (hi := (7023/50000 : ℝ)) (c := (378620404809371023/378750000000000000 : ℝ)) (alpha := (165908674351/90900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2176482407/10000000000 : ℝ)*X 0 0+(2696715179/5000000000 : ℝ)*X 0 1+(2632688467/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344837659/10000000000 : ℝ)*X 1 0+(-2241438921/10000000000 : ℝ)*X 1 1+(5265376943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344837663/10000000000 : ℝ)*X 2 0+(1053075389/2000000000 : ℝ)*X 2 1+(-2241438913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4367496497/10000000000 : ℝ)*X 0 0+(33939673/80000000 : ℝ)*X 0 1+(899243807/2000000000 : ℝ)*X 0 2+(4367496497/10000000000 : ℝ)*X 1 0+(33939673/80000000 : ℝ)*X 1 1+(899243807/2000000000 : ℝ)*X 1 2+(4367496497/10000000000 : ℝ)*X 2 0+(33939673/80000000 : ℝ)*X 2 1+(899243807/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-136030459/625000000 : ℝ)*X 0 0+(2632849287/5000000000 : ℝ)*X 0 1+(5393107557/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312443193/10000000000 : ℝ)*X 1 0+(-1056854153/5000000000 : ℝ)*X 1 1+(107862151/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328110799/2500000000 : ℝ)*X 2 0+(2696553773/5000000000 : ℝ)*X 2 1+(-528427077/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873501257/2000000000 : ℝ)*X 0 0+(899116333/2000000000 : ℝ)*X 0 1+(10607747/25000000 : ℝ)*X 0 2+(873501257/2000000000 : ℝ)*X 1 0+(899116333/2000000000 : ℝ)*X 1 1+(10607747/25000000 : ℝ)*X 1 2+(873501257/2000000000 : ℝ)*X 2 0+(899116333/2000000000 : ℝ)*X 2 1+(10607747/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1971175115431768177341249/315625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1249640599/100000000000000 : ℝ)*(base19) + (1182086167/100000000000000 : ℝ)*(base23) + (3923047/10000000000000 : ℝ)*(lower2) + (150673717/100000000000000 : ℝ)*(upper3) + (13762231/12500000000000 : ℝ)*(upper5) + (73437995519601/1250000000000 : ℝ)*(major0) + (73437995519601/1250000000000 : ℝ)*(major1) + (73437995519601/1250000000000 : ℝ)*(major2) + (7809276309354379/100000000000000 : ℝ)*(sp0) + (976163766812043/12500000000000 : ℝ)*(sp1) + (976163775256347/12500000000000 : ℝ)*(sp2) + (1970374787140621/50000000000000 : ℝ)*(sp3) + (8768695641/25000000000000 : ℝ)*(sp4) + (362330821/2000000000000 : ℝ)*(sp7) + (3940767690822291/100000000000000 : ℝ)*(f.failure) + (7809311384136943/100000000000000 : ℝ)*(f.sum) + (1580174640193/303000000000000000000000000 : ℝ)*base66 + (4053301740821849/236718750000000000000000000000 : ℝ)*base67 + (4006668494365573/473437500000000000000000000000 : ℝ)*base69 + (9695107351165573/473437500000000000000000000000 : ℝ)*base71 + (646666102939/75750000000000000000000000 : ℝ)*base74 + (2723748406421849/236718750000000000000000000000 : ℝ)*base75 + (3543185771515573/473437500000000000000000000000 : ℝ)*base77 + (8117938568665573/473437500000000000000000000000 : ℝ)*base79 + (768545039237/151500000000000000000000000 : ℝ)*base82 + (100336797/10000000000000000000000 : ℝ)*base90 + (100336797/10000000000000000000000 : ℝ)*base92 + (100336797/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22840128340411988897217791/9468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (120488293/25000000000000 : ℝ)*(base19) + (4000511/781250000000 : ℝ)*(base23) + (22968059/50000000000000 : ℝ)*(upper3) + (13165331/100000000000000 : ℝ)*(lower4) + (14472903/25000000000000 : ℝ)*(upper5) + (2952351232252561/50000000000000 : ℝ)*(major0) + (2952351232252561/50000000000000 : ℝ)*(major1) + (2952351232252561/50000000000000 : ℝ)*(major2) + (6678133403/50000000000000 : ℝ)*(sp1) + (1350351417/10000000000000 : ℝ)*(sp2) + (3924370195443681/50000000000000 : ℝ)*(sp4) + (981090819083423/12500000000000 : ℝ)*(sp5) + (981090796913473/12500000000000 : ℝ)*(sp6) + (3960664457717583/100000000000000 : ℝ)*(sp7) + (3960664457717583/100000000000000 : ℝ)*(f.failure) + (3924370195443681/50000000000000 : ℝ)*(f.sum) + (15851614386107/4545000000000000000000000000 : ℝ)*base65 + (152316621543730291/56812500000000000000000000000000 : ℝ)*base68 + (652730277590082209/56812500000000000000000000000000 : ℝ)*base69 + (315038005478644709/56812500000000000000000000000000 : ℝ)*base71 + (8932748920603/4545000000000000000000000000 : ℝ)*base74 + (640242400139082209/56812500000000000000000000000000 : ℝ)*base75 + (331942104217894709/56812500000000000000000000000000 : ℝ)*base77 + (179798357527105291/56812500000000000000000000000000 : ℝ)*base80 + (1414195409689/568125000000000000000000000 : ℝ)*base81 + (38380961/10000000000000000000000 : ℝ)*base90 + (38380961/10000000000000000000000 : ℝ)*base92 + (38380961/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1122_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11319/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1122_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1122_s8_0 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-108824561/500000000 : ℝ)*x 0 + (2696676221/5000000000 : ℝ)*x 1 + (263272443/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108824561/500000000 : ℝ)^8315 ≤ (826459875581/6250000000000 : ℝ)^6267 := by
    have hnat : (108824561 : ℕ)^8315*6250000000000^6267 ≤ 826459875581^6267*500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108824561 500000000 826459875581 6250000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696676221/5000000000 : ℝ)^8315 ≤ (22039545831277/50000000000000 : ℝ)^6267 := by
    have hnat : (2696676221 : ℕ)^8315*50000000000000^6267 ≤ 22039545831277^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696676221 5000000000 22039545831277 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263272443/500000000 : ℝ)^8315 ≤ (42697550308009/100000000000000 : ℝ)^6267 := by
    have hnat : (263272443 : ℕ)^8315*100000000000000^6267 ≤ 42697550308009^6267*500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263272443 500000000 42697550308009 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-108824561/500000000 : ℝ), (2696676221/5000000000 : ℝ), (263272443/500000000 : ℝ)] ![(826459875581/6250000000000 : ℝ), (22039545831277/50000000000000 : ℝ), (42697550308009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-108824561/500000000 : ℝ)|^8315 ≤ (826459875581/6250000000000 : ℝ)^6267
        have hw : |(-108824561/500000000 : ℝ)|=(108824561/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696676221/5000000000 : ℝ)|^8315 ≤ (22039545831277/50000000000000 : ℝ)^6267
        have hw : |(2696676221/5000000000 : ℝ)|=(2696676221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263272443/500000000 : ℝ)|^8315 ≤ (42697550308009/100000000000000 : ℝ)^6267
        have hw : |(263272443/500000000 : ℝ)|=(263272443/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s8_1 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344817503/10000000000 : ℝ)*x 0 + (-560342671/2500000000 : ℝ)*x 1 + (5265448817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344817503/10000000000 : ℝ)^8315 ≤ (2722098132127/6250000000000 : ℝ)^6267 := by
    have hnat : (5344817503 : ℕ)^8315*6250000000000^6267 ≤ 2722098132127^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344817503 10000000000 2722098132127 6250000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560342671/2500000000 : ℝ)^8315 ≤ (13748880030913/100000000000000 : ℝ)^6267 := by
    have hnat : (560342671 : ℕ)^8315*100000000000000^6267 ≤ 13748880030913^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560342671 2500000000 13748880030913 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265448817/10000000000 : ℝ)^8315 ≤ (21348774922687/50000000000000 : ℝ)^6267 := by
    have hnat : (5265448817 : ℕ)^8315*50000000000000^6267 ≤ 21348774922687^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265448817 10000000000 21348774922687 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344817503/10000000000 : ℝ), (-560342671/2500000000 : ℝ), (5265448817/10000000000 : ℝ)] ![(2722098132127/6250000000000 : ℝ), (13748880030913/100000000000000 : ℝ), (21348774922687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344817503/10000000000 : ℝ)|^8315 ≤ (2722098132127/6250000000000 : ℝ)^6267
        have hw : |(5344817503/10000000000 : ℝ)|=(5344817503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560342671/2500000000 : ℝ)|^8315 ≤ (13748880030913/100000000000000 : ℝ)^6267
        have hw : |(-560342671/2500000000 : ℝ)|=(560342671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265448817/10000000000 : ℝ)|^8315 ≤ (21348774922687/50000000000000 : ℝ)^6267
        have hw : |(5265448817/10000000000 : ℝ)|=(5265448817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s8_2 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (133620437/250000000 : ℝ)*x 0 + (1053089769/2000000000 : ℝ)*x 1 + (-2241370677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133620437/250000000 : ℝ)^8315 ≤ (43553569865363/100000000000000 : ℝ)^6267 := by
    have hnat : (133620437 : ℕ)^8315*100000000000000^6267 ≤ 43553569865363^6267*250000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133620437 250000000 43553569865363 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053089769/2000000000 : ℝ)^8315 ≤ (341580401173/800000000000 : ℝ)^6267 := by
    have hnat : (1053089769 : ℕ)^8315*800000000000^6267 ≤ 341580401173^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053089769 2000000000 341580401173 800000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241370677/10000000000 : ℝ)^8315 ≤ (6874439986971/50000000000000 : ℝ)^6267 := by
    have hnat : (2241370677 : ℕ)^8315*50000000000000^6267 ≤ 6874439986971^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241370677 10000000000 6874439986971 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133620437/250000000 : ℝ), (1053089769/2000000000 : ℝ), (-2241370677/10000000000 : ℝ)] ![(43553569865363/100000000000000 : ℝ), (341580401173/800000000000 : ℝ), (6874439986971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133620437/250000000 : ℝ)|^8315 ≤ (43553569865363/100000000000000 : ℝ)^6267
        have hw : |(133620437/250000000 : ℝ)|=(133620437/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053089769/2000000000 : ℝ)|^8315 ≤ (341580401173/800000000000 : ℝ)^6267
        have hw : |(1053089769/2000000000 : ℝ)|=(1053089769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2241370677/10000000000 : ℝ)|^8315 ≤ (6874439986971/50000000000000 : ℝ)^6267
        have hw : |(-2241370677/10000000000 : ℝ)|=(2241370677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s8_3 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873500063/2000000000 : ℝ)*x 0 + (4242607003/10000000000 : ℝ)*x 1 + (899214031/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873500063/2000000000 : ℝ)^8315 ≤ (8329218822463/25000000000000 : ℝ)^6267 := by
    have hnat : (873500063 : ℕ)^8315*25000000000000^6267 ≤ 8329218822463^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873500063 2000000000 8329218822463 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242607003/10000000000 : ℝ)^8315 ≤ (32058744373713/100000000000000 : ℝ)^6267 := by
    have hnat : (4242607003 : ℕ)^8315*100000000000000^6267 ≤ 32058744373713^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242607003 10000000000 32058744373713 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899214031/2000000000 : ℝ)^8315 ≤ (17312190159959/50000000000000 : ℝ)^6267 := by
    have hnat : (899214031 : ℕ)^8315*50000000000000^6267 ≤ 17312190159959^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899214031 2000000000 17312190159959 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873500063/2000000000 : ℝ), (4242607003/10000000000 : ℝ), (899214031/2000000000 : ℝ)] ![(8329218822463/25000000000000 : ℝ), (32058744373713/100000000000000 : ℝ), (17312190159959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873500063/2000000000 : ℝ)|^8315 ≤ (8329218822463/25000000000000 : ℝ)^6267
        have hw : |(873500063/2000000000 : ℝ)|=(873500063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242607003/10000000000 : ℝ)|^8315 ≤ (32058744373713/100000000000000 : ℝ)^6267
        have hw : |(4242607003/10000000000 : ℝ)|=(4242607003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899214031/2000000000 : ℝ)|^8315 ≤ (17312190159959/50000000000000 : ℝ)^6267
        have hw : |(899214031/2000000000 : ℝ)|=(899214031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s8_4 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1088248071/5000000000 : ℝ)*x 0 + (1316442439/2500000000 : ℝ)*x 1 + (1348257597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088248071/5000000000 : ℝ)^8315 ≤ (13223397685413/100000000000000 : ℝ)^6267 := by
    have hnat : (1088248071 : ℕ)^8315*100000000000000^6267 ≤ 13223397685413^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088248071 5000000000 13223397685413 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316442439/2500000000 : ℝ)^8315 ≤ (5337625356029/12500000000000 : ℝ)^6267 := by
    have hnat : (1316442439 : ℕ)^8315*12500000000000^6267 ≤ 5337625356029^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316442439 2500000000 5337625356029 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348257597/2500000000 : ℝ)^8315 ≤ (44075599448513/100000000000000 : ℝ)^6267 := by
    have hnat : (1348257597 : ℕ)^8315*100000000000000^6267 ≤ 44075599448513^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348257597 2500000000 44075599448513 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1088248071/5000000000 : ℝ), (1316442439/2500000000 : ℝ), (1348257597/2500000000 : ℝ)] ![(13223397685413/100000000000000 : ℝ), (5337625356029/12500000000000 : ℝ), (44075599448513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1088248071/5000000000 : ℝ)|^8315 ≤ (13223397685413/100000000000000 : ℝ)^6267
        have hw : |(-1088248071/5000000000 : ℝ)|=(1088248071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316442439/2500000000 : ℝ)|^8315 ≤ (5337625356029/12500000000000 : ℝ)^6267
        have hw : |(1316442439/2500000000 : ℝ)|=(1316442439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348257597/2500000000 : ℝ)|^8315 ≤ (44075599448513/100000000000000 : ℝ)^6267
        have hw : |(1348257597/2500000000 : ℝ)|=(1348257597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s8_5 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062492187/2000000000 : ℝ)*x 0 + (-1056894571/5000000000 : ℝ)*x 1 + (2696515187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062492187/2000000000 : ℝ)^8315 ≤ (8640817512073/20000000000000 : ℝ)^6267 := by
    have hnat : (1062492187 : ℕ)^8315*20000000000000^6267 ≤ 8640817512073^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062492187 2000000000 8640817512073 20000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056894571/5000000000 : ℝ)^8315 ≤ (12720313123537/100000000000000 : ℝ)^6267 := by
    have hnat : (1056894571 : ℕ)^8315*100000000000000^6267 ≤ 12720313123537^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056894571 5000000000 12720313123537 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696515187/5000000000 : ℝ)^8315 ≤ (688681239011/1562500000000 : ℝ)^6267 := by
    have hnat : (2696515187 : ℕ)^8315*1562500000000^6267 ≤ 688681239011^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696515187 5000000000 688681239011 1562500000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062492187/2000000000 : ℝ), (-1056894571/5000000000 : ℝ), (2696515187/5000000000 : ℝ)] ![(8640817512073/20000000000000 : ℝ), (12720313123537/100000000000000 : ℝ), (688681239011/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062492187/2000000000 : ℝ)|^8315 ≤ (8640817512073/20000000000000 : ℝ)^6267
        have hw : |(1062492187/2000000000 : ℝ)|=(1062492187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1056894571/5000000000 : ℝ)|^8315 ≤ (12720313123537/100000000000000 : ℝ)^6267
        have hw : |(-1056894571/5000000000 : ℝ)|=(1056894571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696515187/5000000000 : ℝ)|^8315 ≤ (688681239011/1562500000000 : ℝ)^6267
        have hw : |(2696515187/5000000000 : ℝ)|=(2696515187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s8_6 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312460947/10000000000 : ℝ)*x 0 + (674128797/1250000000 : ℝ)*x 1 + (-528447281/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312460947/10000000000 : ℝ)^8315 ≤ (5400510961231/12500000000000 : ℝ)^6267 := by
    have hnat : (5312460947 : ℕ)^8315*12500000000000^6267 ≤ 5400510961231^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312460947 10000000000 5400510961231 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674128797/1250000000 : ℝ)^8315 ≤ (44075599318391/100000000000000 : ℝ)^6267 := by
    have hnat : (674128797 : ℕ)^8315*100000000000000^6267 ≤ 44075599318391^6267*1250000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674128797 1250000000 44075599318391 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528447281/2500000000 : ℝ)^8315 ≤ (12720312979819/100000000000000 : ℝ)^6267 := by
    have hnat : (528447281 : ℕ)^8315*100000000000000^6267 ≤ 12720312979819^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528447281 2500000000 12720312979819 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312460947/10000000000 : ℝ), (674128797/1250000000 : ℝ), (-528447281/2500000000 : ℝ)] ![(5400510961231/12500000000000 : ℝ), (44075599318391/100000000000000 : ℝ), (12720312979819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312460947/10000000000 : ℝ)|^8315 ≤ (5400510961231/12500000000000 : ℝ)^6267
        have hw : |(5312460947/10000000000 : ℝ)|=(5312460947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674128797/1250000000 : ℝ)|^8315 ≤ (44075599318391/100000000000000 : ℝ)^6267
        have hw : |(674128797/1250000000 : ℝ)|=(674128797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-528447281/2500000000 : ℝ)|^8315 ≤ (12720312979819/100000000000000 : ℝ)^6267
        have hw : |(-528447281/2500000000 : ℝ)|=(528447281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s8_7 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4367510049/10000000000 : ℝ)*x 0 + (2247717101/5000000000 : ℝ)*x 1 + (530405659/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367510049/10000000000 : ℝ)^8315 ≤ (33316973810073/100000000000000 : ℝ)^6267 := by
    have hnat : (4367510049 : ℕ)^8315*100000000000000^6267 ≤ 33316973810073^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367510049 10000000000 33316973810073 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247717101/5000000000 : ℝ)^8315 ≤ (17308941258971/50000000000000 : ℝ)^6267 := by
    have hnat : (2247717101 : ℕ)^8315*50000000000000^6267 ≤ 17308941258971^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247717101 5000000000 17308941258971 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530405659/1250000000 : ℝ)^8315 ≤ (32065143647477/100000000000000 : ℝ)^6267 := by
    have hnat : (530405659 : ℕ)^8315*100000000000000^6267 ≤ 32065143647477^6267*1250000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530405659 1250000000 32065143647477 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367510049/10000000000 : ℝ), (2247717101/5000000000 : ℝ), (530405659/1250000000 : ℝ)] ![(33316973810073/100000000000000 : ℝ), (17308941258971/50000000000000 : ℝ), (32065143647477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367510049/10000000000 : ℝ)|^8315 ≤ (33316973810073/100000000000000 : ℝ)^6267
        have hw : |(4367510049/10000000000 : ℝ)|=(4367510049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247717101/5000000000 : ℝ)|^8315 ≤ (17308941258971/50000000000000 : ℝ)^6267
        have hw : |(2247717101/5000000000 : ℝ)|=(2247717101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530405659/1250000000 : ℝ)|^8315 ≤ (32065143647477/100000000000000 : ℝ)^6267
        have hw : |(530405659/1250000000 : ℝ)|=(530405659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1122_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (354/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14037/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7019/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5663/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7019/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5663/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7019/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5663/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7019/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5663/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7019/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5663/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7019/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5663/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5663/50000 : ℝ) ^ (4157/1024 : ℝ) ≤ (2890595150551571/20000000000000000000 : ℝ) := by
    have hpowers : (5663/50000 : ℝ)^4157 ≤ (2890595150551571/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5663 : ℕ)^4157*20000000000000000000^1024 ≤ 2890595150551571^1024*50000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5663 50000 2890595150551571 20000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5663/50000 : ℝ)) (X := (2890595150551571/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7019/50000 : ℝ) ^ (4157/1024 : ℝ) ≤ (138192874395407/400000000000000000 : ℝ) := by
    have hpowers : (7019/50000 : ℝ)^4157 ≤ (138192874395407/400000000000000000 : ℝ)^1024 := by
      have hnat : (7019 : ℕ)^4157*400000000000000000^1024 ≤ 138192874395407^1024*50000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7019 50000 138192874395407 400000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7019/50000 : ℝ)) (X := (138192874395407/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002890595150551571/10000000000000000000 : ℝ) ≤ (2000142393411907/2000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (10002890595150551571/10000000000000000000 : ℝ)^1024 ≤ (2000142393411907/2000000000000000 : ℝ)^4157 := by
      have hnat : (10002890595150551571 : ℕ)^1024*2000000000000000^4157 ≤ 2000142393411907^4157*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002890595150551571 10000000000000000000 2000142393411907 2000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000142393411907/2000000000000000 : ℝ)) (X := (10002890595150551571/10000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009800238870321921/20000000000000000000 : ℝ) ≤ (2500301707723599/2500000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (20009800238870321921/20000000000000000000 : ℝ)^1024 ≤ (2500301707723599/2500000000000000 : ℝ)^4157 := by
      have hnat : (20009800238870321921 : ℕ)^1024*2500000000000000^4157 ≤ 2500301707723599^4157*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009800238870321921 20000000000000000000 2500301707723599 2500000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500301707723599/2500000000000000 : ℝ)) (X := (20009800238870321921/20000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (200138192874395407/200000000000000000 : ℝ) ≤ (10001701694729257/10000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (200138192874395407/200000000000000000 : ℝ)^1024 ≤ (10001701694729257/10000000000000000 : ℝ)^4157 := by
      have hnat : (200138192874395407 : ℕ)^1024*10000000000000000^4157 ≤ 10001701694729257^4157*200000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200138192874395407 200000000000000000 10001701694729257 10000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001701694729257/10000000000000000 : ℝ)) (X := (200138192874395407/200000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2890595150551571/20000000000000000000 : ℝ) ≤ ((6777680299769546887/6780000000000000000 : ℝ)+2*(494863834861/271200000000000 : ℝ)*(5663/50000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (6777680299769546887/6780000000000000000 : ℝ)+2*(494863834861/271200000000000 : ℝ)*(5663/50000 : ℝ)=(2000142393411907/2000000000000000 : ℝ) by norm_num, show 1+2*(2890595150551571/20000000000000000000 : ℝ)=(10002890595150551571/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(138192874395407/400000000000000000 : ℝ)+(2890595150551571/20000000000000000000 : ℝ) ≤ ((6777680299769546887/6780000000000000000 : ℝ)+(494863834861/271200000000000 : ℝ)*((7019/50000 : ℝ)+(5663/50000 : ℝ)))^(4157/1024 : ℝ) := by
    rw [show (6777680299769546887/6780000000000000000 : ℝ)+(494863834861/271200000000000 : ℝ)*((7019/50000 : ℝ)+(5663/50000 : ℝ))=(2500301707723599/2500000000000000 : ℝ) by norm_num, show 1+(138192874395407/400000000000000000 : ℝ)+(2890595150551571/20000000000000000000 : ℝ)=(20009800238870321921/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(138192874395407/400000000000000000 : ℝ) ≤ ((6777680299769546887/6780000000000000000 : ℝ)+2*(494863834861/271200000000000 : ℝ)*(7019/50000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (6777680299769546887/6780000000000000000 : ℝ)+2*(494863834861/271200000000000 : ℝ)*(7019/50000 : ℝ)=(10001701694729257/10000000000000000 : ℝ) by norm_num, show 1+2*(138192874395407/400000000000000000 : ℝ)=(200138192874395407/200000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6777680299769546887/6780000000000000000 : ℝ)*(X 1 0+X 2 0)+(494863834861/271200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (5663/50000 : ℝ)) (hi := (7019/50000 : ℝ)) (c := (6777680299769546887/6780000000000000000 : ℝ)) (alpha := (494863834861/271200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6777680299769546887/6780000000000000000 : ℝ)*(X 0 1+X 2 1)+(494863834861/271200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (5663/50000 : ℝ)) (hi := (7019/50000 : ℝ)) (c := (6777680299769546887/6780000000000000000 : ℝ)) (alpha := (494863834861/271200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6777680299769546887/6780000000000000000 : ℝ)*(X 0 2+X 1 2)+(494863834861/271200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (5663/50000 : ℝ)) (hi := (7019/50000 : ℝ)) (c := (6777680299769546887/6780000000000000000 : ℝ)) (alpha := (494863834861/271200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-108824561/500000000 : ℝ)*X 0 0+(2696676221/5000000000 : ℝ)*X 0 1+(263272443/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344817503/10000000000 : ℝ)*X 1 0+(-560342671/2500000000 : ℝ)*X 1 1+(5265448817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133620437/250000000 : ℝ)*X 2 0+(1053089769/2000000000 : ℝ)*X 2 1+(-2241370677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873500063/2000000000 : ℝ)*X 0 0+(4242607003/10000000000 : ℝ)*X 0 1+(899214031/2000000000 : ℝ)*X 0 2+(873500063/2000000000 : ℝ)*X 1 0+(4242607003/10000000000 : ℝ)*X 1 1+(899214031/2000000000 : ℝ)*X 1 2+(873500063/2000000000 : ℝ)*X 2 0+(4242607003/10000000000 : ℝ)*X 2 1+(899214031/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1088248071/5000000000 : ℝ)*X 0 0+(1316442439/2500000000 : ℝ)*X 0 1+(1348257597/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062492187/2000000000 : ℝ)*X 1 0+(-1056894571/5000000000 : ℝ)*X 1 1+(2696515187/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312460947/10000000000 : ℝ)*X 2 0+(674128797/1250000000 : ℝ)*X 2 1+(-528447281/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367510049/10000000000 : ℝ)*X 0 0+(2247717101/5000000000 : ℝ)*X 0 1+(530405659/1250000000 : ℝ)*X 0 2+(4367510049/10000000000 : ℝ)*X 1 0+(2247717101/5000000000 : ℝ)*X 1 1+(530405659/1250000000 : ℝ)*X 1 2+(4367510049/10000000000 : ℝ)*X 2 0+(2247717101/5000000000 : ℝ)*X 2 1+(530405659/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54693703039385981598122307/28250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (424035399/100000000000000 : ℝ)*(base19) + (35124469/10000000000000 : ℝ)*(base23) + (20922969/100000000000000 : ℝ)*(lower2) + (53219519/100000000000000 : ℝ)*(upper3) + (28738859/100000000000000 : ℝ)*(upper5) + (1470470769909339/25000000000000 : ℝ)*(major0) + (1470470769909339/25000000000000 : ℝ)*(major1) + (1470470769909339/25000000000000 : ℝ)*(major2) + (7818399139562953/100000000000000 : ℝ)*(sp0) + (3909203822479603/50000000000000 : ℝ)*(sp1) + (1563681543549983/20000000000000 : ℝ)*(sp2) + (3945352058483131/100000000000000 : ℝ)*(sp3) + (8929431651/100000000000000 : ℝ)*(sp4) + (745907703/12500000000000 : ℝ)*(sp7) + (789071605148951/20000000000000 : ℝ)*(f.failure) + (1954602017248651/25000000000000 : ℝ)*(f.sum) + (8201394727223/1130000000000000000000000000 : ℝ)*base65 + (281688352424384231/56500000000000000000000000000000 : ℝ)*base67 + (832115173067384231/56500000000000000000000000000000 : ℝ)*base69 + (309968317990384231/56500000000000000000000000000000 : ℝ)*base71 + (1792925074517/1130000000000000000000000000 : ℝ)*base74 + (1092380207003615769/56500000000000000000000000000000 : ℝ)*base76 + (987361983607384231/56500000000000000000000000000000 : ℝ)*base77 + (196040040880115769/56500000000000000000000000000000 : ℝ)*base80 + (7767393549153/1130000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1218983/2000000000000000000000 : ℝ)*base89 + (1218983/2000000000000000000000 : ℝ)*base91 + (1218983/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (476628054791560077540222111/56500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1542675143/100000000000000 : ℝ)*(base19) + (13616211/800000000000 : ℝ)*(base23) + (530714537/100000000000000 : ℝ)*(lower1) + (33798047/20000000000000 : ℝ)*(upper3) + (30132059/50000000000000 : ℝ)*(lower4) + (166666561/100000000000000 : ℝ)*(upper5) + (2955776619766647/50000000000000 : ℝ)*(major0) + (2955776619766647/50000000000000 : ℝ)*(major1) + (2955776619766647/50000000000000 : ℝ)*(major2) + (288991083/6250000000000 : ℝ)*(sp2) + (7857846483858869/100000000000000 : ℝ)*(sp4) + (314313797647349/4000000000000 : ℝ)*(sp5) + (1964460039493791/25000000000000 : ℝ)*(sp6) + (495657464251399/12500000000000 : ℝ)*(sp7) + (495657464251399/12500000000000 : ℝ)*(f.failure) + (7857846483858869/100000000000000 : ℝ)*(f.sum) + (1197128228911/2260000000000000000000000000 : ℝ)*base66 + (13023828297106650963/113000000000000000000000000000000 : ℝ)*base67 + (825139896117349037/113000000000000000000000000000000 : ℝ)*base70 + (10797977288651650963/113000000000000000000000000000000 : ℝ)*base71 + (3655985231151/2260000000000000000000000000 : ℝ)*base74 + (4777495930368650963/113000000000000000000000000000000 : ℝ)*base75 + (1558135499997349037/113000000000000000000000000000000 : ℝ)*base78 + (2772987886926650963/113000000000000000000000000000000 : ℝ)*base79 + (7920815053369/2260000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/50000000000000 : ℝ)*base88 + (13252567/1250000000000000000000 : ℝ)*base89 + (13252567/1250000000000000000000 : ℝ)*base91 + (13252567/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1122_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1122_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1122_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1122_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1122_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1122_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1122_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

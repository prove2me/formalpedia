-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1036_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:43:05.366925+00:00
-- url     : https://prove2.me/submissions/54050568-2825-4f79-81f9-0bbff8b941a0

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
theorem support_rectangle_w1036_s3_0 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-138341477/625000000 : ℝ)*x 0 + (5441077011/10000000000 : ℝ)*x 1 + (5221062041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138341477/625000000 : ℝ)^8229 ≤ (6714907117561/50000000000000 : ℝ)^6181 := by
    have hnat : (138341477 : ℕ)^8229*50000000000000^6181 ≤ 6714907117561^6181*625000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138341477 625000000 6714907117561 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441077011/10000000000 : ℝ)^8229 ≤ (44474106814171/100000000000000 : ℝ)^6181 := by
    have hnat : (5441077011 : ℕ)^8229*100000000000000^6181 ≤ 44474106814171^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441077011 10000000000 44474106814171 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5221062041/10000000000 : ℝ)^8229 ≤ (21048039470063/50000000000000 : ℝ)^6181 := by
    have hnat : (5221062041 : ℕ)^8229*50000000000000^6181 ≤ 21048039470063^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221062041 10000000000 21048039470063 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-138341477/625000000 : ℝ), (5441077011/10000000000 : ℝ), (5221062041/10000000000 : ℝ)] ![(6714907117561/50000000000000 : ℝ), (44474106814171/100000000000000 : ℝ), (21048039470063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-138341477/625000000 : ℝ)|^8229 ≤ (6714907117561/50000000000000 : ℝ)^6181
        have hw : |(-138341477/625000000 : ℝ)|=(138341477/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441077011/10000000000 : ℝ)|^8229 ≤ (44474106814171/100000000000000 : ℝ)^6181
        have hw : |(5441077011/10000000000 : ℝ)|=(5441077011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5221062041/10000000000 : ℝ)|^8229 ≤ (21048039470063/50000000000000 : ℝ)^6181
        have hw : |(5221062041/10000000000 : ℝ)|=(5221062041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s3_1 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5356465309/10000000000 : ℝ)*x 0 + (-1163107227/5000000000 : ℝ)*x 1 + (1044212489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356465309/10000000000 : ℝ)^8229 ≤ (10888934616731/25000000000000 : ℝ)^6181 := by
    have hnat : (5356465309 : ℕ)^8229*25000000000000^6181 ≤ 10888934616731^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356465309 10000000000 10888934616731 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1163107227/5000000000 : ℝ)^8229 ≤ (14348178237319/100000000000000 : ℝ)^6181 := by
    have hnat : (1163107227 : ℕ)^8229*100000000000000^6181 ≤ 14348178237319^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163107227 5000000000 14348178237319 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044212489/2000000000 : ℝ)^8229 ≤ (42096083276757/100000000000000 : ℝ)^6181 := by
    have hnat : (1044212489 : ℕ)^8229*100000000000000^6181 ≤ 42096083276757^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044212489 2000000000 42096083276757 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356465309/10000000000 : ℝ), (-1163107227/5000000000 : ℝ), (1044212489/2000000000 : ℝ)] ![(10888934616731/25000000000000 : ℝ), (14348178237319/100000000000000 : ℝ), (42096083276757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356465309/10000000000 : ℝ)|^8229 ≤ (10888934616731/25000000000000 : ℝ)^6181
        have hw : |(5356465309/10000000000 : ℝ)|=(5356465309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1163107227/5000000000 : ℝ)|^8229 ≤ (14348178237319/100000000000000 : ℝ)^6181
        have hw : |(-1163107227/5000000000 : ℝ)|=(1163107227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044212489/2000000000 : ℝ)|^8229 ≤ (42096083276757/100000000000000 : ℝ)^6181
        have hw : |(1044212489/2000000000 : ℝ)|=(1044212489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s3_2 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5356465529/10000000000 : ℝ)*x 0 + (652632797/1250000000 : ℝ)*x 1 + (-1163107127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356465529/10000000000 : ℝ)^8229 ≤ (21777870424287/50000000000000 : ℝ)^6181 := by
    have hnat : (5356465529 : ℕ)^8229*50000000000000^6181 ≤ 21777870424287^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356465529 10000000000 21777870424287 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652632797/1250000000 : ℝ)^8229 ≤ (8419216507219/20000000000000 : ℝ)^6181 := by
    have hnat : (652632797 : ℕ)^8229*20000000000000^6181 ≤ 8419216507219^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652632797 1250000000 8419216507219 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1163107127/5000000000 : ℝ)^8229 ≤ (14348176594971/100000000000000 : ℝ)^6181 := by
    have hnat : (1163107127 : ℕ)^8229*100000000000000^6181 ≤ 14348176594971^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163107127 5000000000 14348176594971 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356465529/10000000000 : ℝ), (652632797/1250000000 : ℝ), (-1163107127/5000000000 : ℝ)] ![(21777870424287/50000000000000 : ℝ), (8419216507219/20000000000000 : ℝ), (14348176594971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356465529/10000000000 : ℝ)|^8229 ≤ (21777870424287/50000000000000 : ℝ)^6181
        have hw : |(5356465529/10000000000 : ℝ)|=(5356465529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652632797/1250000000 : ℝ)|^8229 ≤ (8419216507219/20000000000000 : ℝ)^6181
        have hw : |(652632797/1250000000 : ℝ)|=(652632797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1163107127/5000000000 : ℝ)|^8229 ≤ (14348176594971/100000000000000 : ℝ)^6181
        have hw : |(-1163107127/5000000000 : ℝ)|=(1163107127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s3_3 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376777517/10000000000 : ℝ)*x 0 + (833561549/2000000000 : ℝ)*x 1 + (4596437719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376777517/10000000000 : ℝ)^8229 ≤ (33285518098189/100000000000000 : ℝ)^6181 := by
    have hnat : (4376777517 : ℕ)^8229*100000000000000^6181 ≤ 33285518098189^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376777517 10000000000 33285518098189 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833561549/2000000000 : ℝ)^8229 ≤ (15593322558417/50000000000000 : ℝ)^6181 := by
    have hnat : (833561549 : ℕ)^8229*50000000000000^6181 ≤ 15593322558417^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833561549 2000000000 15593322558417 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4596437719/10000000000 : ℝ)^8229 ≤ (888195919087/2500000000000 : ℝ)^6181 := by
    have hnat : (4596437719 : ℕ)^8229*2500000000000^6181 ≤ 888195919087^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4596437719 10000000000 888195919087 2500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376777517/10000000000 : ℝ), (833561549/2000000000 : ℝ), (4596437719/10000000000 : ℝ)] ![(33285518098189/100000000000000 : ℝ), (15593322558417/50000000000000 : ℝ), (888195919087/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376777517/10000000000 : ℝ)|^8229 ≤ (33285518098189/100000000000000 : ℝ)^6181
        have hw : |(4376777517/10000000000 : ℝ)|=(4376777517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833561549/2000000000 : ℝ)|^8229 ≤ (15593322558417/50000000000000 : ℝ)^6181
        have hw : |(833561549/2000000000 : ℝ)|=(833561549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4596437719/10000000000 : ℝ)|^8229 ≤ (888195919087/2500000000000 : ℝ)^6181
        have hw : |(4596437719/10000000000 : ℝ)|=(4596437719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s3_4 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-553372131/2500000000 : ℝ)*x 0 + (2610992219/5000000000 : ℝ)*x 1 + (1360037153/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (553372131/2500000000 : ℝ)^8229 ≤ (6715007652389/50000000000000 : ℝ)^6181 := by
    have hnat : (553372131 : ℕ)^8229*50000000000000^6181 ≤ 6715007652389^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553372131 2500000000 6715007652389 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610992219/5000000000 : ℝ)^8229 ≤ (42105980456323/100000000000000 : ℝ)^6181 := by
    have hnat : (2610992219 : ℕ)^8229*100000000000000^6181 ≤ 42105980456323^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610992219 5000000000 42105980456323 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360037153/2500000000 : ℝ)^8229 ≤ (22232002108137/50000000000000 : ℝ)^6181 := by
    have hnat : (1360037153 : ℕ)^8229*50000000000000^6181 ≤ 22232002108137^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360037153 2500000000 22232002108137 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-553372131/2500000000 : ℝ), (2610992219/5000000000 : ℝ), (1360037153/2500000000 : ℝ)] ![(6715007652389/50000000000000 : ℝ), (42105980456323/100000000000000 : ℝ), (22232002108137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-553372131/2500000000 : ℝ)|^8229 ≤ (6715007652389/50000000000000 : ℝ)^6181
        have hw : |(-553372131/2500000000 : ℝ)|=(553372131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610992219/5000000000 : ℝ)|^8229 ≤ (42105980456323/100000000000000 : ℝ)^6181
        have hw : |(2610992219/5000000000 : ℝ)|=(2610992219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360037153/2500000000 : ℝ)|^8229 ≤ (22232002108137/50000000000000 : ℝ)^6181
        have hw : |(1360037153/2500000000 : ℝ)|=(1360037153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s3_5 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301175227/10000000000 : ℝ)*x 0 + (-84285117/400000000 : ℝ)*x 1 + (5440148953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301175227/10000000000 : ℝ)^8229 ≤ (21479105677651/50000000000000 : ℝ)^6181 := by
    have hnat : (5301175227 : ℕ)^8229*50000000000000^6181 ≤ 21479105677651^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301175227 10000000000 21479105677651 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84285117/400000000 : ℝ)^8229 ≤ (12577780704757/100000000000000 : ℝ)^6181 := by
    have hnat : (84285117 : ℕ)^8229*100000000000000^6181 ≤ 12577780704757^6181*400000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84285117 400000000 12577780704757 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440148953/10000000000 : ℝ)^8229 ≤ (44464007926843/100000000000000 : ℝ)^6181 := by
    have hnat : (5440148953 : ℕ)^8229*100000000000000^6181 ≤ 44464007926843^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440148953 10000000000 44464007926843 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301175227/10000000000 : ℝ), (-84285117/400000000 : ℝ), (5440148953/10000000000 : ℝ)] ![(21479105677651/50000000000000 : ℝ), (12577780704757/100000000000000 : ℝ), (44464007926843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301175227/10000000000 : ℝ)|^8229 ≤ (21479105677651/50000000000000 : ℝ)^6181
        have hw : |(5301175227/10000000000 : ℝ)|=(5301175227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84285117/400000000 : ℝ)|^8229 ≤ (12577780704757/100000000000000 : ℝ)^6181
        have hw : |(-84285117/400000000 : ℝ)|=(84285117/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440148953/10000000000 : ℝ)|^8229 ≤ (44464007926843/100000000000000 : ℝ)^6181
        have hw : |(5440148953/10000000000 : ℝ)|=(5440148953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s3_6 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212047003/400000000 : ℝ)*x 0 + (1088029763/2000000000 : ℝ)*x 1 + (-2107128321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212047003/400000000 : ℝ)^8229 ≤ (8591641943089/20000000000000 : ℝ)^6181 := by
    have hnat : (212047003 : ℕ)^8229*20000000000000^6181 ≤ 8591641943089^6181*400000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212047003 400000000 8591641943089 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088029763/2000000000 : ℝ)^8229 ≤ (8892801285041/20000000000000 : ℝ)^6181 := by
    have hnat : (1088029763 : ℕ)^8229*20000000000000^6181 ≤ 8892801285041^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088029763 2000000000 8892801285041 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107128321/10000000000 : ℝ)^8229 ≤ (3144445962939/25000000000000 : ℝ)^6181 := by
    have hnat : (2107128321 : ℕ)^8229*25000000000000^6181 ≤ 3144445962939^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107128321 10000000000 3144445962939 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212047003/400000000 : ℝ), (1088029763/2000000000 : ℝ), (-2107128321/10000000000 : ℝ)] ![(8591641943089/20000000000000 : ℝ), (8892801285041/20000000000000 : ℝ), (3144445962939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212047003/400000000 : ℝ)|^8229 ≤ (8591641943089/20000000000000 : ℝ)^6181
        have hw : |(212047003/400000000 : ℝ)|=(212047003/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088029763/2000000000 : ℝ)|^8229 ≤ (8892801285041/20000000000000 : ℝ)^6181
        have hw : |(1088029763/2000000000 : ℝ)|=(1088029763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2107128321/10000000000 : ℝ)|^8229 ≤ (3144445962939/25000000000000 : ℝ)^6181
        have hw : |(-2107128321/10000000000 : ℝ)|=(2107128321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s3_7 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1094206211/2500000000 : ℝ)*x 0 + (2297321007/5000000000 : ℝ)*x 1 + (41696143/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094206211/2500000000 : ℝ)^8229 ≤ (16642998639227/50000000000000 : ℝ)^6181 := by
    have hnat : (1094206211 : ℕ)^8229*50000000000000^6181 ≤ 16642998639227^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094206211 2500000000 16642998639227 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2297321007/5000000000 : ℝ)^8229 ≤ (35509359290173/100000000000000 : ℝ)^6181 := by
    have hnat : (2297321007 : ℕ)^8229*100000000000000^6181 ≤ 35509359290173^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2297321007 5000000000 35509359290173 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41696143/100000000 : ℝ)^8229 ≤ (7801160856113/25000000000000 : ℝ)^6181 := by
    have hnat : (41696143 : ℕ)^8229*25000000000000^6181 ≤ 7801160856113^6181*100000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41696143 100000000 7801160856113 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094206211/2500000000 : ℝ), (2297321007/5000000000 : ℝ), (41696143/100000000 : ℝ)] ![(16642998639227/50000000000000 : ℝ), (35509359290173/100000000000000 : ℝ), (7801160856113/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094206211/2500000000 : ℝ)|^8229 ≤ (16642998639227/50000000000000 : ℝ)^6181
        have hw : |(1094206211/2500000000 : ℝ)|=(1094206211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2297321007/5000000000 : ℝ)|^8229 ≤ (35509359290173/100000000000000 : ℝ)^6181
        have hw : |(2297321007/5000000000 : ℝ)|=(2297321007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41696143/100000000 : ℝ)|^8229 ≤ (7801160856113/25000000000000 : ℝ)^6181
        have hw : |(41696143/100000000 : ℝ)|=(41696143/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1036_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16839/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1713/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2059/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (299/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16839/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1713/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16839/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1713/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16839/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1713/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16839/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1713/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16839/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1713/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16839/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1713/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1713/20000 : ℝ) ^ (2057/512 : ℝ) ≤ (5154052255873723/100000000000000000000 : ℝ) := by
    have hpowers : (1713/20000 : ℝ)^2057 ≤ (5154052255873723/100000000000000000000 : ℝ)^512 := by
      have hnat : (1713 : ℕ)^2057*100000000000000000000^512 ≤ 5154052255873723^512*20000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1713 20000 5154052255873723 100000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1713/20000 : ℝ)) (X := (5154052255873723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16839/100000 : ℝ) ^ (2057/512 : ℝ) ≤ (1558458616934483/2000000000000000000 : ℝ) := by
    have hpowers : (16839/100000 : ℝ)^2057 ≤ (1558458616934483/2000000000000000000 : ℝ)^512 := by
      have hnat : (16839 : ℕ)^2057*2000000000000000000^512 ≤ 1558458616934483^512*100000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16839 100000 1558458616934483 2000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16839/100000 : ℝ)) (X := (1558458616934483/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005154052255873723/50000000000000000000 : ℝ) ≤ (2000051313030737/2000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (50005154052255873723/50000000000000000000 : ℝ)^512 ≤ (2000051313030737/2000000000000000 : ℝ)^2057 := by
      have hnat : (50005154052255873723 : ℕ)^512*2000000000000000^2057 ≤ 2000051313030737^2057*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005154052255873723 50000000000000000000 2000051313030737 2000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000051313030737/2000000000000000 : ℝ)) (X := (50005154052255873723/50000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100083076983102597873/100000000000000000000 : ℝ) ≤ (10002067192563263/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (100083076983102597873/100000000000000000000 : ℝ)^512 ≤ (10002067192563263/10000000000000000 : ℝ)^2057 := by
      have hnat : (100083076983102597873 : ℕ)^512*10000000000000000^2057 ≤ 10002067192563263^2057*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100083076983102597873 100000000000000000000 10002067192563263 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002067192563263/10000000000000000 : ℝ)) (X := (100083076983102597873/100000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1001558458616934483/1000000000000000000 : ℝ) ≤ (10003877819972841/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (1001558458616934483/1000000000000000000 : ℝ)^512 ≤ (10003877819972841/10000000000000000 : ℝ)^2057 := by
      have hnat : (1001558458616934483 : ℕ)^512*10000000000000000^2057 ≤ 10003877819972841^2057*1000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1001558458616934483 1000000000000000000 10003877819972841 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003877819972841/10000000000000000 : ℝ)) (X := (1001558458616934483/1000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5154052255873723/100000000000000000000 : ℝ) ≤ ((551407378483703457/551600000000000000 : ℝ)+2*(905313704789/413700000000000 : ℝ)*(1713/20000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (551407378483703457/551600000000000000 : ℝ)+2*(905313704789/413700000000000 : ℝ)*(1713/20000 : ℝ)=(2000051313030737/2000000000000000 : ℝ) by norm_num, show 1+2*(5154052255873723/100000000000000000000 : ℝ)=(50005154052255873723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1558458616934483/2000000000000000000 : ℝ)+(5154052255873723/100000000000000000000 : ℝ) ≤ ((551407378483703457/551600000000000000 : ℝ)+(905313704789/413700000000000 : ℝ)*((16839/100000 : ℝ)+(1713/20000 : ℝ)))^(2057/512 : ℝ) := by
    rw [show (551407378483703457/551600000000000000 : ℝ)+(905313704789/413700000000000 : ℝ)*((16839/100000 : ℝ)+(1713/20000 : ℝ))=(10002067192563263/10000000000000000 : ℝ) by norm_num, show 1+(1558458616934483/2000000000000000000 : ℝ)+(5154052255873723/100000000000000000000 : ℝ)=(100083076983102597873/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1558458616934483/2000000000000000000 : ℝ) ≤ ((551407378483703457/551600000000000000 : ℝ)+2*(905313704789/413700000000000 : ℝ)*(16839/100000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (551407378483703457/551600000000000000 : ℝ)+2*(905313704789/413700000000000 : ℝ)*(16839/100000 : ℝ)=(10003877819972841/10000000000000000 : ℝ) by norm_num, show 1+2*(1558458616934483/2000000000000000000 : ℝ)=(1001558458616934483/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (551407378483703457/551600000000000000 : ℝ)*(X 1 0+X 2 0)+(905313704789/413700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (1713/20000 : ℝ)) (hi := (16839/100000 : ℝ)) (c := (551407378483703457/551600000000000000 : ℝ)) (alpha := (905313704789/413700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (551407378483703457/551600000000000000 : ℝ)*(X 0 1+X 2 1)+(905313704789/413700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (1713/20000 : ℝ)) (hi := (16839/100000 : ℝ)) (c := (551407378483703457/551600000000000000 : ℝ)) (alpha := (905313704789/413700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (551407378483703457/551600000000000000 : ℝ)*(X 0 2+X 1 2)+(905313704789/413700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (1713/20000 : ℝ)) (hi := (16839/100000 : ℝ)) (c := (551407378483703457/551600000000000000 : ℝ)) (alpha := (905313704789/413700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-138341477/625000000 : ℝ)*X 0 0+(5441077011/10000000000 : ℝ)*X 0 1+(5221062041/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356465309/10000000000 : ℝ)*X 1 0+(-1163107227/5000000000 : ℝ)*X 1 1+(1044212489/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356465529/10000000000 : ℝ)*X 2 0+(652632797/1250000000 : ℝ)*X 2 1+(-1163107127/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4376777517/10000000000 : ℝ)*X 0 0+(833561549/2000000000 : ℝ)*X 0 1+(4596437719/10000000000 : ℝ)*X 0 2+(4376777517/10000000000 : ℝ)*X 1 0+(833561549/2000000000 : ℝ)*X 1 1+(4596437719/10000000000 : ℝ)*X 1 2+(4376777517/10000000000 : ℝ)*X 2 0+(833561549/2000000000 : ℝ)*X 2 1+(4596437719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-553372131/2500000000 : ℝ)*X 0 0+(2610992219/5000000000 : ℝ)*X 0 1+(1360037153/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301175227/10000000000 : ℝ)*X 1 0+(-84285117/400000000 : ℝ)*X 1 1+(5440148953/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212047003/400000000 : ℝ)*X 2 0+(1088029763/2000000000 : ℝ)*X 2 1+(-2107128321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1094206211/2500000000 : ℝ)*X 0 0+(2297321007/5000000000 : ℝ)*X 0 1+(41696143/100000000 : ℝ)*X 0 2+(1094206211/2500000000 : ℝ)*X 1 0+(2297321007/5000000000 : ℝ)*X 1 1+(41696143/100000000 : ℝ)*X 1 2+(1094206211/2500000000 : ℝ)*X 2 0+(2297321007/5000000000 : ℝ)*X 2 1+(41696143/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4840716790011319351923/689500000000000000000000000 : ℝ) := by norm_num
    linear_combination (757255383/50000000000000 : ℝ)*(base19) + (671762863/50000000000000 : ℝ)*(base23) + (228135351/100000000000000 : ℝ)*(lower2) + (54756527/100000000000000 : ℝ)*(upper3) + (18276497/50000000000000 : ℝ)*(lower4) + (687826136680719/20000000000000 : ℝ)*(major0) + (687826136680719/20000000000000 : ℝ)*(major1) + (687826136680719/20000000000000 : ℝ)*(major2) + (1136295302288243/25000000000000 : ℝ)*(sp0) + (4545218612846997/100000000000000 : ℝ)*(sp1) + (4545218783832037/100000000000000 : ℝ)*(sp2) + (291628315181369/12500000000000 : ℝ)*(sp3) + (38918204791/100000000000000 : ℝ)*(sp4) + (14483977837/100000000000000 : ℝ)*(sp7) + (583260251357197/25000000000000 : ℝ)*(f.failure) + (4545220127357763/100000000000000 : ℝ)*(f.sum) + (11244144979801/1379000000000000000000000000 : ℝ)*base65 + (85560672373522417/11032000000000000000000000000000 : ℝ)*base68 + (65716428284909583/11032000000000000000000000000000 : ℝ)*base69 + (1266479546986417/11032000000000000000000000000000 : ℝ)*base72 + (263026008183/1379000000000000000000000000 : ℝ)*base74 + (50207734018837583/11032000000000000000000000000000 : ℝ)*base75 + (25640287137013583/11032000000000000000000000000000 : ℝ)*base77 + (11134065019906417/11032000000000000000000000000000 : ℝ)*base80 + (3030164071087/1379000000000000000000000000 : ℝ)*base81 + (9741749/2500000000000000000000 : ℝ)*base90 + (9741749/2500000000000000000000 : ℝ)*base92 + (9741749/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54426044615165613054692871/6895000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1917243269/100000000000000 : ℝ)*(base19) + (219290149/12500000000000 : ℝ)*(base23) + (431173/25000000000000 : ℝ)*(upper2) + (12121619/4000000000000 : ℝ)*(upper3) + (13324799/25000000000000 : ℝ)*(upper5) + (867060756962501/25000000000000 : ℝ)*(major0) + (867060756962501/25000000000000 : ℝ)*(major1) + (867060756962501/25000000000000 : ℝ)*(major2) + (16602983029/50000000000000 : ℝ)*(sp1) + (14937087033/50000000000000 : ℝ)*(sp2) + (2291847762512593/50000000000000 : ℝ)*(sp4) + (229183020090793/5000000000000 : ℝ)*(sp5) + (4583663896529927/100000000000000 : ℝ)*(sp6) + (2352790267556397/100000000000000 : ℝ)*(sp7) + (2352790267556397/100000000000000 : ℝ)*(f.failure) + (2291847762512593/50000000000000 : ℝ)*(f.sum) + (4912334043151/1292812500000000000000000000 : ℝ)*base65 + (195456493022733871/41370000000000000000000000000000 : ℝ)*base67 + (252034519088486129/41370000000000000000000000000000 : ℝ)*base70 + (259923375889346129/41370000000000000000000000000000 : ℝ)*base72 + (52071565500923/10342500000000000000000000000 : ℝ)*base73 + (606300083452946129/41370000000000000000000000000000 : ℝ)*base76 + (74691612636236129/41370000000000000000000000000000 : ℝ)*base78 + (435461575464123871/41370000000000000000000000000000 : ℝ)*base79 + (42137197682609/20685000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (22031851/10000000000000000000000 : ℝ)*base89 + (22031851/10000000000000000000000 : ℝ)*base91 + (22031851/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1036_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16839/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1713/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2059/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (299/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1036_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1036_s4_0 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-44348853/200000000 : ℝ)*x 0 + (1081503091/2000000000 : ℝ)*x 1 + (328251587/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44348853/200000000 : ℝ)^8229 ≤ (1346196498487/10000000000000 : ℝ)^6181 := by
    have hnat : (44348853 : ℕ)^8229*10000000000000^6181 ≤ 1346196498487^6181*200000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44348853 200000000 1346196498487 10000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081503091/2000000000 : ℝ)^8229 ≤ (11027315509217/25000000000000 : ℝ)^6181 := by
    have hnat : (1081503091 : ℕ)^8229*25000000000000^6181 ≤ 11027315509217^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081503091 2000000000 11027315509217 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328251587/625000000 : ℝ)^8229 ≤ (10607193238461/25000000000000 : ℝ)^6181 := by
    have hnat : (328251587 : ℕ)^8229*25000000000000^6181 ≤ 10607193238461^6181*625000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328251587 625000000 10607193238461 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44348853/200000000 : ℝ), (1081503091/2000000000 : ℝ), (328251587/625000000 : ℝ)] ![(1346196498487/10000000000000 : ℝ), (11027315509217/25000000000000 : ℝ), (10607193238461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44348853/200000000 : ℝ)|^8229 ≤ (1346196498487/10000000000000 : ℝ)^6181
        have hw : |(-44348853/200000000 : ℝ)|=(44348853/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081503091/2000000000 : ℝ)|^8229 ≤ (11027315509217/25000000000000 : ℝ)^6181
        have hw : |(1081503091/2000000000 : ℝ)|=(1081503091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328251587/625000000 : ℝ)|^8229 ≤ (10607193238461/25000000000000 : ℝ)^6181
        have hw : |(328251587/625000000 : ℝ)|=(328251587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s4_1 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1337044751/2500000000 : ℝ)*x 0 + (-2296558873/10000000000 : ℝ)*x 1 + (1050405087/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337044751/2500000000 : ℝ)^8229 ≤ (1086651413339/2500000000000 : ℝ)^6181 := by
    have hnat : (1337044751 : ℕ)^8229*2500000000000^6181 ≤ 1086651413339^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337044751 2500000000 1086651413339 2500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2296558873/10000000000 : ℝ)^8229 ≤ (3526292508481/25000000000000 : ℝ)^6181 := by
    have hnat : (2296558873 : ℕ)^8229*25000000000000^6181 ≤ 3526292508481^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296558873 10000000000 3526292508481 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050405087/2000000000 : ℝ)^8229 ≤ (42428773416321/100000000000000 : ℝ)^6181 := by
    have hnat : (1050405087 : ℕ)^8229*100000000000000^6181 ≤ 42428773416321^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050405087 2000000000 42428773416321 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337044751/2500000000 : ℝ), (-2296558873/10000000000 : ℝ), (1050405087/2000000000 : ℝ)] ![(1086651413339/2500000000000 : ℝ), (3526292508481/25000000000000 : ℝ), (42428773416321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337044751/2500000000 : ℝ)|^8229 ≤ (1086651413339/2500000000000 : ℝ)^6181
        have hw : |(1337044751/2500000000 : ℝ)|=(1337044751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2296558873/10000000000 : ℝ)|^8229 ≤ (3526292508481/25000000000000 : ℝ)^6181
        have hw : |(-2296558873/10000000000 : ℝ)|=(2296558873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050405087/2000000000 : ℝ)|^8229 ≤ (42428773416321/100000000000000 : ℝ)^6181
        have hw : |(1050405087/2000000000 : ℝ)|=(1050405087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s4_2 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5348179083/10000000000 : ℝ)*x 0 + (1313006333/2500000000 : ℝ)*x 1 + (-287069863/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348179083/10000000000 : ℝ)^8229 ≤ (43466057388351/100000000000000 : ℝ)^6181 := by
    have hnat : (5348179083 : ℕ)^8229*100000000000000^6181 ≤ 43466057388351^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348179083 10000000000 43466057388351 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313006333/2500000000 : ℝ)^8229 ≤ (21214386154263/50000000000000 : ℝ)^6181 := by
    have hnat : (1313006333 : ℕ)^8229*50000000000000^6181 ≤ 21214386154263^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313006333 2500000000 21214386154263 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (287069863/1250000000 : ℝ)^8229 ≤ (881573142963/6250000000000 : ℝ)^6181 := by
    have hnat : (287069863 : ℕ)^8229*6250000000000^6181 ≤ 881573142963^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287069863 1250000000 881573142963 6250000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348179083/10000000000 : ℝ), (1313006333/2500000000 : ℝ), (-287069863/1250000000 : ℝ)] ![(43466057388351/100000000000000 : ℝ), (21214386154263/50000000000000 : ℝ), (881573142963/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348179083/10000000000 : ℝ)|^8229 ≤ (43466057388351/100000000000000 : ℝ)^6181
        have hw : |(5348179083/10000000000 : ℝ)|=(5348179083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313006333/2500000000 : ℝ)|^8229 ≤ (21214386154263/50000000000000 : ℝ)^6181
        have hw : |(1313006333/2500000000 : ℝ)|=(1313006333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-287069863/1250000000 : ℝ)|^8229 ≤ (881573142963/6250000000000 : ℝ)^6181
        have hw : |(-287069863/1250000000 : ℝ)|=(287069863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s4_3 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379139891/10000000000 : ℝ)*x 0 + (132198399/312500000 : ℝ)*x 1 + (2266636931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379139891/10000000000 : ℝ)^8229 ≤ (8327359737651/25000000000000 : ℝ)^6181 := by
    have hnat : (4379139891 : ℕ)^8229*25000000000000^6181 ≤ 8327359737651^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379139891 10000000000 8327359737651 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132198399/312500000 : ℝ)^8229 ≤ (31811226464837/100000000000000 : ℝ)^6181 := by
    have hnat : (132198399 : ℕ)^8229*100000000000000^6181 ≤ 31811226464837^6181*312500000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132198399 312500000 31811226464837 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266636931/5000000000 : ℝ)^8229 ≤ (17439667287139/50000000000000 : ℝ)^6181 := by
    have hnat : (2266636931 : ℕ)^8229*50000000000000^6181 ≤ 17439667287139^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266636931 5000000000 17439667287139 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379139891/10000000000 : ℝ), (132198399/312500000 : ℝ), (2266636931/5000000000 : ℝ)] ![(8327359737651/25000000000000 : ℝ), (31811226464837/100000000000000 : ℝ), (17439667287139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379139891/10000000000 : ℝ)|^8229 ≤ (8327359737651/25000000000000 : ℝ)^6181
        have hw : |(4379139891/10000000000 : ℝ)|=(4379139891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132198399/312500000 : ℝ)|^8229 ≤ (31811226464837/100000000000000 : ℝ)^6181
        have hw : |(132198399/312500000 : ℝ)|=(132198399/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2266636931/5000000000 : ℝ)|^8229 ≤ (17439667287139/50000000000000 : ℝ)^6181
        have hw : |(2266636931/5000000000 : ℝ)|=(2266636931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s4_4 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2217451423/10000000000 : ℝ)*x 0 + (2626243251/5000000000 : ℝ)*x 1 + (5407052239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2217451423/10000000000 : ℝ)^8229 ≤ (13462035892471/100000000000000 : ℝ)^6181 := by
    have hnat : (2217451423 : ℕ)^8229*100000000000000^6181 ≤ 13462035892471^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217451423 10000000000 13462035892471 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626243251/5000000000 : ℝ)^8229 ≤ (21216866198011/50000000000000 : ℝ)^6181 := by
    have hnat : (2626243251 : ℕ)^8229*50000000000000^6181 ≤ 21216866198011^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626243251 5000000000 21216866198011 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407052239/10000000000 : ℝ)^8229 ≤ (689128620193/1562500000000 : ℝ)^6181 := by
    have hnat : (5407052239 : ℕ)^8229*1562500000000^6181 ≤ 689128620193^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407052239 10000000000 689128620193 1562500000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2217451423/10000000000 : ℝ), (2626243251/5000000000 : ℝ), (5407052239/10000000000 : ℝ)] ![(13462035892471/100000000000000 : ℝ), (21216866198011/50000000000000 : ℝ), (689128620193/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2217451423/10000000000 : ℝ)|^8229 ≤ (13462035892471/100000000000000 : ℝ)^6181
        have hw : |(-2217451423/10000000000 : ℝ)|=(2217451423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626243251/5000000000 : ℝ)|^8229 ≤ (21216866198011/50000000000000 : ℝ)^6181
        have hw : |(2626243251/5000000000 : ℝ)|=(2626243251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407052239/10000000000 : ℝ)|^8229 ≤ (689128620193/1562500000000 : ℝ)^6181
        have hw : |(5407052239/10000000000 : ℝ)|=(5407052239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s4_5 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309110473/10000000000 : ℝ)*x 0 + (-2141532203/10000000000 : ℝ)*x 1 + (5407052127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309110473/10000000000 : ℝ)^8229 ≤ (21521921116399/50000000000000 : ℝ)^6181 := by
    have hnat : (5309110473 : ℕ)^8229*50000000000000^6181 ≤ 21521921116399^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309110473 10000000000 21521921116399 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2141532203/10000000000 : ℝ)^8229 ≤ (12851927274609/100000000000000 : ℝ)^6181 := by
    have hnat : (2141532203 : ℕ)^8229*100000000000000^6181 ≤ 12851927274609^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141532203 10000000000 12851927274609 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407052127/10000000000 : ℝ)^8229 ≤ (44104230476093/100000000000000 : ℝ)^6181 := by
    have hnat : (5407052127 : ℕ)^8229*100000000000000^6181 ≤ 44104230476093^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407052127 10000000000 44104230476093 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309110473/10000000000 : ℝ), (-2141532203/10000000000 : ℝ), (5407052127/10000000000 : ℝ)] ![(21521921116399/50000000000000 : ℝ), (12851927274609/100000000000000 : ℝ), (44104230476093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309110473/10000000000 : ℝ)|^8229 ≤ (21521921116399/50000000000000 : ℝ)^6181
        have hw : |(5309110473/10000000000 : ℝ)|=(5309110473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2141532203/10000000000 : ℝ)|^8229 ≤ (12851927274609/100000000000000 : ℝ)^6181
        have hw : |(-2141532203/10000000000 : ℝ)|=(2141532203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407052127/10000000000 : ℝ)|^8229 ≤ (44104230476093/100000000000000 : ℝ)^6181
        have hw : |(5407052127/10000000000 : ℝ)|=(5407052127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s4_6 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309110463/10000000000 : ℝ)*x 0 + (5407052173/10000000000 : ℝ)*x 1 + (-1070766077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309110463/10000000000 : ℝ)^8229 ≤ (2152192106243/5000000000000 : ℝ)^6181 := by
    have hnat : (5309110463 : ℕ)^8229*5000000000000^6181 ≤ 2152192106243^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309110463 10000000000 2152192106243 5000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407052173/10000000000 : ℝ)^8229 ≤ (11026057743907/25000000000000 : ℝ)^6181 := by
    have hnat : (5407052173 : ℕ)^8229*25000000000000^6181 ≤ 11026057743907^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407052173 10000000000 11026057743907 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1070766077/5000000000 : ℝ)^8229 ≤ (1606490860389/12500000000000 : ℝ)^6181 := by
    have hnat : (1070766077 : ℕ)^8229*12500000000000^6181 ≤ 1606490860389^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070766077 5000000000 1606490860389 12500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309110463/10000000000 : ℝ), (5407052173/10000000000 : ℝ), (-1070766077/5000000000 : ℝ)] ![(2152192106243/5000000000000 : ℝ), (11026057743907/25000000000000 : ℝ), (1606490860389/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309110463/10000000000 : ℝ)|^8229 ≤ (2152192106243/5000000000000 : ℝ)^6181
        have hw : |(5309110463/10000000000 : ℝ)|=(5309110463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407052173/10000000000 : ℝ)|^8229 ≤ (11026057743907/25000000000000 : ℝ)^6181
        have hw : |(5407052173/10000000000 : ℝ)|=(5407052173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1070766077/5000000000 : ℝ)|^8229 ≤ (1606490860389/12500000000000 : ℝ)^6181
        have hw : |(-1070766077/5000000000 : ℝ)|=(1070766077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s4_7 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2189578313/5000000000 : ℝ)*x 0 + (4532374807/10000000000 : ℝ)*x 1 + (528906459/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189578313/5000000000 : ℝ)^8229 ≤ (33309608420597/100000000000000 : ℝ)^6181 := by
    have hnat : (2189578313 : ℕ)^8229*100000000000000^6181 ≤ 33309608420597^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189578313 5000000000 33309608420597 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4532374807/10000000000 : ℝ)^8229 ≤ (17435062743977/50000000000000 : ℝ)^6181 := by
    have hnat : (4532374807 : ℕ)^8229*50000000000000^6181 ≤ 17435062743977^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532374807 10000000000 17435062743977 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528906459/1250000000 : ℝ)^8229 ≤ (31820266070607/100000000000000 : ℝ)^6181 := by
    have hnat : (528906459 : ℕ)^8229*100000000000000^6181 ≤ 31820266070607^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528906459 1250000000 31820266070607 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189578313/5000000000 : ℝ), (4532374807/10000000000 : ℝ), (528906459/1250000000 : ℝ)] ![(33309608420597/100000000000000 : ℝ), (17435062743977/50000000000000 : ℝ), (31820266070607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189578313/5000000000 : ℝ)|^8229 ≤ (33309608420597/100000000000000 : ℝ)^6181
        have hw : |(2189578313/5000000000 : ℝ)|=(2189578313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4532374807/10000000000 : ℝ)|^8229 ≤ (17435062743977/50000000000000 : ℝ)^6181
        have hw : |(4532374807/10000000000 : ℝ)|=(4532374807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528906459/1250000000 : ℝ)|^8229 ≤ (31820266070607/100000000000000 : ℝ)^6181
        have hw : |(528906459/1250000000 : ℝ)|=(528906459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1036_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (299/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2059/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2739/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14249/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (299/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2059/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (299/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2059/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (299/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2059/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (299/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2059/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (299/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2059/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (299/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2059/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2059/20000 : ℝ) ^ (2057/512 : ℝ) ≤ (10793175189990877/100000000000000000000 : ℝ) := by
    have hpowers : (2059/20000 : ℝ)^2057 ≤ (10793175189990877/100000000000000000000 : ℝ)^512 := by
      have hnat : (2059 : ℕ)^2057*100000000000000000000^512 ≤ 10793175189990877^512*20000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2059 20000 10793175189990877 100000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2059/20000 : ℝ)) (X := (10793175189990877/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hpowhi : (299/2000 : ℝ) ^ (2057/512 : ℝ) ≤ (24156083084726979/50000000000000000000 : ℝ) := by
    have hpowers : (299/2000 : ℝ)^2057 ≤ (24156083084726979/50000000000000000000 : ℝ)^512 := by
      have hnat : (299 : ℕ)^2057*50000000000000000000^512 ≤ 24156083084726979^512*2000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        299 2000 24156083084726979 50000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (299/2000 : ℝ)) (X := (24156083084726979/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010793175189990877/50000000000000000000 : ℝ) ≤ (10000537254036909/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (50010793175189990877/50000000000000000000 : ℝ)^512 ≤ (10000537254036909/10000000000000000 : ℝ)^2057 := by
      have hnat : (50010793175189990877 : ℕ)^512*10000000000000000^2057 ≤ 10000537254036909^2057*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010793175189990877 50000000000000000000 10000537254036909 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537254036909/10000000000000000 : ℝ)) (X := (50010793175189990877/50000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20011821068271888967/20000000000000000000 : ℝ) ≤ (10001470841998189/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (20011821068271888967/20000000000000000000 : ℝ)^512 ≤ (10001470841998189/10000000000000000 : ℝ)^2057 := by
      have hnat : (20011821068271888967 : ℕ)^512*10000000000000000^2057 ≤ 10001470841998189^2057*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20011821068271888967 20000000000000000000 10001470841998189 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001470841998189/10000000000000000 : ℝ)) (X := (20011821068271888967/20000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25024156083084726979/25000000000000000000 : ℝ) ≤ (10002404429959469/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (25024156083084726979/25000000000000000000 : ℝ)^512 ≤ (10002404429959469/10000000000000000 : ℝ)^2057 := by
      have hnat : (25024156083084726979 : ℕ)^512*10000000000000000^2057 ≤ 10002404429959469^2057*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25024156083084726979 25000000000000000000 10002404429959469 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002404429959469/10000000000000000 : ℝ)) (X := (25024156083084726979/25000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10793175189990877/100000000000000000000 : ℝ) ≤ ((9306655668283811239/9310000000000000000 : ℝ)+2*(2917462379/1454687500000 : ℝ)*(2059/20000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (9306655668283811239/9310000000000000000 : ℝ)+2*(2917462379/1454687500000 : ℝ)*(2059/20000 : ℝ)=(10000537254036909/10000000000000000 : ℝ) by norm_num, show 1+2*(10793175189990877/100000000000000000000 : ℝ)=(50010793175189990877/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24156083084726979/50000000000000000000 : ℝ)+(10793175189990877/100000000000000000000 : ℝ) ≤ ((9306655668283811239/9310000000000000000 : ℝ)+(2917462379/1454687500000 : ℝ)*((299/2000 : ℝ)+(2059/20000 : ℝ)))^(2057/512 : ℝ) := by
    rw [show (9306655668283811239/9310000000000000000 : ℝ)+(2917462379/1454687500000 : ℝ)*((299/2000 : ℝ)+(2059/20000 : ℝ))=(10001470841998189/10000000000000000 : ℝ) by norm_num, show 1+(24156083084726979/50000000000000000000 : ℝ)+(10793175189990877/100000000000000000000 : ℝ)=(20011821068271888967/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24156083084726979/50000000000000000000 : ℝ) ≤ ((9306655668283811239/9310000000000000000 : ℝ)+2*(2917462379/1454687500000 : ℝ)*(299/2000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (9306655668283811239/9310000000000000000 : ℝ)+2*(2917462379/1454687500000 : ℝ)*(299/2000 : ℝ)=(10002404429959469/10000000000000000 : ℝ) by norm_num, show 1+2*(24156083084726979/50000000000000000000 : ℝ)=(25024156083084726979/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9306655668283811239/9310000000000000000 : ℝ)*(X 1 0+X 2 0)+(2917462379/1454687500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (2059/20000 : ℝ)) (hi := (299/2000 : ℝ)) (c := (9306655668283811239/9310000000000000000 : ℝ)) (alpha := (2917462379/1454687500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9306655668283811239/9310000000000000000 : ℝ)*(X 0 1+X 2 1)+(2917462379/1454687500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (2059/20000 : ℝ)) (hi := (299/2000 : ℝ)) (c := (9306655668283811239/9310000000000000000 : ℝ)) (alpha := (2917462379/1454687500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9306655668283811239/9310000000000000000 : ℝ)*(X 0 2+X 1 2)+(2917462379/1454687500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (2059/20000 : ℝ)) (hi := (299/2000 : ℝ)) (c := (9306655668283811239/9310000000000000000 : ℝ)) (alpha := (2917462379/1454687500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-44348853/200000000 : ℝ)*X 0 0+(1081503091/2000000000 : ℝ)*X 0 1+(328251587/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337044751/2500000000 : ℝ)*X 1 0+(-2296558873/10000000000 : ℝ)*X 1 1+(1050405087/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348179083/10000000000 : ℝ)*X 2 0+(1313006333/2500000000 : ℝ)*X 2 1+(-287069863/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4379139891/10000000000 : ℝ)*X 0 0+(132198399/312500000 : ℝ)*X 0 1+(2266636931/5000000000 : ℝ)*X 0 2+(4379139891/10000000000 : ℝ)*X 1 0+(132198399/312500000 : ℝ)*X 1 1+(2266636931/5000000000 : ℝ)*X 1 2+(4379139891/10000000000 : ℝ)*X 2 0+(132198399/312500000 : ℝ)*X 2 1+(2266636931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2217451423/10000000000 : ℝ)*X 0 0+(2626243251/5000000000 : ℝ)*X 0 1+(5407052239/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309110473/10000000000 : ℝ)*X 1 0+(-2141532203/10000000000 : ℝ)*X 1 1+(5407052127/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309110463/10000000000 : ℝ)*X 2 0+(5407052173/10000000000 : ℝ)*X 2 1+(-1070766077/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2189578313/5000000000 : ℝ)*X 0 0+(4532374807/10000000000 : ℝ)*X 0 1+(528906459/1250000000 : ℝ)*X 0 2+(2189578313/5000000000 : ℝ)*X 1 0+(4532374807/10000000000 : ℝ)*X 1 1+(528906459/1250000000 : ℝ)*X 1 2+(2189578313/5000000000 : ℝ)*X 2 0+(4532374807/10000000000 : ℝ)*X 2 1+(528906459/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (695731003737426796495261923/66500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (547657159/25000000000000 : ℝ)*(base19) + (546840139/25000000000000 : ℝ)*(base23) + (52555731/100000000000000 : ℝ)*(lower2) + (280769257/100000000000000 : ℝ)*(upper3) + (91547421/50000000000000 : ℝ)*(upper5) + (4866291101199189/100000000000000 : ℝ)*(major0) + (4866291101199189/100000000000000 : ℝ)*(major1) + (4866291101199189/100000000000000 : ℝ)*(major2) + (6431331533340439/100000000000000 : ℝ)*(sp0) + (6431380107505473/100000000000000 : ℝ)*(sp1) + (6431380110773553/100000000000000 : ℝ)*(sp2) + (20632321785547/625000000000 : ℝ)*(sp3) + (5076479367/10000000000000 : ℝ)*(sp4) + (14034919697/50000000000000 : ℝ)*(sp7) + (1650599777763457/50000000000000 : ℝ)*(f.failure) + (6431382298134109/100000000000000 : ℝ)*(f.sum) + (6398057558941/1163750000000000000000000000 : ℝ)*base65 + (18158296062061285171/931000000000000000000000000000000 : ℝ)*base67 + (13001232132848285171/931000000000000000000000000000000 : ℝ)*base69 + (355505096318285171/931000000000000000000000000000000 : ℝ)*base71 + (31550904019589/4655000000000000000000000000 : ℝ)*base73 + (1230830451901285171/931000000000000000000000000000000 : ℝ)*base75 + (4460746796801285171/931000000000000000000000000000000 : ℝ)*base77 + (12281249159320285171/931000000000000000000000000000000 : ℝ)*base79 + (2298790246063/581875000000000000000000000 : ℝ)*base81 + (28300169/5000000000000000000000 : ℝ)*base90 + (28300169/5000000000000000000000 : ℝ)*base92 + (28300169/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1836999001238084160048887727/232750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22385497/1250000000000 : ℝ)*(base19) + (949051343/50000000000000 : ℝ)*(base23) + (84983639/100000000000000 : ℝ)*(upper2) + (33411193/50000000000000 : ℝ)*(upper3) + (20516469/5000000000000 : ℝ)*(upper5) + (4895322419597469/100000000000000 : ℝ)*(major0) + (4895322419597469/100000000000000 : ℝ)*(major1) + (4895322419597469/100000000000000 : ℝ)*(major2) + (22036197891/50000000000000 : ℝ)*(sp1) + (38552055139/100000000000000 : ℝ)*(sp2) + (6469750724988019/100000000000000 : ℝ)*(sp4) + (6469704861752477/100000000000000 : ℝ)*(sp5) + (3234855137415097/50000000000000 : ℝ)*(sp6) + (3320893851120769/100000000000000 : ℝ)*(sp7) + (3320893851120769/100000000000000 : ℝ)*(f.failure) + (6469750724988019/100000000000000 : ℝ)*(f.sum) + (1402372981771/4655000000000000000000000000 : ℝ)*base66 + (1391896491086445909/931000000000000000000000000000000 : ℝ)*base68 + (5569177299885554091/931000000000000000000000000000000 : ℝ)*base69 + (13063524496431554091/931000000000000000000000000000000 : ℝ)*base71 + (8606800243583/2327500000000000000000000000 : ℝ)*base74 + (6705966277237554091/931000000000000000000000000000000 : ℝ)*base75 + (4189954384521554091/931000000000000000000000000000000 : ℝ)*base77 + (3772106185781554091/931000000000000000000000000000000 : ℝ)*base79 + (224496137129/1163750000000000000000000000 : ℝ)*base82 + (34916873/10000000000000000000000 : ℝ)*base90 + (34916873/10000000000000000000000 : ℝ)*base92 + (34916873/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1036_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (299/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2059/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2739/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14249/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1036_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1036_s5_0 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-443672473/2000000000 : ℝ)*x 0 + (134946991/250000000 : ℝ)*x 1 + (5261058161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443672473/2000000000 : ℝ)^8229 ≤ (13469399069257/100000000000000 : ℝ)^6181 := by
    have hnat : (443672473 : ℕ)^8229*100000000000000^6181 ≤ 13469399069257^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443672473 2000000000 13469399069257 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134946991/250000000 : ℝ)^8229 ≤ (5500581284379/12500000000000 : ℝ)^6181 := by
    have hnat : (134946991 : ℕ)^8229*12500000000000^6181 ≤ 5500581284379^6181*250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134946991 250000000 5500581284379 12500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261058161/10000000000 : ℝ)^8229 ≤ (42525950640273/100000000000000 : ℝ)^6181 := by
    have hnat : (5261058161 : ℕ)^8229*100000000000000^6181 ≤ 42525950640273^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261058161 10000000000 42525950640273 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-443672473/2000000000 : ℝ), (134946991/250000000 : ℝ), (5261058161/10000000000 : ℝ)] ![(13469399069257/100000000000000 : ℝ), (5500581284379/12500000000000 : ℝ), (42525950640273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-443672473/2000000000 : ℝ)|^8229 ≤ (13469399069257/100000000000000 : ℝ)^6181
        have hw : |(-443672473/2000000000 : ℝ)|=(443672473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134946991/250000000 : ℝ)|^8229 ≤ (5500581284379/12500000000000 : ℝ)^6181
        have hw : |(134946991/250000000 : ℝ)|=(134946991/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261058161/10000000000 : ℝ)|^8229 ≤ (42525950640273/100000000000000 : ℝ)^6181
        have hw : |(5261058161/10000000000 : ℝ)|=(5261058161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s5_1 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672893061/5000000000 : ℝ)*x 0 + (-114391757/500000000 : ℝ)*x 1 + (5261058197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672893061/5000000000 : ℝ)^8229 ≤ (21720083574949/50000000000000 : ℝ)^6181 := by
    have hnat : (2672893061 : ℕ)^8229*50000000000000^6181 ≤ 21720083574949^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672893061 5000000000 21720083574949 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114391757/500000000 : ℝ)^8229 ≤ (2806776361773/20000000000000 : ℝ)^6181 := by
    have hnat : (114391757 : ℕ)^8229*20000000000000^6181 ≤ 2806776361773^6181*500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114391757 500000000 2806776361773 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261058197/10000000000 : ℝ)^8229 ≤ (10631487756921/25000000000000 : ℝ)^6181 := by
    have hnat : (5261058197 : ℕ)^8229*25000000000000^6181 ≤ 10631487756921^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261058197 10000000000 10631487756921 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672893061/5000000000 : ℝ), (-114391757/500000000 : ℝ), (5261058197/10000000000 : ℝ)] ![(21720083574949/50000000000000 : ℝ), (2806776361773/20000000000000 : ℝ), (10631487756921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672893061/5000000000 : ℝ)|^8229 ≤ (21720083574949/50000000000000 : ℝ)^6181
        have hw : |(2672893061/5000000000 : ℝ)|=(2672893061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-114391757/500000000 : ℝ)|^8229 ≤ (2806776361773/20000000000000 : ℝ)^6181
        have hw : |(-114391757/500000000 : ℝ)|=(114391757/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261058197/10000000000 : ℝ)|^8229 ≤ (10631487756921/25000000000000 : ℝ)^6181
        have hw : |(5261058197/10000000000 : ℝ)|=(5261058197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s5_2 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336446527/2500000000 : ℝ)*x 0 + (82204033/156250000 : ℝ)*x 1 + (-228783527/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336446527/2500000000 : ℝ)^8229 ≤ (43440166998439/100000000000000 : ℝ)^6181 := by
    have hnat : (1336446527 : ℕ)^8229*100000000000000^6181 ≤ 43440166998439^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336446527 2500000000 43440166998439 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82204033/156250000 : ℝ)^8229 ≤ (10631487528241/25000000000000 : ℝ)^6181 := by
    have hnat : (82204033 : ℕ)^8229*25000000000000^6181 ≤ 10631487528241^6181*156250000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82204033 156250000 10631487528241 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228783527/1000000000 : ℝ)^8229 ≤ (14033882870523/100000000000000 : ℝ)^6181 := by
    have hnat : (228783527 : ℕ)^8229*100000000000000^6181 ≤ 14033882870523^6181*1000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228783527 1000000000 14033882870523 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336446527/2500000000 : ℝ), (82204033/156250000 : ℝ), (-228783527/1000000000 : ℝ)] ![(43440166998439/100000000000000 : ℝ), (10631487528241/25000000000000 : ℝ), (14033882870523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336446527/2500000000 : ℝ)|^8229 ≤ (43440166998439/100000000000000 : ℝ)^6181
        have hw : |(1336446527/2500000000 : ℝ)|=(1336446527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82204033/156250000 : ℝ)|^8229 ≤ (10631487528241/25000000000000 : ℝ)^6181
        have hw : |(82204033/156250000 : ℝ)|=(82204033/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-228783527/1000000000 : ℝ)|^8229 ≤ (14033882870523/100000000000000 : ℝ)^6181
        have hw : |(-228783527/1000000000 : ℝ)|=(228783527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s5_3 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (175186887/400000000 : ℝ)*x 0 + (849692673/2000000000 : ℝ)*x 1 + (4515018681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175186887/400000000 : ℝ)^8229 ≤ (33314829325543/100000000000000 : ℝ)^6181 := by
    have hnat : (175186887 : ℕ)^8229*100000000000000^6181 ≤ 33314829325543^6181*400000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175186887 400000000 33314829325543 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849692673/2000000000 : ℝ)^8229 ≤ (999772079011/3125000000000 : ℝ)^6181 := by
    have hnat : (849692673 : ℕ)^8229*3125000000000^6181 ≤ 999772079011^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849692673 2000000000 999772079011 3125000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4515018681/10000000000 : ℝ)^8229 ≤ (34692464135557/100000000000000 : ℝ)^6181 := by
    have hnat : (4515018681 : ℕ)^8229*100000000000000^6181 ≤ 34692464135557^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515018681 10000000000 34692464135557 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(175186887/400000000 : ℝ), (849692673/2000000000 : ℝ), (4515018681/10000000000 : ℝ)] ![(33314829325543/100000000000000 : ℝ), (999772079011/3125000000000 : ℝ), (34692464135557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(175186887/400000000 : ℝ)|^8229 ≤ (33314829325543/100000000000000 : ℝ)^6181
        have hw : |(175186887/400000000 : ℝ)|=(175186887/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849692673/2000000000 : ℝ)|^8229 ≤ (999772079011/3125000000000 : ℝ)^6181
        have hw : |(849692673/2000000000 : ℝ)|=(849692673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4515018681/10000000000 : ℝ)|^8229 ≤ (34692464135557/100000000000000 : ℝ)^6181
        have hw : |(4515018681/10000000000 : ℝ)|=(4515018681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s5_4 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2218368281/10000000000 : ℝ)*x 0 + (5261415601/10000000000 : ℝ)*x 1 + (2698760407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2218368281/10000000000 : ℝ)^8229 ≤ (3367361722943/25000000000000 : ℝ)^6181 := by
    have hnat : (2218368281 : ℕ)^8229*25000000000000^6181 ≤ 3367361722943^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218368281 10000000000 3367361722943 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261415601/10000000000 : ℝ)^8229 ≤ (21264898621283/50000000000000 : ℝ)^6181 := by
    have hnat : (5261415601 : ℕ)^8229*50000000000000^6181 ≤ 21264898621283^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261415601 10000000000 21264898621283 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698760407/5000000000 : ℝ)^8229 ≤ (11000188963691/25000000000000 : ℝ)^6181 := by
    have hnat : (2698760407 : ℕ)^8229*25000000000000^6181 ≤ 11000188963691^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698760407 5000000000 11000188963691 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2218368281/10000000000 : ℝ), (5261415601/10000000000 : ℝ), (2698760407/5000000000 : ℝ)] ![(3367361722943/25000000000000 : ℝ), (21264898621283/50000000000000 : ℝ), (11000188963691/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2218368281/10000000000 : ℝ)|^8229 ≤ (3367361722943/25000000000000 : ℝ)^6181
        have hw : |(-2218368281/10000000000 : ℝ)|=(2218368281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261415601/10000000000 : ℝ)|^8229 ≤ (21264898621283/50000000000000 : ℝ)^6181
        have hw : |(5261415601/10000000000 : ℝ)|=(5261415601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698760407/5000000000 : ℝ)|^8229 ≤ (11000188963691/25000000000000 : ℝ)^6181
        have hw : |(2698760407/5000000000 : ℝ)|=(2698760407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s5_5 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311407351/10000000000 : ℝ)*x 0 + (-2151372459/10000000000 : ℝ)*x 1 + (2698760401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311407351/10000000000 : ℝ)^8229 ≤ (43068636235177/100000000000000 : ℝ)^6181 := by
    have hnat : (5311407351 : ℕ)^8229*100000000000000^6181 ≤ 43068636235177^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311407351 10000000000 43068636235177 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2151372459/10000000000 : ℝ)^8229 ≤ (12930608027243/100000000000000 : ℝ)^6181 := by
    have hnat : (2151372459 : ℕ)^8229*100000000000000^6181 ≤ 12930608027243^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151372459 10000000000 12930608027243 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698760401/5000000000 : ℝ)^8229 ≤ (22000377862263/50000000000000 : ℝ)^6181 := by
    have hnat : (2698760401 : ℕ)^8229*50000000000000^6181 ≤ 22000377862263^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698760401 5000000000 22000377862263 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311407351/10000000000 : ℝ), (-2151372459/10000000000 : ℝ), (2698760401/5000000000 : ℝ)] ![(43068636235177/100000000000000 : ℝ), (12930608027243/100000000000000 : ℝ), (22000377862263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311407351/10000000000 : ℝ)|^8229 ≤ (43068636235177/100000000000000 : ℝ)^6181
        have hw : |(5311407351/10000000000 : ℝ)|=(5311407351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2151372459/10000000000 : ℝ)|^8229 ≤ (12930608027243/100000000000000 : ℝ)^6181
        have hw : |(-2151372459/10000000000 : ℝ)|=(2151372459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698760401/5000000000 : ℝ)|^8229 ≤ (22000377862263/50000000000000 : ℝ)^6181
        have hw : |(2698760401/5000000000 : ℝ)|=(2698760401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s5_6 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327851831/2500000000 : ℝ)*x 0 + (269876041/500000000 : ℝ)*x 1 + (-268921559/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327851831/2500000000 : ℝ)^8229 ≤ (43068635943701/100000000000000 : ℝ)^6181 := by
    have hnat : (1327851831 : ℕ)^8229*100000000000000^6181 ≤ 43068635943701^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327851831 2500000000 43068635943701 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269876041/500000000 : ℝ)^8229 ≤ (22000377959941/50000000000000 : ℝ)^6181 := by
    have hnat : (269876041 : ℕ)^8229*50000000000000^6181 ≤ 22000377959941^6181*500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269876041 500000000 22000377959941 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268921559/1250000000 : ℝ)^8229 ≤ (3232652032817/25000000000000 : ℝ)^6181 := by
    have hnat : (268921559 : ℕ)^8229*25000000000000^6181 ≤ 3232652032817^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268921559 1250000000 3232652032817 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327851831/2500000000 : ℝ), (269876041/500000000 : ℝ), (-268921559/1250000000 : ℝ)] ![(43068635943701/100000000000000 : ℝ), (22000377959941/50000000000000 : ℝ), (3232652032817/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327851831/2500000000 : ℝ)|^8229 ≤ (43068635943701/100000000000000 : ℝ)^6181
        have hw : |(1327851831/2500000000 : ℝ)|=(1327851831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269876041/500000000 : ℝ)|^8229 ≤ (22000377959941/50000000000000 : ℝ)^6181
        have hw : |(269876041/500000000 : ℝ)|=(269876041/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-268921559/1250000000 : ℝ)|^8229 ≤ (3232652032817/25000000000000 : ℝ)^6181
        have hw : |(-268921559/1250000000 : ℝ)|=(268921559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s5_7 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379683571/10000000000 : ℝ)*x 0 + (4514322161/10000000000 : ℝ)*x 1 + (2124581261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379683571/10000000000 : ℝ)^8229 ≤ (16657472366907/50000000000000 : ℝ)^6181 := by
    have hnat : (4379683571 : ℕ)^8229*50000000000000^6181 ≤ 16657472366907^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379683571 10000000000 16657472366907 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514322161/10000000000 : ℝ)^8229 ≤ (17342669555163/50000000000000 : ℝ)^6181 := by
    have hnat : (4514322161 : ℕ)^8229*50000000000000^6181 ≤ 17342669555163^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514322161 10000000000 17342669555163 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124581261/5000000000 : ℝ)^8229 ≤ (999991129383/3125000000000 : ℝ)^6181 := by
    have hnat : (2124581261 : ℕ)^8229*3125000000000^6181 ≤ 999991129383^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124581261 5000000000 999991129383 3125000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379683571/10000000000 : ℝ), (4514322161/10000000000 : ℝ), (2124581261/5000000000 : ℝ)] ![(16657472366907/50000000000000 : ℝ), (17342669555163/50000000000000 : ℝ), (999991129383/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379683571/10000000000 : ℝ)|^8229 ≤ (16657472366907/50000000000000 : ℝ)^6181
        have hw : |(4379683571/10000000000 : ℝ)|=(4379683571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514322161/10000000000 : ℝ)|^8229 ≤ (17342669555163/50000000000000 : ℝ)^6181
        have hw : |(4514322161/10000000000 : ℝ)|=(4514322161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124581261/5000000000 : ℝ)|^8229 ≤ (999991129383/3125000000000 : ℝ)^6181
        have hw : |(2124581261/5000000000 : ℝ)|=(2124581261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1036_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14249/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2739/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11149/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14047/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14249/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2739/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14249/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2739/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14249/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2739/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14249/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2739/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14249/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2739/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14249/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2739/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2739/25000 : ℝ) ^ (2057/512 : ℝ) ≤ (13858843085132381/100000000000000000000 : ℝ) := by
    have hpowers : (2739/25000 : ℝ)^2057 ≤ (13858843085132381/100000000000000000000 : ℝ)^512 := by
      have hnat : (2739 : ℕ)^2057*100000000000000000000^512 ≤ 13858843085132381^512*25000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2739 25000 13858843085132381 100000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2739/25000 : ℝ)) (X := (13858843085132381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14249/100000 : ℝ) ^ (2057/512 : ℝ) ≤ (1991740096385341/5000000000000000000 : ℝ) := by
    have hpowers : (14249/100000 : ℝ)^2057 ≤ (1991740096385341/5000000000000000000 : ℝ)^512 := by
      have hnat : (14249 : ℕ)^2057*5000000000000000000^512 ≤ 1991740096385341^512*100000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14249 100000 1991740096385341 5000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14249/100000 : ℝ)) (X := (1991740096385341/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013858843085132381/50000000000000000000 : ℝ) ≤ (10000689838518629/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (50013858843085132381/50000000000000000000 : ℝ)^512 ≤ (10000689838518629/10000000000000000 : ℝ)^2057 := by
      have hnat : (50013858843085132381 : ℕ)^512*10000000000000000^2057 ≤ 10000689838518629^2057*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013858843085132381 50000000000000000000 10000689838518629 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000689838518629/10000000000000000 : ℝ)) (X := (50013858843085132381/50000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053693645012839201/100000000000000000000 : ℝ) ≤ (5000668099283809/5000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (100053693645012839201/100000000000000000000 : ℝ)^512 ≤ (5000668099283809/5000000000000000 : ℝ)^2057 := by
      have hnat : (100053693645012839201 : ℕ)^512*5000000000000000^2057 ≤ 5000668099283809^2057*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053693645012839201 100000000000000000000 5000668099283809 5000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000668099283809/5000000000000000 : ℝ)) (X := (100053693645012839201/100000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501991740096385341/2500000000000000000 : ℝ) ≤ (10001982558616607/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (2501991740096385341/2500000000000000000 : ℝ)^512 ≤ (10001982558616607/10000000000000000 : ℝ)^2057 := by
      have hnat : (2501991740096385341 : ℕ)^512*10000000000000000^2057 ≤ 10001982558616607^2057*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501991740096385341 2500000000000000000 10001982558616607 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001982558616607/10000000000000000 : ℝ)) (X := (2501991740096385341/2500000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13858843085132381/100000000000000000000 : ℝ) ≤ ((32918108596848398329/32930000000000000000 : ℝ)+2*(646360048989/329300000000000 : ℝ)*(2739/25000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (32918108596848398329/32930000000000000000 : ℝ)+2*(646360048989/329300000000000 : ℝ)*(2739/25000 : ℝ)=(10000689838518629/10000000000000000 : ℝ) by norm_num, show 1+2*(13858843085132381/100000000000000000000 : ℝ)=(50013858843085132381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1991740096385341/5000000000000000000 : ℝ)+(13858843085132381/100000000000000000000 : ℝ) ≤ ((32918108596848398329/32930000000000000000 : ℝ)+(646360048989/329300000000000 : ℝ)*((14249/100000 : ℝ)+(2739/25000 : ℝ)))^(2057/512 : ℝ) := by
    rw [show (32918108596848398329/32930000000000000000 : ℝ)+(646360048989/329300000000000 : ℝ)*((14249/100000 : ℝ)+(2739/25000 : ℝ))=(5000668099283809/5000000000000000 : ℝ) by norm_num, show 1+(1991740096385341/5000000000000000000 : ℝ)+(13858843085132381/100000000000000000000 : ℝ)=(100053693645012839201/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1991740096385341/5000000000000000000 : ℝ) ≤ ((32918108596848398329/32930000000000000000 : ℝ)+2*(646360048989/329300000000000 : ℝ)*(14249/100000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (32918108596848398329/32930000000000000000 : ℝ)+2*(646360048989/329300000000000 : ℝ)*(14249/100000 : ℝ)=(10001982558616607/10000000000000000 : ℝ) by norm_num, show 1+2*(1991740096385341/5000000000000000000 : ℝ)=(2501991740096385341/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32918108596848398329/32930000000000000000 : ℝ)*(X 1 0+X 2 0)+(646360048989/329300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (2739/25000 : ℝ)) (hi := (14249/100000 : ℝ)) (c := (32918108596848398329/32930000000000000000 : ℝ)) (alpha := (646360048989/329300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32918108596848398329/32930000000000000000 : ℝ)*(X 0 1+X 2 1)+(646360048989/329300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (2739/25000 : ℝ)) (hi := (14249/100000 : ℝ)) (c := (32918108596848398329/32930000000000000000 : ℝ)) (alpha := (646360048989/329300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32918108596848398329/32930000000000000000 : ℝ)*(X 0 2+X 1 2)+(646360048989/329300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (2739/25000 : ℝ)) (hi := (14249/100000 : ℝ)) (c := (32918108596848398329/32930000000000000000 : ℝ)) (alpha := (646360048989/329300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-443672473/2000000000 : ℝ)*X 0 0+(134946991/250000000 : ℝ)*X 0 1+(5261058161/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672893061/5000000000 : ℝ)*X 1 0+(-114391757/500000000 : ℝ)*X 1 1+(5261058197/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336446527/2500000000 : ℝ)*X 2 0+(82204033/156250000 : ℝ)*X 2 1+(-228783527/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((175186887/400000000 : ℝ)*X 0 0+(849692673/2000000000 : ℝ)*X 0 1+(4515018681/10000000000 : ℝ)*X 0 2+(175186887/400000000 : ℝ)*X 1 0+(849692673/2000000000 : ℝ)*X 1 1+(4515018681/10000000000 : ℝ)*X 1 2+(175186887/400000000 : ℝ)*X 2 0+(849692673/2000000000 : ℝ)*X 2 1+(4515018681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2218368281/10000000000 : ℝ)*X 0 0+(5261415601/10000000000 : ℝ)*X 0 1+(2698760407/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311407351/10000000000 : ℝ)*X 1 0+(-2151372459/10000000000 : ℝ)*X 1 1+(2698760401/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327851831/2500000000 : ℝ)*X 2 0+(269876041/500000000 : ℝ)*X 2 1+(-268921559/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4379683571/10000000000 : ℝ)*X 0 0+(4514322161/10000000000 : ℝ)*X 0 1+(2124581261/5000000000 : ℝ)*X 0 2+(4379683571/10000000000 : ℝ)*X 1 0+(4514322161/10000000000 : ℝ)*X 1 1+(2124581261/5000000000 : ℝ)*X 1 2+(4379683571/10000000000 : ℝ)*X 2 0+(4514322161/10000000000 : ℝ)*X 2 1+(2124581261/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12942994028503314573114103599/1646500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1339339723/100000000000000 : ℝ)*(base19) + (1174313351/100000000000000 : ℝ)*(base23) + (19715909/20000000000000 : ℝ)*(lower2) + (61703419/20000000000000 : ℝ)*(upper3) + (2574047/12500000000000 : ℝ)*(lower4) + (5530230873466959/100000000000000 : ℝ)*(major0) + (5530230873466959/100000000000000 : ℝ)*(major1) + (5530230873466959/100000000000000 : ℝ)*(major2) + (3654415976732623/50000000000000 : ℝ)*(sp0) + (7308856445375827/100000000000000 : ℝ)*(sp1) + (3654428305201099/50000000000000 : ℝ)*(sp2) + (234473859841223/6250000000000 : ℝ)*(sp3) + (201806643/781250000000 : ℝ)*(sp4) + (21942728337/100000000000000 : ℝ)*(sp7) + (14654701953859/390625000000 : ℝ)*(f.failure) + (7308857784715549/100000000000000 : ℝ)*(f.sum) + (64797959671797/8232500000000000000000000000 : ℝ)*base66 + (53455418644355588489/3293000000000000000000000000000000 : ℝ)*base68 + (95770432628814588489/3293000000000000000000000000000000 : ℝ)*base70 + (50410901838355588489/3293000000000000000000000000000000 : ℝ)*base72 + (15536689916577/8232500000000000000000000000 : ℝ)*base74 + (47040631329915588489/3293000000000000000000000000000000 : ℝ)*base76 + (54725365707925588489/3293000000000000000000000000000000 : ℝ)*base78 + (39420474927731588489/3293000000000000000000000000000000 : ℝ)*base80 + (130500747639379/16465000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (171611/19531250000000000000 : ℝ)*base89 + (171611/19531250000000000000 : ℝ)*base91 + (171611/19531250000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1135546926544398086697057603/164650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1355809017/100000000000000 : ℝ)*(base19) + (728129819/50000000000000 : ℝ)*(base23) + (158925889/100000000000000 : ℝ)*(upper3) + (63505169/100000000000000 : ℝ)*(lower4) + (9033813/6250000000000 : ℝ)*(upper5) + (1111856735530569/20000000000000 : ℝ)*(major0) + (1111856735530569/20000000000000 : ℝ)*(major1) + (1111856735530569/20000000000000 : ℝ)*(major2) + (6687043479/20000000000000 : ℝ)*(sp1) + (4531573829/12500000000000 : ℝ)*(sp2) + (734725455408219/10000000000000 : ℝ)*(sp4) + (7347219763055777/100000000000000 : ℝ)*(sp5) + (7347216845231921/100000000000000 : ℝ)*(sp6) + (3771312571332423/100000000000000 : ℝ)*(sp7) + (3771312571332423/100000000000000 : ℝ)*(f.failure) + (734725455408219/10000000000000 : ℝ)*(f.sum) + (3773839288579/1646500000000000000000000000 : ℝ)*base66 + (10477260334027680799/658600000000000000000000000000000 : ℝ)*base68 + (10181602394565480799/658600000000000000000000000000000 : ℝ)*base70 + (5935988854827880799/658600000000000000000000000000000 : ℝ)*base72 + (2074095257861/3293000000000000000000000000 : ℝ)*base73 + (1216256111727119201/658600000000000000000000000000000 : ℝ)*base75 + (6469270936167680799/658600000000000000000000000000000 : ℝ)*base78 + (13192441453128080799/658600000000000000000000000000000 : ℝ)*base80 + (1386720283281/3293000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (4705791/10000000000000000000000 : ℝ)*base90 + (4705791/10000000000000000000000 : ℝ)*base92 + (4705791/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1036_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14249/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2739/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11149/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1036_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1036_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16839/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1713/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11149/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1036_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1036_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1036_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16839/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1713/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11149/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1036_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

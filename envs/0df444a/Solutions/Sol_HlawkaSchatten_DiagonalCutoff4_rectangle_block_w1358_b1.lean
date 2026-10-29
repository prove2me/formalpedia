-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1358_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:10:27.846767+00:00
-- url     : https://prove2.me/submissions/373c23ee-590e-4fb0-b854-58ef4d693848

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
theorem support_rectangle_w1358_s3_0 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-126789083/625000000 : ℝ)*x 0 + (542516537/1000000000 : ℝ)*x 1 + (1046571323/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126789083/625000000 : ℝ)^2159 ≤ (2470943937199/20000000000000 : ℝ)^1647 := by
    have hnat : (126789083 : ℕ)^2159*20000000000000^1647 ≤ 2470943937199^1647*625000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126789083 625000000 2470943937199 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542516537/1000000000 : ℝ)^2159 ≤ (22429542466441/50000000000000 : ℝ)^1647 := by
    have hnat : (542516537 : ℕ)^2159*50000000000000^1647 ≤ 22429542466441^1647*1000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542516537 1000000000 22429542466441 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046571323/2000000000 : ℝ)^2159 ≤ (42786195375019/100000000000000 : ℝ)^1647 := by
    have hnat : (1046571323 : ℕ)^2159*100000000000000^1647 ≤ 42786195375019^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046571323 2000000000 42786195375019 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-126789083/625000000 : ℝ), (542516537/1000000000 : ℝ), (1046571323/2000000000 : ℝ)] ![(2470943937199/20000000000000 : ℝ), (22429542466441/50000000000000 : ℝ), (42786195375019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-126789083/625000000 : ℝ)|^2159 ≤ (2470943937199/20000000000000 : ℝ)^1647
        have hw : |(-126789083/625000000 : ℝ)|=(126789083/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542516537/1000000000 : ℝ)|^2159 ≤ (22429542466441/50000000000000 : ℝ)^1647
        have hw : |(542516537/1000000000 : ℝ)|=(542516537/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046571323/2000000000 : ℝ)|^2159 ≤ (42786195375019/100000000000000 : ℝ)^1647
        have hw : |(1046571323/2000000000 : ℝ)|=(1046571323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s3_1 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (535211243/1000000000 : ℝ)*x 0 + (-2126870277/10000000000 : ℝ)*x 1 + (1308214133/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535211243/1000000000 : ℝ)^2159 ≤ (5508614169713/12500000000000 : ℝ)^1647 := by
    have hnat : (535211243 : ℕ)^2159*12500000000000^1647 ≤ 5508614169713^1647*1000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535211243 1000000000 5508614169713 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126870277/10000000000 : ℝ)^2159 ≤ (13144892142511/100000000000000 : ℝ)^1647 := by
    have hnat : (2126870277 : ℕ)^2159*100000000000000^1647 ≤ 13144892142511^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126870277 10000000000 13144892142511 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308214133/2500000000 : ℝ)^2159 ≤ (10696548621351/25000000000000 : ℝ)^1647 := by
    have hnat : (1308214133 : ℕ)^2159*25000000000000^1647 ≤ 10696548621351^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308214133 2500000000 10696548621351 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535211243/1000000000 : ℝ), (-2126870277/10000000000 : ℝ), (1308214133/2500000000 : ℝ)] ![(5508614169713/12500000000000 : ℝ), (13144892142511/100000000000000 : ℝ), (10696548621351/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535211243/1000000000 : ℝ)|^2159 ≤ (5508614169713/12500000000000 : ℝ)^1647
        have hw : |(535211243/1000000000 : ℝ)|=(535211243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2126870277/10000000000 : ℝ)|^2159 ≤ (13144892142511/100000000000000 : ℝ)^1647
        have hw : |(-2126870277/10000000000 : ℝ)|=(2126870277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1308214133/2500000000 : ℝ)|^2159 ≤ (10696548621351/25000000000000 : ℝ)^1647
        have hw : |(1308214133/2500000000 : ℝ)|=(1308214133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s3_2 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2676056163/5000000000 : ℝ)*x 0 + (5232856693/10000000000 : ℝ)*x 1 + (-2126870201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676056163/5000000000 : ℝ)^2159 ≤ (4406891223517/10000000000000 : ℝ)^1647 := by
    have hnat : (2676056163 : ℕ)^2159*10000000000000^1647 ≤ 4406891223517^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676056163 5000000000 4406891223517 10000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5232856693/10000000000 : ℝ)^2159 ≤ (42786196211043/100000000000000 : ℝ)^1647 := by
    have hnat : (5232856693 : ℕ)^2159*100000000000000^1647 ≤ 42786196211043^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232856693 10000000000 42786196211043 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126870201/10000000000 : ℝ)^2159 ≤ (13144891526783/100000000000000 : ℝ)^1647 := by
    have hnat : (2126870201 : ℕ)^2159*100000000000000^1647 ≤ 13144891526783^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126870201 10000000000 13144891526783 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676056163/5000000000 : ℝ), (5232856693/10000000000 : ℝ), (-2126870201/10000000000 : ℝ)] ![(4406891223517/10000000000000 : ℝ), (42786196211043/100000000000000 : ℝ), (13144891526783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676056163/5000000000 : ℝ)|^2159 ≤ (4406891223517/10000000000000 : ℝ)^1647
        have hw : |(2676056163/5000000000 : ℝ)|=(2676056163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5232856693/10000000000 : ℝ)|^2159 ≤ (42786196211043/100000000000000 : ℝ)^1647
        have hw : |(5232856693/10000000000 : ℝ)|=(5232856693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2126870201/10000000000 : ℝ)|^2159 ≤ (13144891526783/100000000000000 : ℝ)^1647
        have hw : |(-2126870201/10000000000 : ℝ)|=(2126870201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s3_3 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4321481821/10000000000 : ℝ)*x 0 + (412327173/1000000000 : ℝ)*x 1 + (2264251391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321481821/10000000000 : ℝ)^2159 ≤ (16646865421421/50000000000000 : ℝ)^1647 := by
    have hnat : (4321481821 : ℕ)^2159*50000000000000^1647 ≤ 16646865421421^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321481821 10000000000 16646865421421 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412327173/1000000000 : ℝ)^2159 ≤ (31306383323587/100000000000000 : ℝ)^1647 := by
    have hnat : (412327173 : ℕ)^2159*100000000000000^1647 ≤ 31306383323587^1647*1000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412327173 1000000000 31306383323587 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2264251391/5000000000 : ℝ)^2159 ≤ (17699942907001/50000000000000 : ℝ)^1647 := by
    have hnat : (2264251391 : ℕ)^2159*50000000000000^1647 ≤ 17699942907001^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264251391 5000000000 17699942907001 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321481821/10000000000 : ℝ), (412327173/1000000000 : ℝ), (2264251391/5000000000 : ℝ)] ![(16646865421421/50000000000000 : ℝ), (31306383323587/100000000000000 : ℝ), (17699942907001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321481821/10000000000 : ℝ)|^2159 ≤ (16646865421421/50000000000000 : ℝ)^1647
        have hw : |(4321481821/10000000000 : ℝ)|=(4321481821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(412327173/1000000000 : ℝ)|^2159 ≤ (31306383323587/100000000000000 : ℝ)^1647
        have hw : |(412327173/1000000000 : ℝ)|=(412327173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2264251391/5000000000 : ℝ)|^2159 ≤ (17699942907001/50000000000000 : ℝ)^1647
        have hw : |(2264251391/5000000000 : ℝ)|=(2264251391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s3_4 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-12679023/62500000 : ℝ)*x 0 + (2616825351/5000000000 : ℝ)*x 1 + (5424366589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12679023/62500000 : ℝ)^2159 ≤ (6177433099151/50000000000000 : ℝ)^1647 := by
    have hnat : (12679023 : ℕ)^2159*50000000000000^1647 ≤ 6177433099151^1647*62500000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12679023 62500000 6177433099151 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616825351/5000000000 : ℝ)^2159 ≤ (4279470679867/10000000000000 : ℝ)^1647 := by
    have hnat : (2616825351 : ℕ)^2159*10000000000000^1647 ≤ 4279470679867^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616825351 5000000000 4279470679867 10000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424366589/10000000000 : ℝ)^2159 ≤ (8970085399823/20000000000000 : ℝ)^1647 := by
    have hnat : (5424366589 : ℕ)^2159*20000000000000^1647 ≤ 8970085399823^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424366589 10000000000 8970085399823 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12679023/62500000 : ℝ), (2616825351/5000000000 : ℝ), (5424366589/10000000000 : ℝ)] ![(6177433099151/50000000000000 : ℝ), (4279470679867/10000000000000 : ℝ), (8970085399823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12679023/62500000 : ℝ)|^2159 ≤ (6177433099151/50000000000000 : ℝ)^1647
        have hw : |(-12679023/62500000 : ℝ)|=(12679023/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616825351/5000000000 : ℝ)|^2159 ≤ (4279470679867/10000000000000 : ℝ)^1647
        have hw : |(2616825351/5000000000 : ℝ)|=(2616825351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424366589/10000000000 : ℝ)|^2159 ≤ (8970085399823/20000000000000 : ℝ)^1647
        have hw : |(5424366589/10000000000 : ℝ)|=(5424366589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s3_5 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2651243559/5000000000 : ℝ)*x 0 + (-967680133/5000000000 : ℝ)*x 1 + (2712183291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651243559/5000000000 : ℝ)^2159 ≤ (21767025699627/50000000000000 : ℝ)^1647 := by
    have hnat : (2651243559 : ℕ)^2159*50000000000000^1647 ≤ 21767025699627^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651243559 5000000000 21767025699627 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (967680133/5000000000 : ℝ)^2159 ≤ (2323104332899/20000000000000 : ℝ)^1647 := by
    have hnat : (967680133 : ℕ)^2159*20000000000000^1647 ≤ 2323104332899^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967680133 5000000000 2323104332899 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712183291/5000000000 : ℝ)^2159 ≤ (11212606730811/25000000000000 : ℝ)^1647 := by
    have hnat : (2712183291 : ℕ)^2159*25000000000000^1647 ≤ 11212606730811^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712183291 5000000000 11212606730811 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651243559/5000000000 : ℝ), (-967680133/5000000000 : ℝ), (2712183291/5000000000 : ℝ)] ![(21767025699627/50000000000000 : ℝ), (2323104332899/20000000000000 : ℝ), (11212606730811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651243559/5000000000 : ℝ)|^2159 ≤ (21767025699627/50000000000000 : ℝ)^1647
        have hw : |(2651243559/5000000000 : ℝ)|=(2651243559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-967680133/5000000000 : ℝ)|^2159 ≤ (2323104332899/20000000000000 : ℝ)^1647
        have hw : |(-967680133/5000000000 : ℝ)|=(967680133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712183291/5000000000 : ℝ)|^2159 ≤ (11212606730811/25000000000000 : ℝ)^1647
        have hw : |(2712183291/5000000000 : ℝ)|=(2712183291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s3_6 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2651243481/5000000000 : ℝ)*x 0 + (5424366691/10000000000 : ℝ)*x 1 + (-1935360329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651243481/5000000000 : ℝ)^2159 ≤ (21767024860161/50000000000000 : ℝ)^1647 := by
    have hnat : (2651243481 : ℕ)^2159*50000000000000^1647 ≤ 21767024860161^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651243481 5000000000 21767024860161 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424366691/10000000000 : ℝ)^2159 ≤ (44850428104661/100000000000000 : ℝ)^1647 := by
    have hnat : (5424366691 : ℕ)^2159*100000000000000^1647 ≤ 44850428104661^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424366691 10000000000 44850428104661 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1935360329/10000000000 : ℝ)^2159 ≤ (5807761080073/50000000000000 : ℝ)^1647 := by
    have hnat : (1935360329 : ℕ)^2159*50000000000000^1647 ≤ 5807761080073^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935360329 10000000000 5807761080073 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651243481/5000000000 : ℝ), (5424366691/10000000000 : ℝ), (-1935360329/10000000000 : ℝ)] ![(21767024860161/50000000000000 : ℝ), (44850428104661/100000000000000 : ℝ), (5807761080073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651243481/5000000000 : ℝ)|^2159 ≤ (21767024860161/50000000000000 : ℝ)^1647
        have hw : |(2651243481/5000000000 : ℝ)|=(2651243481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424366691/10000000000 : ℝ)|^2159 ≤ (44850428104661/100000000000000 : ℝ)^1647
        have hw : |(5424366691/10000000000 : ℝ)|=(5424366691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1935360329/10000000000 : ℝ)|^2159 ≤ (5807761080073/50000000000000 : ℝ)^1647
        have hw : |(-1935360329/10000000000 : ℝ)|=(1935360329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s3_7 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2160760311/5000000000 : ℝ)*x 0 + (4526829309/10000000000 : ℝ)*x 1 + (515619389/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160760311/5000000000 : ℝ)^2159 ≤ (2080882669007/6250000000000 : ℝ)^1647 := by
    have hnat : (2160760311 : ℕ)^2159*6250000000000^1647 ≤ 2080882669007^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160760311 5000000000 2080882669007 6250000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4526829309/10000000000 : ℝ)^2159 ≤ (35382738344987/100000000000000 : ℝ)^1647 := by
    have hnat : (4526829309 : ℕ)^2159*100000000000000^1647 ≤ 35382738344987^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526829309 10000000000 35382738344987 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515619389/1250000000 : ℝ)^2159 ≤ (6264627786541/20000000000000 : ℝ)^1647 := by
    have hnat : (515619389 : ℕ)^2159*20000000000000^1647 ≤ 6264627786541^1647*1250000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515619389 1250000000 6264627786541 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160760311/5000000000 : ℝ), (4526829309/10000000000 : ℝ), (515619389/1250000000 : ℝ)] ![(2080882669007/6250000000000 : ℝ), (35382738344987/100000000000000 : ℝ), (6264627786541/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160760311/5000000000 : ℝ)|^2159 ≤ (2080882669007/6250000000000 : ℝ)^1647
        have hw : |(2160760311/5000000000 : ℝ)|=(2160760311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4526829309/10000000000 : ℝ)|^2159 ≤ (35382738344987/100000000000000 : ℝ)^1647
        have hw : |(4526829309/10000000000 : ℝ)|=(4526829309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(515619389/1250000000 : ℝ)|^2159 ≤ (6264627786541/20000000000000 : ℝ)^1647
        have hw : |(515619389/1250000000 : ℝ)|=(515619389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1358_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1991/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (437/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2999/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8021/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1991/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8021/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1991/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8021/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1991/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8021/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1991/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8021/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1991/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8021/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1991/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1991/20000 : ℝ) ^ (4317/1024 : ℝ) ≤ (2984640407324943/50000000000000000000 : ℝ) := by
    have hpowers : (1991/20000 : ℝ)^4317 ≤ (2984640407324943/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1991 : ℕ)^4317*50000000000000000000^1024 ≤ 2984640407324943^1024*20000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1991 20000 2984640407324943 50000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1991/20000 : ℝ)) (X := (2984640407324943/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8021/50000 : ℝ) ^ (4317/1024 : ℝ) ≤ (44618266352811553/100000000000000000000 : ℝ) := by
    have hpowers : (8021/50000 : ℝ)^4317 ≤ (44618266352811553/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8021 : ℕ)^4317*100000000000000000000^1024 ≤ 44618266352811553^1024*50000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8021 50000 44618266352811553 100000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8021/50000 : ℝ)) (X := (44618266352811553/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002984640407324943/25000000000000000000 : ℝ) ≤ (100002831718901/100000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (25002984640407324943/25000000000000000000 : ℝ)^1024 ≤ (100002831718901/100000000000000 : ℝ)^4317 := by
      have hnat : (25002984640407324943 : ℕ)^1024*100000000000000^4317 ≤ 100002831718901^4317*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002984640407324943 25000000000000000000 100002831718901 100000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100002831718901/100000000000000 : ℝ)) (X := (25002984640407324943/25000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050587547167461439/100000000000000000000 : ℝ) ≤ (10001199714075413/10000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (100050587547167461439/100000000000000000000 : ℝ)^1024 ≤ (10001199714075413/10000000000000000 : ℝ)^4317 := by
      have hnat : (100050587547167461439 : ℕ)^1024*10000000000000000^4317 ≤ 10001199714075413^4317*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050587547167461439 100000000000000000000 10001199714075413 10000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001199714075413/10000000000000000 : ℝ)) (X := (100050587547167461439/100000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50044618266352811553/50000000000000000000 : ℝ) ≤ (5001058128130363/5000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (50044618266352811553/50000000000000000000 : ℝ)^1024 ≤ (5001058128130363/5000000000000000 : ℝ)^4317 := by
      have hnat : (50044618266352811553 : ℕ)^1024*5000000000000000^4317 ≤ 5001058128130363^4317*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50044618266352811553 50000000000000000000 5001058128130363 5000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001058128130363/5000000000000000 : ℝ)) (X := (50044618266352811553/50000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2984640407324943/50000000000000000000 : ℝ) ≤ ((2028449177079515229/2029000000000000000 : ℝ)+2*(305514061771/202900000000000 : ℝ)*(1991/20000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (2028449177079515229/2029000000000000000 : ℝ)+2*(305514061771/202900000000000 : ℝ)*(1991/20000 : ℝ)=(100002831718901/100000000000000 : ℝ) by norm_num, show 1+2*(2984640407324943/50000000000000000000 : ℝ)=(25002984640407324943/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44618266352811553/100000000000000000000 : ℝ)+(2984640407324943/50000000000000000000 : ℝ) ≤ ((2028449177079515229/2029000000000000000 : ℝ)+(305514061771/202900000000000 : ℝ)*((8021/50000 : ℝ)+(1991/20000 : ℝ)))^(4317/1024 : ℝ) := by
    rw [show (2028449177079515229/2029000000000000000 : ℝ)+(305514061771/202900000000000 : ℝ)*((8021/50000 : ℝ)+(1991/20000 : ℝ))=(10001199714075413/10000000000000000 : ℝ) by norm_num, show 1+(44618266352811553/100000000000000000000 : ℝ)+(2984640407324943/50000000000000000000 : ℝ)=(100050587547167461439/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44618266352811553/100000000000000000000 : ℝ) ≤ ((2028449177079515229/2029000000000000000 : ℝ)+2*(305514061771/202900000000000 : ℝ)*(8021/50000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (2028449177079515229/2029000000000000000 : ℝ)+2*(305514061771/202900000000000 : ℝ)*(8021/50000 : ℝ)=(5001058128130363/5000000000000000 : ℝ) by norm_num, show 1+2*(44618266352811553/100000000000000000000 : ℝ)=(50044618266352811553/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2028449177079515229/2029000000000000000 : ℝ)*(X 1 0+X 2 0)+(305514061771/202900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (1991/20000 : ℝ)) (hi := (8021/50000 : ℝ)) (c := (2028449177079515229/2029000000000000000 : ℝ)) (alpha := (305514061771/202900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2028449177079515229/2029000000000000000 : ℝ)*(X 0 1+X 2 1)+(305514061771/202900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (1991/20000 : ℝ)) (hi := (8021/50000 : ℝ)) (c := (2028449177079515229/2029000000000000000 : ℝ)) (alpha := (305514061771/202900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2028449177079515229/2029000000000000000 : ℝ)*(X 0 2+X 1 2)+(305514061771/202900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (1991/20000 : ℝ)) (hi := (8021/50000 : ℝ)) (c := (2028449177079515229/2029000000000000000 : ℝ)) (alpha := (305514061771/202900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-126789083/625000000 : ℝ)*X 0 0+(542516537/1000000000 : ℝ)*X 0 1+(1046571323/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535211243/1000000000 : ℝ)*X 1 0+(-2126870277/10000000000 : ℝ)*X 1 1+(1308214133/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676056163/5000000000 : ℝ)*X 2 0+(5232856693/10000000000 : ℝ)*X 2 1+(-2126870201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321481821/10000000000 : ℝ)*X 0 0+(412327173/1000000000 : ℝ)*X 0 1+(2264251391/5000000000 : ℝ)*X 0 2+(4321481821/10000000000 : ℝ)*X 1 0+(412327173/1000000000 : ℝ)*X 1 1+(2264251391/5000000000 : ℝ)*X 1 2+(4321481821/10000000000 : ℝ)*X 2 0+(412327173/1000000000 : ℝ)*X 2 1+(2264251391/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-12679023/62500000 : ℝ)*X 0 0+(2616825351/5000000000 : ℝ)*X 0 1+(5424366589/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651243559/5000000000 : ℝ)*X 1 0+(-967680133/5000000000 : ℝ)*X 1 1+(2712183291/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651243481/5000000000 : ℝ)*X 2 0+(5424366691/10000000000 : ℝ)*X 2 1+(-1935360329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2160760311/5000000000 : ℝ)*X 0 0+(4526829309/10000000000 : ℝ)*X 0 1+(515619389/1250000000 : ℝ)*X 0 2+(2160760311/5000000000 : ℝ)*X 1 0+(4526829309/10000000000 : ℝ)*X 1 1+(515619389/1250000000 : ℝ)*X 1 2+(2160760311/5000000000 : ℝ)*X 2 0+(4526829309/10000000000 : ℝ)*X 2 1+(515619389/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2114839064676157307207859/507250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (507457033/50000000000000 : ℝ)*(base19) + (911452167/100000000000000 : ℝ)*(base23) + (646941/50000000000000 : ℝ)*(lower2) + (185749/312500000000 : ℝ)*(upper3) + (24285143/20000000000000 : ℝ)*(upper5) + (38338787037407/1000000000000 : ℝ)*(major0) + (38338787037407/1000000000000 : ℝ)*(major1) + (38338787037407/1000000000000 : ℝ)*(major2) + (259999478588329/5000000000000 : ℝ)*(sp0) + (520000846309181/10000000000000 : ℝ)*(sp1) + (5200008566553709/100000000000000 : ℝ)*(sp2) + (246773838837467/10000000000000 : ℝ)*(sp3) + (311034989/1562500000000 : ℝ)*(sp4) + (9402126701/100000000000000 : ℝ)*(sp7) + (2467747790501371/100000000000000 : ℝ)*(f.failure) + (1300002369501469/25000000000000 : ℝ)*(f.sum) + (1287030251331/253625000000000000000000000 : ℝ)*base66 + (18569281168787797/2029000000000000000000000000000 : ℝ)*base68 + (12847717044242797/2029000000000000000000000000000 : ℝ)*base70 + (20842413068226797/2029000000000000000000000000000 : ℝ)*base72 + (4992461914891/2029000000000000000000000000 : ℝ)*base74 + (20200802647646797/2029000000000000000000000000000 : ℝ)*base76 + (30475534582412797/2029000000000000000000000000000 : ℝ)*base78 + (8102118726807203/2029000000000000000000000000000 : ℝ)*base79 + (464280763593/2029000000000000000000000000 : ℝ)*base81 + (44383781/5000000000000000000000 : ℝ)*base89 + (44383781/5000000000000000000000 : ℝ)*base91 + (44383781/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (426842633935630208366884299/50725000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6147861/390625000000 : ℝ)*(base19) + (1528671759/100000000000000 : ℝ)*(base23) + (4032361/2500000000000 : ℝ)*(upper3) + (1940537/3125000000000 : ℝ)*(lower4) + (5836241/3125000000000 : ℝ)*(upper5) + (3865870071207277/100000000000000 : ℝ)*(major0) + (3865870071207277/100000000000000 : ℝ)*(major1) + (3865870071207277/100000000000000 : ℝ)*(major2) + (28989201947/100000000000000 : ℝ)*(sp1) + (703282847/2500000000000 : ℝ)*(sp2) + (1310850057232959/25000000000000 : ℝ)*(sp4) + (2621684832938737/50000000000000 : ℝ)*(sp5) + (2621685284473099/50000000000000 : ℝ)*(sp6) + (77760613530879/3125000000000 : ℝ)*(sp7) + (77760613530879/3125000000000 : ℝ)*(f.failure) + (1310850057232959/25000000000000 : ℝ)*(f.sum) + (30448889372847/10145000000000000000000000000 : ℝ)*base65 + (805008613816808567/202900000000000000000000000000000 : ℝ)*base68 + (164726278433208567/202900000000000000000000000000000 : ℝ)*base70 + (2505404827185408567/202900000000000000000000000000000 : ℝ)*base72 + (2697464562981/5072500000000000000000000000 : ℝ)*base73 + (9480766589591433/202900000000000000000000000000000 : ℝ)*base75 + (1354368185206008567/202900000000000000000000000000000 : ℝ)*base78 + (1018569139296208567/202900000000000000000000000000000 : ℝ)*base80 + (22802986577037/10145000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (16531/156250000000000000000 : ℝ)*base90 + (16531/156250000000000000000 : ℝ)*base92 + (16531/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1358_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1991/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (437/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2999/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1358_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1358_s4_0 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-405992677/2000000000 : ℝ)*x 0 + (5414166091/10000000000 : ℝ)*x 1 + (52429767/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (405992677/2000000000 : ℝ)^2159 ≤ (494616123181/4000000000000 : ℝ)^1647 := by
    have hnat : (405992677 : ℕ)^2159*4000000000000^1647 ≤ 494616123181^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405992677 2000000000 494616123181 4000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414166091/10000000000 : ℝ)^2159 ≤ (22369949672403/50000000000000 : ℝ)^1647 := by
    have hnat : (5414166091 : ℕ)^2159*50000000000000^1647 ≤ 22369949672403^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414166091 10000000000 22369949672403 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52429767/100000000 : ℝ)^2159 ≤ (1072367439167/2500000000000 : ℝ)^1647 := by
    have hnat : (52429767 : ℕ)^2159*2500000000000^1647 ≤ 1072367439167^1647*100000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52429767 100000000 1072367439167 2500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-405992677/2000000000 : ℝ), (5414166091/10000000000 : ℝ), (52429767/100000000 : ℝ)] ![(494616123181/4000000000000 : ℝ), (22369949672403/50000000000000 : ℝ), (1072367439167/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-405992677/2000000000 : ℝ)|^2159 ≤ (494616123181/4000000000000 : ℝ)^1647
        have hw : |(-405992677/2000000000 : ℝ)|=(405992677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414166091/10000000000 : ℝ)|^2159 ≤ (22369949672403/50000000000000 : ℝ)^1647
        have hw : |(5414166091/10000000000 : ℝ)|=(5414166091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52429767/100000000 : ℝ)|^2159 ≤ (1072367439167/2500000000000 : ℝ)^1647
        have hw : |(52429767/100000000 : ℝ)|=(52429767/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s4_1 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674650999/5000000000 : ℝ)*x 0 + (-105860647/500000000 : ℝ)*x 1 + (5242978051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674650999/5000000000 : ℝ)^2159 ≤ (11009645291603/25000000000000 : ℝ)^1647 := by
    have hnat : (2674650999 : ℕ)^2159*25000000000000^1647 ≤ 11009645291603^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674650999 5000000000 11009645291603 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105860647/500000000 : ℝ)^2159 ≤ (2613341353833/20000000000000 : ℝ)^1647 := by
    have hnat : (105860647 : ℕ)^2159*20000000000000^1647 ≤ 2613341353833^1647*500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105860647 500000000 2613341353833 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242978051/10000000000 : ℝ)^2159 ≤ (5361839006967/12500000000000 : ℝ)^1647 := by
    have hnat : (5242978051 : ℕ)^2159*12500000000000^1647 ≤ 5361839006967^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242978051 10000000000 5361839006967 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674650999/5000000000 : ℝ), (-105860647/500000000 : ℝ), (5242978051/10000000000 : ℝ)] ![(11009645291603/25000000000000 : ℝ), (2613341353833/20000000000000 : ℝ), (5361839006967/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674650999/5000000000 : ℝ)|^2159 ≤ (11009645291603/25000000000000 : ℝ)^1647
        have hw : |(2674650999/5000000000 : ℝ)|=(2674650999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105860647/500000000 : ℝ)|^2159 ≤ (2613341353833/20000000000000 : ℝ)^1647
        have hw : |(-105860647/500000000 : ℝ)|=(105860647/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242978051/10000000000 : ℝ)|^2159 ≤ (5361839006967/12500000000000 : ℝ)^1647
        have hw : |(5242978051/10000000000 : ℝ)|=(5242978051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s4_2 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337325537/2500000000 : ℝ)*x 0 + (5242977363/10000000000 : ℝ)*x 1 + (-2117213651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337325537/2500000000 : ℝ)^2159 ≤ (44038582785187/100000000000000 : ℝ)^1647 := by
    have hnat : (1337325537 : ℕ)^2159*100000000000000^1647 ≤ 44038582785187^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337325537 2500000000 44038582785187 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242977363/10000000000 : ℝ)^2159 ≤ (42894704677149/100000000000000 : ℝ)^1647 := by
    have hnat : (5242977363 : ℕ)^2159*100000000000000^1647 ≤ 42894704677149^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242977363 10000000000 42894704677149 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117213651/10000000000 : ℝ)^2159 ≤ (3266678130329/25000000000000 : ℝ)^1647 := by
    have hnat : (2117213651 : ℕ)^2159*25000000000000^1647 ≤ 3266678130329^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117213651 10000000000 3266678130329 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337325537/2500000000 : ℝ), (5242977363/10000000000 : ℝ), (-2117213651/10000000000 : ℝ)] ![(44038582785187/100000000000000 : ℝ), (42894704677149/100000000000000 : ℝ), (3266678130329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337325537/2500000000 : ℝ)|^2159 ≤ (44038582785187/100000000000000 : ℝ)^1647
        have hw : |(1337325537/2500000000 : ℝ)|=(1337325537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242977363/10000000000 : ℝ)|^2159 ≤ (42894704677149/100000000000000 : ℝ)^1647
        have hw : |(5242977363/10000000000 : ℝ)|=(5242977363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2117213651/10000000000 : ℝ)|^2159 ≤ (3266678130329/25000000000000 : ℝ)^1647
        have hw : |(-2117213651/10000000000 : ℝ)|=(2117213651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s4_3 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (864459433/2000000000 : ℝ)*x 0 + (4145421891/10000000000 : ℝ)*x 1 + (2253075053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864459433/2000000000 : ℝ)^2159 ≤ (8325491360351/25000000000000 : ℝ)^1647 := by
    have hnat : (864459433 : ℕ)^2159*25000000000000^1647 ≤ 8325491360351^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864459433 2000000000 8325491360351 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4145421891/10000000000 : ℝ)^2159 ≤ (31527025690003/100000000000000 : ℝ)^1647 := by
    have hnat : (4145421891 : ℕ)^2159*100000000000000^1647 ≤ 31527025690003^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145421891 10000000000 31527025690003 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253075053/5000000000 : ℝ)^2159 ≤ (35171008851407/100000000000000 : ℝ)^1647 := by
    have hnat : (2253075053 : ℕ)^2159*100000000000000^1647 ≤ 35171008851407^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253075053 5000000000 35171008851407 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864459433/2000000000 : ℝ), (4145421891/10000000000 : ℝ), (2253075053/5000000000 : ℝ)] ![(8325491360351/25000000000000 : ℝ), (31527025690003/100000000000000 : ℝ), (35171008851407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864459433/2000000000 : ℝ)|^2159 ≤ (8325491360351/25000000000000 : ℝ)^1647
        have hw : |(864459433/2000000000 : ℝ)|=(864459433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4145421891/10000000000 : ℝ)|^2159 ≤ (31527025690003/100000000000000 : ℝ)^1647
        have hw : |(4145421891/10000000000 : ℝ)|=(4145421891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253075053/5000000000 : ℝ)|^2159 ≤ (35171008851407/100000000000000 : ℝ)^1647
        have hw : |(2253075053/5000000000 : ℝ)|=(2253075053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s4_4 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2029975383/10000000000 : ℝ)*x 0 + (2621803527/5000000000 : ℝ)*x 1 + (2706766567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2029975383/10000000000 : ℝ)^2159 ≤ (12365498884569/100000000000000 : ℝ)^1647 := by
    have hnat : (2029975383 : ℕ)^2159*100000000000000^1647 ≤ 12365498884569^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029975383 10000000000 12365498884569 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621803527/5000000000 : ℝ)^2159 ≤ (42901458043909/100000000000000 : ℝ)^1647 := by
    have hnat : (2621803527 : ℕ)^2159*100000000000000^1647 ≤ 42901458043909^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621803527 5000000000 42901458043909 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706766567/5000000000 : ℝ)^2159 ≤ (44733043060997/100000000000000 : ℝ)^1647 := by
    have hnat : (2706766567 : ℕ)^2159*100000000000000^1647 ≤ 44733043060997^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706766567 5000000000 44733043060997 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2029975383/10000000000 : ℝ), (2621803527/5000000000 : ℝ), (2706766567/5000000000 : ℝ)] ![(12365498884569/100000000000000 : ℝ), (42901458043909/100000000000000 : ℝ), (44733043060997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2029975383/10000000000 : ℝ)|^2159 ≤ (12365498884569/100000000000000 : ℝ)^1647
        have hw : |(-2029975383/10000000000 : ℝ)|=(2029975383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621803527/5000000000 : ℝ)|^2159 ≤ (42901458043909/100000000000000 : ℝ)^1647
        have hw : |(2621803527/5000000000 : ℝ)|=(2621803527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706766567/5000000000 : ℝ)|^2159 ≤ (44733043060997/100000000000000 : ℝ)^1647
        have hw : |(2706766567/5000000000 : ℝ)|=(2706766567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s4_5 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305127207/10000000000 : ℝ)*x 0 + (-97332907/500000000 : ℝ)*x 1 + (5413533283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305127207/10000000000 : ℝ)^2159 ≤ (10890616812767/25000000000000 : ℝ)^1647 := by
    have hnat : (5305127207 : ℕ)^2159*25000000000000^1647 ≤ 10890616812767^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305127207 10000000000 10890616812767 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97332907/500000000 : ℝ)^2159 ≤ (11704488066351/100000000000000 : ℝ)^1647 := by
    have hnat : (97332907 : ℕ)^2159*100000000000000^1647 ≤ 11704488066351^1647*500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97332907 500000000 11704488066351 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413533283/10000000000 : ℝ)^2159 ≤ (22366522337479/50000000000000 : ℝ)^1647 := by
    have hnat : (5413533283 : ℕ)^2159*50000000000000^1647 ≤ 22366522337479^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413533283 10000000000 22366522337479 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305127207/10000000000 : ℝ), (-97332907/500000000 : ℝ), (5413533283/10000000000 : ℝ)] ![(10890616812767/25000000000000 : ℝ), (11704488066351/100000000000000 : ℝ), (22366522337479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305127207/10000000000 : ℝ)|^2159 ≤ (10890616812767/25000000000000 : ℝ)^1647
        have hw : |(5305127207/10000000000 : ℝ)|=(5305127207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-97332907/500000000 : ℝ)|^2159 ≤ (11704488066351/100000000000000 : ℝ)^1647
        have hw : |(-97332907/500000000 : ℝ)|=(97332907/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413533283/10000000000 : ℝ)|^2159 ≤ (22366522337479/50000000000000 : ℝ)^1647
        have hw : |(5413533283/10000000000 : ℝ)|=(5413533283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s4_6 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (331570459/625000000 : ℝ)*x 0 + (5413533051/10000000000 : ℝ)*x 1 + (-194665827/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331570459/625000000 : ℝ)^2159 ≤ (43562468725743/100000000000000 : ℝ)^1647 := by
    have hnat : (331570459 : ℕ)^2159*100000000000000^1647 ≤ 43562468725743^1647*625000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331570459 625000000 43562468725743 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413533051/10000000000 : ℝ)^2159 ≤ (8946608432389/20000000000000 : ℝ)^1647 := by
    have hnat : (5413533051 : ℕ)^2159*20000000000000^1647 ≤ 8946608432389^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413533051 10000000000 8946608432389 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194665827/1000000000 : ℝ)^2159 ≤ (365765284093/3125000000000 : ℝ)^1647 := by
    have hnat : (194665827 : ℕ)^2159*3125000000000^1647 ≤ 365765284093^1647*1000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194665827 1000000000 365765284093 3125000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331570459/625000000 : ℝ), (5413533051/10000000000 : ℝ), (-194665827/1000000000 : ℝ)] ![(43562468725743/100000000000000 : ℝ), (8946608432389/20000000000000 : ℝ), (365765284093/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331570459/625000000 : ℝ)|^2159 ≤ (43562468725743/100000000000000 : ℝ)^1647
        have hw : |(331570459/625000000 : ℝ)|=(331570459/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413533051/10000000000 : ℝ)|^2159 ≤ (8946608432389/20000000000000 : ℝ)^1647
        have hw : |(5413533051/10000000000 : ℝ)|=(5413533051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-194665827/1000000000 : ℝ)|^2159 ≤ (365765284093/3125000000000 : ℝ)^1647
        have hw : |(-194665827/1000000000 : ℝ)|=(194665827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s4_7 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (16884073/39062500 : ℝ)*x 0 + (2252411717/5000000000 : ℝ)*x 1 + (4146757439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16884073/39062500 : ℝ)^2159 ≤ (16651111609867/50000000000000 : ℝ)^1647 := by
    have hnat : (16884073 : ℕ)^2159*50000000000000^1647 ≤ 16651111609867^1647*39062500^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16884073 39062500 16651111609867 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252411717/5000000000 : ℝ)^2159 ≤ (35157435662241/100000000000000 : ℝ)^1647 := by
    have hnat : (2252411717 : ℕ)^2159*100000000000000^1647 ≤ 35157435662241^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252411717 5000000000 35157435662241 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4146757439/10000000000 : ℝ)^2159 ≤ (31540341100343/100000000000000 : ℝ)^1647 := by
    have hnat : (4146757439 : ℕ)^2159*100000000000000^1647 ≤ 31540341100343^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146757439 10000000000 31540341100343 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16884073/39062500 : ℝ), (2252411717/5000000000 : ℝ), (4146757439/10000000000 : ℝ)] ![(16651111609867/50000000000000 : ℝ), (35157435662241/100000000000000 : ℝ), (31540341100343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16884073/39062500 : ℝ)|^2159 ≤ (16651111609867/50000000000000 : ℝ)^1647
        have hw : |(16884073/39062500 : ℝ)|=(16884073/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252411717/5000000000 : ℝ)|^2159 ≤ (35157435662241/100000000000000 : ℝ)^1647
        have hw : |(2252411717/5000000000 : ℝ)|=(2252411717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4146757439/10000000000 : ℝ)|^2159 ≤ (31540341100343/100000000000000 : ℝ)^1647
        have hw : |(4146757439/10000000000 : ℝ)|=(4146757439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s4_8 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-5235991/2500000000 : ℝ)*x 0 + (5891883829/10000000000 : ℝ)*x 1 + (1472985531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5235991/2500000000 : ℝ)^2159 ≤ (30779471489/100000000000000 : ℝ)^1647 := by
    have hnat : (5235991 : ℕ)^2159*100000000000000^1647 ≤ 30779471489^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235991 2500000000 30779471489 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5891883829/10000000000 : ℝ)^2159 ≤ (49984286113883/100000000000000 : ℝ)^1647 := by
    have hnat : (5891883829 : ℕ)^2159*100000000000000^1647 ≤ 49984286113883^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5891883829 10000000000 49984286113883 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1472985531/2500000000 : ℝ)^2159 ≤ (12496233601349/25000000000000 : ℝ)^1647 := by
    have hnat : (1472985531 : ℕ)^2159*25000000000000^1647 ≤ 12496233601349^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1472985531 2500000000 12496233601349 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5235991/2500000000 : ℝ), (5891883829/10000000000 : ℝ), (1472985531/2500000000 : ℝ)] ![(30779471489/100000000000000 : ℝ), (49984286113883/100000000000000 : ℝ), (12496233601349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5235991/2500000000 : ℝ)|^2159 ≤ (30779471489/100000000000000 : ℝ)^1647
        have hw : |(-5235991/2500000000 : ℝ)|=(5235991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5891883829/10000000000 : ℝ)|^2159 ≤ (49984286113883/100000000000000 : ℝ)^1647
        have hw : |(5891883829/10000000000 : ℝ)|=(5891883829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1472985531/2500000000 : ℝ)|^2159 ≤ (12496233601349/25000000000000 : ℝ)^1647
        have hw : |(1472985531/2500000000 : ℝ)|=(1472985531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s4_9 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (118015961/1250000000 : ℝ)*x 0 + (6803506919/10000000000 : ℝ)*x 1 + (-4500074153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (118015961/1250000000 : ℝ)^2159 ≤ (4533152579341/100000000000000 : ℝ)^1647 := by
    have hnat : (118015961 : ℕ)^2159*100000000000000^1647 ≤ 4533152579341^1647*1250000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118015961 1250000000 4533152579341 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6803506919/10000000000 : ℝ)^2159 ≤ (15089497869433/25000000000000 : ℝ)^1647 := by
    have hnat : (6803506919 : ℕ)^2159*25000000000000^1647 ≤ 15089497869433^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6803506919 10000000000 15089497869433 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500074153/10000000000 : ℝ)^2159 ≤ (219430349549/625000000000 : ℝ)^1647 := by
    have hnat : (4500074153 : ℕ)^2159*625000000000^1647 ≤ 219430349549^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500074153 10000000000 219430349549 625000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(118015961/1250000000 : ℝ), (6803506919/10000000000 : ℝ), (-4500074153/10000000000 : ℝ)] ![(4533152579341/100000000000000 : ℝ), (15089497869433/25000000000000 : ℝ), (219430349549/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(118015961/1250000000 : ℝ)|^2159 ≤ (4533152579341/100000000000000 : ℝ)^1647
        have hw : |(118015961/1250000000 : ℝ)|=(118015961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6803506919/10000000000 : ℝ)|^2159 ≤ (15089497869433/25000000000000 : ℝ)^1647
        have hw : |(6803506919/10000000000 : ℝ)|=(6803506919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4500074153/10000000000 : ℝ)|^2159 ≤ (219430349549/625000000000 : ℝ)^1647
        have hw : |(-4500074153/10000000000 : ℝ)|=(4500074153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s4_10 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1779417/12500000 : ℝ)*x 0 + (1385054643/2500000000 : ℝ)*x 1 + (5541488387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1779417/12500000 : ℝ)^2159 ≤ (3882814440537/50000000000000 : ℝ)^1647 := by
    have hnat : (1779417 : ℕ)^2159*50000000000000^1647 ≤ 3882814440537^1647*12500000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1779417 12500000 3882814440537 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1385054643/2500000000 : ℝ)^2159 ≤ (46110258385809/100000000000000 : ℝ)^1647 := by
    have hnat : (1385054643 : ℕ)^2159*100000000000000^1647 ≤ 46110258385809^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385054643 2500000000 46110258385809 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5541488387/10000000000 : ℝ)^2159 ≤ (46124112718873/100000000000000 : ℝ)^1647 := by
    have hnat : (5541488387 : ℕ)^2159*100000000000000^1647 ≤ 46124112718873^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5541488387 10000000000 46124112718873 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1779417/12500000 : ℝ), (1385054643/2500000000 : ℝ), (5541488387/10000000000 : ℝ)] ![(3882814440537/50000000000000 : ℝ), (46110258385809/100000000000000 : ℝ), (46124112718873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1779417/12500000 : ℝ)|^2159 ≤ (3882814440537/50000000000000 : ℝ)^1647
        have hw : |(1779417/12500000 : ℝ)|=(1779417/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1385054643/2500000000 : ℝ)|^2159 ≤ (46110258385809/100000000000000 : ℝ)^1647
        have hw : |(1385054643/2500000000 : ℝ)|=(1385054643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5541488387/10000000000 : ℝ)|^2159 ≤ (46124112718873/100000000000000 : ℝ)^1647
        have hw : |(5541488387/10000000000 : ℝ)|=(5541488387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1358_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2999/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (437/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (11141/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2953/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2999/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (437/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2999/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (437/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2999/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (437/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2999/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (437/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2999/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (437/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2999/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (437/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (437/4000 : ℝ) ^ (4317/1024 : ℝ) ≤ (4417002070237189/50000000000000000000 : ℝ) := by
    have hpowers : (437/4000 : ℝ)^4317 ≤ (4417002070237189/50000000000000000000 : ℝ)^1024 := by
      have hnat : (437 : ℕ)^4317*50000000000000000000^1024 ≤ 4417002070237189^1024*4000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        437 4000 4417002070237189 50000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (437/4000 : ℝ)) (X := (4417002070237189/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2999/20000 : ℝ) ^ (4317/1024 : ℝ) ≤ (8392249728848239/25000000000000000000 : ℝ) := by
    have hpowers : (2999/20000 : ℝ)^4317 ≤ (8392249728848239/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2999 : ℕ)^4317*25000000000000000000^1024 ≤ 8392249728848239^1024*20000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2999 20000 8392249728848239 25000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2999/20000 : ℝ)) (X := (8392249728848239/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004417002070237189/25000000000000000000 : ℝ) ≤ (10000419060029251/10000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (25004417002070237189/25000000000000000000 : ℝ)^1024 ≤ (10000419060029251/10000000000000000 : ℝ)^4317 := by
      have hnat : (25004417002070237189 : ℕ)^1024*10000000000000000^4317 ≤ 10000419060029251^4317*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004417002070237189 25000000000000000000 10000419060029251 10000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000419060029251/10000000000000000 : ℝ)) (X := (25004417002070237189/25000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021201501527933667/50000000000000000000 : ℝ) ≤ (312531426377319/312500000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (50021201501527933667/50000000000000000000 : ℝ)^1024 ≤ (312531426377319/312500000000000 : ℝ)^4317 := by
      have hnat : (50021201501527933667 : ℕ)^1024*312500000000000^4317 ≤ 312531426377319^4317*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021201501527933667 50000000000000000000 312531426377319 312500000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312531426377319/312500000000000 : ℝ)) (X := (50021201501527933667/50000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508392249728848239/12500000000000000000 : ℝ) ≤ (2000318445623833/2000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (12508392249728848239/12500000000000000000 : ℝ)^1024 ≤ (2000318445623833/2000000000000000 : ℝ)^4317 := by
      have hnat : (12508392249728848239 : ℕ)^1024*2000000000000000^4317 ≤ 2000318445623833^4317*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508392249728848239 12500000000000000000 2000318445623833 2000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000318445623833/2000000000000000 : ℝ)) (X := (12508392249728848239/12500000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4417002070237189/50000000000000000000 : ℝ) ≤ ((31788194306981829/31796875000000000 : ℝ)+2*(586584044957/407000000000000 : ℝ)*(437/4000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (31788194306981829/31796875000000000 : ℝ)+2*(586584044957/407000000000000 : ℝ)*(437/4000 : ℝ)=(10000419060029251/10000000000000000 : ℝ) by norm_num, show 1+2*(4417002070237189/50000000000000000000 : ℝ)=(25004417002070237189/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8392249728848239/25000000000000000000 : ℝ)+(4417002070237189/50000000000000000000 : ℝ) ≤ ((31788194306981829/31796875000000000 : ℝ)+(586584044957/407000000000000 : ℝ)*((2999/20000 : ℝ)+(437/4000 : ℝ)))^(4317/1024 : ℝ) := by
    rw [show (31788194306981829/31796875000000000 : ℝ)+(586584044957/407000000000000 : ℝ)*((2999/20000 : ℝ)+(437/4000 : ℝ))=(312531426377319/312500000000000 : ℝ) by norm_num, show 1+(8392249728848239/25000000000000000000 : ℝ)+(4417002070237189/50000000000000000000 : ℝ)=(50021201501527933667/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8392249728848239/25000000000000000000 : ℝ) ≤ ((31788194306981829/31796875000000000 : ℝ)+2*(586584044957/407000000000000 : ℝ)*(2999/20000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (31788194306981829/31796875000000000 : ℝ)+2*(586584044957/407000000000000 : ℝ)*(2999/20000 : ℝ)=(2000318445623833/2000000000000000 : ℝ) by norm_num, show 1+2*(8392249728848239/25000000000000000000 : ℝ)=(12508392249728848239/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31788194306981829/31796875000000000 : ℝ)*(X 1 0+X 2 0)+(586584044957/407000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (437/4000 : ℝ)) (hi := (2999/20000 : ℝ)) (c := (31788194306981829/31796875000000000 : ℝ)) (alpha := (586584044957/407000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31788194306981829/31796875000000000 : ℝ)*(X 0 1+X 2 1)+(586584044957/407000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (437/4000 : ℝ)) (hi := (2999/20000 : ℝ)) (c := (31788194306981829/31796875000000000 : ℝ)) (alpha := (586584044957/407000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31788194306981829/31796875000000000 : ℝ)*(X 0 2+X 1 2)+(586584044957/407000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (437/4000 : ℝ)) (hi := (2999/20000 : ℝ)) (c := (31788194306981829/31796875000000000 : ℝ)) (alpha := (586584044957/407000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-405992677/2000000000 : ℝ)*X 0 0+(5414166091/10000000000 : ℝ)*X 0 1+(52429767/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674650999/5000000000 : ℝ)*X 1 0+(-105860647/500000000 : ℝ)*X 1 1+(5242978051/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337325537/2500000000 : ℝ)*X 2 0+(5242977363/10000000000 : ℝ)*X 2 1+(-2117213651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((864459433/2000000000 : ℝ)*X 0 0+(4145421891/10000000000 : ℝ)*X 0 1+(2253075053/5000000000 : ℝ)*X 0 2+(864459433/2000000000 : ℝ)*X 1 0+(4145421891/10000000000 : ℝ)*X 1 1+(2253075053/5000000000 : ℝ)*X 1 2+(864459433/2000000000 : ℝ)*X 2 0+(4145421891/10000000000 : ℝ)*X 2 1+(2253075053/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2029975383/10000000000 : ℝ)*X 0 0+(2621803527/5000000000 : ℝ)*X 0 1+(2706766567/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305127207/10000000000 : ℝ)*X 1 0+(-97332907/500000000 : ℝ)*X 1 1+(5413533283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331570459/625000000 : ℝ)*X 2 0+(5413533051/10000000000 : ℝ)*X 2 1+(-194665827/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((16884073/39062500 : ℝ)*X 0 0+(2252411717/5000000000 : ℝ)*X 0 1+(4146757439/10000000000 : ℝ)*X 0 2+(16884073/39062500 : ℝ)*X 1 0+(2252411717/5000000000 : ℝ)*X 1 1+(4146757439/10000000000 : ℝ)*X 1 2+(16884073/39062500 : ℝ)*X 2 0+(2252411717/5000000000 : ℝ)*X 2 1+(4146757439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-5235991/2500000000 : ℝ)*X 0 0+(5891883829/10000000000 : ℝ)*X 0 1+(1472985531/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s4_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((118015961/1250000000 : ℝ)*X 2 0+(6803506919/10000000000 : ℝ)*X 2 1+(-4500074153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1779417/12500000 : ℝ)*X 0 0+(1385054643/2500000000 : ℝ)*X 0 1+(5541488387/10000000000 : ℝ)*X 0 2+(1779417/12500000 : ℝ)*X 1 0+(1385054643/2500000000 : ℝ)*X 1 1+(5541488387/10000000000 : ℝ)*X 1 2+(1779417/12500000 : ℝ)*X 2 0+(1385054643/2500000000 : ℝ)*X 2 1+(5541488387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s4_10 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37341082654548430613618511/6359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (212202899/20000000000000 : ℝ)*(lower2) + (1048690069/100000000000000 : ℝ)*(lower4) + (65798379/25000000000000 : ℝ)*(lower5) + (67294527571419/1562500000000 : ℝ)*(major0) + (67294527571419/1562500000000 : ℝ)*(major1) + (67294527571419/1562500000000 : ℝ)*(major2) + (2920749149821623/50000000000000 : ℝ)*(sp0) + (5841514866500757/100000000000000 : ℝ)*(sp1) + (5841497820971789/100000000000000 : ℝ)*(sp2) + (693043842007367/25000000000000 : ℝ)*(sp3) + (2988479691/50000000000000 : ℝ)*(sp4) + (2130691121/12500000000000 : ℝ)*(sp6) + (363955367/4000000000000 : ℝ)*(sp7) + (10589898129/100000000000000 : ℝ)*(sp8) + (1386092233456821/50000000000000 : ℝ)*(f.failure) + (5841514866500757/100000000000000 : ℝ)*(f.sum) + (7452837091993/1271875000000000000000000000 : ℝ)*base66 + (122435044972686947/6359375000000000000000000000000 : ℝ)*base68 + (229188727926874447/6359375000000000000000000000000 : ℝ)*base70 + (204734451930133089/3179687500000000000000000000000 : ℝ)*base71 + (5611174715097/5087500000000000000000000000 : ℝ)*base74 + (10271958490392509/794921875000000000000000000000 : ℝ)*base76 + (1728621487391567/397460937500000000000000000000 : ℝ)*base78 + (11813881046749447/6359375000000000000000000000000 : ℝ)*base80 + (5355014389247/5087500000000000000000000000 : ℝ)*base82 + (13741269/2500000000000000000000 : ℝ)*base90 + (13741269/2500000000000000000000 : ℝ)*base92 + (13741269/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60997500551163966963365499/6359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (964733/50000000000000 : ℝ)*(lower2) + (148933007/100000000000000 : ℝ)*(lower3) + (63399093/100000000000000 : ℝ)*(lower5) + (4338849626131379/100000000000000 : ℝ)*(major0) + (4338849626131379/100000000000000 : ℝ)*(major1) + (4338849626131379/100000000000000 : ℝ)*(major2) + (4392335523/50000000000000 : ℝ)*(sp1) + (5884915341593567/100000000000000 : ℝ)*(sp4) + (735613546385487/12500000000000 : ℝ)*(sp5) + (735614633036267/12500000000000 : ℝ)*(sp6) + (1396390135085099/50000000000000 : ℝ)*(sp7) + (14513291/800000000000 : ℝ)*(sp8) + (18292961/20000000000000 : ℝ)*(sp9) + (1506612789/100000000000000 : ℝ)*(sp10) + (698195444195747/25000000000000 : ℝ)*(f.failure) + (2942458577877471/50000000000000 : ℝ)*(f.sum) + (45003556308653/20350000000000000000000000000 : ℝ)*base65 + (31861611153074403/25437500000000000000000000000000 : ℝ)*base67 + (326088779023699403/25437500000000000000000000000000 : ℝ)*base69 + (50308701197011903/25437500000000000000000000000000 : ℝ)*base71 + (283001332209703/20350000000000000000000000000 : ℝ)*base73 + (153049868932949403/25437500000000000000000000000000 : ℝ)*base75 + (191960186427761903/25437500000000000000000000000000 : ℝ)*base77 + (269177098348949403/25437500000000000000000000000000 : ℝ)*base79 + (82175059227297/20350000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (16889117/1250000000000000000000 : ℝ)*base89 + (16889117/1250000000000000000000 : ℝ)*base91 + (16889117/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1358_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2999/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (437/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1358_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1358_s5_0 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-253773469/1250000000 : ℝ)*x 0 + (54122179/100000000 : ℝ)*x 1 + (163899287/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (253773469/1250000000 : ℝ)^2159 ≤ (3091798674527/25000000000000 : ℝ)^1647 := by
    have hnat : (253773469 : ℕ)^2159*25000000000000^1647 ≤ 3091798674527^1647*1250000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253773469 1250000000 3091798674527 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54122179/100000000 : ℝ)^2159 ≤ (5589849631097/12500000000000 : ℝ)^1647 := by
    have hnat : (54122179 : ℕ)^2159*12500000000000^1647 ≤ 5589849631097^1647*100000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54122179 100000000 5589849631097 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163899287/312500000 : ℝ)^2159 ≤ (10728502057267/25000000000000 : ℝ)^1647 := by
    have hnat : (163899287 : ℕ)^2159*25000000000000^1647 ≤ 10728502057267^1647*312500000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163899287 312500000 10728502057267 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-253773469/1250000000 : ℝ), (54122179/100000000 : ℝ), (163899287/312500000 : ℝ)] ![(3091798674527/25000000000000 : ℝ), (5589849631097/12500000000000 : ℝ), (10728502057267/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-253773469/1250000000 : ℝ)|^2159 ≤ (3091798674527/25000000000000 : ℝ)^1647
        have hw : |(-253773469/1250000000 : ℝ)|=(253773469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54122179/100000000 : ℝ)|^2159 ≤ (5589849631097/12500000000000 : ℝ)^1647
        have hw : |(54122179/100000000 : ℝ)|=(54122179/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163899287/312500000 : ℝ)|^2159 ≤ (10728502057267/25000000000000 : ℝ)^1647
        have hw : |(163899287/312500000 : ℝ)|=(163899287/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s5_1 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674401403/5000000000 : ℝ)*x 0 + (-2115493437/10000000000 : ℝ)*x 1 + (5244777217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674401403/5000000000 : ℝ)^2159 ≤ (22016597023751/50000000000000 : ℝ)^1647 := by
    have hnat : (2674401403 : ℕ)^2159*50000000000000^1647 ≤ 22016597023751^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674401403 5000000000 22016597023751 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115493437/10000000000 : ℝ)^2159 ≤ (6526398678937/50000000000000 : ℝ)^1647 := by
    have hnat : (2115493437 : ℕ)^2159*50000000000000^1647 ≤ 6526398678937^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115493437 10000000000 6526398678937 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244777217/10000000000 : ℝ)^2159 ≤ (2145700429151/5000000000000 : ℝ)^1647 := by
    have hnat : (5244777217 : ℕ)^2159*5000000000000^1647 ≤ 2145700429151^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244777217 10000000000 2145700429151 5000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674401403/5000000000 : ℝ), (-2115493437/10000000000 : ℝ), (5244777217/10000000000 : ℝ)] ![(22016597023751/50000000000000 : ℝ), (6526398678937/50000000000000 : ℝ), (2145700429151/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674401403/5000000000 : ℝ)|^2159 ≤ (22016597023751/50000000000000 : ℝ)^1647
        have hw : |(2674401403/5000000000 : ℝ)|=(2674401403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2115493437/10000000000 : ℝ)|^2159 ≤ (6526398678937/50000000000000 : ℝ)^1647
        have hw : |(-2115493437/10000000000 : ℝ)|=(2115493437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244777217/10000000000 : ℝ)|^2159 ≤ (2145700429151/5000000000000 : ℝ)^1647
        have hw : |(5244777217/10000000000 : ℝ)|=(5244777217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s5_2 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348802809/10000000000 : ℝ)*x 0 + (524477723/1000000000 : ℝ)*x 1 + (-423098683/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348802809/10000000000 : ℝ)^2159 ≤ (44033194079877/100000000000000 : ℝ)^1647 := by
    have hnat : (5348802809 : ℕ)^2159*100000000000000^1647 ≤ 44033194079877^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348802809 10000000000 44033194079877 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524477723/1000000000 : ℝ)^2159 ≤ (5364251090307/12500000000000 : ℝ)^1647 := by
    have hnat : (524477723 : ℕ)^2159*12500000000000^1647 ≤ 5364251090307^1647*1000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524477723 1000000000 5364251090307 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423098683/2000000000 : ℝ)^2159 ≤ (6526398589967/50000000000000 : ℝ)^1647 := by
    have hnat : (423098683 : ℕ)^2159*50000000000000^1647 ≤ 6526398589967^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423098683 2000000000 6526398589967 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348802809/10000000000 : ℝ), (524477723/1000000000 : ℝ), (-423098683/2000000000 : ℝ)] ![(44033194079877/100000000000000 : ℝ), (5364251090307/12500000000000 : ℝ), (6526398589967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348802809/10000000000 : ℝ)|^2159 ≤ (44033194079877/100000000000000 : ℝ)^1647
        have hw : |(5348802809/10000000000 : ℝ)|=(5348802809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524477723/1000000000 : ℝ)|^2159 ≤ (5364251090307/12500000000000 : ℝ)^1647
        have hw : |(524477723/1000000000 : ℝ)|=(524477723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423098683/2000000000 : ℝ)|^2159 ≤ (6526398589967/50000000000000 : ℝ)^1647
        have hw : |(-423098683/2000000000 : ℝ)|=(423098683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s5_3 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (432242973/1000000000 : ℝ)*x 0 + (4149355831/10000000000 : ℝ)*x 1 + (4502184927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432242973/1000000000 : ℝ)^2159 ≤ (16651652166219/50000000000000 : ℝ)^1647 := by
    have hnat : (432242973 : ℕ)^2159*50000000000000^1647 ≤ 16651652166219^1647*1000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432242973 1000000000 16651652166219 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4149355831/10000000000 : ℝ)^2159 ≤ (15783125441129/50000000000000 : ℝ)^1647 := by
    have hnat : (4149355831 : ℕ)^2159*50000000000000^1647 ≤ 15783125441129^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149355831 10000000000 15783125441129 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4502184927/10000000000 : ℝ)^2159 ≤ (35130444774667/100000000000000 : ℝ)^1647 := by
    have hnat : (4502184927 : ℕ)^2159*100000000000000^1647 ≤ 35130444774667^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502184927 10000000000 35130444774667 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432242973/1000000000 : ℝ), (4149355831/10000000000 : ℝ), (4502184927/10000000000 : ℝ)] ![(16651652166219/50000000000000 : ℝ), (15783125441129/50000000000000 : ℝ), (35130444774667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432242973/1000000000 : ℝ)|^2159 ≤ (16651652166219/50000000000000 : ℝ)^1647
        have hw : |(432242973/1000000000 : ℝ)|=(432242973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4149355831/10000000000 : ℝ)|^2159 ≤ (15783125441129/50000000000000 : ℝ)^1647
        have hw : |(4149355831/10000000000 : ℝ)|=(4149355831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4502184927/10000000000 : ℝ)|^2159 ≤ (35130444774667/100000000000000 : ℝ)^1647
        have hw : |(4502184927/10000000000 : ℝ)|=(4502184927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s5_4 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-253774981/1250000000 : ℝ)*x 0 + (163918117/312500000 : ℝ)*x 1 + (5411612259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (253774981/1250000000 : ℝ)^2159 ≤ (12367291289009/100000000000000 : ℝ)^1647 := by
    have hnat : (253774981 : ℕ)^2159*100000000000000^1647 ≤ 12367291289009^1647*1250000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253774981 1250000000 12367291289009 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163918117/312500000 : ℝ)^2159 ≤ (2682529456447/6250000000000 : ℝ)^1647 := by
    have hnat : (163918117 : ℕ)^2159*6250000000000^1647 ≤ 2682529456447^1647*312500000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163918117 312500000 2682529456447 6250000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411612259/10000000000 : ℝ)^2159 ≤ (22356118692377/50000000000000 : ℝ)^1647 := by
    have hnat : (5411612259 : ℕ)^2159*50000000000000^1647 ≤ 22356118692377^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411612259 10000000000 22356118692377 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-253774981/1250000000 : ℝ), (163918117/312500000 : ℝ), (5411612259/10000000000 : ℝ)] ![(12367291289009/100000000000000 : ℝ), (2682529456447/6250000000000 : ℝ), (22356118692377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-253774981/1250000000 : ℝ)|^2159 ≤ (12367291289009/100000000000000 : ℝ)^1647
        have hw : |(-253774981/1250000000 : ℝ)|=(253774981/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163918117/312500000 : ℝ)|^2159 ≤ (2682529456447/6250000000000 : ℝ)^1647
        have hw : |(163918117/312500000 : ℝ)|=(163918117/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411612259/10000000000 : ℝ)|^2159 ≤ (22356118692377/50000000000000 : ℝ)^1647
        have hw : |(5411612259/10000000000 : ℝ)|=(5411612259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s5_5 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (265279769/500000000 : ℝ)*x 0 + (-1948658351/10000000000 : ℝ)*x 1 + (5411612271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265279769/500000000 : ℝ)^2159 ≤ (5445938344727/12500000000000 : ℝ)^1647 := by
    have hnat : (265279769 : ℕ)^2159*12500000000000^1647 ≤ 5445938344727^1647*500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265279769 500000000 5445938344727 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1948658351/10000000000 : ℝ)^2159 ≤ (11720255714741/100000000000000 : ℝ)^1647 := by
    have hnat : (1948658351 : ℕ)^2159*100000000000000^1647 ≤ 11720255714741^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948658351 10000000000 11720255714741 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411612271/10000000000 : ℝ)^2159 ≤ (44712237514723/100000000000000 : ℝ)^1647 := by
    have hnat : (5411612271 : ℕ)^2159*100000000000000^1647 ≤ 44712237514723^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411612271 10000000000 44712237514723 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265279769/500000000 : ℝ), (-1948658351/10000000000 : ℝ), (5411612271/10000000000 : ℝ)] ![(5445938344727/12500000000000 : ℝ), (11720255714741/100000000000000 : ℝ), (44712237514723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265279769/500000000 : ℝ)|^2159 ≤ (5445938344727/12500000000000 : ℝ)^1647
        have hw : |(265279769/500000000 : ℝ)|=(265279769/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1948658351/10000000000 : ℝ)|^2159 ≤ (11720255714741/100000000000000 : ℝ)^1647
        have hw : |(-1948658351/10000000000 : ℝ)|=(1948658351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411612271/10000000000 : ℝ)|^2159 ≤ (44712237514723/100000000000000 : ℝ)^1647
        have hw : |(5411612271/10000000000 : ℝ)|=(5411612271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s5_6 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305595403/10000000000 : ℝ)*x 0 + (5411612237/10000000000 : ℝ)*x 1 + (-974329183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305595403/10000000000 : ℝ)^2159 ≤ (10891876751349/25000000000000 : ℝ)^1647 := by
    have hnat : (5305595403 : ℕ)^2159*25000000000000^1647 ≤ 10891876751349^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305595403 10000000000 10891876751349 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411612237/10000000000 : ℝ)^2159 ≤ (44712237146477/100000000000000 : ℝ)^1647 := by
    have hnat : (5411612237 : ℕ)^2159*100000000000000^1647 ≤ 44712237146477^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411612237 10000000000 44712237146477 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974329183/5000000000 : ℝ)^2159 ≤ (2344051166601/20000000000000 : ℝ)^1647 := by
    have hnat : (974329183 : ℕ)^2159*20000000000000^1647 ≤ 2344051166601^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974329183 5000000000 2344051166601 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305595403/10000000000 : ℝ), (5411612237/10000000000 : ℝ), (-974329183/5000000000 : ℝ)] ![(10891876751349/25000000000000 : ℝ), (44712237146477/100000000000000 : ℝ), (2344051166601/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305595403/10000000000 : ℝ)|^2159 ≤ (10891876751349/25000000000000 : ℝ)^1647
        have hw : |(5305595403/10000000000 : ℝ)|=(5305595403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411612237/10000000000 : ℝ)|^2159 ≤ (44712237146477/100000000000000 : ℝ)^1647
        have hw : |(5411612237/10000000000 : ℝ)|=(5411612237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-974329183/5000000000 : ℝ)|^2159 ≤ (2344051166601/20000000000000 : ℝ)^1647
        have hw : |(-974329183/5000000000 : ℝ)|=(974329183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s5_7 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4322455319/10000000000 : ℝ)*x 0 + (4500915277/10000000000 : ℝ)*x 1 + (415063207/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322455319/10000000000 : ℝ)^2159 ≤ (16651781389911/50000000000000 : ℝ)^1647 := by
    have hnat : (4322455319 : ℕ)^2159*50000000000000^1647 ≤ 16651781389911^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322455319 10000000000 16651781389911 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500915277/10000000000 : ℝ)^2159 ≤ (35117458507289/100000000000000 : ℝ)^1647 := by
    have hnat : (4500915277 : ℕ)^2159*100000000000000^1647 ≤ 35117458507289^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500915277 10000000000 35117458507289 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415063207/1000000000 : ℝ)^2159 ≤ (31578978705633/100000000000000 : ℝ)^1647 := by
    have hnat : (415063207 : ℕ)^2159*100000000000000^1647 ≤ 31578978705633^1647*1000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415063207 1000000000 31578978705633 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322455319/10000000000 : ℝ), (4500915277/10000000000 : ℝ), (415063207/1000000000 : ℝ)] ![(16651781389911/50000000000000 : ℝ), (35117458507289/100000000000000 : ℝ), (31578978705633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322455319/10000000000 : ℝ)|^2159 ≤ (16651781389911/50000000000000 : ℝ)^1647
        have hw : |(4322455319/10000000000 : ℝ)|=(4322455319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500915277/10000000000 : ℝ)|^2159 ≤ (35117458507289/100000000000000 : ℝ)^1647
        have hw : |(4500915277/10000000000 : ℝ)|=(4500915277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(415063207/1000000000 : ℝ)|^2159 ≤ (31578978705633/100000000000000 : ℝ)^1647
        have hw : |(415063207/1000000000 : ℝ)|=(415063207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1358_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11179/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3681/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11141/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11141/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11141/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11141/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11141/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11141/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11141/100000 : ℝ) ^ (4317/1024 : ℝ) ≤ (299815164902077/3125000000000000000 : ℝ) := by
    have hpowers : (11141/100000 : ℝ)^4317 ≤ (299815164902077/3125000000000000000 : ℝ)^1024 := by
      have hnat : (11141 : ℕ)^4317*3125000000000000000^1024 ≤ 299815164902077^1024*100000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11141 100000 299815164902077 3125000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11141/100000 : ℝ)) (X := (299815164902077/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2953/20000 : ℝ) ^ (4317/1024 : ℝ) ≤ (31451220909552609/100000000000000000000 : ℝ) := by
    have hpowers : (2953/20000 : ℝ)^4317 ≤ (31451220909552609/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2953 : ℕ)^4317*100000000000000000000^1024 ≤ 31451220909552609^1024*20000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2953 20000 31451220909552609 100000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2953/20000 : ℝ)) (X := (31451220909552609/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562799815164902077/1562500000000000000 : ℝ) ≤ (2500113778369523/2500000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (1562799815164902077/1562500000000000000 : ℝ)^1024 ≤ (2500113778369523/2500000000000000 : ℝ)^4317 := by
      have hnat : (1562799815164902077 : ℕ)^1024*2500000000000000^4317 ≤ 2500113778369523^4317*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562799815164902077 1562500000000000000 2500113778369523 2500000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500113778369523/2500000000000000 : ℝ)) (X := (1562799815164902077/1562500000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041045306186419073/100000000000000000000 : ℝ) ≤ (10000973449511537/10000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (100041045306186419073/100000000000000000000 : ℝ)^1024 ≤ (10000973449511537/10000000000000000 : ℝ)^4317 := by
      have hnat : (100041045306186419073 : ℕ)^1024*10000000000000000^4317 ≤ 10000973449511537^4317*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041045306186419073 100000000000000000000 10000973449511537 10000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000973449511537/10000000000000000 : ℝ)) (X := (100041045306186419073/100000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031451220909552609/50000000000000000000 : ℝ) ≤ (5000745892772491/5000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (50031451220909552609/50000000000000000000 : ℝ)^1024 ≤ (5000745892772491/5000000000000000 : ℝ)^4317 := by
      have hnat : (50031451220909552609 : ℕ)^1024*5000000000000000^4317 ≤ 5000745892772491^4317*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031451220909552609 50000000000000000000 5000745892772491 5000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000745892772491/5000000000000000 : ℝ)) (X := (50031451220909552609/50000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(299815164902077/3125000000000000000 : ℝ) ≤ ((6038349961291230653/6040000000000000000 : ℝ)+2*(34555735563/24160000000000 : ℝ)*(11141/100000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (6038349961291230653/6040000000000000000 : ℝ)+2*(34555735563/24160000000000 : ℝ)*(11141/100000 : ℝ)=(2500113778369523/2500000000000000 : ℝ) by norm_num, show 1+2*(299815164902077/3125000000000000000 : ℝ)=(1562799815164902077/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31451220909552609/100000000000000000000 : ℝ)+(299815164902077/3125000000000000000 : ℝ) ≤ ((6038349961291230653/6040000000000000000 : ℝ)+(34555735563/24160000000000 : ℝ)*((2953/20000 : ℝ)+(11141/100000 : ℝ)))^(4317/1024 : ℝ) := by
    rw [show (6038349961291230653/6040000000000000000 : ℝ)+(34555735563/24160000000000 : ℝ)*((2953/20000 : ℝ)+(11141/100000 : ℝ))=(10000973449511537/10000000000000000 : ℝ) by norm_num, show 1+(31451220909552609/100000000000000000000 : ℝ)+(299815164902077/3125000000000000000 : ℝ)=(100041045306186419073/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31451220909552609/100000000000000000000 : ℝ) ≤ ((6038349961291230653/6040000000000000000 : ℝ)+2*(34555735563/24160000000000 : ℝ)*(2953/20000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (6038349961291230653/6040000000000000000 : ℝ)+2*(34555735563/24160000000000 : ℝ)*(2953/20000 : ℝ)=(5000745892772491/5000000000000000 : ℝ) by norm_num, show 1+2*(31451220909552609/100000000000000000000 : ℝ)=(50031451220909552609/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6038349961291230653/6040000000000000000 : ℝ)*(X 1 0+X 2 0)+(34555735563/24160000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (11141/100000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (6038349961291230653/6040000000000000000 : ℝ)) (alpha := (34555735563/24160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6038349961291230653/6040000000000000000 : ℝ)*(X 0 1+X 2 1)+(34555735563/24160000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (11141/100000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (6038349961291230653/6040000000000000000 : ℝ)) (alpha := (34555735563/24160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6038349961291230653/6040000000000000000 : ℝ)*(X 0 2+X 1 2)+(34555735563/24160000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (11141/100000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (6038349961291230653/6040000000000000000 : ℝ)) (alpha := (34555735563/24160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-253773469/1250000000 : ℝ)*X 0 0+(54122179/100000000 : ℝ)*X 0 1+(163899287/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674401403/5000000000 : ℝ)*X 1 0+(-2115493437/10000000000 : ℝ)*X 1 1+(5244777217/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348802809/10000000000 : ℝ)*X 2 0+(524477723/1000000000 : ℝ)*X 2 1+(-423098683/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((432242973/1000000000 : ℝ)*X 0 0+(4149355831/10000000000 : ℝ)*X 0 1+(4502184927/10000000000 : ℝ)*X 0 2+(432242973/1000000000 : ℝ)*X 1 0+(4149355831/10000000000 : ℝ)*X 1 1+(4502184927/10000000000 : ℝ)*X 1 2+(432242973/1000000000 : ℝ)*X 2 0+(4149355831/10000000000 : ℝ)*X 2 1+(4502184927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-253774981/1250000000 : ℝ)*X 0 0+(163918117/312500000 : ℝ)*X 0 1+(5411612259/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265279769/500000000 : ℝ)*X 1 0+(-1948658351/10000000000 : ℝ)*X 1 1+(5411612271/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305595403/10000000000 : ℝ)*X 2 0+(5411612237/10000000000 : ℝ)*X 2 1+(-974329183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4322455319/10000000000 : ℝ)*X 0 0+(4500915277/10000000000 : ℝ)*X 0 1+(415063207/1000000000 : ℝ)*X 0 2+(4322455319/10000000000 : ℝ)*X 1 0+(4500915277/10000000000 : ℝ)*X 1 1+(415063207/1000000000 : ℝ)*X 1 2+(4322455319/10000000000 : ℝ)*X 2 0+(4500915277/10000000000 : ℝ)*X 2 1+(415063207/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (295770158323924522393156197/30200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1820939841/100000000000000 : ℝ)*(base19) + (1777997547/100000000000000 : ℝ)*(base23) + (1547543/6250000000000 : ℝ)*(lower2) + (5691141/2500000000000 : ℝ)*(upper3) + (220790879/100000000000000 : ℝ)*(upper5) + (440330595720161/10000000000000 : ℝ)*(major0) + (440330595720161/10000000000000 : ℝ)*(major1) + (440330595720161/10000000000000 : ℝ)*(major2) + (2986150924694097/50000000000000 : ℝ)*(sp0) + (5972339466231291/100000000000000 : ℝ)*(sp1) + (2986169754586793/50000000000000 : ℝ)*(sp2) + (708562904127339/25000000000000 : ℝ)*(sp3) + (19718891469/50000000000000 : ℝ)*(sp4) + (9342132793/50000000000000 : ℝ)*(sp7) + (1417135150387471/50000000000000 : ℝ)*(f.failure) + (5972341287171133/100000000000000 : ℝ)*(f.sum) + (1676449022993/604000000000000000000000000 : ℝ)*base66 + (647563505947954867/60400000000000000000000000000000 : ℝ)*base68 + (1094972280363954867/60400000000000000000000000000000 : ℝ)*base70 + (823328456039954867/60400000000000000000000000000000 : ℝ)*base72 + (2780417566349/604000000000000000000000000 : ℝ)*base74 + (1492240868707554867/60400000000000000000000000000000 : ℝ)*base76 + (1217112327931154867/60400000000000000000000000000000 : ℝ)*base78 + (1922049790951154867/60400000000000000000000000000000 : ℝ)*base80 + (3268938112353/604000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (35300881/2500000000000000000000 : ℝ)*base89 + (35300881/2500000000000000000000 : ℝ)*base91 + (35300881/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (298902524530154849671327833/75500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (722479661/100000000000000 : ℝ)*(base19) + (773604651/100000000000000 : ℝ)*(base23) + (8425221/10000000000000 : ℝ)*(upper3) + (13650551/100000000000000 : ℝ)*(lower4) + (11296543/12500000000000 : ℝ)*(upper5) + (1108812904928687/25000000000000 : ℝ)*(major0) + (1108812904928687/25000000000000 : ℝ)*(major1) + (1108812904928687/25000000000000 : ℝ)*(major2) + (7626343231/50000000000000 : ℝ)*(sp1) + (15168971499/100000000000000 : ℝ)*(sp2) + (1203134076610157/20000000000000 : ℝ)*(sp4) + (3007827203942331/50000000000000 : ℝ)*(sp5) + (1503913610118659/25000000000000 : ℝ)*(sp6) + (2854832724412909/100000000000000 : ℝ)*(sp7) + (2854832724412909/100000000000000 : ℝ)*(f.failure) + (1203134076610157/20000000000000 : ℝ)*(f.sum) + (733816956101/302000000000000000000000000 : ℝ)*base66 + (578241729595692611/151000000000000000000000000000000 : ℝ)*base67 + (240881192316307389/151000000000000000000000000000000 : ℝ)*base70 + (2660976607974307389/151000000000000000000000000000000 : ℝ)*base72 + (786083737607/302000000000000000000000000 : ℝ)*base73 + (1865833006192692611/151000000000000000000000000000000 : ℝ)*base75 + (1774299333091307389/151000000000000000000000000000000 : ℝ)*base78 + (958574279166307389/151000000000000000000000000000000 : ℝ)*base80 + (1015273550457/302000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (15789299/5000000000000000000000 : ℝ)*base89 + (15789299/5000000000000000000000 : ℝ)*base91 + (15789299/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1358_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1358_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1358_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1991/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1358_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1358_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1358_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1991/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1358_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

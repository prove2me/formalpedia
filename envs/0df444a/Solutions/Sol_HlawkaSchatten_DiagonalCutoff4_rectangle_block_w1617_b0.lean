-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1617_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:53:07.270395+00:00
-- url     : https://prove2.me/submissions/960bc829-b52c-4144-8720-d7b006d06e22

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
theorem support_rectangle_w1617_s0_0 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-19404653/125000000 : ℝ)*x 0 + (2913858209/5000000000 : ℝ)*x 1 + (489820993/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19404653/125000000 : ℝ)^4787 ≤ (9350761694291/100000000000000 : ℝ)^3763 := by
    have hnat : (19404653 : ℕ)^4787*100000000000000^3763 ≤ 9350761694291^3763*125000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19404653 125000000 9350761694291 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2913858209/5000000000 : ℝ)^4787 ≤ (25156780880031/50000000000000 : ℝ)^3763 := by
    have hnat : (2913858209 : ℕ)^4787*50000000000000^3763 ≤ 25156780880031^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2913858209 5000000000 25156780880031 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (489820993/1000000000 : ℝ)^4787 ≤ (2016783826171/5000000000000 : ℝ)^3763 := by
    have hnat : (489820993 : ℕ)^4787*5000000000000^3763 ≤ 2016783826171^3763*1000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489820993 1000000000 2016783826171 5000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19404653/125000000 : ℝ), (2913858209/5000000000 : ℝ), (489820993/1000000000 : ℝ)] ![(9350761694291/100000000000000 : ℝ), (25156780880031/50000000000000 : ℝ), (2016783826171/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19404653/125000000 : ℝ)|^4787 ≤ (9350761694291/100000000000000 : ℝ)^3763
        have hw : |(-19404653/125000000 : ℝ)|=(19404653/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2913858209/5000000000 : ℝ)|^4787 ≤ (25156780880031/50000000000000 : ℝ)^3763
        have hw : |(2913858209/5000000000 : ℝ)|=(2913858209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(489820993/1000000000 : ℝ)|^4787 ≤ (2016783826171/5000000000000 : ℝ)^3763
        have hw : |(489820993/1000000000 : ℝ)|=(489820993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s0_1 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2725420637/5000000000 : ℝ)*x 0 + (-2066207121/10000000000 : ℝ)*x 1 + (153069059/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2725420637/5000000000 : ℝ)^4787 ≤ (46211399571927/100000000000000 : ℝ)^3763 := by
    have hnat : (2725420637 : ℕ)^4787*100000000000000^3763 ≤ 46211399571927^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725420637 5000000000 46211399571927 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2066207121/10000000000 : ℝ)^4787 ≤ (13452924323211/100000000000000 : ℝ)^3763 := by
    have hnat : (2066207121 : ℕ)^4787*100000000000000^3763 ≤ 13452924323211^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066207121 10000000000 13452924323211 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153069059/312500000 : ℝ)^4787 ≤ (40335676083443/100000000000000 : ℝ)^3763 := by
    have hnat : (153069059 : ℕ)^4787*100000000000000^3763 ≤ 40335676083443^3763*312500000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153069059 312500000 40335676083443 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2725420637/5000000000 : ℝ), (-2066207121/10000000000 : ℝ), (153069059/312500000 : ℝ)] ![(46211399571927/100000000000000 : ℝ), (13452924323211/100000000000000 : ℝ), (40335676083443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2725420637/5000000000 : ℝ)|^4787 ≤ (46211399571927/100000000000000 : ℝ)^3763
        have hw : |(2725420637/5000000000 : ℝ)|=(2725420637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2066207121/10000000000 : ℝ)|^4787 ≤ (13452924323211/100000000000000 : ℝ)^3763
        have hw : |(-2066207121/10000000000 : ℝ)|=(2066207121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(153069059/312500000 : ℝ)|^4787 ≤ (40335676083443/100000000000000 : ℝ)^3763
        have hw : |(153069059/312500000 : ℝ)|=(153069059/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s0_2 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (681355139/1250000000 : ℝ)*x 0 + (1224552489/2500000000 : ℝ)*x 1 + (-2066207247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (681355139/1250000000 : ℝ)^4787 ≤ (46211397824779/100000000000000 : ℝ)^3763 := by
    have hnat : (681355139 : ℕ)^4787*100000000000000^3763 ≤ 46211397824779^3763*1250000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681355139 1250000000 46211397824779 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1224552489/2500000000 : ℝ)^4787 ≤ (40335676795787/100000000000000 : ℝ)^3763 := by
    have hnat : (1224552489 : ℕ)^4787*100000000000000^3763 ≤ 40335676795787^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1224552489 2500000000 40335676795787 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066207247/10000000000 : ℝ)^4787 ≤ (840807835427/6250000000000 : ℝ)^3763 := by
    have hnat : (2066207247 : ℕ)^4787*6250000000000^3763 ≤ 840807835427^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066207247 10000000000 840807835427 6250000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(681355139/1250000000 : ℝ), (1224552489/2500000000 : ℝ), (-2066207247/10000000000 : ℝ)] ![(46211397824779/100000000000000 : ℝ), (40335676795787/100000000000000 : ℝ), (840807835427/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(681355139/1250000000 : ℝ)|^4787 ≤ (46211397824779/100000000000000 : ℝ)^3763
        have hw : |(681355139/1250000000 : ℝ)|=(681355139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1224552489/2500000000 : ℝ)|^4787 ≤ (40335676795787/100000000000000 : ℝ)^3763
        have hw : |(1224552489/2500000000 : ℝ)|=(1224552489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2066207247/10000000000 : ℝ)|^4787 ≤ (840807835427/6250000000000 : ℝ)^3763
        have hw : |(-2066207247/10000000000 : ℝ)|=(2066207247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s0_3 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (821271929/2000000000 : ℝ)*x 0 + (3075491267/10000000000 : ℝ)*x 1 + (5380674857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (821271929/2000000000 : ℝ)^4787 ≤ (4028836404327/12500000000000 : ℝ)^3763 := by
    have hnat : (821271929 : ℕ)^4787*12500000000000^3763 ≤ 4028836404327^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821271929 2000000000 4028836404327 12500000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3075491267/10000000000 : ℝ)^4787 ≤ (22313315104837/100000000000000 : ℝ)^3763 := by
    have hnat : (3075491267 : ℕ)^4787*100000000000000^3763 ≤ 22313315104837^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3075491267 10000000000 22313315104837 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5380674857/10000000000 : ℝ)^4787 ≤ (45455993652477/100000000000000 : ℝ)^3763 := by
    have hnat : (5380674857 : ℕ)^4787*100000000000000^3763 ≤ 45455993652477^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380674857 10000000000 45455993652477 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(821271929/2000000000 : ℝ), (3075491267/10000000000 : ℝ), (5380674857/10000000000 : ℝ)] ![(4028836404327/12500000000000 : ℝ), (22313315104837/100000000000000 : ℝ), (45455993652477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(821271929/2000000000 : ℝ)|^4787 ≤ (4028836404327/12500000000000 : ℝ)^3763
        have hw : |(821271929/2000000000 : ℝ)|=(821271929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3075491267/10000000000 : ℝ)|^4787 ≤ (22313315104837/100000000000000 : ℝ)^3763
        have hw : |(3075491267/10000000000 : ℝ)|=(3075491267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5380674857/10000000000 : ℝ)|^4787 ≤ (45455993652477/100000000000000 : ℝ)^3763
        have hw : |(5380674857/10000000000 : ℝ)|=(5380674857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s0_4 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-388768109/2500000000 : ℝ)*x 0 + (4921658803/10000000000 : ℝ)*x 1 + (181357431/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (388768109/2500000000 : ℝ)^4787 ≤ (9371457309783/100000000000000 : ℝ)^3763 := by
    have hnat : (388768109 : ℕ)^4787*100000000000000^3763 ≤ 9371457309783^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388768109 2500000000 9371457309783 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4921658803/10000000000 : ℝ)^4787 ≤ (20290739313851/50000000000000 : ℝ)^3763 := by
    have hnat : (4921658803 : ℕ)^4787*50000000000000^3763 ≤ 20290739313851^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4921658803 10000000000 20290739313851 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181357431/312500000 : ℝ)^4787 ≤ (2502353202819/5000000000000 : ℝ)^3763 := by
    have hnat : (181357431 : ℕ)^4787*5000000000000^3763 ≤ 2502353202819^3763*312500000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181357431 312500000 2502353202819 5000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-388768109/2500000000 : ℝ), (4921658803/10000000000 : ℝ), (181357431/312500000 : ℝ)] ![(9371457309783/100000000000000 : ℝ), (20290739313851/50000000000000 : ℝ), (2502353202819/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-388768109/2500000000 : ℝ)|^4787 ≤ (9371457309783/100000000000000 : ℝ)^3763
        have hw : |(-388768109/2500000000 : ℝ)|=(388768109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4921658803/10000000000 : ℝ)|^4787 ≤ (20290739313851/50000000000000 : ℝ)^3763
        have hw : |(4921658803/10000000000 : ℝ)|=(4921658803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181357431/312500000 : ℝ)|^4787 ≤ (2502353202819/5000000000000 : ℝ)^3763
        have hw : |(181357431/312500000 : ℝ)|=(181357431/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s0_5 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299250307/2500000000 : ℝ)*x 0 + (-23219587/200000000 : ℝ)*x 1 + (2901718927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299250307/2500000000 : ℝ)^4787 ≤ (434913147823/1000000000000 : ℝ)^3763 := by
    have hnat : (1299250307 : ℕ)^4787*1000000000000^3763 ≤ 434913147823^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299250307 2500000000 434913147823 1000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23219587/200000000 : ℝ)^4787 ≤ (3230810231217/50000000000000 : ℝ)^3763 := by
    have hnat : (23219587 : ℕ)^4787*50000000000000^3763 ≤ 3230810231217^3763*200000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23219587 200000000 3230810231217 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2901718927/5000000000 : ℝ)^4787 ≤ (10009412947309/20000000000000 : ℝ)^3763 := by
    have hnat : (2901718927 : ℕ)^4787*20000000000000^3763 ≤ 10009412947309^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2901718927 5000000000 10009412947309 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299250307/2500000000 : ℝ), (-23219587/200000000 : ℝ), (2901718927/5000000000 : ℝ)] ![(434913147823/1000000000000 : ℝ), (3230810231217/50000000000000 : ℝ), (10009412947309/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299250307/2500000000 : ℝ)|^4787 ≤ (434913147823/1000000000000 : ℝ)^3763
        have hw : |(1299250307/2500000000 : ℝ)|=(1299250307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23219587/200000000 : ℝ)|^4787 ≤ (3230810231217/50000000000000 : ℝ)^3763
        have hw : |(-23219587/200000000 : ℝ)|=(23219587/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2901718927/5000000000 : ℝ)|^4787 ≤ (10009412947309/20000000000000 : ℝ)^3763
        have hw : |(2901718927/5000000000 : ℝ)|=(2901718927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s0_6 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299250313/2500000000 : ℝ)*x 0 + (580343831/1000000000 : ℝ)*x 1 + (-72561163/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299250313/2500000000 : ℝ)^4787 ≤ (43491315037799/100000000000000 : ℝ)^3763 := by
    have hnat : (1299250313 : ℕ)^4787*100000000000000^3763 ≤ 43491315037799^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299250313 2500000000 43491315037799 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (580343831/1000000000 : ℝ)^4787 ≤ (6255883717381/12500000000000 : ℝ)^3763 := by
    have hnat : (580343831 : ℕ)^4787*12500000000000^3763 ≤ 6255883717381^3763*1000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580343831 1000000000 6255883717381 12500000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (72561163/625000000 : ℝ)^4787 ≤ (6461615208919/100000000000000 : ℝ)^3763 := by
    have hnat : (72561163 : ℕ)^4787*100000000000000^3763 ≤ 6461615208919^3763*625000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72561163 625000000 6461615208919 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299250313/2500000000 : ℝ), (580343831/1000000000 : ℝ), (-72561163/625000000 : ℝ)] ![(43491315037799/100000000000000 : ℝ), (6255883717381/12500000000000 : ℝ), (6461615208919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299250313/2500000000 : ℝ)|^4787 ≤ (43491315037799/100000000000000 : ℝ)^3763
        have hw : |(1299250313/2500000000 : ℝ)|=(1299250313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(580343831/1000000000 : ℝ)|^4787 ≤ (6255883717381/12500000000000 : ℝ)^3763
        have hw : |(580343831/1000000000 : ℝ)|=(580343831/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-72561163/625000000 : ℝ)|^4787 ≤ (6461615208919/100000000000000 : ℝ)^3763
        have hw : |(-72561163/625000000 : ℝ)|=(72561163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s0_7 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4113054827/10000000000 : ℝ)*x 0 + (5322520197/10000000000 : ℝ)*x 1 + (3135702759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4113054827/10000000000 : ℝ)^4787 ≤ (32297556493167/100000000000000 : ℝ)^3763 := by
    have hnat : (4113054827 : ℕ)^4787*100000000000000^3763 ≤ 32297556493167^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4113054827 10000000000 32297556493167 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5322520197/10000000000 : ℝ)^4787 ≤ (44831932247987/100000000000000 : ℝ)^3763 := by
    have hnat : (5322520197 : ℕ)^4787*100000000000000^3763 ≤ 44831932247987^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5322520197 10000000000 44831932247987 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3135702759/10000000000 : ℝ)^4787 ≤ (22870511241401/100000000000000 : ℝ)^3763 := by
    have hnat : (3135702759 : ℕ)^4787*100000000000000^3763 ≤ 22870511241401^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3135702759 10000000000 22870511241401 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4113054827/10000000000 : ℝ), (5322520197/10000000000 : ℝ), (3135702759/10000000000 : ℝ)] ![(32297556493167/100000000000000 : ℝ), (44831932247987/100000000000000 : ℝ), (22870511241401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4113054827/10000000000 : ℝ)|^4787 ≤ (32297556493167/100000000000000 : ℝ)^3763
        have hw : |(4113054827/10000000000 : ℝ)|=(4113054827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5322520197/10000000000 : ℝ)|^4787 ≤ (44831932247987/100000000000000 : ℝ)^3763
        have hw : |(5322520197/10000000000 : ℝ)|=(5322520197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3135702759/10000000000 : ℝ)|^4787 ≤ (22870511241401/100000000000000 : ℝ)^3763
        have hw : |(3135702759/10000000000 : ℝ)|=(3135702759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1617_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4173/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12041/50000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4783/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4783 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4783*1^1024 ≤ 0^1024*1^4783 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4783 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4783/1024 : ℝ) ≤ (1384403330042972551/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4783 ≤ (1384403330042972551/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4783*100000000000000000000^1024 ≤ 1384403330042972551^1024*5^4783 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1384403330042972551 100000000000000000000 4783 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1384403330042972551/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4783 := by
      have hnat : (1 : ℕ)^1024*1^4783 ≤ 1^4783*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101384403330042972551/100000000000000000000 : ℝ) ≤ (5014739493606189/5000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (101384403330042972551/100000000000000000000 : ℝ)^1024 ≤ (5014739493606189/5000000000000000 : ℝ)^4783 := by
      have hnat : (101384403330042972551 : ℕ)^1024*5000000000000000^4783 ≤ 5014739493606189^4783*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101384403330042972551 100000000000000000000 5014739493606189 5000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014739493606189/5000000000000000 : ℝ)) (X := (101384403330042972551/100000000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51384403330042972551/50000000000000000000 : ℝ) ≤ (2514739493606189/2500000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (51384403330042972551/50000000000000000000 : ℝ)^1024 ≤ (2514739493606189/2500000000000000 : ℝ)^4783 := by
      have hnat : (51384403330042972551 : ℕ)^1024*2500000000000000^4783 ≤ 2514739493606189^4783*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51384403330042972551 50000000000000000000 2514739493606189 2500000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514739493606189/2500000000000000 : ℝ)) (X := (51384403330042972551/50000000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14739493606189/2000000000000000 : ℝ)*(0 : ℝ))^(4783/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14739493606189/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1384403330042972551/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14739493606189/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4783/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14739493606189/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5014739493606189/5000000000000000 : ℝ) by norm_num, show 1+(1384403330042972551/100000000000000000000 : ℝ)+(0 : ℝ)=(101384403330042972551/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1384403330042972551/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14739493606189/2000000000000000 : ℝ)*(2/5 : ℝ))^(4783/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14739493606189/2000000000000000 : ℝ)*(2/5 : ℝ)=(2514739493606189/2500000000000000 : ℝ) by norm_num, show 1+2*(1384403330042972551/100000000000000000000 : ℝ)=(51384403330042972551/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14739493606189/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14739493606189/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14739493606189/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14739493606189/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14739493606189/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14739493606189/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-19404653/125000000 : ℝ)*X 0 0+(2913858209/5000000000 : ℝ)*X 0 1+(489820993/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2725420637/5000000000 : ℝ)*X 1 0+(-2066207121/10000000000 : ℝ)*X 1 1+(153069059/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((681355139/1250000000 : ℝ)*X 2 0+(1224552489/2500000000 : ℝ)*X 2 1+(-2066207247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((821271929/2000000000 : ℝ)*X 0 0+(3075491267/10000000000 : ℝ)*X 0 1+(5380674857/10000000000 : ℝ)*X 0 2+(821271929/2000000000 : ℝ)*X 1 0+(3075491267/10000000000 : ℝ)*X 1 1+(5380674857/10000000000 : ℝ)*X 1 2+(821271929/2000000000 : ℝ)*X 2 0+(3075491267/10000000000 : ℝ)*X 2 1+(5380674857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-388768109/2500000000 : ℝ)*X 0 0+(4921658803/10000000000 : ℝ)*X 0 1+(181357431/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1299250307/2500000000 : ℝ)*X 1 0+(-23219587/200000000 : ℝ)*X 1 1+(2901718927/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1299250313/2500000000 : ℝ)*X 2 0+(580343831/1000000000 : ℝ)*X 2 1+(-72561163/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4113054827/10000000000 : ℝ)*X 0 0+(5322520197/10000000000 : ℝ)*X 0 1+(3135702759/10000000000 : ℝ)*X 0 2+(4113054827/10000000000 : ℝ)*X 1 0+(5322520197/10000000000 : ℝ)*X 1 1+(3135702759/10000000000 : ℝ)*X 1 2+(4113054827/10000000000 : ℝ)*X 2 0+(5322520197/10000000000 : ℝ)*X 2 1+(3135702759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3546069841710264183/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5442969/100000000000000 : ℝ)*(base1) + (353350387/25000000000000 : ℝ)*(base19) + (1381427109/100000000000000 : ℝ)*(base23) + (222867887/100000000000000 : ℝ)*(upper3) + (43567307/25000000000000 : ℝ)*(upper5) + (754830364513291/100000000000000 : ℝ)*(major0) + (754830364513291/100000000000000 : ℝ)*(major1) + (754830364513291/100000000000000 : ℝ)*(major2) + (134480661523519/12500000000000 : ℝ)*(sp0) + (1075849297781887/100000000000000 : ℝ)*(sp1) + (537924664878163/50000000000000 : ℝ)*(sp2) + (433807224533457/100000000000000 : ℝ)*(sp3) + (1356109563/25000000000000 : ℝ)*(sp4) + (1275731031/50000000000000 : ℝ)*(sp7) + (54226222679811/12500000000000 : ℝ)*(f.failure) + (215170142236687/20000000000000 : ℝ)*(f.sum) + (34666041657999/100000000000000000000000000000 : ℝ)*base65 + (808724214642001/200000000000000000000000000000 : ℝ)*base68 + (1137942319842001/200000000000000000000000000000 : ℝ)*base70 + (655628605042001/200000000000000000000000000000 : ℝ)*base72 + (204648519757999/100000000000000000000000000000 : ℝ)*base73 + (295688262242001/200000000000000000000000000000 : ℝ)*base76 + (734362699842001/200000000000000000000000000000 : ℝ)*base78 + (453918167442001/200000000000000000000000000000 : ℝ)*base80 + (24222891857999/100000000000000000000000000000 : ℝ)*base81 + (724141/125000000000000000000 : ℝ)*base89 + (724141/125000000000000000000 : ℝ)*base91 + (724141/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (137957260595959783253187/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (943034391/100000000000000 : ℝ)*(base19) + (1350552009/100000000000000 : ℝ)*(base23) + (207179071/50000000000000 : ℝ)*(base39) + (42224439/50000000000000 : ℝ)*(upper3) + (337998323/100000000000000 : ℝ)*(upper5) + (795676975682793/100000000000000 : ℝ)*(major0) + (795676975682793/100000000000000 : ℝ)*(major1) + (795676561324651/100000000000000 : ℝ)*(major2) + (3516601363/100000000000000 : ℝ)*(sp1) + (1694815709/50000000000000 : ℝ)*(sp2) + (70879284347421/6250000000000 : ℝ)*(sp4) + (567032044961491/50000000000000 : ℝ)*(sp5) + (1134064223733451/100000000000000 : ℝ)*(sp6) + (457284803505691/100000000000000 : ℝ)*(sp7) + (457284803505691/100000000000000 : ℝ)*(f.failure) + (567034481958439/50000000000000 : ℝ)*(f.sum) + (60888253682271/50000000000000000000000000000 : ℝ)*base66 + (767204055134961/200000000000000000000000000000 : ℝ)*base68 + (414445649405877/200000000000000000000000000000 : ℝ)*base69 + (660375008865039/200000000000000000000000000000 : ℝ)*base71 + (312772950832271/50000000000000000000000000000 : ℝ)*base74 + (682828237405877/200000000000000000000000000000 : ℝ)*base75 + (405444540605877/200000000000000000000000000000 : ℝ)*base77 + (538513183394123/200000000000000000000000000000 : ℝ)*base80 + (182683775894123/100000000000000000000000000000 : ℝ)*base82 + (2076421/1000000000000000000000 : ℝ)*base89 + (2076421/1000000000000000000000 : ℝ)*base91 + (2076421/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1617_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4173/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12041/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1617_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1617_s1_0 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1672566747/10000000000 : ℝ)*x 0 + (4418769/8000000 : ℝ)*x 1 + (512466399/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1672566747/10000000000 : ℝ)^4787 ≤ (5140649593801/50000000000000 : ℝ)^3763 := by
    have hnat : (1672566747 : ℕ)^4787*50000000000000^3763 ≤ 5140649593801^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1672566747 10000000000 5140649593801 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4418769/8000000 : ℝ)^4787 ≤ (734312679737/1562500000000 : ℝ)^3763 := by
    have hnat : (4418769 : ℕ)^4787*1562500000000^3763 ≤ 734312679737^3763*8000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418769 8000000 734312679737 1562500000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512466399/1000000000 : ℝ)^4787 ≤ (42722689293409/100000000000000 : ℝ)^3763 := by
    have hnat : (512466399 : ℕ)^4787*100000000000000^3763 ≤ 42722689293409^3763*1000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512466399 1000000000 42722689293409 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1672566747/10000000000 : ℝ), (4418769/8000000 : ℝ), (512466399/1000000000 : ℝ)] ![(5140649593801/50000000000000 : ℝ), (734312679737/1562500000000 : ℝ), (42722689293409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1672566747/10000000000 : ℝ)|^4787 ≤ (5140649593801/50000000000000 : ℝ)^3763
        have hw : |(-1672566747/10000000000 : ℝ)|=(1672566747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4418769/8000000 : ℝ)|^4787 ≤ (734312679737/1562500000000 : ℝ)^3763
        have hw : |(4418769/8000000 : ℝ)|=(4418769/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(512466399/1000000000 : ℝ)|^4787 ≤ (42722689293409/100000000000000 : ℝ)^3763
        have hw : |(512466399/1000000000 : ℝ)|=(512466399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s1_1 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073978527/2000000000 : ℝ)*x 0 + (-1880891201/10000000000 : ℝ)*x 1 + (2562331907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073978527/2000000000 : ℝ)^4787 ≤ (45340149691039/100000000000000 : ℝ)^3763 := by
    have hnat : (1073978527 : ℕ)^4787*100000000000000^3763 ≤ 45340149691039^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073978527 2000000000 45340149691039 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1880891201/10000000000 : ℝ)^4787 ≤ (11937162861781/100000000000000 : ℝ)^3763 := by
    have hnat : (1880891201 : ℕ)^4787*100000000000000^3763 ≤ 11937162861781^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880891201 10000000000 11937162861781 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2562331907/5000000000 : ℝ)^4787 ≤ (42722687426879/100000000000000 : ℝ)^3763 := by
    have hnat : (2562331907 : ℕ)^4787*100000000000000^3763 ≤ 42722687426879^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562331907 5000000000 42722687426879 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073978527/2000000000 : ℝ), (-1880891201/10000000000 : ℝ), (2562331907/5000000000 : ℝ)] ![(45340149691039/100000000000000 : ℝ), (11937162861781/100000000000000 : ℝ), (42722687426879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073978527/2000000000 : ℝ)|^4787 ≤ (45340149691039/100000000000000 : ℝ)^3763
        have hw : |(1073978527/2000000000 : ℝ)|=(1073978527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1880891201/10000000000 : ℝ)|^4787 ≤ (11937162861781/100000000000000 : ℝ)^3763
        have hw : |(-1880891201/10000000000 : ℝ)|=(1880891201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2562331907/5000000000 : ℝ)|^4787 ≤ (42722687426879/100000000000000 : ℝ)^3763
        have hw : |(2562331907/5000000000 : ℝ)|=(2562331907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s1_2 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369892659/10000000000 : ℝ)*x 0 + (5124663697/10000000000 : ℝ)*x 1 + (-470222831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369892659/10000000000 : ℝ)^4787 ≤ (5667518743603/12500000000000 : ℝ)^3763 := by
    have hnat : (5369892659 : ℕ)^4787*12500000000000^3763 ≤ 5667518743603^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369892659 10000000000 5667518743603 12500000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5124663697/10000000000 : ℝ)^4787 ≤ (2136134309303/5000000000000 : ℝ)^3763 := by
    have hnat : (5124663697 : ℕ)^4787*5000000000000^3763 ≤ 2136134309303^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5124663697 10000000000 2136134309303 5000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (470222831/2500000000 : ℝ)^4787 ≤ (11937163854833/100000000000000 : ℝ)^3763 := by
    have hnat : (470222831 : ℕ)^4787*100000000000000^3763 ≤ 11937163854833^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470222831 2500000000 11937163854833 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369892659/10000000000 : ℝ), (5124663697/10000000000 : ℝ), (-470222831/2500000000 : ℝ)] ![(5667518743603/12500000000000 : ℝ), (2136134309303/5000000000000 : ℝ), (11937163854833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369892659/10000000000 : ℝ)|^4787 ≤ (5667518743603/12500000000000 : ℝ)^3763
        have hw : |(5369892659/10000000000 : ℝ)|=(5369892659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5124663697/10000000000 : ℝ)|^4787 ≤ (2136134309303/5000000000000 : ℝ)^3763
        have hw : |(5124663697/10000000000 : ℝ)|=(5124663697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-470222831/2500000000 : ℝ)|^4787 ≤ (11937163854833/100000000000000 : ℝ)^3763
        have hw : |(-470222831/2500000000 : ℝ)|=(470222831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s1_3 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4196364809/10000000000 : ℝ)*x 0 + (744797921/2000000000 : ℝ)*x 1 + (4713010249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4196364809/10000000000 : ℝ)^4787 ≤ (33132045926497/100000000000000 : ℝ)^3763 := by
    have hnat : (4196364809 : ℕ)^4787*100000000000000^3763 ≤ 33132045926497^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196364809 10000000000 33132045926497 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744797921/2000000000 : ℝ)^4787 ≤ (22769833293/80000000000 : ℝ)^3763 := by
    have hnat : (744797921 : ℕ)^4787*80000000000^3763 ≤ 22769833293^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744797921 2000000000 22769833293 80000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4713010249/10000000000 : ℝ)^4787 ≤ (38405662441497/100000000000000 : ℝ)^3763 := by
    have hnat : (4713010249 : ℕ)^4787*100000000000000^3763 ≤ 38405662441497^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4713010249 10000000000 38405662441497 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4196364809/10000000000 : ℝ), (744797921/2000000000 : ℝ), (4713010249/10000000000 : ℝ)] ![(33132045926497/100000000000000 : ℝ), (22769833293/80000000000 : ℝ), (38405662441497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4196364809/10000000000 : ℝ)|^4787 ≤ (33132045926497/100000000000000 : ℝ)^3763
        have hw : |(4196364809/10000000000 : ℝ)|=(4196364809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(744797921/2000000000 : ℝ)|^4787 ≤ (22769833293/80000000000 : ℝ)^3763
        have hw : |(744797921/2000000000 : ℝ)|=(744797921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4713010249/10000000000 : ℝ)|^4787 ≤ (38405662441497/100000000000000 : ℝ)^3763
        have hw : |(4713010249/10000000000 : ℝ)|=(4713010249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s1_4 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-836387761/5000000000 : ℝ)*x 0 + (2564473481/5000000000 : ℝ)*x 1 + (2759556479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836387761/5000000000 : ℝ)^4787 ≤ (10282931786941/100000000000000 : ℝ)^3763 := by
    have hnat : (836387761 : ℕ)^4787*100000000000000^3763 ≤ 10282931786941^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836387761 5000000000 10282931786941 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564473481/5000000000 : ℝ)^4787 ≤ (8553623320347/20000000000000 : ℝ)^3763 := by
    have hnat : (2564473481 : ℕ)^4787*20000000000000^3763 ≤ 8553623320347^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564473481 5000000000 8553623320347 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2759556479/5000000000 : ℝ)^4787 ≤ (46948951595639/100000000000000 : ℝ)^3763 := by
    have hnat : (2759556479 : ℕ)^4787*100000000000000^3763 ≤ 46948951595639^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759556479 5000000000 46948951595639 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-836387761/5000000000 : ℝ), (2564473481/5000000000 : ℝ), (2759556479/5000000000 : ℝ)] ![(10282931786941/100000000000000 : ℝ), (8553623320347/20000000000000 : ℝ), (46948951595639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-836387761/5000000000 : ℝ)|^4787 ≤ (10282931786941/100000000000000 : ℝ)^3763
        have hw : |(-836387761/5000000000 : ℝ)|=(836387761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564473481/5000000000 : ℝ)|^4787 ≤ (8553623320347/20000000000000 : ℝ)^3763
        have hw : |(2564473481/5000000000 : ℝ)|=(2564473481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2759556479/5000000000 : ℝ)|^4787 ≤ (46948951595639/100000000000000 : ℝ)^3763
        have hw : |(2759556479/5000000000 : ℝ)|=(2759556479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s1_5 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052738591/2000000000 : ℝ)*x 0 + (-1486441541/10000000000 : ℝ)*x 1 + (1103822659/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052738591/2000000000 : ℝ)^4787 ≤ (1768101536797/4000000000000 : ℝ)^3763 := by
    have hnat : (1052738591 : ℕ)^4787*4000000000000^3763 ≤ 1768101536797^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052738591 2000000000 1768101536797 4000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1486441541/10000000000 : ℝ)^4787 ≤ (2212126581223/25000000000000 : ℝ)^3763 := by
    have hnat : (1486441541 : ℕ)^4787*25000000000000^3763 ≤ 2212126581223^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1486441541 10000000000 2212126581223 25000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103822659/2000000000 : ℝ)^4787 ≤ (46948955242471/100000000000000 : ℝ)^3763 := by
    have hnat : (1103822659 : ℕ)^4787*100000000000000^3763 ≤ 46948955242471^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103822659 2000000000 46948955242471 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052738591/2000000000 : ℝ), (-1486441541/10000000000 : ℝ), (1103822659/2000000000 : ℝ)] ![(1768101536797/4000000000000 : ℝ), (2212126581223/25000000000000 : ℝ), (46948955242471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052738591/2000000000 : ℝ)|^4787 ≤ (1768101536797/4000000000000 : ℝ)^3763
        have hw : |(1052738591/2000000000 : ℝ)|=(1052738591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1486441541/10000000000 : ℝ)|^4787 ≤ (2212126581223/25000000000000 : ℝ)^3763
        have hw : |(-1486441541/10000000000 : ℝ)|=(1486441541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103822659/2000000000 : ℝ)|^4787 ≤ (46948955242471/100000000000000 : ℝ)^3763
        have hw : |(1103822659/2000000000 : ℝ)|=(1103822659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s1_6 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2631846153/5000000000 : ℝ)*x 0 + (5519113541/10000000000 : ℝ)*x 1 + (-743221053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2631846153/5000000000 : ℝ)^4787 ≤ (1768101259471/4000000000000 : ℝ)^3763 := by
    have hnat : (2631846153 : ℕ)^4787*4000000000000^3763 ≤ 1768101259471^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631846153 5000000000 1768101259471 4000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5519113541/10000000000 : ℝ)^4787 ≤ (938979158091/2000000000000 : ℝ)^3763 := by
    have hnat : (5519113541 : ℕ)^4787*2000000000000^3763 ≤ 938979158091^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519113541 10000000000 938979158091 2000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (743221053/5000000000 : ℝ)^4787 ≤ (8848510603473/100000000000000 : ℝ)^3763 := by
    have hnat : (743221053 : ℕ)^4787*100000000000000^3763 ≤ 8848510603473^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743221053 5000000000 8848510603473 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2631846153/5000000000 : ℝ), (5519113541/10000000000 : ℝ), (-743221053/5000000000 : ℝ)] ![(1768101259471/4000000000000 : ℝ), (938979158091/2000000000000 : ℝ), (8848510603473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2631846153/5000000000 : ℝ)|^4787 ≤ (1768101259471/4000000000000 : ℝ)^3763
        have hw : |(2631846153/5000000000 : ℝ)|=(2631846153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5519113541/10000000000 : ℝ)|^4787 ≤ (938979158091/2000000000000 : ℝ)^3763
        have hw : |(5519113541/10000000000 : ℝ)|=(5519113541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-743221053/5000000000 : ℝ)|^4787 ≤ (8848510603473/100000000000000 : ℝ)^3763
        have hw : |(-743221053/5000000000 : ℝ)|=(743221053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s1_7 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (839376161/2000000000 : ℝ)*x 0 + (4702389599/10000000000 : ℝ)*x 1 + (3734772491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839376161/2000000000 : ℝ)^4787 ≤ (33137228647473/100000000000000 : ℝ)^3763 := by
    have hnat : (839376161 : ℕ)^4787*100000000000000^3763 ≤ 33137228647473^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839376161 2000000000 33137228647473 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4702389599/10000000000 : ℝ)^4787 ≤ (3829559878683/10000000000000 : ℝ)^3763 := by
    have hnat : (4702389599 : ℕ)^4787*10000000000000^3763 ≤ 3829559878683^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4702389599 10000000000 3829559878683 10000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3734772491/10000000000 : ℝ)^4787 ≤ (28567172556427/100000000000000 : ℝ)^3763 := by
    have hnat : (3734772491 : ℕ)^4787*100000000000000^3763 ≤ 28567172556427^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3734772491 10000000000 28567172556427 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(839376161/2000000000 : ℝ), (4702389599/10000000000 : ℝ), (3734772491/10000000000 : ℝ)] ![(33137228647473/100000000000000 : ℝ), (3829559878683/10000000000000 : ℝ), (28567172556427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(839376161/2000000000 : ℝ)|^4787 ≤ (33137228647473/100000000000000 : ℝ)^3763
        have hw : |(839376161/2000000000 : ℝ)|=(839376161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4702389599/10000000000 : ℝ)|^4787 ≤ (3829559878683/10000000000000 : ℝ)^3763
        have hw : |(4702389599/10000000000 : ℝ)|=(4702389599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3734772491/10000000000 : ℝ)|^4787 ≤ (28567172556427/100000000000000 : ℝ)^3763
        have hw : |(3734772491/10000000000 : ℝ)|=(3734772491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1617_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9253/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4427/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4173/100000 : ℝ) ^ (4783/1024 : ℝ) ≤ (35996022590457/100000000000000000000 : ℝ) := by
    have hpowers : (4173/100000 : ℝ)^4783 ≤ (35996022590457/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4173 : ℕ)^4783*100000000000000000000^1024 ≤ 35996022590457^1024*100000^4783 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4173 100000 35996022590457 100000000000000000000 4783 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4173/100000 : ℝ)) (X := (35996022590457/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12041/50000 : ℝ) ^ (4783/1024 : ℝ) ≤ (64702149953486717/50000000000000000000 : ℝ) := by
    have hpowers : (12041/50000 : ℝ)^4783 ≤ (64702149953486717/50000000000000000000 : ℝ)^1024 := by
      have hnat : (12041 : ℕ)^4783*50000000000000000000^1024 ≤ 64702149953486717^1024*50000^4783 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12041 50000 64702149953486717 50000000000000000000 4783 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12041/50000 : ℝ)) (X := (64702149953486717/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000035996022590457/50000000000000000000 : ℝ) ≤ (5000000770644297/5000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (50000035996022590457/50000000000000000000 : ℝ)^1024 ≤ (5000000770644297/5000000000000000 : ℝ)^4783 := by
      have hnat : (50000035996022590457 : ℕ)^1024*5000000000000000^4783 ≤ 5000000770644297^4783*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000035996022590457 50000000000000000000 5000000770644297 5000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000770644297/5000000000000000 : ℝ)) (X := (50000035996022590457/50000000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100129440295929563891/100000000000000000000 : ℝ) ≤ (5001384899604367/5000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (100129440295929563891/100000000000000000000 : ℝ)^1024 ≤ (5001384899604367/5000000000000000 : ℝ)^4783 := by
      have hnat : (100129440295929563891 : ℕ)^1024*5000000000000000^4783 ≤ 5001384899604367^4783*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100129440295929563891 100000000000000000000 5001384899604367 5000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001384899604367/5000000000000000 : ℝ)) (X := (100129440295929563891/100000000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25064702149953486717/25000000000000000000 : ℝ) ≤ (5002769028564437/5000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (25064702149953486717/25000000000000000000 : ℝ)^1024 ≤ (5002769028564437/5000000000000000 : ℝ)^4783 := by
      have hnat : (25064702149953486717 : ℕ)^1024*5000000000000000^4783 ≤ 5002769028564437^4783*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25064702149953486717 25000000000000000000 5002769028564437 5000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002769028564437/5000000000000000 : ℝ)) (X := (25064702149953486717/25000000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(35996022590457/100000000000000000000 : ℝ) ≤ ((99533463402456564753/99545000000000000000 : ℝ)+2*(138412896007/99545000000000 : ℝ)*(4173/100000 : ℝ))^(4783/1024 : ℝ) := by
    rw [show (99533463402456564753/99545000000000000000 : ℝ)+2*(138412896007/99545000000000 : ℝ)*(4173/100000 : ℝ)=(5000000770644297/5000000000000000 : ℝ) by norm_num, show 1+2*(35996022590457/100000000000000000000 : ℝ)=(50000035996022590457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(64702149953486717/50000000000000000000 : ℝ)+(35996022590457/100000000000000000000 : ℝ) ≤ ((99533463402456564753/99545000000000000000 : ℝ)+(138412896007/99545000000000 : ℝ)*((12041/50000 : ℝ)+(4173/100000 : ℝ)))^(4783/1024 : ℝ) := by
    rw [show (99533463402456564753/99545000000000000000 : ℝ)+(138412896007/99545000000000 : ℝ)*((12041/50000 : ℝ)+(4173/100000 : ℝ))=(5001384899604367/5000000000000000 : ℝ) by norm_num, show 1+(64702149953486717/50000000000000000000 : ℝ)+(35996022590457/100000000000000000000 : ℝ)=(100129440295929563891/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(64702149953486717/50000000000000000000 : ℝ) ≤ ((99533463402456564753/99545000000000000000 : ℝ)+2*(138412896007/99545000000000 : ℝ)*(12041/50000 : ℝ))^(4783/1024 : ℝ) := by
    rw [show (99533463402456564753/99545000000000000000 : ℝ)+2*(138412896007/99545000000000 : ℝ)*(12041/50000 : ℝ)=(5002769028564437/5000000000000000 : ℝ) by norm_num, show 1+2*(64702149953486717/50000000000000000000 : ℝ)=(25064702149953486717/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (99533463402456564753/99545000000000000000 : ℝ)*(X 1 0+X 2 0)+(138412896007/99545000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (4173/100000 : ℝ)) (hi := (12041/50000 : ℝ)) (c := (99533463402456564753/99545000000000000000 : ℝ)) (alpha := (138412896007/99545000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (99533463402456564753/99545000000000000000 : ℝ)*(X 0 1+X 2 1)+(138412896007/99545000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (4173/100000 : ℝ)) (hi := (12041/50000 : ℝ)) (c := (99533463402456564753/99545000000000000000 : ℝ)) (alpha := (138412896007/99545000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (99533463402456564753/99545000000000000000 : ℝ)*(X 0 2+X 1 2)+(138412896007/99545000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (4173/100000 : ℝ)) (hi := (12041/50000 : ℝ)) (c := (99533463402456564753/99545000000000000000 : ℝ)) (alpha := (138412896007/99545000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1672566747/10000000000 : ℝ)*X 0 0+(4418769/8000000 : ℝ)*X 0 1+(512466399/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1073978527/2000000000 : ℝ)*X 1 0+(-1880891201/10000000000 : ℝ)*X 1 1+(2562331907/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5369892659/10000000000 : ℝ)*X 2 0+(5124663697/10000000000 : ℝ)*X 2 1+(-470222831/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4196364809/10000000000 : ℝ)*X 0 0+(744797921/2000000000 : ℝ)*X 0 1+(4713010249/10000000000 : ℝ)*X 0 2+(4196364809/10000000000 : ℝ)*X 1 0+(744797921/2000000000 : ℝ)*X 1 1+(4713010249/10000000000 : ℝ)*X 1 2+(4196364809/10000000000 : ℝ)*X 2 0+(744797921/2000000000 : ℝ)*X 2 1+(4713010249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-836387761/5000000000 : ℝ)*X 0 0+(2564473481/5000000000 : ℝ)*X 0 1+(2759556479/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1052738591/2000000000 : ℝ)*X 1 0+(-1486441541/10000000000 : ℝ)*X 1 1+(1103822659/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2631846153/5000000000 : ℝ)*X 2 0+(5519113541/10000000000 : ℝ)*X 2 1+(-743221053/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((839376161/2000000000 : ℝ)*X 0 0+(4702389599/10000000000 : ℝ)*X 0 1+(3734772491/10000000000 : ℝ)*X 0 2+(839376161/2000000000 : ℝ)*X 1 0+(4702389599/10000000000 : ℝ)*X 1 1+(3734772491/10000000000 : ℝ)*X 1 2+(839376161/2000000000 : ℝ)*X 2 0+(4702389599/10000000000 : ℝ)*X 2 1+(3734772491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9313073534551309272891396867/1244312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118950601/50000000000000 : ℝ)*(base1) + (733909467/50000000000000 : ℝ)*(base19) + (369756529/25000000000000 : ℝ)*(base23) + (200094683/100000000000000 : ℝ)*(upper3) + (65398421/50000000000000 : ℝ)*(upper5) + (879667058576013/50000000000000 : ℝ)*(major0) + (879667058576013/50000000000000 : ℝ)*(major1) + (879667058576013/50000000000000 : ℝ)*(major2) + (1253774801458617/50000000000000 : ℝ)*(sp0) + (1253778378411077/50000000000000 : ℝ)*(sp1) + (626889186403743/25000000000000 : ℝ)*(sp2) + (252776282192149/25000000000000 : ℝ)*(sp3) + (1771925011/20000000000000 : ℝ)*(sp4) + (4393509379/100000000000000 : ℝ)*(sp7) + (505554880089589/50000000000000 : ℝ)*(f.failure) + (2507558224641087/100000000000000 : ℝ)*(f.sum) + (51633343015069/19909000000000000000000000000 : ℝ)*base65 + (18473281274998319789/4977250000000000000000000000000000 : ℝ)*base67 + (1460061618573680211/4977250000000000000000000000000000 : ℝ)*base70 + (37823572417887180211/4977250000000000000000000000000000 : ℝ)*base72 + (28225895285121/3981800000000000000000000000 : ℝ)*base73 + (41950831553687180211/4977250000000000000000000000000000 : ℝ)*base76 + (26942581012142680211/4977250000000000000000000000000000 : ℝ)*base78 + (39713538944318180211/4977250000000000000000000000000000 : ℝ)*base80 + (125895031622143/19909000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1377259/500000000000000000000 : ℝ)*base89 + (1377259/500000000000000000000 : ℝ)*base91 + (1377259/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10842091129294862828061065271/1244312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17479791/1000000000000 : ℝ)*(base19) + (1482418409/100000000000000 : ℝ)*(base23) + (6808527/20000000000000 : ℝ)*(upper2) + (345290009/100000000000000 : ℝ)*(upper3) + (91323609/100000000000000 : ℝ)*(upper5) + (899118453984669/50000000000000 : ℝ)*(major0) + (899118453984669/50000000000000 : ℝ)*(major1) + (899118453984669/50000000000000 : ℝ)*(major2) + (664638877/5000000000000 : ℝ)*(sp1) + (6293869321/50000000000000 : ℝ)*(sp2) + (1281502939695741/50000000000000 : ℝ)*(sp4) + (1281495419317421/50000000000000 : ℝ)*(sp5) + (2562991809234431/100000000000000 : ℝ)*(sp6) + (1033467646103239/100000000000000 : ℝ)*(sp7) + (1033467646103239/100000000000000 : ℝ)*(f.failure) + (1281502939695741/50000000000000 : ℝ)*(f.sum) + (13593366324311/3981800000000000000000000000 : ℝ)*base66 + (1313167428174521757/4977250000000000000000000000000000 : ℝ)*base67 + (38230253915160478243/4977250000000000000000000000000000 : ℝ)*base70 + (31109607445585478243/4977250000000000000000000000000000 : ℝ)*base72 + (55944986436473/19909000000000000000000000000 : ℝ)*base73 + (35549199441246978243/4977250000000000000000000000000000 : ℝ)*base76 + (35584458578881978243/4977250000000000000000000000000000 : ℝ)*base78 + (13342006549712728243/4977250000000000000000000000000000 : ℝ)*base80 + (78319130642931/19909000000000000000000000000 : ℝ)*base82 + (7800409/1000000000000000000000 : ℝ)*base89 + (7800409/1000000000000000000000 : ℝ)*base91 + (7800409/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1617_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9253/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4427/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1617_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1617_s2_0 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-67421489/400000000 : ℝ)*x 0 + (1092752989/2000000000 : ℝ)*x 1 + (41406857/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67421489/400000000 : ℝ)^4787 ≤ (519141605299/5000000000000 : ℝ)^3763 := by
    have hnat : (67421489 : ℕ)^4787*5000000000000^3763 ≤ 519141605299^3763*400000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67421489 400000000 519141605299 5000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092752989/2000000000 : ℝ)^4787 ≤ (46350824582847/100000000000000 : ℝ)^3763 := by
    have hnat : (1092752989 : ℕ)^4787*100000000000000^3763 ≤ 46350824582847^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092752989 2000000000 46350824582847 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41406857/80000000 : ℝ)^4787 ≤ (43266343296907/100000000000000 : ℝ)^3763 := by
    have hnat : (41406857 : ℕ)^4787*100000000000000^3763 ≤ 43266343296907^3763*80000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41406857 80000000 43266343296907 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67421489/400000000 : ℝ), (1092752989/2000000000 : ℝ), (41406857/80000000 : ℝ)] ![(519141605299/5000000000000 : ℝ), (46350824582847/100000000000000 : ℝ), (43266343296907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67421489/400000000 : ℝ)|^4787 ≤ (519141605299/5000000000000 : ℝ)^3763
        have hw : |(-67421489/400000000 : ℝ)|=(67421489/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092752989/2000000000 : ℝ)|^4787 ≤ (46350824582847/100000000000000 : ℝ)^3763
        have hw : |(1092752989/2000000000 : ℝ)|=(1092752989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41406857/80000000 : ℝ)|^4787 ≤ (43266343296907/100000000000000 : ℝ)^3763
        have hw : |(41406857/80000000 : ℝ)|=(41406857/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s2_1 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107085791/200000000 : ℝ)*x 0 + (-458536137/2500000000 : ℝ)*x 1 + (5175857173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107085791/200000000 : ℝ)^4787 ≤ (9034524509961/20000000000000 : ℝ)^3763 := by
    have hnat : (107085791 : ℕ)^4787*20000000000000^3763 ≤ 9034524509961^3763*200000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107085791 200000000 9034524509961 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458536137/2500000000 : ℝ)^4787 ≤ (1156103362563/10000000000000 : ℝ)^3763 := by
    have hnat : (458536137 : ℕ)^4787*10000000000000^3763 ≤ 1156103362563^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458536137 2500000000 1156103362563 10000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175857173/10000000000 : ℝ)^4787 ≤ (2163317190367/5000000000000 : ℝ)^3763 := by
    have hnat : (5175857173 : ℕ)^4787*5000000000000^3763 ≤ 2163317190367^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175857173 10000000000 2163317190367 5000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107085791/200000000 : ℝ), (-458536137/2500000000 : ℝ), (5175857173/10000000000 : ℝ)] ![(9034524509961/20000000000000 : ℝ), (1156103362563/10000000000000 : ℝ), (2163317190367/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107085791/200000000 : ℝ)|^4787 ≤ (9034524509961/20000000000000 : ℝ)^3763
        have hw : |(107085791/200000000 : ℝ)|=(107085791/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-458536137/2500000000 : ℝ)|^4787 ≤ (1156103362563/10000000000000 : ℝ)^3763
        have hw : |(-458536137/2500000000 : ℝ)|=(458536137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175857173/10000000000 : ℝ)|^4787 ≤ (2163317190367/5000000000000 : ℝ)^3763
        have hw : |(5175857173/10000000000 : ℝ)|=(5175857173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s2_2 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338572393/2500000000 : ℝ)*x 0 + (5175857083/10000000000 : ℝ)*x 1 + (-917072319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338572393/2500000000 : ℝ)^4787 ≤ (45172622785921/100000000000000 : ℝ)^3763 := by
    have hnat : (1338572393 : ℕ)^4787*100000000000000^3763 ≤ 45172622785921^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338572393 2500000000 45172622785921 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175857083/10000000000 : ℝ)^4787 ≤ (43266342850279/100000000000000 : ℝ)^3763 := by
    have hnat : (5175857083 : ℕ)^4787*100000000000000^3763 ≤ 43266342850279^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175857083 10000000000 43266342850279 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (917072319/5000000000 : ℝ)^4787 ≤ (11561034347293/100000000000000 : ℝ)^3763 := by
    have hnat : (917072319 : ℕ)^4787*100000000000000^3763 ≤ 11561034347293^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917072319 5000000000 11561034347293 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338572393/2500000000 : ℝ), (5175857083/10000000000 : ℝ), (-917072319/5000000000 : ℝ)] ![(45172622785921/100000000000000 : ℝ), (43266342850279/100000000000000 : ℝ), (11561034347293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338572393/2500000000 : ℝ)|^4787 ≤ (45172622785921/100000000000000 : ℝ)^3763
        have hw : |(1338572393/2500000000 : ℝ)|=(1338572393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175857083/10000000000 : ℝ)|^4787 ≤ (43266342850279/100000000000000 : ℝ)^3763
        have hw : |(5175857083/10000000000 : ℝ)|=(5175857083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-917072319/5000000000 : ℝ)|^4787 ≤ (11561034347293/100000000000000 : ℝ)^3763
        have hw : |(-917072319/5000000000 : ℝ)|=(917072319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s2_3 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525744279/1250000000 : ℝ)*x 0 + (772097593/2000000000 : ℝ)*x 1 + (4574501279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525744279/1250000000 : ℝ)^4787 ≤ (16614195736087/50000000000000 : ℝ)^3763 := by
    have hnat : (525744279 : ℕ)^4787*50000000000000^3763 ≤ 16614195736087^3763*1250000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525744279 1250000000 16614195736087 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (772097593/2000000000 : ℝ)^4787 ≤ (29795996365621/100000000000000 : ℝ)^3763 := by
    have hnat : (772097593 : ℕ)^4787*100000000000000^3763 ≤ 29795996365621^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772097593 2000000000 29795996365621 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4574501279/10000000000 : ℝ)^4787 ≤ (36975612147103/100000000000000 : ℝ)^3763 := by
    have hnat : (4574501279 : ℕ)^4787*100000000000000^3763 ≤ 36975612147103^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4574501279 10000000000 36975612147103 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525744279/1250000000 : ℝ), (772097593/2000000000 : ℝ), (4574501279/10000000000 : ℝ)] ![(16614195736087/50000000000000 : ℝ), (29795996365621/100000000000000 : ℝ), (36975612147103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525744279/1250000000 : ℝ)|^4787 ≤ (16614195736087/50000000000000 : ℝ)^3763
        have hw : |(525744279/1250000000 : ℝ)|=(525744279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(772097593/2000000000 : ℝ)|^4787 ≤ (29795996365621/100000000000000 : ℝ)^3763
        have hw : |(772097593/2000000000 : ℝ)|=(772097593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4574501279/10000000000 : ℝ)|^4787 ≤ (36975612147103/100000000000000 : ℝ)^3763
        have hw : |(4574501279/10000000000 : ℝ)|=(4574501279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s2_4 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1685616003/10000000000 : ℝ)*x 0 + (647262047/1250000000 : ℝ)*x 1 + (2730750489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1685616003/10000000000 : ℝ)^4787 ≤ (10383449431747/100000000000000 : ℝ)^3763 := by
    have hnat : (1685616003 : ℕ)^4787*100000000000000^3763 ≤ 10383449431747^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1685616003 10000000000 10383449431747 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647262047/1250000000 : ℝ)^4787 ≤ (43290156919123/100000000000000 : ℝ)^3763 := by
    have hnat : (647262047 : ℕ)^4787*100000000000000^3763 ≤ 43290156919123^3763*1250000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647262047 1250000000 43290156919123 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730750489/5000000000 : ℝ)^4787 ≤ (4632639363759/10000000000000 : ℝ)^3763 := by
    have hnat : (2730750489 : ℕ)^4787*10000000000000^3763 ≤ 4632639363759^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730750489 5000000000 4632639363759 10000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1685616003/10000000000 : ℝ), (647262047/1250000000 : ℝ), (2730750489/5000000000 : ℝ)] ![(10383449431747/100000000000000 : ℝ), (43290156919123/100000000000000 : ℝ), (4632639363759/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1685616003/10000000000 : ℝ)|^4787 ≤ (10383449431747/100000000000000 : ℝ)^3763
        have hw : |(-1685616003/10000000000 : ℝ)|=(1685616003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647262047/1250000000 : ℝ)|^4787 ≤ (43290156919123/100000000000000 : ℝ)^3763
        have hw : |(647262047/1250000000 : ℝ)|=(647262047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730750489/5000000000 : ℝ)|^4787 ≤ (4632639363759/10000000000000 : ℝ)^3763
        have hw : |(2730750489/5000000000 : ℝ)|=(2730750489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s2_5 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055545107/2000000000 : ℝ)*x 0 + (-30970013/200000000 : ℝ)*x 1 + (2730750537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055545107/2000000000 : ℝ)^4787 ≤ (44352500273409/100000000000000 : ℝ)^3763 := by
    have hnat : (1055545107 : ℕ)^4787*100000000000000^3763 ≤ 44352500273409^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055545107 2000000000 44352500273409 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30970013/200000000 : ℝ)^4787 ≤ (1864221007327/20000000000000 : ℝ)^3763 := by
    have hnat : (30970013 : ℕ)^4787*20000000000000^3763 ≤ 1864221007327^3763*200000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30970013 200000000 1864221007327 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730750537/5000000000 : ℝ)^4787 ≤ (2895399667093/6250000000000 : ℝ)^3763 := by
    have hnat : (2730750537 : ℕ)^4787*6250000000000^3763 ≤ 2895399667093^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730750537 5000000000 2895399667093 6250000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055545107/2000000000 : ℝ), (-30970013/200000000 : ℝ), (2730750537/5000000000 : ℝ)] ![(44352500273409/100000000000000 : ℝ), (1864221007327/20000000000000 : ℝ), (2895399667093/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055545107/2000000000 : ℝ)|^4787 ≤ (44352500273409/100000000000000 : ℝ)^3763
        have hw : |(1055545107/2000000000 : ℝ)|=(1055545107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30970013/200000000 : ℝ)|^4787 ≤ (1864221007327/20000000000000 : ℝ)^3763
        have hw : |(-30970013/200000000 : ℝ)|=(30970013/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730750537/5000000000 : ℝ)|^4787 ≤ (2895399667093/6250000000000 : ℝ)^3763
        have hw : |(2730750537/5000000000 : ℝ)|=(2730750537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s2_6 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277725423/10000000000 : ℝ)*x 0 + (2730750677/5000000000 : ℝ)*x 1 + (-1548500411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277725423/10000000000 : ℝ)^4787 ≤ (22176249538033/50000000000000 : ℝ)^3763 := by
    have hnat : (5277725423 : ℕ)^4787*50000000000000^3763 ≤ 22176249538033^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277725423 10000000000 22176249538033 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730750677/5000000000 : ℝ)^4787 ≤ (5790799711857/12500000000000 : ℝ)^3763 := by
    have hnat : (2730750677 : ℕ)^4787*12500000000000^3763 ≤ 5790799711857^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730750677 5000000000 5790799711857 12500000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1548500411/10000000000 : ℝ)^4787 ≤ (18642206413/200000000000 : ℝ)^3763 := by
    have hnat : (1548500411 : ℕ)^4787*200000000000^3763 ≤ 18642206413^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1548500411 10000000000 18642206413 200000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277725423/10000000000 : ℝ), (2730750677/5000000000 : ℝ), (-1548500411/10000000000 : ℝ)] ![(22176249538033/50000000000000 : ℝ), (5790799711857/12500000000000 : ℝ), (18642206413/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277725423/10000000000 : ℝ)|^4787 ≤ (22176249538033/50000000000000 : ℝ)^3763
        have hw : |(5277725423/10000000000 : ℝ)|=(5277725423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730750677/5000000000 : ℝ)|^4787 ≤ (5790799711857/12500000000000 : ℝ)^3763
        have hw : |(2730750677/5000000000 : ℝ)|=(2730750677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1548500411/10000000000 : ℝ)|^4787 ≤ (18642206413/200000000000 : ℝ)^3763
        have hw : |(-1548500411/10000000000 : ℝ)|=(1548500411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s2_7 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4206149103/10000000000 : ℝ)*x 0 + (571118509/1250000000 : ℝ)*x 1 + (3866102093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206149103/10000000000 : ℝ)^4787 ≤ (166151749869/500000000000 : ℝ)^3763 := by
    have hnat : (4206149103 : ℕ)^4787*500000000000^3763 ≤ 166151749869^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206149103 10000000000 166151749869 500000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571118509/1250000000 : ℝ)^4787 ≤ (1845926022647/5000000000000 : ℝ)^3763 := by
    have hnat : (571118509 : ℕ)^4787*5000000000000^3763 ≤ 1845926022647^3763*1250000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571118509 1250000000 1845926022647 5000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3866102093/10000000000 : ℝ)^4787 ≤ (14925564777929/50000000000000 : ℝ)^3763 := by
    have hnat : (3866102093 : ℕ)^4787*50000000000000^3763 ≤ 14925564777929^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3866102093 10000000000 14925564777929 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206149103/10000000000 : ℝ), (571118509/1250000000 : ℝ), (3866102093/10000000000 : ℝ)] ![(166151749869/500000000000 : ℝ), (1845926022647/5000000000000 : ℝ), (14925564777929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206149103/10000000000 : ℝ)|^4787 ≤ (166151749869/500000000000 : ℝ)^3763
        have hw : |(4206149103/10000000000 : ℝ)|=(4206149103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(571118509/1250000000 : ℝ)|^4787 ≤ (1845926022647/5000000000000 : ℝ)^3763
        have hw : |(571118509/1250000000 : ℝ)|=(571118509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3866102093/10000000000 : ℝ)|^4787 ≤ (14925564777929/50000000000000 : ℝ)^3763
        have hw : |(3866102093/10000000000 : ℝ)|=(3866102093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1617_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4427/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10359/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3293/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4427/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4427/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4427/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4427/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4427/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4427/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9253/100000 : ℝ) ^ (4783/1024 : ℝ) ≤ (1484604712620643/100000000000000000000 : ℝ) := by
    have hpowers : (9253/100000 : ℝ)^4783 ≤ (1484604712620643/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9253 : ℕ)^4783*100000000000000000000^1024 ≤ 1484604712620643^1024*100000^4783 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9253 100000 1484604712620643 100000000000000000000 4783 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9253/100000 : ℝ)) (X := (1484604712620643/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4427/25000 : ℝ) ^ (4783/1024 : ℝ) ≤ (3078053431653891/10000000000000000000 : ℝ) := by
    have hpowers : (4427/25000 : ℝ)^4783 ≤ (3078053431653891/10000000000000000000 : ℝ)^1024 := by
      have hnat : (4427 : ℕ)^4783*10000000000000000000^1024 ≤ 3078053431653891^1024*25000^4783 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4427 25000 3078053431653891 10000000000000000000 4783 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4427/25000 : ℝ)) (X := (3078053431653891/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001484604712620643/50000000000000000000 : ℝ) ≤ (5000031783765179/5000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (50001484604712620643/50000000000000000000 : ℝ)^1024 ≤ (5000031783765179/5000000000000000 : ℝ)^4783 := by
      have hnat : (50001484604712620643 : ℕ)^1024*5000000000000000^4783 ≤ 5000031783765179^4783*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001484604712620643 50000000000000000000 5000031783765179 5000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000031783765179/5000000000000000 : ℝ)) (X := (50001484604712620643/50000000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032265139029159553/100000000000000000000 : ℝ) ≤ (10000690681877139/10000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (100032265139029159553/100000000000000000000 : ℝ)^1024 ≤ (10000690681877139/10000000000000000 : ℝ)^4783 := by
      have hnat : (100032265139029159553 : ℕ)^1024*10000000000000000^4783 ≤ 10000690681877139^4783*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032265139029159553 100000000000000000000 10000690681877139 10000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000690681877139/10000000000000000 : ℝ)) (X := (100032265139029159553/100000000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003078053431653891/5000000000000000000 : ℝ) ≤ (125016472452799/125000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (5003078053431653891/5000000000000000000 : ℝ)^1024 ≤ (125016472452799/125000000000000 : ℝ)^4783 := by
      have hnat : (5003078053431653891 : ℕ)^1024*125000000000000^4783 ≤ 125016472452799^4783*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003078053431653891 5000000000000000000 125016472452799 125000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125016472452799/125000000000000 : ℝ)) (X := (5003078053431653891/5000000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1484604712620643/100000000000000000000 : ℝ) ≤ ((556177184772155577/556250000000000000 : ℝ)+2*(627114346781/845500000000000 : ℝ)*(9253/100000 : ℝ))^(4783/1024 : ℝ) := by
    rw [show (556177184772155577/556250000000000000 : ℝ)+2*(627114346781/845500000000000 : ℝ)*(9253/100000 : ℝ)=(5000031783765179/5000000000000000 : ℝ) by norm_num, show 1+2*(1484604712620643/100000000000000000000 : ℝ)=(50001484604712620643/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3078053431653891/10000000000000000000 : ℝ)+(1484604712620643/100000000000000000000 : ℝ) ≤ ((556177184772155577/556250000000000000 : ℝ)+(627114346781/845500000000000 : ℝ)*((4427/25000 : ℝ)+(9253/100000 : ℝ)))^(4783/1024 : ℝ) := by
    rw [show (556177184772155577/556250000000000000 : ℝ)+(627114346781/845500000000000 : ℝ)*((4427/25000 : ℝ)+(9253/100000 : ℝ))=(10000690681877139/10000000000000000 : ℝ) by norm_num, show 1+(3078053431653891/10000000000000000000 : ℝ)+(1484604712620643/100000000000000000000 : ℝ)=(100032265139029159553/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3078053431653891/10000000000000000000 : ℝ) ≤ ((556177184772155577/556250000000000000 : ℝ)+2*(627114346781/845500000000000 : ℝ)*(4427/25000 : ℝ))^(4783/1024 : ℝ) := by
    rw [show (556177184772155577/556250000000000000 : ℝ)+2*(627114346781/845500000000000 : ℝ)*(4427/25000 : ℝ)=(125016472452799/125000000000000 : ℝ) by norm_num, show 1+2*(3078053431653891/10000000000000000000 : ℝ)=(5003078053431653891/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (556177184772155577/556250000000000000 : ℝ)*(X 1 0+X 2 0)+(627114346781/845500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (9253/100000 : ℝ)) (hi := (4427/25000 : ℝ)) (c := (556177184772155577/556250000000000000 : ℝ)) (alpha := (627114346781/845500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (556177184772155577/556250000000000000 : ℝ)*(X 0 1+X 2 1)+(627114346781/845500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (9253/100000 : ℝ)) (hi := (4427/25000 : ℝ)) (c := (556177184772155577/556250000000000000 : ℝ)) (alpha := (627114346781/845500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (556177184772155577/556250000000000000 : ℝ)*(X 0 2+X 1 2)+(627114346781/845500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (9253/100000 : ℝ)) (hi := (4427/25000 : ℝ)) (c := (556177184772155577/556250000000000000 : ℝ)) (alpha := (627114346781/845500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-67421489/400000000 : ℝ)*X 0 0+(1092752989/2000000000 : ℝ)*X 0 1+(41406857/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((107085791/200000000 : ℝ)*X 1 0+(-458536137/2500000000 : ℝ)*X 1 1+(5175857173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338572393/2500000000 : ℝ)*X 2 0+(5175857083/10000000000 : ℝ)*X 2 1+(-917072319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((525744279/1250000000 : ℝ)*X 0 0+(772097593/2000000000 : ℝ)*X 0 1+(4574501279/10000000000 : ℝ)*X 0 2+(525744279/1250000000 : ℝ)*X 1 0+(772097593/2000000000 : ℝ)*X 1 1+(4574501279/10000000000 : ℝ)*X 1 2+(525744279/1250000000 : ℝ)*X 2 0+(772097593/2000000000 : ℝ)*X 2 1+(4574501279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1685616003/10000000000 : ℝ)*X 0 0+(647262047/1250000000 : ℝ)*X 0 1+(2730750489/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055545107/2000000000 : ℝ)*X 1 0+(-30970013/200000000 : ℝ)*X 1 1+(2730750537/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277725423/10000000000 : ℝ)*X 2 0+(2730750677/5000000000 : ℝ)*X 2 1+(-1548500411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4206149103/10000000000 : ℝ)*X 0 0+(571118509/1250000000 : ℝ)*X 0 1+(3866102093/10000000000 : ℝ)*X 0 2+(4206149103/10000000000 : ℝ)*X 1 0+(571118509/1250000000 : ℝ)*X 1 1+(3866102093/10000000000 : ℝ)*X 1 2+(4206149103/10000000000 : ℝ)*X 2 0+(571118509/1250000000 : ℝ)*X 2 1+(3866102093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (163920028781730361389388167/52843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (109838471/25000000000000 : ℝ)*(base19) + (214484997/50000000000000 : ℝ)*(base23) + (1320119/10000000000000 : ℝ)*(lower2) + (14411247/12500000000000 : ℝ)*(upper3) + (16199549/50000000000000 : ℝ)*(upper5) + (487388176926997/20000000000000 : ℝ)*(major0) + (487388176926997/20000000000000 : ℝ)*(major1) + (487388176926997/20000000000000 : ℝ)*(major2) + (868334863791343/25000000000000 : ℝ)*(sp0) + (108541968232273/3125000000000 : ℝ)*(sp1) + (1736671496908313/50000000000000 : ℝ)*(sp2) + (700267904205033/50000000000000 : ℝ)*(sp3) + (3967621249/100000000000000 : ℝ)*(sp4) + (243467409/10000000000000 : ℝ)*(sp7) + (350134560771039/25000000000000 : ℝ)*(f.failure) + (173667171139331/5000000000000 : ℝ)*(f.sum) + (2321481862173/528437500000000000000000000 : ℝ)*base66 + (632585302886795611/211375000000000000000000000000000 : ℝ)*base67 + (85839880242795611/211375000000000000000000000000000 : ℝ)*base69 + (84136813634204389/211375000000000000000000000000000 : ℝ)*base72 + (12471357197547/8455000000000000000000000000 : ℝ)*base73 + (2977014805812045611/211375000000000000000000000000000 : ℝ)*base75 + (4785420746795611/211375000000000000000000000000000 : ℝ)*base77 + (762309565930045611/211375000000000000000000000000000 : ℝ)*base79 + (1567733783477/8455000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2209/250000000000000000000 : ℝ)*base89 + (2209/250000000000000000000 : ℝ)*base91 + (2209/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2300953601141009414646937929/264218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (723060803/50000000000000 : ℝ)*(base19) + (1495163259/100000000000000 : ℝ)*(base23) + (26366917/100000000000000 : ℝ)*(upper2) + (140583049/50000000000000 : ℝ)*(upper3) + (22545569/12500000000000 : ℝ)*(upper5) + (1237827327355713/50000000000000 : ℝ)*(major0) + (1237827327355713/50000000000000 : ℝ)*(major1) + (1237827327355713/50000000000000 : ℝ)*(major2) + (7159786059/50000000000000 : ℝ)*(sp1) + (1941793129/10000000000000 : ℝ)*(sp2) + (3528521522546869/100000000000000 : ℝ)*(sp4) + (705701151370629/20000000000000 : ℝ)*(sp5) + (22053128809077/625000000000 : ℝ)*(sp6) + (1422787496592061/100000000000000 : ℝ)*(sp7) + (1422787496592061/100000000000000 : ℝ)*(f.failure) + (3528521522546869/100000000000000 : ℝ)*(f.sum) + (62875495895903/21137500000000000000000000000 : ℝ)*base65 + (2562890029102629119/528437500000000000000000000000000 : ℝ)*base67 + (3916472952062316619/528437500000000000000000000000000 : ℝ)*base69 + (423303334164504119/528437500000000000000000000000000 : ℝ)*base71 + (7587421448407/5284375000000000000000000000 : ℝ)*base73 + (3163691400486691619/528437500000000000000000000000000 : ℝ)*base75 + (4260016000534816619/528437500000000000000000000000000 : ℝ)*base77 + (2154290736682004119/528437500000000000000000000000000 : ℝ)*base79 + (228888021722131/42275000000000000000000000000 : ℝ)*base81 + (4246109/1000000000000000000000 : ℝ)*base90 + (4246109/1000000000000000000000 : ℝ)*base92 + (4246109/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1617_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4427/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3293/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1617_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1617_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3293/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1617_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1617_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1617_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3293/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1617_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

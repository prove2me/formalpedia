-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1382_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:23:34.287781+00:00
-- url     : https://prove2.me/submissions/19b57194-f197-4351-96df-b07c711a8c23

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
theorem support_rectangle_w1382_s3_0 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2008520553/10000000000 : ℝ)*x 0 + (5422327517/10000000000 : ℝ)*x 1 + (5234986963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2008520553/10000000000 : ℝ)^2171 ≤ (1223855662287/10000000000000 : ℝ)^1659 := by
    have hnat : (2008520553 : ℕ)^2171*10000000000000^1659 ≤ 1223855662287^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008520553 10000000000 1223855662287 10000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422327517/10000000000 : ℝ)^2171 ≤ (44890066006399/100000000000000 : ℝ)^1659 := by
    have hnat : (5422327517 : ℕ)^2171*100000000000000^1659 ≤ 44890066006399^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422327517 10000000000 44890066006399 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234986963/10000000000 : ℝ)^2171 ≤ (42871377355703/100000000000000 : ℝ)^1659 := by
    have hnat : (5234986963 : ℕ)^2171*100000000000000^1659 ≤ 42871377355703^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234986963 10000000000 42871377355703 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2008520553/10000000000 : ℝ), (5422327517/10000000000 : ℝ), (5234986963/10000000000 : ℝ)] ![(1223855662287/10000000000000 : ℝ), (44890066006399/100000000000000 : ℝ), (42871377355703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2008520553/10000000000 : ℝ)|^2171 ≤ (1223855662287/10000000000000 : ℝ)^1659
        have hw : |(-2008520553/10000000000 : ℝ)|=(2008520553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422327517/10000000000 : ℝ)|^2171 ≤ (44890066006399/100000000000000 : ℝ)^1659
        have hw : |(5422327517/10000000000 : ℝ)|=(5422327517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234986963/10000000000 : ℝ)|^2171 ≤ (42871377355703/100000000000000 : ℝ)^1659
        have hw : |(5234986963/10000000000 : ℝ)|=(5234986963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s3_1 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5351268187/10000000000 : ℝ)*x 0 + (-2104174353/10000000000 : ℝ)*x 1 + (1308746817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351268187/10000000000 : ℝ)^2171 ≤ (22060895025183/50000000000000 : ℝ)^1659 := by
    have hnat : (5351268187 : ℕ)^2171*50000000000000^1659 ≤ 22060895025183^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351268187 10000000000 22060895025183 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2104174353/10000000000 : ℝ)^2171 ≤ (3251707326107/25000000000000 : ℝ)^1659 := by
    have hnat : (2104174353 : ℕ)^2171*25000000000000^1659 ≤ 3251707326107^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104174353 10000000000 3251707326107 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308746817/2500000000 : ℝ)^2171 ≤ (5358922578041/12500000000000 : ℝ)^1659 := by
    have hnat : (1308746817 : ℕ)^2171*12500000000000^1659 ≤ 5358922578041^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308746817 2500000000 5358922578041 12500000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351268187/10000000000 : ℝ), (-2104174353/10000000000 : ℝ), (1308746817/2500000000 : ℝ)] ![(22060895025183/50000000000000 : ℝ), (3251707326107/25000000000000 : ℝ), (5358922578041/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351268187/10000000000 : ℝ)|^2171 ≤ (22060895025183/50000000000000 : ℝ)^1659
        have hw : |(5351268187/10000000000 : ℝ)|=(5351268187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2104174353/10000000000 : ℝ)|^2171 ≤ (3251707326107/25000000000000 : ℝ)^1659
        have hw : |(-2104174353/10000000000 : ℝ)|=(2104174353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1308746817/2500000000 : ℝ)|^2171 ≤ (5358922578041/12500000000000 : ℝ)^1659
        have hw : |(1308746817/2500000000 : ℝ)|=(1308746817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s3_2 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5351268169/10000000000 : ℝ)*x 0 + (654373419/1250000000 : ℝ)*x 1 + (-1052087133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351268169/10000000000 : ℝ)^2171 ≤ (44121789856151/100000000000000 : ℝ)^1659 := by
    have hnat : (5351268169 : ℕ)^2171*100000000000000^1659 ≤ 44121789856151^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351268169 10000000000 44121789856151 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654373419/1250000000 : ℝ)^2171 ≤ (2143569076227/5000000000000 : ℝ)^1659 := by
    have hnat : (654373419 : ℕ)^2171*5000000000000^1659 ≤ 2143569076227^1659*1250000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654373419 1250000000 2143569076227 5000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052087133/5000000000 : ℝ)^2171 ≤ (13006828600671/100000000000000 : ℝ)^1659 := by
    have hnat : (1052087133 : ℕ)^2171*100000000000000^1659 ≤ 13006828600671^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052087133 5000000000 13006828600671 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351268169/10000000000 : ℝ), (654373419/1250000000 : ℝ), (-1052087133/5000000000 : ℝ)] ![(44121789856151/100000000000000 : ℝ), (2143569076227/5000000000000 : ℝ), (13006828600671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351268169/10000000000 : ℝ)|^2171 ≤ (44121789856151/100000000000000 : ℝ)^1659
        have hw : |(5351268169/10000000000 : ℝ)|=(5351268169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654373419/1250000000 : ℝ)|^2171 ≤ (2143569076227/5000000000000 : ℝ)^1659
        have hw : |(654373419/1250000000 : ℝ)|=(654373419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1052087133/5000000000 : ℝ)|^2171 ≤ (13006828600671/100000000000000 : ℝ)^1659
        have hw : |(-1052087133/5000000000 : ℝ)|=(1052087133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s3_3 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1078855437/2500000000 : ℝ)*x 0 + (1030120997/2500000000 : ℝ)*x 1 + (4518793953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078855437/2500000000 : ℝ)^2171 ≤ (33295400837941/100000000000000 : ℝ)^1659 := by
    have hnat : (1078855437 : ℕ)^2171*100000000000000^1659 ≤ 33295400837941^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078855437 2500000000 33295400837941 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030120997/2500000000 : ℝ)^2171 ≤ (15670530274239/50000000000000 : ℝ)^1659 := by
    have hnat : (1030120997 : ℕ)^2171*50000000000000^1659 ≤ 15670530274239^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030120997 2500000000 15670530274239 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4518793953/10000000000 : ℝ)^2171 ≤ (8840884648673/25000000000000 : ℝ)^1659 := by
    have hnat : (4518793953 : ℕ)^2171*25000000000000^1659 ≤ 8840884648673^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518793953 10000000000 8840884648673 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078855437/2500000000 : ℝ), (1030120997/2500000000 : ℝ), (4518793953/10000000000 : ℝ)] ![(33295400837941/100000000000000 : ℝ), (15670530274239/50000000000000 : ℝ), (8840884648673/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078855437/2500000000 : ℝ)|^2171 ≤ (33295400837941/100000000000000 : ℝ)^1659
        have hw : |(1078855437/2500000000 : ℝ)|=(1078855437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030120997/2500000000 : ℝ)|^2171 ≤ (15670530274239/50000000000000 : ℝ)^1659
        have hw : |(1030120997/2500000000 : ℝ)|=(1030120997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4518793953/10000000000 : ℝ)|^2171 ≤ (8840884648673/25000000000000 : ℝ)^1659
        have hw : |(4518793953/10000000000 : ℝ)|=(4518793953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s3_4 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-502134477/2500000000 : ℝ)*x 0 + (20452153/39062500 : ℝ)*x 1 + (5421558753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502134477/2500000000 : ℝ)^2171 ≤ (6119347504499/50000000000000 : ℝ)^1659 := by
    have hnat : (502134477 : ℕ)^2171*50000000000000^1659 ≤ 6119347504499^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502134477 2500000000 6119347504499 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20452153/39062500 : ℝ)^2171 ≤ (10719891843759/25000000000000 : ℝ)^1659 := by
    have hnat : (20452153 : ℕ)^2171*25000000000000^1659 ≤ 10719891843759^1659*39062500^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20452153 39062500 10719891843759 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421558753/10000000000 : ℝ)^2171 ≤ (8976347521679/20000000000000 : ℝ)^1659 := by
    have hnat : (5421558753 : ℕ)^2171*20000000000000^1659 ≤ 8976347521679^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421558753 10000000000 8976347521679 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-502134477/2500000000 : ℝ), (20452153/39062500 : ℝ), (5421558753/10000000000 : ℝ)] ![(6119347504499/50000000000000 : ℝ), (10719891843759/25000000000000 : ℝ), (8976347521679/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-502134477/2500000000 : ℝ)|^2171 ≤ (6119347504499/50000000000000 : ℝ)^1659
        have hw : |(-502134477/2500000000 : ℝ)|=(502134477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20452153/39062500 : ℝ)|^2171 ≤ (10719891843759/25000000000000 : ℝ)^1659
        have hw : |(20452153/39062500 : ℝ)|=(20452153/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421558753/10000000000 : ℝ)|^2171 ≤ (8976347521679/20000000000000 : ℝ)^1659
        have hw : |(5421558753/10000000000 : ℝ)|=(5421558753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s3_5 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (41428117/78125000 : ℝ)*x 0 + (-1917602701/10000000000 : ℝ)*x 1 + (5421558611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41428117/78125000 : ℝ)^2171 ≤ (1089988842479/2500000000000 : ℝ)^1659 := by
    have hnat : (41428117 : ℕ)^2171*2500000000000^1659 ≤ 1089988842479^1659*78125000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41428117 78125000 1089988842479 2500000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1917602701/10000000000 : ℝ)^2171 ≤ (179979847191/1562500000000 : ℝ)^1659 := by
    have hnat : (1917602701 : ℕ)^2171*1562500000000^1659 ≤ 179979847191^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917602701 10000000000 179979847191 1562500000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421558611/10000000000 : ℝ)^2171 ≤ (44881736070073/100000000000000 : ℝ)^1659 := by
    have hnat : (5421558611 : ℕ)^2171*100000000000000^1659 ≤ 44881736070073^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421558611 10000000000 44881736070073 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41428117/78125000 : ℝ), (-1917602701/10000000000 : ℝ), (5421558611/10000000000 : ℝ)] ![(1089988842479/2500000000000 : ℝ), (179979847191/1562500000000 : ℝ), (44881736070073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41428117/78125000 : ℝ)|^2171 ≤ (1089988842479/2500000000000 : ℝ)^1659
        have hw : |(41428117/78125000 : ℝ)|=(41428117/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1917602701/10000000000 : ℝ)|^2171 ≤ (179979847191/1562500000000 : ℝ)^1659
        have hw : |(-1917602701/10000000000 : ℝ)|=(1917602701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421558611/10000000000 : ℝ)|^2171 ≤ (44881736070073/100000000000000 : ℝ)^1659
        have hw : |(5421558611/10000000000 : ℝ)|=(5421558611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s3_6 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1325699631/2500000000 : ℝ)*x 0 + (84711859/156250000 : ℝ)*x 1 + (-1872659/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325699631/2500000000 : ℝ)^2171 ≤ (21799774417943/50000000000000 : ℝ)^1659 := by
    have hnat : (1325699631 : ℕ)^2171*50000000000000^1659 ≤ 21799774417943^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325699631 2500000000 21799774417943 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84711859/156250000 : ℝ)^2171 ≤ (44881740024211/100000000000000 : ℝ)^1659 := by
    have hnat : (84711859 : ℕ)^2171*100000000000000^1659 ≤ 44881740024211^1659*156250000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84711859 156250000 44881740024211 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1872659/9765625 : ℝ)^2171 ≤ (11518711124199/100000000000000 : ℝ)^1659 := by
    have hnat : (1872659 : ℕ)^2171*100000000000000^1659 ≤ 11518711124199^1659*9765625^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872659 9765625 11518711124199 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325699631/2500000000 : ℝ), (84711859/156250000 : ℝ), (-1872659/9765625 : ℝ)] ![(21799774417943/50000000000000 : ℝ), (44881740024211/100000000000000 : ℝ), (11518711124199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325699631/2500000000 : ℝ)|^2171 ≤ (21799774417943/50000000000000 : ℝ)^1659
        have hw : |(1325699631/2500000000 : ℝ)|=(1325699631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84711859/156250000 : ℝ)|^2171 ≤ (44881740024211/100000000000000 : ℝ)^1659
        have hw : |(84711859/156250000 : ℝ)|=(84711859/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1872659/9765625 : ℝ)|^2171 ≤ (11518711124199/100000000000000 : ℝ)^1659
        have hw : |(-1872659/9765625 : ℝ)|=(1872659/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s3_7 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (269716117/625000000 : ℝ)*x 0 + (1129292587/2500000000 : ℝ)*x 1 + (4122117659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269716117/625000000 : ℝ)^2171 ≤ (33295765567393/100000000000000 : ℝ)^1659 := by
    have hnat : (269716117 : ℕ)^2171*100000000000000^1659 ≤ 33295765567393^1659*625000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269716117 625000000 33295765567393 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129292587/2500000000 : ℝ)^2171 ≤ (17673456007609/50000000000000 : ℝ)^1659 := by
    have hnat : (1129292587 : ℕ)^2171*50000000000000^1659 ≤ 17673456007609^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129292587 2500000000 17673456007609 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4122117659/10000000000 : ℝ)^2171 ≤ (3919665300329/12500000000000 : ℝ)^1659 := by
    have hnat : (4122117659 : ℕ)^2171*12500000000000^1659 ≤ 3919665300329^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4122117659 10000000000 3919665300329 12500000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269716117/625000000 : ℝ), (1129292587/2500000000 : ℝ), (4122117659/10000000000 : ℝ)] ![(33295765567393/100000000000000 : ℝ), (17673456007609/50000000000000 : ℝ), (3919665300329/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269716117/625000000 : ℝ)|^2171 ≤ (33295765567393/100000000000000 : ℝ)^1659
        have hw : |(269716117/625000000 : ℝ)|=(269716117/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1129292587/2500000000 : ℝ)|^2171 ≤ (17673456007609/50000000000000 : ℝ)^1659
        have hw : |(1129292587/2500000000 : ℝ)|=(1129292587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4122117659/10000000000 : ℝ)|^2171 ≤ (3919665300329/12500000000000 : ℝ)^1659
        have hw : |(4122117659/10000000000 : ℝ)|=(4122117659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1382_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7977/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5051/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1101/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (468/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7977/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5051/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7977/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5051/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7977/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5051/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7977/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5051/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7977/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5051/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7977/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5051/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5051/50000 : ℝ) ^ (4341/1024 : ℝ) ≤ (1203527827130397/20000000000000000000 : ℝ) := by
    have hpowers : (5051/50000 : ℝ)^4341 ≤ (1203527827130397/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5051 : ℕ)^4341*20000000000000000000^1024 ≤ 1203527827130397^1024*50000^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5051 50000 1203527827130397 20000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5051/50000 : ℝ)) (X := (1203527827130397/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7977/50000 : ℝ) ^ (4341/1024 : ℝ) ≤ (10439956300724021/25000000000000000000 : ℝ) := by
    have hpowers : (7977/50000 : ℝ)^4341 ≤ (10439956300724021/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7977 : ℕ)^4341*25000000000000000000^1024 ≤ 10439956300724021^1024*50000^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7977 50000 10439956300724021 25000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7977/50000 : ℝ)) (X := (10439956300724021/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001203527827130397/10000000000000000000 : ℝ) ≤ (10000283887544573/10000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (10001203527827130397/10000000000000000000 : ℝ)^1024 ≤ (10000283887544573/10000000000000000 : ℝ)^4341 := by
      have hnat : (10001203527827130397 : ℕ)^1024*10000000000000000^4341 ≤ 10000283887544573^4341*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001203527827130397 10000000000000000000 10000283887544573 10000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283887544573/10000000000000000 : ℝ)) (X := (10001203527827130397/10000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047777464338548069/100000000000000000000 : ℝ) ≤ (5000563409301679/5000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (100047777464338548069/100000000000000000000 : ℝ)^1024 ≤ (5000563409301679/5000000000000000 : ℝ)^4341 := by
      have hnat : (100047777464338548069 : ℕ)^1024*5000000000000000^4341 ≤ 5000563409301679^4341*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047777464338548069 100000000000000000000 5000563409301679 5000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000563409301679/5000000000000000 : ℝ)) (X := (100047777464338548069/100000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12510439956300724021/12500000000000000000 : ℝ) ≤ (10001969749662143/10000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (12510439956300724021/12500000000000000000 : ℝ)^1024 ≤ (10001969749662143/10000000000000000 : ℝ)^4341 := by
      have hnat : (12510439956300724021 : ℕ)^1024*10000000000000000^4341 ≤ 10001969749662143^4341*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12510439956300724021 12500000000000000000 10001969749662143 10000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001969749662143/10000000000000000 : ℝ)) (X := (12510439956300724021/12500000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1203527827130397/20000000000000000000 : ℝ) ≤ ((14283357112011511/14287109375000000 : ℝ)+2*(168586211757/117040000000000 : ℝ)*(5051/50000 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (14283357112011511/14287109375000000 : ℝ)+2*(168586211757/117040000000000 : ℝ)*(5051/50000 : ℝ)=(10000283887544573/10000000000000000 : ℝ) by norm_num, show 1+2*(1203527827130397/20000000000000000000 : ℝ)=(10001203527827130397/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10439956300724021/25000000000000000000 : ℝ)+(1203527827130397/20000000000000000000 : ℝ) ≤ ((14283357112011511/14287109375000000 : ℝ)+(168586211757/117040000000000 : ℝ)*((7977/50000 : ℝ)+(5051/50000 : ℝ)))^(4341/1024 : ℝ) := by
    rw [show (14283357112011511/14287109375000000 : ℝ)+(168586211757/117040000000000 : ℝ)*((7977/50000 : ℝ)+(5051/50000 : ℝ))=(5000563409301679/5000000000000000 : ℝ) by norm_num, show 1+(10439956300724021/25000000000000000000 : ℝ)+(1203527827130397/20000000000000000000 : ℝ)=(100047777464338548069/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10439956300724021/25000000000000000000 : ℝ) ≤ ((14283357112011511/14287109375000000 : ℝ)+2*(168586211757/117040000000000 : ℝ)*(7977/50000 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (14283357112011511/14287109375000000 : ℝ)+2*(168586211757/117040000000000 : ℝ)*(7977/50000 : ℝ)=(10001969749662143/10000000000000000 : ℝ) by norm_num, show 1+2*(10439956300724021/25000000000000000000 : ℝ)=(12510439956300724021/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14283357112011511/14287109375000000 : ℝ)*(X 1 0+X 2 0)+(168586211757/117040000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (5051/50000 : ℝ)) (hi := (7977/50000 : ℝ)) (c := (14283357112011511/14287109375000000 : ℝ)) (alpha := (168586211757/117040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14283357112011511/14287109375000000 : ℝ)*(X 0 1+X 2 1)+(168586211757/117040000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (5051/50000 : ℝ)) (hi := (7977/50000 : ℝ)) (c := (14283357112011511/14287109375000000 : ℝ)) (alpha := (168586211757/117040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14283357112011511/14287109375000000 : ℝ)*(X 0 2+X 1 2)+(168586211757/117040000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (5051/50000 : ℝ)) (hi := (7977/50000 : ℝ)) (c := (14283357112011511/14287109375000000 : ℝ)) (alpha := (168586211757/117040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2008520553/10000000000 : ℝ)*X 0 0+(5422327517/10000000000 : ℝ)*X 0 1+(5234986963/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351268187/10000000000 : ℝ)*X 1 0+(-2104174353/10000000000 : ℝ)*X 1 1+(1308746817/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351268169/10000000000 : ℝ)*X 2 0+(654373419/1250000000 : ℝ)*X 2 1+(-1052087133/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1078855437/2500000000 : ℝ)*X 0 0+(1030120997/2500000000 : ℝ)*X 0 1+(4518793953/10000000000 : ℝ)*X 0 2+(1078855437/2500000000 : ℝ)*X 1 0+(1030120997/2500000000 : ℝ)*X 1 1+(4518793953/10000000000 : ℝ)*X 1 2+(1078855437/2500000000 : ℝ)*X 2 0+(1030120997/2500000000 : ℝ)*X 2 1+(4518793953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-502134477/2500000000 : ℝ)*X 0 0+(20452153/39062500 : ℝ)*X 0 1+(5421558753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((41428117/78125000 : ℝ)*X 1 0+(-1917602701/10000000000 : ℝ)*X 1 1+(5421558611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325699631/2500000000 : ℝ)*X 2 0+(84711859/156250000 : ℝ)*X 2 1+(-1872659/9765625 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((269716117/625000000 : ℝ)*X 0 0+(1129292587/2500000000 : ℝ)*X 0 1+(4122117659/10000000000 : ℝ)*X 0 2+(269716117/625000000 : ℝ)*X 1 0+(1129292587/2500000000 : ℝ)*X 1 1+(4122117659/10000000000 : ℝ)*X 1 2+(269716117/625000000 : ℝ)*X 2 0+(1129292587/2500000000 : ℝ)*X 2 1+(4122117659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (368338981255955227912207557/45718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1227621821/100000000000000 : ℝ)*(base19) + (111363881/12500000000000 : ℝ)*(base23) + (170574691/100000000000000 : ℝ)*(lower2) + (42462153/20000000000000 : ℝ)*(upper3) + (66220689/100000000000000 : ℝ)*(upper5) + (3924277442982639/100000000000000 : ℝ)*(major0) + (3924277442982639/100000000000000 : ℝ)*(major1) + (3924277442982639/100000000000000 : ℝ)*(major2) + (2668951319312813/50000000000000 : ℝ)*(sp0) + (2668965055460751/50000000000000 : ℝ)*(sp1) + (213517217905291/4000000000000 : ℝ)*(sp2) + (1255306920824721/50000000000000 : ℝ)*(sp3) + (224218107/781250000000 : ℝ)*(sp4) + (4718609113/50000000000000 : ℝ)*(sp7) + (627655819716917/25000000000000 : ℝ)*(f.failure) + (5337931338543323/100000000000000 : ℝ)*(f.sum) + (10816030858939/5852000000000000000000000000 : ℝ)*base65 + (229366721950460587/182875000000000000000000000000000 : ℝ)*base67 + (1592614412870960587/182875000000000000000000000000000 : ℝ)*base69 + (1835763781177539413/182875000000000000000000000000000 : ℝ)*base72 + (18570337011147/5852000000000000000000000000 : ℝ)*base73 + (999856260442210587/182875000000000000000000000000000 : ℝ)*base75 + (44612270039585587/182875000000000000000000000000000 : ℝ)*base77 + (1730132727360789413/182875000000000000000000000000000 : ℝ)*base80 + (4502828355797/5852000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (18544217/2500000000000000000000 : ℝ)*base89 + (18544217/2500000000000000000000 : ℝ)*base91 + (18544217/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61127689009308882690692427/5714843750000000000000000000000 : ℝ) := by norm_num
    linear_combination (175779731/10000000000000 : ℝ)*(base19) + (1274254889/100000000000000 : ℝ)*(base23) + (698317/10000000000000 : ℝ)*(upper2) + (82451161/50000000000000 : ℝ)*(upper3) + (33590581/25000000000000 : ℝ)*(upper5) + (494575889999957/12500000000000 : ℝ)*(major0) + (494575889999957/12500000000000 : ℝ)*(major1) + (494575889999957/12500000000000 : ℝ)*(major2) + (30201411647/100000000000000 : ℝ)*(sp1) + (13023616089/50000000000000 : ℝ)*(sp2) + (2690953571759467/50000000000000 : ℝ)*(sp4) + (2690937592154989/50000000000000 : ℝ)*(sp5) + (5381879822031867/100000000000000 : ℝ)*(sp6) + (1265653369968501/50000000000000 : ℝ)*(sp7) + (1265653369968501/50000000000000 : ℝ)*(f.failure) + (2690953571759467/50000000000000 : ℝ)*(f.sum) + (2210860110619/731500000000000000000000000 : ℝ)*base66 + (129097016829715919/22859375000000000000000000000000 : ℝ)*base68 + (298823670354028419/22859375000000000000000000000000 : ℝ)*base70 + (93649688940943897/11429687500000000000000000000000 : ℝ)*base72 + (859676662703/1463000000000000000000000000 : ℝ)*base74 + (233493900305215919/22859375000000000000000000000000 : ℝ)*base76 + (187417100759997169/22859375000000000000000000000000 : ℝ)*base78 + (248164321897965919/22859375000000000000000000000000 : ℝ)*base80 + (2351108656669/365750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (58925401/5000000000000000000000 : ℝ)*base89 + (58925401/5000000000000000000000 : ℝ)*base91 + (58925401/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1382_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7977/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5051/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1101/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (468/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1382_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1382_s4_0 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2009690277/10000000000 : ℝ)*x 0 + (1082513991/2000000000 : ℝ)*x 1 + (1310993863/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2009690277/10000000000 : ℝ)^2171 ≤ (6123942324793/50000000000000 : ℝ)^1659 := by
    have hnat : (2009690277 : ℕ)^2171*50000000000000^1659 ≤ 6123942324793^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009690277 10000000000 6123942324793 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082513991/2000000000 : ℝ)^2171 ≤ (44784384598139/100000000000000 : ℝ)^1659 := by
    have hnat : (1082513991 : ℕ)^2171*100000000000000^1659 ≤ 44784384598139^1659*2000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082513991 2000000000 44784384598139 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310993863/2500000000 : ℝ)^2171 ≤ (4296773073851/10000000000000 : ℝ)^1659 := by
    have hnat : (1310993863 : ℕ)^2171*10000000000000^1659 ≤ 4296773073851^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310993863 2500000000 4296773073851 10000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2009690277/10000000000 : ℝ), (1082513991/2000000000 : ℝ), (1310993863/2500000000 : ℝ)] ![(6123942324793/50000000000000 : ℝ), (44784384598139/100000000000000 : ℝ), (4296773073851/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2009690277/10000000000 : ℝ)|^2171 ≤ (6123942324793/50000000000000 : ℝ)^1659
        have hw : |(-2009690277/10000000000 : ℝ)|=(2009690277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082513991/2000000000 : ℝ)|^2171 ≤ (44784384598139/100000000000000 : ℝ)^1659
        have hw : |(1082513991/2000000000 : ℝ)|=(1082513991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310993863/2500000000 : ℝ)|^2171 ≤ (4296773073851/10000000000000 : ℝ)^1659
        have hw : |(1310993863/2500000000 : ℝ)|=(1310993863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s4_1 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674383281/5000000000 : ℝ)*x 0 + (-2095594197/10000000000 : ℝ)*x 1 + (5243975663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674383281/5000000000 : ℝ)^2171 ≤ (22047400092461/50000000000000 : ℝ)^1659 := by
    have hnat : (2674383281 : ℕ)^2171*50000000000000^1659 ≤ 22047400092461^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674383281 5000000000 22047400092461 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2095594197/10000000000 : ℝ)^2171 ≤ (6468733403127/50000000000000 : ℝ)^1659 := by
    have hnat : (2095594197 : ℕ)^2171*50000000000000^1659 ≤ 6468733403127^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095594197 10000000000 6468733403127 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243975663/10000000000 : ℝ)^2171 ≤ (42967733000953/100000000000000 : ℝ)^1659 := by
    have hnat : (5243975663 : ℕ)^2171*100000000000000^1659 ≤ 42967733000953^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243975663 10000000000 42967733000953 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674383281/5000000000 : ℝ), (-2095594197/10000000000 : ℝ), (5243975663/10000000000 : ℝ)] ![(22047400092461/50000000000000 : ℝ), (6468733403127/50000000000000 : ℝ), (42967733000953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674383281/5000000000 : ℝ)|^2171 ≤ (22047400092461/50000000000000 : ℝ)^1659
        have hw : |(2674383281/5000000000 : ℝ)|=(2674383281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2095594197/10000000000 : ℝ)|^2171 ≤ (6468733403127/50000000000000 : ℝ)^1659
        have hw : |(-2095594197/10000000000 : ℝ)|=(2095594197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243975663/10000000000 : ℝ)|^2171 ≤ (42967733000953/100000000000000 : ℝ)^1659
        have hw : |(5243975663/10000000000 : ℝ)|=(5243975663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s4_2 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337191651/2500000000 : ℝ)*x 0 + (524397539/1000000000 : ℝ)*x 1 + (-1047797251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337191651/2500000000 : ℝ)^2171 ≤ (1763792025521/4000000000000 : ℝ)^1659 := by
    have hnat : (1337191651 : ℕ)^2171*4000000000000^1659 ≤ 1763792025521^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337191651 2500000000 1763792025521 4000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524397539/1000000000 : ℝ)^2171 ≤ (42967730073717/100000000000000 : ℝ)^1659 := by
    have hnat : (524397539 : ℕ)^2171*100000000000000^1659 ≤ 42967730073717^1659*1000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524397539 1000000000 42967730073717 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047797251/5000000000 : ℝ)^2171 ≤ (12937469270337/100000000000000 : ℝ)^1659 := by
    have hnat : (1047797251 : ℕ)^2171*100000000000000^1659 ≤ 12937469270337^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047797251 5000000000 12937469270337 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337191651/2500000000 : ℝ), (524397539/1000000000 : ℝ), (-1047797251/5000000000 : ℝ)] ![(1763792025521/4000000000000 : ℝ), (42967730073717/100000000000000 : ℝ), (12937469270337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337191651/2500000000 : ℝ)|^2171 ≤ (1763792025521/4000000000000 : ℝ)^1659
        have hw : |(1337191651/2500000000 : ℝ)|=(1337191651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524397539/1000000000 : ℝ)|^2171 ≤ (42967730073717/100000000000000 : ℝ)^1659
        have hw : |(524397539/1000000000 : ℝ)|=(524397539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1047797251/5000000000 : ℝ)|^2171 ≤ (12937469270337/100000000000000 : ℝ)^1659
        have hw : |(-1047797251/5000000000 : ℝ)|=(1047797251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s4_3 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4316135607/10000000000 : ℝ)*x 0 + (2070161847/5000000000 : ℝ)*x 1 + (224938973/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316135607/10000000000 : ℝ)^2171 ≤ (33302608558879/100000000000000 : ℝ)^1659 := by
    have hnat : (4316135607 : ℕ)^2171*100000000000000^1659 ≤ 33302608558879^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316135607 10000000000 33302608558879 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070161847/5000000000 : ℝ)^2171 ≤ (31538683019369/100000000000000 : ℝ)^1659 := by
    have hnat : (2070161847 : ℕ)^2171*100000000000000^1659 ≤ 31538683019369^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070161847 5000000000 31538683019369 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224938973/500000000 : ℝ)^2171 ≤ (4394838550029/12500000000000 : ℝ)^1659 := by
    have hnat : (224938973 : ℕ)^2171*12500000000000^1659 ≤ 4394838550029^1659*500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224938973 500000000 4394838550029 12500000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316135607/10000000000 : ℝ), (2070161847/5000000000 : ℝ), (224938973/500000000 : ℝ)] ![(33302608558879/100000000000000 : ℝ), (31538683019369/100000000000000 : ℝ), (4394838550029/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316135607/10000000000 : ℝ)|^2171 ≤ (33302608558879/100000000000000 : ℝ)^1659
        have hw : |(4316135607/10000000000 : ℝ)|=(4316135607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2070161847/5000000000 : ℝ)|^2171 ≤ (31538683019369/100000000000000 : ℝ)^1659
        have hw : |(2070161847/5000000000 : ℝ)|=(2070161847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224938973/500000000 : ℝ)|^2171 ≤ (4394838550029/12500000000000 : ℝ)^1659
        have hw : |(224938973/500000000 : ℝ)|=(224938973/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s4_4 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2009702629/10000000000 : ℝ)*x 0 + (5244593763/10000000000 : ℝ)*x 1 + (5411948533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2009702629/10000000000 : ℝ)^2171 ≤ (6123991580107/50000000000000 : ℝ)^1659 := by
    have hnat : (2009702629 : ℕ)^2171*50000000000000^1659 ≤ 6123991580107^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009702629 10000000000 6123991580107 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244593763/10000000000 : ℝ)^2171 ≤ (2148718034293/5000000000000 : ℝ)^1659 := by
    have hnat : (5244593763 : ℕ)^2171*5000000000000^1659 ≤ 2148718034293^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244593763 10000000000 2148718034293 5000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411948533/10000000000 : ℝ)^2171 ≤ (1399301754423/3125000000000 : ℝ)^1659 := by
    have hnat : (5411948533 : ℕ)^2171*3125000000000^1659 ≤ 1399301754423^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411948533 10000000000 1399301754423 3125000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2009702629/10000000000 : ℝ), (5244593763/10000000000 : ℝ), (5411948533/10000000000 : ℝ)] ![(6123991580107/50000000000000 : ℝ), (2148718034293/5000000000000 : ℝ), (1399301754423/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2009702629/10000000000 : ℝ)|^2171 ≤ (6123991580107/50000000000000 : ℝ)^1659
        have hw : |(-2009702629/10000000000 : ℝ)|=(2009702629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244593763/10000000000 : ℝ)|^2171 ≤ (2148718034293/5000000000000 : ℝ)^1659
        have hw : |(5244593763/10000000000 : ℝ)|=(5244593763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411948533/10000000000 : ℝ)|^2171 ≤ (1399301754423/3125000000000 : ℝ)^1659
        have hw : |(5411948533/10000000000 : ℝ)|=(5411948533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s4_5 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305147711/10000000000 : ℝ)*x 0 + (-1927621953/10000000000 : ℝ)*x 1 + (5411947221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305147711/10000000000 : ℝ)^2171 ≤ (10906206634323/25000000000000 : ℝ)^1659 := by
    have hnat : (5305147711 : ℕ)^2171*25000000000000^1659 ≤ 10906206634323^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305147711 10000000000 10906206634323 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1927621953/10000000000 : ℝ)^2171 ≤ (11597531511667/100000000000000 : ℝ)^1659 := by
    have hnat : (1927621953 : ℕ)^2171*100000000000000^1659 ≤ 11597531511667^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927621953 10000000000 11597531511667 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411947221/10000000000 : ℝ)^2171 ≤ (44777641936087/100000000000000 : ℝ)^1659 := by
    have hnat : (5411947221 : ℕ)^2171*100000000000000^1659 ≤ 44777641936087^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411947221 10000000000 44777641936087 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305147711/10000000000 : ℝ), (-1927621953/10000000000 : ℝ), (5411947221/10000000000 : ℝ)] ![(10906206634323/25000000000000 : ℝ), (11597531511667/100000000000000 : ℝ), (44777641936087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305147711/10000000000 : ℝ)|^2171 ≤ (10906206634323/25000000000000 : ℝ)^1659
        have hw : |(5305147711/10000000000 : ℝ)|=(5305147711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1927621953/10000000000 : ℝ)|^2171 ≤ (11597531511667/100000000000000 : ℝ)^1659
        have hw : |(-1927621953/10000000000 : ℝ)|=(1927621953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411947221/10000000000 : ℝ)|^2171 ≤ (44777641936087/100000000000000 : ℝ)^1659
        have hw : |(5411947221/10000000000 : ℝ)|=(5411947221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s4_6 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305147297/10000000000 : ℝ)*x 0 + (2705973603/5000000000 : ℝ)*x 1 + (-96381127/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305147297/10000000000 : ℝ)^2171 ≤ (43624822082269/100000000000000 : ℝ)^1659 := by
    have hnat : (5305147297 : ℕ)^2171*100000000000000^1659 ≤ 43624822082269^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305147297 10000000000 43624822082269 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705973603/5000000000 : ℝ)^2171 ≤ (44777641773677/100000000000000 : ℝ)^1659 := by
    have hnat : (2705973603 : ℕ)^2171*100000000000000^1659 ≤ 44777641773677^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705973603 5000000000 44777641773677 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96381127/500000000 : ℝ)^2171 ≤ (5798768066649/50000000000000 : ℝ)^1659 := by
    have hnat : (96381127 : ℕ)^2171*50000000000000^1659 ≤ 5798768066649^1659*500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96381127 500000000 5798768066649 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305147297/10000000000 : ℝ), (2705973603/5000000000 : ℝ), (-96381127/500000000 : ℝ)] ![(43624822082269/100000000000000 : ℝ), (44777641773677/100000000000000 : ℝ), (5798768066649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305147297/10000000000 : ℝ)|^2171 ≤ (43624822082269/100000000000000 : ℝ)^1659
        have hw : |(5305147297/10000000000 : ℝ)|=(5305147297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705973603/5000000000 : ℝ)|^2171 ≤ (44777641773677/100000000000000 : ℝ)^1659
        have hw : |(2705973603/5000000000 : ℝ)|=(2705973603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-96381127/500000000 : ℝ)|^2171 ≤ (5798768066649/50000000000000 : ℝ)^1659
        have hw : |(-96381127/500000000 : ℝ)|=(96381127/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s4_7 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4316162457/10000000000 : ℝ)*x 0 + (2248731533/5000000000 : ℝ)*x 1 + (2070823467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316162457/10000000000 : ℝ)^2171 ≤ (8325719916561/25000000000000 : ℝ)^1659 := by
    have hnat : (4316162457 : ℕ)^2171*25000000000000^1659 ≤ 8325719916561^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316162457 10000000000 8325719916561 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248731533/5000000000 : ℝ)^2171 ≤ (8786311535407/25000000000000 : ℝ)^1659 := by
    have hnat : (2248731533 : ℕ)^2171*25000000000000^1659 ≤ 8786311535407^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248731533 5000000000 8786311535407 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070823467/5000000000 : ℝ)^2171 ≤ (31551874171603/100000000000000 : ℝ)^1659 := by
    have hnat : (2070823467 : ℕ)^2171*100000000000000^1659 ≤ 31551874171603^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070823467 5000000000 31551874171603 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316162457/10000000000 : ℝ), (2248731533/5000000000 : ℝ), (2070823467/5000000000 : ℝ)] ![(8325719916561/25000000000000 : ℝ), (8786311535407/25000000000000 : ℝ), (31551874171603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316162457/10000000000 : ℝ)|^2171 ≤ (8325719916561/25000000000000 : ℝ)^1659
        have hw : |(4316162457/10000000000 : ℝ)|=(4316162457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248731533/5000000000 : ℝ)|^2171 ≤ (8786311535407/25000000000000 : ℝ)^1659
        have hw : |(2248731533/5000000000 : ℝ)|=(2248731533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2070823467/5000000000 : ℝ)|^2171 ≤ (31551874171603/100000000000000 : ℝ)^1659
        have hw : |(2070823467/5000000000 : ℝ)|=(2070823467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1382_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (468/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1101/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5601/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3693/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (468/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1101/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (468/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1101/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (468/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1101/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (468/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1101/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (468/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1101/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (468/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1101/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1101/10000 : ℝ) ^ (4341/1024 : ℝ) ≤ (8667411300366701/100000000000000000000 : ℝ) := by
    have hpowers : (1101/10000 : ℝ)^4341 ≤ (8667411300366701/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1101 : ℕ)^4341*100000000000000000000^1024 ≤ 8667411300366701^1024*10000^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1101 10000 8667411300366701 100000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1101/10000 : ℝ)) (X := (8667411300366701/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (468/3125 : ℝ) ^ (4341/1024 : ℝ) ≤ (99802255816757/312500000000000000 : ℝ) := by
    have hpowers : (468/3125 : ℝ)^4341 ≤ (99802255816757/312500000000000000 : ℝ)^1024 := by
      have hnat : (468 : ℕ)^4341*312500000000000000^1024 ≤ 99802255816757^1024*3125^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        468 3125 99802255816757 312500000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (468/3125 : ℝ)) (X := (99802255816757/312500000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008667411300366701/50000000000000000000 : ℝ) ≤ (10000408884654453/10000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (50008667411300366701/50000000000000000000 : ℝ)^1024 ≤ (10000408884654453/10000000000000000 : ℝ)^4341 := by
      have hnat : (50008667411300366701 : ℕ)^1024*10000000000000000^4341 ≤ 10000408884654453^4341*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008667411300366701 50000000000000000000 10000408884654453 10000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000408884654453/10000000000000000 : ℝ)) (X := (50008667411300366701/50000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040604133161728941/100000000000000000000 : ℝ) ≤ (10000957663759547/10000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (100040604133161728941/100000000000000000000 : ℝ)^1024 ≤ (10000957663759547/10000000000000000 : ℝ)^4341 := by
      have hnat : (100040604133161728941 : ℕ)^1024*10000000000000000^4341 ≤ 10000957663759547^4341*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040604133161728941 100000000000000000000 10000957663759547 10000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000957663759547/10000000000000000 : ℝ)) (X := (100040604133161728941/100000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (156349802255816757/156250000000000000 : ℝ) ≤ (10001506442864641/10000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (156349802255816757/156250000000000000 : ℝ)^1024 ≤ (10001506442864641/10000000000000000 : ℝ)^4341 := by
      have hnat : (156349802255816757 : ℕ)^1024*10000000000000000^4341 ≤ 10001506442864641^4341*156250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        156349802255816757 156250000000000000 10001506442864641 10000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001506442864641/10000000000000000 : ℝ)) (X := (156349802255816757/156250000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8667411300366701/100000000000000000000 : ℝ) ≤ ((6608256253440898453/6610000000000000000 : ℝ)+2*(274389552547/198300000000000 : ℝ)*(1101/10000 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (6608256253440898453/6610000000000000000 : ℝ)+2*(274389552547/198300000000000 : ℝ)*(1101/10000 : ℝ)=(10000408884654453/10000000000000000 : ℝ) by norm_num, show 1+2*(8667411300366701/100000000000000000000 : ℝ)=(50008667411300366701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(99802255816757/312500000000000000 : ℝ)+(8667411300366701/100000000000000000000 : ℝ) ≤ ((6608256253440898453/6610000000000000000 : ℝ)+(274389552547/198300000000000 : ℝ)*((468/3125 : ℝ)+(1101/10000 : ℝ)))^(4341/1024 : ℝ) := by
    rw [show (6608256253440898453/6610000000000000000 : ℝ)+(274389552547/198300000000000 : ℝ)*((468/3125 : ℝ)+(1101/10000 : ℝ))=(10000957663759547/10000000000000000 : ℝ) by norm_num, show 1+(99802255816757/312500000000000000 : ℝ)+(8667411300366701/100000000000000000000 : ℝ)=(100040604133161728941/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(99802255816757/312500000000000000 : ℝ) ≤ ((6608256253440898453/6610000000000000000 : ℝ)+2*(274389552547/198300000000000 : ℝ)*(468/3125 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (6608256253440898453/6610000000000000000 : ℝ)+2*(274389552547/198300000000000 : ℝ)*(468/3125 : ℝ)=(10001506442864641/10000000000000000 : ℝ) by norm_num, show 1+2*(99802255816757/312500000000000000 : ℝ)=(156349802255816757/156250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6608256253440898453/6610000000000000000 : ℝ)*(X 1 0+X 2 0)+(274389552547/198300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (1101/10000 : ℝ)) (hi := (468/3125 : ℝ)) (c := (6608256253440898453/6610000000000000000 : ℝ)) (alpha := (274389552547/198300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6608256253440898453/6610000000000000000 : ℝ)*(X 0 1+X 2 1)+(274389552547/198300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (1101/10000 : ℝ)) (hi := (468/3125 : ℝ)) (c := (6608256253440898453/6610000000000000000 : ℝ)) (alpha := (274389552547/198300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6608256253440898453/6610000000000000000 : ℝ)*(X 0 2+X 1 2)+(274389552547/198300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (1101/10000 : ℝ)) (hi := (468/3125 : ℝ)) (c := (6608256253440898453/6610000000000000000 : ℝ)) (alpha := (274389552547/198300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2009690277/10000000000 : ℝ)*X 0 0+(1082513991/2000000000 : ℝ)*X 0 1+(1310993863/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674383281/5000000000 : ℝ)*X 1 0+(-2095594197/10000000000 : ℝ)*X 1 1+(5243975663/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337191651/2500000000 : ℝ)*X 2 0+(524397539/1000000000 : ℝ)*X 2 1+(-1047797251/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4316135607/10000000000 : ℝ)*X 0 0+(2070161847/5000000000 : ℝ)*X 0 1+(224938973/500000000 : ℝ)*X 0 2+(4316135607/10000000000 : ℝ)*X 1 0+(2070161847/5000000000 : ℝ)*X 1 1+(224938973/500000000 : ℝ)*X 1 2+(4316135607/10000000000 : ℝ)*X 2 0+(2070161847/5000000000 : ℝ)*X 2 1+(224938973/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2009702629/10000000000 : ℝ)*X 0 0+(5244593763/10000000000 : ℝ)*X 0 1+(5411948533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305147711/10000000000 : ℝ)*X 1 0+(-1927621953/10000000000 : ℝ)*X 1 1+(5411947221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305147297/10000000000 : ℝ)*X 2 0+(2705973603/5000000000 : ℝ)*X 2 1+(-96381127/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4316162457/10000000000 : ℝ)*X 0 0+(2248731533/5000000000 : ℝ)*X 0 1+(2070823467/5000000000 : ℝ)*X 0 2+(4316162457/10000000000 : ℝ)*X 1 0+(2248731533/5000000000 : ℝ)*X 1 1+(2070823467/5000000000 : ℝ)*X 1 2+(4316162457/10000000000 : ℝ)*X 2 0+(2248731533/5000000000 : ℝ)*X 2 1+(2070823467/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (414051335819419641743615523/66100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (301152181/25000000000000 : ℝ)*(base19) + (238506937/20000000000000 : ℝ)*(base23) + (8406719/20000000000000 : ℝ)*(lower2) + (40889159/10000000000000 : ℝ)*(upper3) + (1066343/10000000000000 : ℝ)*(lower4) + (872121230579201/20000000000000 : ℝ)*(major0) + (872121230579201/20000000000000 : ℝ)*(major1) + (872121230579201/20000000000000 : ℝ)*(major2) + (5931422884709337/100000000000000 : ℝ)*(sp0) + (370714930984637/6250000000000 : ℝ)*(sp1) + (5931438907828231/100000000000000 : ℝ)*(sp2) + (697438759685587/25000000000000 : ℝ)*(sp3) + (8607826789/50000000000000 : ℝ)*(sp4) + (16957886261/100000000000000 : ℝ)*(sp7) + (278977199662861/10000000000000 : ℝ)*(f.failure) + (1482860025090729/25000000000000 : ℝ)*(f.sum) + (16999205836181/1983000000000000000000000000 : ℝ)*base65 + (2957397493935128159/396600000000000000000000000000000 : ℝ)*base67 + (5639242917396128159/396600000000000000000000000000000 : ℝ)*base69 + (6775750123557128159/396600000000000000000000000000000 : ℝ)*base71 + (1550776829497/396600000000000000000000000 : ℝ)*base73 + (5083315650049328159/396600000000000000000000000000000 : ℝ)*base75 + (6696323192265128159/396600000000000000000000000000000 : ℝ)*base77 + (1287857743754528159/396600000000000000000000000000000 : ℝ)*base79 + (10146068309111/1983000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2296239/1000000000000000000000 : ℝ)*base90 + (2296239/1000000000000000000000 : ℝ)*base92 + (2296239/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24944190653026089853491/3305000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2241774757/100000000000000 : ℝ)*(base19) + (1992922203/100000000000000 : ℝ)*(base23) + (56651417/25000000000000 : ℝ)*(lower4) + (364583193/100000000000000 : ℝ)*(upper5) + (4392897439366699/100000000000000 : ℝ)*(major0) + (4392897439366699/100000000000000 : ℝ)*(major1) + (4392897439366699/100000000000000 : ℝ)*(major2) + (14971082311/100000000000000 : ℝ)*(sp0) + (29531443199/100000000000000 : ℝ)*(sp1) + (2013685511/50000000000000 : ℝ)*(sp2) + (5975348759378149/100000000000000 : ℝ)*(sp4) + (5975331957242503/100000000000000 : ℝ)*(sp5) + (1493839427541809/25000000000000 : ℝ)*(sp6) + (281043089669259/10000000000000 : ℝ)*(sp7) + (281043089669259/10000000000000 : ℝ)*(f.failure) + (298768186523023/5000000000000 : ℝ)*(f.sum) + (57627676042123/9915000000000000000000000000 : ℝ)*base65 + (5166326525354250059/1983000000000000000000000000000000 : ℝ)*base68 + (16148423278265250059/1983000000000000000000000000000000 : ℝ)*base70 + (6595571322618749941/1983000000000000000000000000000000 : ℝ)*base71 + (50690679844483/9915000000000000000000000000 : ℝ)*base73 + (20480432106621749941/1983000000000000000000000000000000 : ℝ)*base75 + (5012268949071749941/1983000000000000000000000000000000 : ℝ)*base77 + (41010321644786250059/1983000000000000000000000000000000 : ℝ)*base80 + (35622832551313/9915000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (743641/1000000000000000000000 : ℝ)*base90 + (743641/1000000000000000000000 : ℝ)*base92 + (743641/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1382_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (468/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1101/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1382_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1382_s5_0 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2009879267/10000000000 : ℝ)*x 0 + (2705458673/5000000000 : ℝ)*x 1 + (5245503561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2009879267/10000000000 : ℝ)^2171 ≤ (1224939191773/10000000000000 : ℝ)^1659 := by
    have hnat : (2009879267 : ℕ)^2171*10000000000000^1659 ≤ 1224939191773^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009879267 10000000000 1224939191773 10000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705458673/5000000000 : ℝ)^2171 ≤ (44766491473977/100000000000000 : ℝ)^1659 := by
    have hnat : (2705458673 : ℕ)^2171*100000000000000^1659 ≤ 44766491473977^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705458673 5000000000 44766491473977 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245503561/10000000000 : ℝ)^2171 ≤ (8596823318387/20000000000000 : ℝ)^1659 := by
    have hnat : (5245503561 : ℕ)^2171*20000000000000^1659 ≤ 8596823318387^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245503561 10000000000 8596823318387 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2009879267/10000000000 : ℝ), (2705458673/5000000000 : ℝ), (5245503561/10000000000 : ℝ)] ![(1224939191773/10000000000000 : ℝ), (44766491473977/100000000000000 : ℝ), (8596823318387/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2009879267/10000000000 : ℝ)|^2171 ≤ (1224939191773/10000000000000 : ℝ)^1659
        have hw : |(-2009879267/10000000000 : ℝ)|=(2009879267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705458673/5000000000 : ℝ)|^2171 ≤ (44766491473977/100000000000000 : ℝ)^1659
        have hw : |(2705458673/5000000000 : ℝ)|=(2705458673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245503561/10000000000 : ℝ)|^2171 ≤ (8596823318387/20000000000000 : ℝ)^1659
        have hw : |(5245503561/10000000000 : ℝ)|=(5245503561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s5_1 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348342013/10000000000 : ℝ)*x 0 + (-523533249/2500000000 : ℝ)*x 1 + (209820143/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348342013/10000000000 : ℝ)^2171 ≤ (44090220140661/100000000000000 : ℝ)^1659 := by
    have hnat : (5348342013 : ℕ)^2171*100000000000000^1659 ≤ 44090220140661^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348342013 10000000000 44090220140661 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523533249/2500000000 : ℝ)^2171 ≤ (3231415772771/25000000000000 : ℝ)^1659 := by
    have hnat : (523533249 : ℕ)^2171*25000000000000^1659 ≤ 3231415772771^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523533249 2500000000 3231415772771 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209820143/400000000 : ℝ)^2171 ≤ (42984116742063/100000000000000 : ℝ)^1659 := by
    have hnat : (209820143 : ℕ)^2171*100000000000000^1659 ≤ 42984116742063^1659*400000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209820143 400000000 42984116742063 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348342013/10000000000 : ℝ), (-523533249/2500000000 : ℝ), (209820143/400000000 : ℝ)] ![(44090220140661/100000000000000 : ℝ), (3231415772771/25000000000000 : ℝ), (42984116742063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348342013/10000000000 : ℝ)|^2171 ≤ (44090220140661/100000000000000 : ℝ)^1659
        have hw : |(5348342013/10000000000 : ℝ)|=(5348342013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523533249/2500000000 : ℝ)|^2171 ≤ (3231415772771/25000000000000 : ℝ)^1659
        have hw : |(-523533249/2500000000 : ℝ)|=(523533249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209820143/400000000 : ℝ)|^2171 ≤ (42984116742063/100000000000000 : ℝ)^1659
        have hw : |(209820143/400000000 : ℝ)|=(209820143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s5_2 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668542751/1250000000 : ℝ)*x 0 + (2622751787/5000000000 : ℝ)*x 1 + (-418826601/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668542751/1250000000 : ℝ)^2171 ≤ (22045110043361/50000000000000 : ℝ)^1659 := by
    have hnat : (668542751 : ℕ)^2171*50000000000000^1659 ≤ 22045110043361^1659*1250000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668542751 1250000000 22045110043361 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622751787/5000000000 : ℝ)^2171 ≤ (2149205836567/5000000000000 : ℝ)^1659 := by
    have hnat : (2622751787 : ℕ)^2171*5000000000000^1659 ≤ 2149205836567^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622751787 5000000000 2149205836567 5000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418826601/2000000000 : ℝ)^2171 ≤ (12925663163779/100000000000000 : ℝ)^1659 := by
    have hnat : (418826601 : ℕ)^2171*100000000000000^1659 ≤ 12925663163779^1659*2000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418826601 2000000000 12925663163779 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668542751/1250000000 : ℝ), (2622751787/5000000000 : ℝ), (-418826601/2000000000 : ℝ)] ![(22045110043361/50000000000000 : ℝ), (2149205836567/5000000000000 : ℝ), (12925663163779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668542751/1250000000 : ℝ)|^2171 ≤ (22045110043361/50000000000000 : ℝ)^1659
        have hw : |(668542751/1250000000 : ℝ)|=(668542751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622751787/5000000000 : ℝ)|^2171 ≤ (2149205836567/5000000000000 : ℝ)^1659
        have hw : |(2622751787/5000000000 : ℝ)|=(2622751787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418826601/2000000000 : ℝ)|^2171 ≤ (12925663163779/100000000000000 : ℝ)^1659
        have hw : |(-418826601/2000000000 : ℝ)|=(418826601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s5_3 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2158124491/5000000000 : ℝ)*x 0 + (103592289/250000000 : ℝ)*x 1 + (224769203/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158124491/5000000000 : ℝ)^2171 ≤ (4162969165263/12500000000000 : ℝ)^1659 := by
    have hnat : (2158124491 : ℕ)^2171*12500000000000^1659 ≤ 4162969165263^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158124491 5000000000 4162969165263 12500000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103592289/250000000 : ℝ)^2171 ≤ (31572259254569/100000000000000 : ℝ)^1659 := by
    have hnat : (103592289 : ℕ)^2171*100000000000000^1659 ≤ 31572259254569^1659*250000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103592289 250000000 31572259254569 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224769203/500000000 : ℝ)^2171 ≤ (4390498427283/12500000000000 : ℝ)^1659 := by
    have hnat : (224769203 : ℕ)^2171*12500000000000^1659 ≤ 4390498427283^1659*500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224769203 500000000 4390498427283 12500000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158124491/5000000000 : ℝ), (103592289/250000000 : ℝ), (224769203/500000000 : ℝ)] ![(4162969165263/12500000000000 : ℝ), (31572259254569/100000000000000 : ℝ), (4390498427283/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158124491/5000000000 : ℝ)|^2171 ≤ (4162969165263/12500000000000 : ℝ)^1659
        have hw : |(2158124491/5000000000 : ℝ)|=(2158124491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103592289/250000000 : ℝ)|^2171 ≤ (31572259254569/100000000000000 : ℝ)^1659
        have hw : |(103592289/250000000 : ℝ)|=(103592289/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224769203/500000000 : ℝ)|^2171 ≤ (4390498427283/12500000000000 : ℝ)^1659
        have hw : |(224769203/500000000 : ℝ)|=(224769203/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s5_4 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1004945649/5000000000 : ℝ)*x 0 + (209843983/400000000 : ℝ)*x 1 + (1352579533/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1004945649/5000000000 : ℝ)^2171 ≤ (12249487871077/100000000000000 : ℝ)^1659 := by
    have hnat : (1004945649 : ℕ)^2171*100000000000000^1659 ≤ 12249487871077^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004945649 5000000000 12249487871077 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209843983/400000000 : ℝ)^2171 ≤ (10747627006571/25000000000000 : ℝ)^1659 := by
    have hnat : (209843983 : ℕ)^2171*25000000000000^1659 ≤ 10747627006571^1659*400000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209843983 400000000 10747627006571 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352579533/2500000000 : ℝ)^2171 ≤ (11190001020551/25000000000000 : ℝ)^1659 := by
    have hnat : (1352579533 : ℕ)^2171*25000000000000^1659 ≤ 11190001020551^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352579533 2500000000 11190001020551 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1004945649/5000000000 : ℝ), (209843983/400000000 : ℝ), (1352579533/2500000000 : ℝ)] ![(12249487871077/100000000000000 : ℝ), (10747627006571/25000000000000 : ℝ), (11190001020551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1004945649/5000000000 : ℝ)|^2171 ≤ (12249487871077/100000000000000 : ℝ)^1659
        have hw : |(-1004945649/5000000000 : ℝ)|=(1004945649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209843983/400000000 : ℝ)|^2171 ≤ (10747627006571/25000000000000 : ℝ)^1659
        have hw : |(209843983/400000000 : ℝ)|=(209843983/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352579533/2500000000 : ℝ)|^2171 ≤ (11190001020551/25000000000000 : ℝ)^1659
        have hw : |(1352579533/2500000000 : ℝ)|=(1352579533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s5_5 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305545113/10000000000 : ℝ)*x 0 + (-1929318361/10000000000 : ℝ)*x 1 + (5410318431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305545113/10000000000 : ℝ)^2171 ≤ (21814551500243/50000000000000 : ℝ)^1659 := by
    have hnat : (5305545113 : ℕ)^2171*50000000000000^1659 ≤ 21814551500243^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305545113 10000000000 21814551500243 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1929318361/10000000000 : ℝ)^2171 ≤ (11610889664511/100000000000000 : ℝ)^1659 := by
    have hnat : (1929318361 : ℕ)^2171*100000000000000^1659 ≤ 11610889664511^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929318361 10000000000 11610889664511 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410318431/10000000000 : ℝ)^2171 ≤ (44760007319273/100000000000000 : ℝ)^1659 := by
    have hnat : (5410318431 : ℕ)^2171*100000000000000^1659 ≤ 44760007319273^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410318431 10000000000 44760007319273 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305545113/10000000000 : ℝ), (-1929318361/10000000000 : ℝ), (5410318431/10000000000 : ℝ)] ![(21814551500243/50000000000000 : ℝ), (11610889664511/100000000000000 : ℝ), (44760007319273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305545113/10000000000 : ℝ)|^2171 ≤ (21814551500243/50000000000000 : ℝ)^1659
        have hw : |(5305545113/10000000000 : ℝ)|=(5305545113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1929318361/10000000000 : ℝ)|^2171 ≤ (11610889664511/100000000000000 : ℝ)^1659
        have hw : |(-1929318361/10000000000 : ℝ)|=(1929318361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410318431/10000000000 : ℝ)|^2171 ≤ (44760007319273/100000000000000 : ℝ)^1659
        have hw : |(5410318431/10000000000 : ℝ)|=(5410318431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s5_6 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326386243/2500000000 : ℝ)*x 0 + (5410318323/10000000000 : ℝ)*x 1 + (-964659351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326386243/2500000000 : ℝ)^2171 ≤ (1090727537079/2500000000000 : ℝ)^1659 := by
    have hnat : (1326386243 : ℕ)^2171*2500000000000^1659 ≤ 1090727537079^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326386243 2500000000 1090727537079 2500000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410318323/10000000000 : ℝ)^2171 ≤ (4476000615003/10000000000000 : ℝ)^1659 := by
    have hnat : (5410318323 : ℕ)^2171*10000000000000^1659 ≤ 4476000615003^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410318323 10000000000 4476000615003 10000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964659351/5000000000 : ℝ)^2171 ≤ (5805446175019/50000000000000 : ℝ)^1659 := by
    have hnat : (964659351 : ℕ)^2171*50000000000000^1659 ≤ 5805446175019^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964659351 5000000000 5805446175019 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326386243/2500000000 : ℝ), (5410318323/10000000000 : ℝ), (-964659351/5000000000 : ℝ)] ![(1090727537079/2500000000000 : ℝ), (4476000615003/10000000000000 : ℝ), (5805446175019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326386243/2500000000 : ℝ)|^2171 ≤ (1090727537079/2500000000000 : ℝ)^1659
        have hw : |(1326386243/2500000000 : ℝ)|=(1326386243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410318323/10000000000 : ℝ)|^2171 ≤ (4476000615003/10000000000000 : ℝ)^1659
        have hw : |(5410318323/10000000000 : ℝ)|=(5410318323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-964659351/5000000000 : ℝ)|^2171 ≤ (5805446175019/50000000000000 : ℝ)^1659
        have hw : |(-964659351/5000000000 : ℝ)|=(964659351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s5_7 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (43162741/100000000 : ℝ)*x 0 + (4494116961/10000000000 : ℝ)*x 1 + (828993073/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43162741/100000000 : ℝ)^2171 ≤ (33304006943317/100000000000000 : ℝ)^1659 := by
    have hnat : (43162741 : ℕ)^2171*100000000000000^1659 ≤ 33304006943317^1659*100000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43162741 100000000 33304006943317 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494116961/10000000000 : ℝ)^2171 ≤ (35111032278399/100000000000000 : ℝ)^1659 := by
    have hnat : (4494116961 : ℕ)^2171*100000000000000^1659 ≤ 35111032278399^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494116961 10000000000 35111032278399 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828993073/2000000000 : ℝ)^2171 ≤ (31584960760799/100000000000000 : ℝ)^1659 := by
    have hnat : (828993073 : ℕ)^2171*100000000000000^1659 ≤ 31584960760799^1659*2000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828993073 2000000000 31584960760799 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43162741/100000000 : ℝ), (4494116961/10000000000 : ℝ), (828993073/2000000000 : ℝ)] ![(33304006943317/100000000000000 : ℝ), (35111032278399/100000000000000 : ℝ), (31584960760799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43162741/100000000 : ℝ)|^2171 ≤ (33304006943317/100000000000000 : ℝ)^1659
        have hw : |(43162741/100000000 : ℝ)|=(43162741/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494116961/10000000000 : ℝ)|^2171 ≤ (35111032278399/100000000000000 : ℝ)^1659
        have hw : |(4494116961/10000000000 : ℝ)|=(4494116961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(828993073/2000000000 : ℝ)|^2171 ≤ (31584960760799/100000000000000 : ℝ)^1659
        have hw : |(828993073/2000000000 : ℝ)|=(828993073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1382_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2247/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14737/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5601/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5601/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5601/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5601/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5601/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5601/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5601/50000 : ℝ) ^ (4341/1024 : ℝ) ≤ (2331625623374639/25000000000000000000 : ℝ) := by
    have hpowers : (5601/50000 : ℝ)^4341 ≤ (2331625623374639/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5601 : ℕ)^4341*25000000000000000000^1024 ≤ 2331625623374639^1024*50000^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5601 50000 2331625623374639 25000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5601/50000 : ℝ)) (X := (2331625623374639/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3693/25000 : ℝ) ^ (4341/1024 : ℝ) ≤ (15066385095818773/50000000000000000000 : ℝ) := by
    have hpowers : (3693/25000 : ℝ)^4341 ≤ (15066385095818773/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3693 : ℕ)^4341*50000000000000000000^1024 ≤ 15066385095818773^1024*25000^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3693 25000 15066385095818773 50000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3693/25000 : ℝ)) (X := (15066385095818773/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502331625623374639/12500000000000000000 : ℝ) ≤ (1000043997502999/1000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (12502331625623374639/12500000000000000000 : ℝ)^1024 ≤ (1000043997502999/1000000000000000 : ℝ)^4341 := by
      have hnat : (12502331625623374639 : ℕ)^1024*1000000000000000^4341 ≤ 1000043997502999^4341*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502331625623374639 12500000000000000000 1000043997502999 1000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000043997502999/1000000000000000 : ℝ)) (X := (12502331625623374639/12500000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019729636342568051/50000000000000000000 : ℝ) ≤ (1250116333232979/1250000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (50019729636342568051/50000000000000000000 : ℝ)^1024 ≤ (1250116333232979/1250000000000000 : ℝ)^4341 := by
      have hnat : (50019729636342568051 : ℕ)^1024*1250000000000000^4341 ≤ 1250116333232979^4341*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019729636342568051 50000000000000000000 1250116333232979 1250000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250116333232979/1250000000000000 : ℝ)) (X := (50019729636342568051/50000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015066385095818773/25000000000000000000 : ℝ) ≤ (5000710678348837/5000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (25015066385095818773/25000000000000000000 : ℝ)^1024 ≤ (5000710678348837/5000000000000000 : ℝ)^4341 := by
      have hnat : (25015066385095818773 : ℕ)^1024*5000000000000000^4341 ≤ 5000710678348837^4341*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015066385095818773 25000000000000000000 5000710678348837 5000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000710678348837/5000000000000000 : ℝ)) (X := (25015066385095818773/25000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2331625623374639/25000000000000000000 : ℝ) ≤ ((2974214772784639011/2975000000000000000 : ℝ)+2*(245345416921/178500000000000 : ℝ)*(5601/50000 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (2974214772784639011/2975000000000000000 : ℝ)+2*(245345416921/178500000000000 : ℝ)*(5601/50000 : ℝ)=(1000043997502999/1000000000000000 : ℝ) by norm_num, show 1+2*(2331625623374639/25000000000000000000 : ℝ)=(12502331625623374639/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15066385095818773/50000000000000000000 : ℝ)+(2331625623374639/25000000000000000000 : ℝ) ≤ ((2974214772784639011/2975000000000000000 : ℝ)+(245345416921/178500000000000 : ℝ)*((3693/25000 : ℝ)+(5601/50000 : ℝ)))^(4341/1024 : ℝ) := by
    rw [show (2974214772784639011/2975000000000000000 : ℝ)+(245345416921/178500000000000 : ℝ)*((3693/25000 : ℝ)+(5601/50000 : ℝ))=(1250116333232979/1250000000000000 : ℝ) by norm_num, show 1+(15066385095818773/50000000000000000000 : ℝ)+(2331625623374639/25000000000000000000 : ℝ)=(50019729636342568051/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15066385095818773/50000000000000000000 : ℝ) ≤ ((2974214772784639011/2975000000000000000 : ℝ)+2*(245345416921/178500000000000 : ℝ)*(3693/25000 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (2974214772784639011/2975000000000000000 : ℝ)+2*(245345416921/178500000000000 : ℝ)*(3693/25000 : ℝ)=(5000710678348837/5000000000000000 : ℝ) by norm_num, show 1+2*(15066385095818773/50000000000000000000 : ℝ)=(25015066385095818773/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2974214772784639011/2975000000000000000 : ℝ)*(X 1 0+X 2 0)+(245345416921/178500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (5601/50000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (2974214772784639011/2975000000000000000 : ℝ)) (alpha := (245345416921/178500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2974214772784639011/2975000000000000000 : ℝ)*(X 0 1+X 2 1)+(245345416921/178500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (5601/50000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (2974214772784639011/2975000000000000000 : ℝ)) (alpha := (245345416921/178500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2974214772784639011/2975000000000000000 : ℝ)*(X 0 2+X 1 2)+(245345416921/178500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (5601/50000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (2974214772784639011/2975000000000000000 : ℝ)) (alpha := (245345416921/178500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2009879267/10000000000 : ℝ)*X 0 0+(2705458673/5000000000 : ℝ)*X 0 1+(5245503561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348342013/10000000000 : ℝ)*X 1 0+(-523533249/2500000000 : ℝ)*X 1 1+(209820143/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668542751/1250000000 : ℝ)*X 2 0+(2622751787/5000000000 : ℝ)*X 2 1+(-418826601/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158124491/5000000000 : ℝ)*X 0 0+(103592289/250000000 : ℝ)*X 0 1+(224769203/500000000 : ℝ)*X 0 2+(2158124491/5000000000 : ℝ)*X 1 0+(103592289/250000000 : ℝ)*X 1 1+(224769203/500000000 : ℝ)*X 1 2+(2158124491/5000000000 : ℝ)*X 2 0+(103592289/250000000 : ℝ)*X 2 1+(224769203/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1004945649/5000000000 : ℝ)*X 0 0+(209843983/400000000 : ℝ)*X 0 1+(1352579533/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305545113/10000000000 : ℝ)*X 1 0+(-1929318361/10000000000 : ℝ)*X 1 1+(5410318431/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326386243/2500000000 : ℝ)*X 2 0+(5410318323/10000000000 : ℝ)*X 2 1+(-964659351/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((43162741/100000000 : ℝ)*X 0 0+(4494116961/10000000000 : ℝ)*X 0 1+(828993073/2000000000 : ℝ)*X 0 2+(43162741/100000000 : ℝ)*X 1 0+(4494116961/10000000000 : ℝ)*X 1 1+(828993073/2000000000 : ℝ)*X 1 2+(43162741/100000000 : ℝ)*X 2 0+(4494116961/10000000000 : ℝ)*X 2 1+(828993073/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (202380617744186833250514997/74375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101853217/20000000000000 : ℝ)*(base19) + (47702123/10000000000000 : ℝ)*(base23) + (7111459/50000000000000 : ℝ)*(lower2) + (36892603/50000000000000 : ℝ)*(upper3) + (2132523/5000000000000 : ℝ)*(upper5) + (2222217750593303/50000000000000 : ℝ)*(major0) + (2222217750593303/50000000000000 : ℝ)*(major1) + (2222217750593303/50000000000000 : ℝ)*(major2) + (6045456935093527/100000000000000 : ℝ)*(sp0) + (755683394196221/12500000000000 : ℝ)*(sp1) + (6045467185814623/100000000000000 : ℝ)*(sp2) + (2843397846058089/100000000000000 : ℝ)*(sp3) + (5363871163/50000000000000 : ℝ)*(sp4) + (5402776463/100000000000000 : ℝ)*(sp7) + (355425406104319/12500000000000 : ℝ)*(f.failure) + (6045467662835853/100000000000000 : ℝ)*(f.sum) + (41850037879201/8925000000000000000000000000 : ℝ)*base65 + (3348289632803170001/446250000000000000000000000000000 : ℝ)*base68 + (2740952949956920001/446250000000000000000000000000000 : ℝ)*base70 + (3947441888051920001/446250000000000000000000000000000 : ℝ)*base72 + (41182030770749/8925000000000000000000000000 : ℝ)*base74 + (11008946179703170001/446250000000000000000000000000000 : ℝ)*base76 + (2506286438051920001/446250000000000000000000000000000 : ℝ)*base78 + (7156244328015670001/446250000000000000000000000000000 : ℝ)*base80 + (21032269014187/4462500000000000000000000000 : ℝ)*base82 + (10605419/1250000000000000000000 : ℝ)*base89 + (10605419/1250000000000000000000 : ℝ)*base91 + (10605419/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1305266418375322530449/212500000000000000000000000 : ℝ) := by norm_num
    linear_combination (128960249/25000000000000 : ℝ)*(base19) + (467749791/100000000000000 : ℝ)*(base23) + (95081573/100000000000000 : ℝ)*(upper2) + (185193443/100000000000000 : ℝ)*(upper3) + (7814679/6250000000000 : ℝ)*(upper5) + (4476762152619659/100000000000000 : ℝ)*(major0) + (4476762152619659/100000000000000 : ℝ)*(major1) + (4476762152619659/100000000000000 : ℝ)*(major2) + (14175626461/100000000000000 : ℝ)*(sp1) + (1514812609/25000000000000 : ℝ)*(sp2) + (6089439326256583/100000000000000 : ℝ)*(sp4) + (761178079348641/12500000000000 : ℝ)*(sp5) + (1522358199814089/25000000000000 : ℝ)*(sp6) + (1432042387117527/50000000000000 : ℝ)*(sp7) + (1432042387117527/50000000000000 : ℝ)*(f.failure) + (6089439326256583/100000000000000 : ℝ)*(f.sum) + (1972374265127/1275000000000000000000000000 : ℝ)*base65 + (1492659583759971179/127500000000000000000000000000000 : ℝ)*base68 + (799386936497528821/127500000000000000000000000000000 : ℝ)*base69 + (974351140354971179/127500000000000000000000000000000 : ℝ)*base72 + (4673407511473/1275000000000000000000000000 : ℝ)*base74 + (1414988857594971179/127500000000000000000000000000000 : ℝ)*base76 + (433348301612528821/127500000000000000000000000000000 : ℝ)*base77 + (416931245297528821/127500000000000000000000000000000 : ℝ)*base79 + (3907686626327/1275000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base85 + (18153827/5000000000000000000000 : ℝ)*base89 + (18153827/5000000000000000000000 : ℝ)*base91 + (18153827/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1382_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1382_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1382_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7977/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5051/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1382_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1382_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1382_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7977/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5051/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1382_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

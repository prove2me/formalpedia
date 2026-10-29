-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1364_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:18:47.776579+00:00
-- url     : https://prove2.me/submissions/825dd0e6-cf64-4049-af7c-2f797de29908

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
theorem support_rectangle_w1364_s6_0 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2025112801/10000000000 : ℝ)*x 0 + (5411585191/10000000000 : ℝ)*x 1 + (5245248403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025112801/10000000000 : ℝ)^1081 ≤ (12337816589563/100000000000000 : ℝ)^825 := by
    have hnat : (2025112801 : ℕ)^1081*100000000000000^825 ≤ 12337816589563^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025112801 10000000000 12337816589563 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411585191/10000000000 : ℝ)^1081 ≤ (44727464921529/100000000000000 : ℝ)^825 := by
    have hnat : (5411585191 : ℕ)^1081*100000000000000^825 ≤ 44727464921529^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411585191 10000000000 44727464921529 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245248403/10000000000 : ℝ)^1081 ≤ (8586943693981/20000000000000 : ℝ)^825 := by
    have hnat : (5245248403 : ℕ)^1081*20000000000000^825 ≤ 8586943693981^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245248403 10000000000 8586943693981 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2025112801/10000000000 : ℝ), (5411585191/10000000000 : ℝ), (5245248403/10000000000 : ℝ)] ![(12337816589563/100000000000000 : ℝ), (44727464921529/100000000000000 : ℝ), (8586943693981/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2025112801/10000000000 : ℝ)|^1081 ≤ (12337816589563/100000000000000 : ℝ)^825
        have hw : |(-2025112801/10000000000 : ℝ)|=(2025112801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411585191/10000000000 : ℝ)|^1081 ≤ (44727464921529/100000000000000 : ℝ)^825
        have hw : |(5411585191/10000000000 : ℝ)|=(5411585191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245248403/10000000000 : ℝ)|^1081 ≤ (8586943693981/20000000000000 : ℝ)^825
        have hw : |(5245248403/10000000000 : ℝ)|=(5245248403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s6_1 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348611031/10000000000 : ℝ)*x 0 + (-2109845689/10000000000 : ℝ)*x 1 + (327828029/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348611031/10000000000 : ℝ)^1081 ≤ (44046700296883/100000000000000 : ℝ)^825 := by
    have hnat : (5348611031 : ℕ)^1081*100000000000000^825 ≤ 44046700296883^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348611031 10000000000 44046700296883 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109845689/10000000000 : ℝ)^1081 ≤ (13018580565183/100000000000000 : ℝ)^825 := by
    have hnat : (2109845689 : ℕ)^1081*100000000000000^825 ≤ 13018580565183^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109845689 10000000000 13018580565183 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327828029/625000000 : ℝ)^1081 ≤ (8586943824831/20000000000000 : ℝ)^825 := by
    have hnat : (327828029 : ℕ)^1081*20000000000000^825 ≤ 8586943824831^825*625000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327828029 625000000 8586943824831 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348611031/10000000000 : ℝ), (-2109845689/10000000000 : ℝ), (327828029/625000000 : ℝ)] ![(44046700296883/100000000000000 : ℝ), (13018580565183/100000000000000 : ℝ), (8586943824831/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348611031/10000000000 : ℝ)|^1081 ≤ (44046700296883/100000000000000 : ℝ)^825
        have hw : |(5348611031/10000000000 : ℝ)|=(5348611031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109845689/10000000000 : ℝ)|^1081 ≤ (13018580565183/100000000000000 : ℝ)^825
        have hw : |(-2109845689/10000000000 : ℝ)|=(2109845689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327828029/625000000 : ℝ)|^1081 ≤ (8586943824831/20000000000000 : ℝ)^825
        have hw : |(327828029/625000000 : ℝ)|=(327828029/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s6_2 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674305629/5000000000 : ℝ)*x 0 + (5245248403/10000000000 : ℝ)*x 1 + (-2109845467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674305629/5000000000 : ℝ)^1081 ≤ (2202335137317/5000000000000 : ℝ)^825 := by
    have hnat : (2674305629 : ℕ)^1081*5000000000000^825 ≤ 2202335137317^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674305629 5000000000 2202335137317 5000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245248403/10000000000 : ℝ)^1081 ≤ (8586943693981/20000000000000 : ℝ)^825 := by
    have hnat : (5245248403 : ℕ)^1081*20000000000000^825 ≤ 8586943693981^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245248403 10000000000 8586943693981 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109845467/10000000000 : ℝ)^1081 ≤ (6509289385147/50000000000000 : ℝ)^825 := by
    have hnat : (2109845467 : ℕ)^1081*50000000000000^825 ≤ 6509289385147^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109845467 10000000000 6509289385147 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674305629/5000000000 : ℝ), (5245248403/10000000000 : ℝ), (-2109845467/10000000000 : ℝ)] ![(2202335137317/5000000000000 : ℝ), (8586943693981/20000000000000 : ℝ), (6509289385147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674305629/5000000000 : ℝ)|^1081 ≤ (2202335137317/5000000000000 : ℝ)^825
        have hw : |(2674305629/5000000000 : ℝ)|=(2674305629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245248403/10000000000 : ℝ)|^1081 ≤ (8586943693981/20000000000000 : ℝ)^825
        have hw : |(5245248403/10000000000 : ℝ)|=(5245248403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2109845467/10000000000 : ℝ)|^1081 ≤ (6509289385147/50000000000000 : ℝ)^825
        have hw : |(-2109845467/10000000000 : ℝ)|=(2109845467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s6_3 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (108022451/250000000 : ℝ)*x 0 + (4148557109/10000000000 : ℝ)*x 1 + (2249923893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108022451/250000000 : ℝ)^1081 ≤ (3330362686071/10000000000000 : ℝ)^825 := by
    have hnat : (108022451 : ℕ)^1081*10000000000000^825 ≤ 3330362686071^825*250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108022451 250000000 3330362686071 10000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4148557109/10000000000 : ℝ)^1081 ≤ (31573983437321/100000000000000 : ℝ)^825 := by
    have hnat : (4148557109 : ℕ)^1081*100000000000000^825 ≤ 31573983437321^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148557109 10000000000 31573983437321 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249923893/5000000000 : ℝ)^1081 ≤ (1404895587193/4000000000000 : ℝ)^825 := by
    have hnat : (2249923893 : ℕ)^1081*4000000000000^825 ≤ 1404895587193^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249923893 5000000000 1404895587193 4000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108022451/250000000 : ℝ), (4148557109/10000000000 : ℝ), (2249923893/5000000000 : ℝ)] ![(3330362686071/10000000000000 : ℝ), (31573983437321/100000000000000 : ℝ), (1404895587193/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108022451/250000000 : ℝ)|^1081 ≤ (3330362686071/10000000000000 : ℝ)^825
        have hw : |(108022451/250000000 : ℝ)|=(108022451/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4148557109/10000000000 : ℝ)|^1081 ≤ (31573983437321/100000000000000 : ℝ)^825
        have hw : |(4148557109/10000000000 : ℝ)|=(4148557109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249923893/5000000000 : ℝ)|^1081 ≤ (1404895587193/4000000000000 : ℝ)^825
        have hw : |(2249923893/5000000000 : ℝ)|=(2249923893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s6_4 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2025124619/10000000000 : ℝ)*x 0 + (327865317/625000000 : ℝ)*x 1 + (5410985543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025124619/10000000000 : ℝ)^1081 ≤ (12337910931593/100000000000000 : ℝ)^825 := by
    have hnat : (2025124619 : ℕ)^1081*100000000000000^825 ≤ 12337910931593^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025124619 10000000000 12337910931593 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327865317/625000000 : ℝ)^1081 ≤ (42941118108427/100000000000000 : ℝ)^825 := by
    have hnat : (327865317 : ℕ)^1081*100000000000000^825 ≤ 42941118108427^825*625000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327865317 625000000 42941118108427 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410985543/10000000000 : ℝ)^1081 ≤ (44720970948921/100000000000000 : ℝ)^825 := by
    have hnat : (5410985543 : ℕ)^1081*100000000000000^825 ≤ 44720970948921^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410985543 10000000000 44720970948921 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2025124619/10000000000 : ℝ), (327865317/625000000 : ℝ), (5410985543/10000000000 : ℝ)] ![(12337910931593/100000000000000 : ℝ), (42941118108427/100000000000000 : ℝ), (44720970948921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2025124619/10000000000 : ℝ)|^1081 ≤ (12337910931593/100000000000000 : ℝ)^825
        have hw : |(-2025124619/10000000000 : ℝ)|=(2025124619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327865317/625000000 : ℝ)|^1081 ≤ (42941118108427/100000000000000 : ℝ)^825
        have hw : |(327865317/625000000 : ℝ)|=(327865317/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410985543/10000000000 : ℝ)|^1081 ≤ (44720970948921/100000000000000 : ℝ)^825
        have hw : |(5410985543/10000000000 : ℝ)|=(5410985543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s6_5 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530565989/1000000000 : ℝ)*x 0 + (-1944108421/10000000000 : ℝ)*x 1 + (2705492773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530565989/1000000000 : ℝ)^1081 ≤ (21791905905613/50000000000000 : ℝ)^825 := by
    have hnat : (530565989 : ℕ)^1081*50000000000000^825 ≤ 21791905905613^825*1000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530565989 1000000000 21791905905613 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1944108421/10000000000 : ℝ)^1081 ≤ (11695217190089/100000000000000 : ℝ)^825 := by
    have hnat : (1944108421 : ℕ)^1081*100000000000000^825 ≤ 11695217190089^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944108421 10000000000 11695217190089 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705492773/5000000000 : ℝ)^1081 ≤ (44720970981409/100000000000000 : ℝ)^825 := by
    have hnat : (2705492773 : ℕ)^1081*100000000000000^825 ≤ 44720970981409^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705492773 5000000000 44720970981409 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530565989/1000000000 : ℝ), (-1944108421/10000000000 : ℝ), (2705492773/5000000000 : ℝ)] ![(21791905905613/50000000000000 : ℝ), (11695217190089/100000000000000 : ℝ), (44720970981409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530565989/1000000000 : ℝ)|^1081 ≤ (21791905905613/50000000000000 : ℝ)^825
        have hw : |(530565989/1000000000 : ℝ)|=(530565989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1944108421/10000000000 : ℝ)|^1081 ≤ (11695217190089/100000000000000 : ℝ)^825
        have hw : |(-1944108421/10000000000 : ℝ)|=(1944108421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705492773/5000000000 : ℝ)|^1081 ≤ (44720970981409/100000000000000 : ℝ)^825
        have hw : |(2705492773/5000000000 : ℝ)|=(2705492773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s6_6 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652829949/5000000000 : ℝ)*x 0 + (84546649/156250000 : ℝ)*x 1 + (-243013553/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652829949/5000000000 : ℝ)^1081 ≤ (8716762379467/20000000000000 : ℝ)^825 := by
    have hnat : (2652829949 : ℕ)^1081*20000000000000^825 ≤ 8716762379467^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652829949 5000000000 8716762379467 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84546649/156250000 : ℝ)^1081 ≤ (8944194174623/20000000000000 : ℝ)^825 := by
    have hnat : (84546649 : ℕ)^1081*20000000000000^825 ≤ 8944194174623^825*156250000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84546649 156250000 8944194174623 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (243013553/1250000000 : ℝ)^1081 ≤ (1461902151717/12500000000000 : ℝ)^825 := by
    have hnat : (243013553 : ℕ)^1081*12500000000000^825 ≤ 1461902151717^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243013553 1250000000 1461902151717 12500000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652829949/5000000000 : ℝ), (84546649/156250000 : ℝ), (-243013553/1250000000 : ℝ)] ![(8716762379467/20000000000000 : ℝ), (8944194174623/20000000000000 : ℝ), (1461902151717/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652829949/5000000000 : ℝ)|^1081 ≤ (8716762379467/20000000000000 : ℝ)^825
        have hw : |(2652829949/5000000000 : ℝ)|=(2652829949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84546649/156250000 : ℝ)|^1081 ≤ (8944194174623/20000000000000 : ℝ)^825
        have hw : |(84546649/156250000 : ℝ)|=(84546649/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-243013553/1250000000 : ℝ)|^1081 ≤ (1461902151717/12500000000000 : ℝ)^825
        have hw : |(-243013553/1250000000 : ℝ)|=(243013553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s6_7 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1080230889/2500000000 : ℝ)*x 0 + (4498587531/10000000000 : ℝ)*x 1 + (4149823599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080230889/2500000000 : ℝ)^1081 ≤ (3330388455349/10000000000000 : ℝ)^825 := by
    have hnat : (1080230889 : ℕ)^1081*10000000000000^825 ≤ 3330388455349^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080230889 2500000000 3330388455349 10000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498587531/10000000000 : ℝ)^1081 ≤ (8777375330869/25000000000000 : ℝ)^825 := by
    have hnat : (4498587531 : ℕ)^1081*25000000000000^825 ≤ 8777375330869^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498587531 10000000000 8777375330869 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4149823599/10000000000 : ℝ)^1081 ≤ (7896653526789/25000000000000 : ℝ)^825 := by
    have hnat : (4149823599 : ℕ)^1081*25000000000000^825 ≤ 7896653526789^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149823599 10000000000 7896653526789 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080230889/2500000000 : ℝ), (4498587531/10000000000 : ℝ), (4149823599/10000000000 : ℝ)] ![(3330388455349/10000000000000 : ℝ), (8777375330869/25000000000000 : ℝ), (7896653526789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080230889/2500000000 : ℝ)|^1081 ≤ (3330388455349/10000000000000 : ℝ)^825
        have hw : |(1080230889/2500000000 : ℝ)|=(1080230889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498587531/10000000000 : ℝ)|^1081 ≤ (8777375330869/25000000000000 : ℝ)^825
        have hw : |(4498587531/10000000000 : ℝ)|=(4498587531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4149823599/10000000000 : ℝ)|^1081 ≤ (7896653526789/25000000000000 : ℝ)^825
        have hw : |(4149823599/10000000000 : ℝ)|=(4149823599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1364_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11193/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11199/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14721/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1841/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11193/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1841/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11193/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1841/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11193/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1841/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11193/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1841/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11193/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1841/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11193/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11193/100000 : ℝ) ^ (4323/1024 : ℝ) ≤ (9659547294601573/100000000000000000000 : ℝ) := by
    have hpowers : (11193/100000 : ℝ)^4323 ≤ (9659547294601573/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11193 : ℕ)^4323*100000000000000000000^1024 ≤ 9659547294601573^1024*100000^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11193 100000 9659547294601573 100000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11193/100000 : ℝ)) (X := (9659547294601573/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1841/12500 : ℝ) ^ (4323/1024 : ℝ) ≤ (15386487148376479/50000000000000000000 : ℝ) := by
    have hpowers : (1841/12500 : ℝ)^4323 ≤ (15386487148376479/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1841 : ℕ)^4323*50000000000000000000^1024 ≤ 15386487148376479^1024*12500^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1841 12500 15386487148376479 50000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1841/12500 : ℝ)) (X := (15386487148376479/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009659547294601573/50000000000000000000 : ℝ) ≤ (5000228791287833/5000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (50009659547294601573/50000000000000000000 : ℝ)^1024 ≤ (5000228791287833/5000000000000000 : ℝ)^4323 := by
      have hnat : (50009659547294601573 : ℕ)^1024*5000000000000000^4323 ≤ 5000228791287833^4323*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009659547294601573 50000000000000000000 5000228791287833 5000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000228791287833/5000000000000000 : ℝ)) (X := (50009659547294601573/50000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040432521591354531/100000000000000000000 : ℝ) ≤ (10000957587697423/10000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (100040432521591354531/100000000000000000000 : ℝ)^1024 ≤ (10000957587697423/10000000000000000 : ℝ)^4323 := by
      have hnat : (100040432521591354531 : ℕ)^1024*10000000000000000^4323 ≤ 10000957587697423^4323*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040432521591354531 100000000000000000000 10000957587697423 10000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000957587697423/10000000000000000 : ℝ)) (X := (100040432521591354531/100000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015386487148376479/25000000000000000000 : ℝ) ≤ (500072879640959/500000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (25015386487148376479/25000000000000000000 : ℝ)^1024 ≤ (500072879640959/500000000000000 : ℝ)^4323 := by
      have hnat : (25015386487148376479 : ℕ)^1024*500000000000000^4323 ≤ 500072879640959^4323*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015386487148376479 25000000000000000000 500072879640959 500000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500072879640959/500000000000000 : ℝ)) (X := (25015386487148376479/25000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9659547294601573/100000000000000000000 : ℝ) ≤ ((1262158015705333111/1262500000000000000 : ℝ)+2*(500005121757/353500000000000 : ℝ)*(11193/100000 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (1262158015705333111/1262500000000000000 : ℝ)+2*(500005121757/353500000000000 : ℝ)*(11193/100000 : ℝ)=(5000228791287833/5000000000000000 : ℝ) by norm_num, show 1+2*(9659547294601573/100000000000000000000 : ℝ)=(50009659547294601573/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15386487148376479/50000000000000000000 : ℝ)+(9659547294601573/100000000000000000000 : ℝ) ≤ ((1262158015705333111/1262500000000000000 : ℝ)+(500005121757/353500000000000 : ℝ)*((1841/12500 : ℝ)+(11193/100000 : ℝ)))^(4323/1024 : ℝ) := by
    rw [show (1262158015705333111/1262500000000000000 : ℝ)+(500005121757/353500000000000 : ℝ)*((1841/12500 : ℝ)+(11193/100000 : ℝ))=(10000957587697423/10000000000000000 : ℝ) by norm_num, show 1+(15386487148376479/50000000000000000000 : ℝ)+(9659547294601573/100000000000000000000 : ℝ)=(100040432521591354531/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15386487148376479/50000000000000000000 : ℝ) ≤ ((1262158015705333111/1262500000000000000 : ℝ)+2*(500005121757/353500000000000 : ℝ)*(1841/12500 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (1262158015705333111/1262500000000000000 : ℝ)+2*(500005121757/353500000000000 : ℝ)*(1841/12500 : ℝ)=(500072879640959/500000000000000 : ℝ) by norm_num, show 1+2*(15386487148376479/50000000000000000000 : ℝ)=(25015386487148376479/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1262158015705333111/1262500000000000000 : ℝ)*(X 1 0+X 2 0)+(500005121757/353500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (11193/100000 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (1262158015705333111/1262500000000000000 : ℝ)) (alpha := (500005121757/353500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1262158015705333111/1262500000000000000 : ℝ)*(X 0 1+X 2 1)+(500005121757/353500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (11193/100000 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (1262158015705333111/1262500000000000000 : ℝ)) (alpha := (500005121757/353500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1262158015705333111/1262500000000000000 : ℝ)*(X 0 2+X 1 2)+(500005121757/353500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (11193/100000 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (1262158015705333111/1262500000000000000 : ℝ)) (alpha := (500005121757/353500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2025112801/10000000000 : ℝ)*X 0 0+(5411585191/10000000000 : ℝ)*X 0 1+(5245248403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348611031/10000000000 : ℝ)*X 1 0+(-2109845689/10000000000 : ℝ)*X 1 1+(327828029/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674305629/5000000000 : ℝ)*X 2 0+(5245248403/10000000000 : ℝ)*X 2 1+(-2109845467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((108022451/250000000 : ℝ)*X 0 0+(4148557109/10000000000 : ℝ)*X 0 1+(2249923893/5000000000 : ℝ)*X 0 2+(108022451/250000000 : ℝ)*X 1 0+(4148557109/10000000000 : ℝ)*X 1 1+(2249923893/5000000000 : ℝ)*X 1 2+(108022451/250000000 : ℝ)*X 2 0+(4148557109/10000000000 : ℝ)*X 2 1+(2249923893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2025124619/10000000000 : ℝ)*X 0 0+(327865317/625000000 : ℝ)*X 0 1+(5410985543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530565989/1000000000 : ℝ)*X 1 0+(-1944108421/10000000000 : ℝ)*X 1 1+(2705492773/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652829949/5000000000 : ℝ)*X 2 0+(84546649/156250000 : ℝ)*X 2 1+(-243013553/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080230889/2500000000 : ℝ)*X 0 0+(4498587531/10000000000 : ℝ)*X 0 1+(4149823599/10000000000 : ℝ)*X 0 2+(1080230889/2500000000 : ℝ)*X 1 0+(4498587531/10000000000 : ℝ)*X 1 1+(4149823599/10000000000 : ℝ)*X 1 2+(1080230889/2500000000 : ℝ)*X 2 0+(4498587531/10000000000 : ℝ)*X 2 1+(4149823599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (296899276620205309036971633/27617187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (228789577/12500000000000 : ℝ)*(base19) + (1925149003/100000000000000 : ℝ)*(base23) + (23912589/20000000000000 : ℝ)*(upper3) + (42874897/50000000000000 : ℝ)*(upper4) + (162113259/50000000000000 : ℝ)*(upper5) + (276833400449909/6250000000000 : ℝ)*(major0) + (276833400449909/6250000000000 : ℝ)*(major1) + (276833400449909/6250000000000 : ℝ)*(major2) + (150298363792153/2500000000000 : ℝ)*(sp0) + (3005990114570567/50000000000000 : ℝ)*(sp1) + (6011980134308747/100000000000000 : ℝ)*(sp2) + (284666657017831/10000000000000 : ℝ)*(sp3) + (47507771631/100000000000000 : ℝ)*(sp4) + (4956602543/25000000000000 : ℝ)*(sp7) + (1423343198294241/50000000000000 : ℝ)*(f.failure) + (24047928237831/400000000000 : ℝ)*(f.sum) + (15010199262783/17675000000000000000000000000 : ℝ)*base65 + (877000813875810457/55234375000000000000000000000000 : ℝ)*base68 + (292137465974975541/27617187500000000000000000000000 : ℝ)*base70 + (34825767265185457/55234375000000000000000000000000 : ℝ)*base72 + (5650468318123/4418750000000000000000000000 : ℝ)*base74 + (240657531667216707/55234375000000000000000000000000 : ℝ)*base76 + (4731734890752043/55234375000000000000000000000000 : ℝ)*base77 + (161101327712239979/6904296875000000000000000000000 : ℝ)*base80 + (26228271457517/17675000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (68477909/5000000000000000000000 : ℝ)*base89 + (68477909/5000000000000000000000 : ℝ)*base91 + (68477909/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (166380544244124204045026151/31562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (907846827/100000000000000 : ℝ)*(base19) + (994097841/100000000000000 : ℝ)*(base23) + (103983761/100000000000000 : ℝ)*(upper3) + (4489601/12500000000000 : ℝ)*(lower4) + (110864897/100000000000000 : ℝ)*(upper5) + (2230679798852547/50000000000000 : ℝ)*(major0) + (2230679798852547/50000000000000 : ℝ)*(major1) + (2230679798852547/50000000000000 : ℝ)*(major2) + (4743131291/25000000000000 : ℝ)*(sp1) + (10068347771/50000000000000 : ℝ)*(sp2) + (6055450371737991/100000000000000 : ℝ)*(sp4) + (3027715245683/50000000000 : ℝ)*(sp5) + (189232163779519/3125000000000 : ℝ)*(sp6) + (573453729591353/20000000000000 : ℝ)*(sp7) + (573453729591353/20000000000000 : ℝ)*(f.failure) + (6055450371737991/100000000000000 : ℝ)*(f.sum) + (6722441656681/2525000000000000000000000000 : ℝ)*base66 + (303396551228666283/63125000000000000000000000000000 : ℝ)*base68 + (170110246154291283/63125000000000000000000000000000 : ℝ)*base70 + (691328262826791283/63125000000000000000000000000000 : ℝ)*base72 + (1389784140619/2525000000000000000000000000 : ℝ)*base73 + (247567679918833717/63125000000000000000000000000000 : ℝ)*base75 + (220239805088208717/63125000000000000000000000000000 : ℝ)*base77 + (181904848204916283/63125000000000000000000000000000 : ℝ)*base80 + (4157939087131/2525000000000000000000000000 : ℝ)*base82 + (9500403/2000000000000000000000 : ℝ)*base90 + (9500403/2000000000000000000000 : ℝ)*base92 + (9500403/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1364_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11193/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11199/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1364_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1364_s7_0 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2025120241/10000000000 : ℝ)*x 0 + (2705766047/5000000000 : ℝ)*x 1 + (32783103/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025120241/10000000000 : ℝ)^1081 ≤ (12337875982393/100000000000000 : ℝ)^825 := by
    have hnat : (2025120241 : ℕ)^1081*100000000000000^825 ≤ 12337875982393^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025120241 10000000000 12337875982393 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705766047/5000000000 : ℝ)^1081 ≤ (22363444945533/50000000000000 : ℝ)^825 := by
    have hnat : (2705766047 : ℕ)^1081*50000000000000^825 ≤ 22363444945533^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705766047 5000000000 22363444945533 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32783103/62500000 : ℝ)^1081 ≤ (42935234116651/100000000000000 : ℝ)^825 := by
    have hnat : (32783103 : ℕ)^1081*100000000000000^825 ≤ 42935234116651^825*62500000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32783103 62500000 42935234116651 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2025120241/10000000000 : ℝ), (2705766047/5000000000 : ℝ), (32783103/62500000 : ℝ)] ![(12337875982393/100000000000000 : ℝ), (22363444945533/50000000000000 : ℝ), (42935234116651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2025120241/10000000000 : ℝ)|^1081 ≤ (12337875982393/100000000000000 : ℝ)^825
        have hw : |(-2025120241/10000000000 : ℝ)|=(2025120241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705766047/5000000000 : ℝ)|^1081 ≤ (22363444945533/50000000000000 : ℝ)^825
        have hw : |(2705766047/5000000000 : ℝ)|=(2705766047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32783103/62500000 : ℝ)|^1081 ≤ (42935234116651/100000000000000 : ℝ)^825
        have hw : |(32783103/62500000 : ℝ)|=(32783103/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s7_1 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674298547/5000000000 : ℝ)*x 0 + (-527450149/2500000000 : ℝ)*x 1 + (5245296477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674298547/5000000000 : ℝ)^1081 ≤ (8809309981773/20000000000000 : ℝ)^825 := by
    have hnat : (2674298547 : ℕ)^1081*20000000000000^825 ≤ 8809309981773^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674298547 5000000000 8809309981773 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527450149/2500000000 : ℝ)^1081 ≤ (3254553996393/25000000000000 : ℝ)^825 := by
    have hnat : (527450149 : ℕ)^1081*25000000000000^825 ≤ 3254553996393^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527450149 2500000000 3254553996393 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245296477/10000000000 : ℝ)^1081 ≤ (1717409363379/4000000000000 : ℝ)^825 := by
    have hnat : (5245296477 : ℕ)^1081*4000000000000^825 ≤ 1717409363379^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245296477 10000000000 1717409363379 4000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674298547/5000000000 : ℝ), (-527450149/2500000000 : ℝ), (5245296477/10000000000 : ℝ)] ![(8809309981773/20000000000000 : ℝ), (3254553996393/25000000000000 : ℝ), (1717409363379/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674298547/5000000000 : ℝ)|^1081 ≤ (8809309981773/20000000000000 : ℝ)^825
        have hw : |(2674298547/5000000000 : ℝ)|=(2674298547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-527450149/2500000000 : ℝ)|^1081 ≤ (3254553996393/25000000000000 : ℝ)^825
        have hw : |(-527450149/2500000000 : ℝ)|=(527450149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245296477/10000000000 : ℝ)|^1081 ≤ (1717409363379/4000000000000 : ℝ)^825
        have hw : |(5245296477/10000000000 : ℝ)|=(5245296477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s7_2 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1069719419/2000000000 : ℝ)*x 0 + (5245296477/10000000000 : ℝ)*x 1 + (-421960119/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069719419/2000000000 : ℝ)^1081 ≤ (5505818739957/12500000000000 : ℝ)^825 := by
    have hnat : (1069719419 : ℕ)^1081*12500000000000^825 ≤ 5505818739957^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069719419 2000000000 5505818739957 12500000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245296477/10000000000 : ℝ)^1081 ≤ (1717409363379/4000000000000 : ℝ)^825 := by
    have hnat : (5245296477 : ℕ)^1081*4000000000000^825 ≤ 1717409363379^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245296477 10000000000 1717409363379 4000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421960119/2000000000 : ℝ)^1081 ≤ (13018215977487/100000000000000 : ℝ)^825 := by
    have hnat : (421960119 : ℕ)^1081*100000000000000^825 ≤ 13018215977487^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421960119 2000000000 13018215977487 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069719419/2000000000 : ℝ), (5245296477/10000000000 : ℝ), (-421960119/2000000000 : ℝ)] ![(5505818739957/12500000000000 : ℝ), (1717409363379/4000000000000 : ℝ), (13018215977487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069719419/2000000000 : ℝ)|^1081 ≤ (5505818739957/12500000000000 : ℝ)^825
        have hw : |(1069719419/2000000000 : ℝ)|=(1069719419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245296477/10000000000 : ℝ)|^1081 ≤ (1717409363379/4000000000000 : ℝ)^825
        have hw : |(5245296477/10000000000 : ℝ)|=(5245296477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-421960119/2000000000 : ℝ)|^1081 ≤ (13018215977487/100000000000000 : ℝ)^825
        have hw : |(-421960119/2000000000 : ℝ)|=(421960119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s7_3 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (540112737/1250000000 : ℝ)*x 0 + (1037165863/2500000000 : ℝ)*x 1 + (4499740283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540112737/1250000000 : ℝ)^1081 ≤ (6660733160687/20000000000000 : ℝ)^825 := by
    have hnat : (540112737 : ℕ)^1081*20000000000000^825 ≤ 6660733160687^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540112737 1250000000 6660733160687 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037165863/2500000000 : ℝ)^1081 ≤ (31575043947117/100000000000000 : ℝ)^825 := by
    have hnat : (1037165863 : ℕ)^1081*100000000000000^825 ≤ 31575043947117^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037165863 2500000000 31575043947117 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499740283/10000000000 : ℝ)^1081 ≤ (7024258045221/20000000000000 : ℝ)^825 := by
    have hnat : (4499740283 : ℕ)^1081*20000000000000^825 ≤ 7024258045221^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499740283 10000000000 7024258045221 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540112737/1250000000 : ℝ), (1037165863/2500000000 : ℝ), (4499740283/10000000000 : ℝ)] ![(6660733160687/20000000000000 : ℝ), (31575043947117/100000000000000 : ℝ), (7024258045221/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540112737/1250000000 : ℝ)|^1081 ≤ (6660733160687/20000000000000 : ℝ)^825
        have hw : |(540112737/1250000000 : ℝ)|=(540112737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037165863/2500000000 : ℝ)|^1081 ≤ (31575043947117/100000000000000 : ℝ)^825
        have hw : |(1037165863/2500000000 : ℝ)|=(1037165863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499740283/10000000000 : ℝ)|^1081 ≤ (7024258045221/20000000000000 : ℝ)^825
        have hw : |(4499740283/10000000000 : ℝ)|=(4499740283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s7_4 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1012566121/5000000000 : ℝ)*x 0 + (655736541/1250000000 : ℝ)*x 1 + (8454583/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1012566121/5000000000 : ℝ)^1081 ≤ (6168985892703/50000000000000 : ℝ)^825 := by
    have hnat : (1012566121 : ℕ)^1081*50000000000000^825 ≤ 6168985892703^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012566121 5000000000 6168985892703 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655736541/1250000000 : ℝ)^1081 ≤ (42941624967469/100000000000000 : ℝ)^825 := by
    have hnat : (655736541 : ℕ)^1081*100000000000000^825 ≤ 42941624967469^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655736541 1250000000 42941624967469 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8454583/15625000 : ℝ)^1081 ≤ (22360201618631/50000000000000 : ℝ)^825 := by
    have hnat : (8454583 : ℕ)^1081*50000000000000^825 ≤ 22360201618631^825*15625000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8454583 15625000 22360201618631 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1012566121/5000000000 : ℝ), (655736541/1250000000 : ℝ), (8454583/15625000 : ℝ)] ![(6168985892703/50000000000000 : ℝ), (42941624967469/100000000000000 : ℝ), (22360201618631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1012566121/5000000000 : ℝ)|^1081 ≤ (6168985892703/50000000000000 : ℝ)^825
        have hw : |(-1012566121/5000000000 : ℝ)|=(1012566121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655736541/1250000000 : ℝ)|^1081 ≤ (42941624967469/100000000000000 : ℝ)^825
        have hw : |(655736541/1250000000 : ℝ)|=(655736541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8454583/15625000 : ℝ)|^1081 ≤ (22360201618631/50000000000000 : ℝ)^825
        have hw : |(8454583/15625000 : ℝ)|=(8454583/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s7_5 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305672059/10000000000 : ℝ)*x 0 + (-486040999/2500000000 : ℝ)*x 1 + (5410932999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305672059/10000000000 : ℝ)^1081 ≤ (43583942793521/100000000000000 : ℝ)^825 := by
    have hnat : (5305672059 : ℕ)^1081*100000000000000^825 ≤ 43583942793521^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305672059 10000000000 43583942793521 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486040999/2500000000 : ℝ)^1081 ≤ (11695655257507/100000000000000 : ℝ)^825 := by
    have hnat : (486040999 : ℕ)^1081*100000000000000^825 ≤ 11695655257507^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486040999 2500000000 11695655257507 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410932999/10000000000 : ℝ)^1081 ≤ (22360200963451/50000000000000 : ℝ)^825 := by
    have hnat : (5410932999 : ℕ)^1081*50000000000000^825 ≤ 22360200963451^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410932999 10000000000 22360200963451 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305672059/10000000000 : ℝ), (-486040999/2500000000 : ℝ), (5410932999/10000000000 : ℝ)] ![(43583942793521/100000000000000 : ℝ), (11695655257507/100000000000000 : ℝ), (22360200963451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305672059/10000000000 : ℝ)|^1081 ≤ (43583942793521/100000000000000 : ℝ)^825
        have hw : |(5305672059/10000000000 : ℝ)|=(5305672059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-486040999/2500000000 : ℝ)|^1081 ≤ (11695655257507/100000000000000 : ℝ)^825
        have hw : |(-486040999/2500000000 : ℝ)|=(486040999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410932999/10000000000 : ℝ)|^1081 ≤ (22360200963451/50000000000000 : ℝ)^825
        have hw : |(5410932999/10000000000 : ℝ)|=(5410932999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s7_6 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652835991/5000000000 : ℝ)*x 0 + (5410933117/10000000000 : ℝ)*x 1 + (-1944163941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652835991/5000000000 : ℝ)^1081 ≤ (43583941964723/100000000000000 : ℝ)^825 := by
    have hnat : (2652835991 : ℕ)^1081*100000000000000^825 ≤ 43583941964723^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652835991 5000000000 43583941964723 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410933117/10000000000 : ℝ)^1081 ≤ (44720403204773/100000000000000 : ℝ)^825 := by
    have hnat : (5410933117 : ℕ)^1081*100000000000000^825 ≤ 44720403204773^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410933117 10000000000 44720403204773 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1944163941/10000000000 : ℝ)^1081 ≤ (1169565482397/10000000000000 : ℝ)^825 := by
    have hnat : (1944163941 : ℕ)^1081*10000000000000^825 ≤ 1169565482397^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944163941 10000000000 1169565482397 10000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652835991/5000000000 : ℝ), (5410933117/10000000000 : ℝ), (-1944163941/10000000000 : ℝ)] ![(43583941964723/100000000000000 : ℝ), (44720403204773/100000000000000 : ℝ), (1169565482397/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652835991/5000000000 : ℝ)|^1081 ≤ (43583941964723/100000000000000 : ℝ)^825
        have hw : |(2652835991/5000000000 : ℝ)|=(2652835991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410933117/10000000000 : ℝ)|^1081 ≤ (44720403204773/100000000000000 : ℝ)^825
        have hw : |(5410933117/10000000000 : ℝ)|=(5410933117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1944163941/10000000000 : ℝ)|^1081 ≤ (1169565482397/10000000000000 : ℝ)^825
        have hw : |(-1944163941/10000000000 : ℝ)|=(1944163941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s7_7 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (270057941/625000000 : ℝ)*x 0 + (899696339/2000000000 : ℝ)*x 1 + (2074964287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270057941/625000000 : ℝ)^1081 ≤ (6660783980189/20000000000000 : ℝ)^825 := by
    have hnat : (270057941 : ℕ)^1081*20000000000000^825 ≤ 6660783980189^825*625000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270057941 625000000 6660783980189 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899696339/2000000000 : ℝ)^1081 ≤ (17554209506249/50000000000000 : ℝ)^825 := by
    have hnat : (899696339 : ℕ)^1081*50000000000000^825 ≤ 17554209506249^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899696339 2000000000 17554209506249 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074964287/5000000000 : ℝ)^1081 ≤ (31587661073623/100000000000000 : ℝ)^825 := by
    have hnat : (2074964287 : ℕ)^1081*100000000000000^825 ≤ 31587661073623^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074964287 5000000000 31587661073623 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270057941/625000000 : ℝ), (899696339/2000000000 : ℝ), (2074964287/5000000000 : ℝ)] ![(6660783980189/20000000000000 : ℝ), (17554209506249/50000000000000 : ℝ), (31587661073623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270057941/625000000 : ℝ)|^1081 ≤ (6660783980189/20000000000000 : ℝ)^825
        have hw : |(270057941/625000000 : ℝ)|=(270057941/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899696339/2000000000 : ℝ)|^1081 ≤ (17554209506249/50000000000000 : ℝ)^825
        have hw : |(899696339/2000000000 : ℝ)|=(899696339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2074964287/5000000000 : ℝ)|^1081 ≤ (31587661073623/100000000000000 : ℝ)^825
        have hw : |(2074964287/5000000000 : ℝ)|=(2074964287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1364_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11199/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (14/125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (92/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14721/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11199/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14721/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11199/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11199/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11199/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11199/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11199/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11199/100000 : ℝ) ^ (4323/1024 : ℝ) ≤ (9681426008764859/100000000000000000000 : ℝ) := by
    have hpowers : (11199/100000 : ℝ)^4323 ≤ (9681426008764859/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11199 : ℕ)^4323*100000000000000000000^1024 ≤ 9681426008764859^1024*100000^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11199 100000 9681426008764859 100000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11199/100000 : ℝ)) (X := (9681426008764859/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14721/100000 : ℝ) ^ (4323/1024 : ℝ) ≤ (6142255105305353/20000000000000000000 : ℝ) := by
    have hpowers : (14721/100000 : ℝ)^4323 ≤ (6142255105305353/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14721 : ℕ)^4323*20000000000000000000^1024 ≤ 6142255105305353^1024*100000^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14721 100000 6142255105305353 20000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14721/100000 : ℝ)) (X := (6142255105305353/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009681426008764859/50000000000000000000 : ℝ) ≤ (10000458618916039/10000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (50009681426008764859/50000000000000000000 : ℝ)^1024 ≤ (10000458618916039/10000000000000000 : ℝ)^4323 := by
      have hnat : (50009681426008764859 : ℕ)^1024*10000000000000000^4323 ≤ 10000458618916039^4323*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009681426008764859 50000000000000000000 10000458618916039 10000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000458618916039/10000000000000000 : ℝ)) (X := (50009681426008764859/50000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505049087691911453/12500000000000000000 : ℝ) ≤ (10000956644760419/10000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (12505049087691911453/12500000000000000000 : ℝ)^1024 ≤ (10000956644760419/10000000000000000 : ℝ)^4323 := by
      have hnat : (12505049087691911453 : ℕ)^1024*10000000000000000^4323 ≤ 10000956644760419^4323*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505049087691911453 12500000000000000000 10000956644760419 10000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000956644760419/10000000000000000 : ℝ)) (X := (12505049087691911453/12500000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006142255105305353/10000000000000000000 : ℝ) ≤ (10001454670604799/10000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (10006142255105305353/10000000000000000000 : ℝ)^1024 ≤ (10001454670604799/10000000000000000 : ℝ)^4323 := by
      have hnat : (10006142255105305353 : ℕ)^1024*10000000000000000^4323 ≤ 10001454670604799^4323*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006142255105305353 10000000000000000000 10001454670604799 10000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001454670604799/10000000000000000 : ℝ)) (X := (10006142255105305353/10000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9681426008764859/100000000000000000000 : ℝ) ≤ ((5868410078826644353/5870000000000000000 : ℝ)+2*(24901292219/17610000000000 : ℝ)*(11199/100000 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (5868410078826644353/5870000000000000000 : ℝ)+2*(24901292219/17610000000000 : ℝ)*(11199/100000 : ℝ)=(10000458618916039/10000000000000000 : ℝ) by norm_num, show 1+2*(9681426008764859/100000000000000000000 : ℝ)=(50009681426008764859/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6142255105305353/20000000000000000000 : ℝ)+(9681426008764859/100000000000000000000 : ℝ) ≤ ((5868410078826644353/5870000000000000000 : ℝ)+(24901292219/17610000000000 : ℝ)*((14721/100000 : ℝ)+(11199/100000 : ℝ)))^(4323/1024 : ℝ) := by
    rw [show (5868410078826644353/5870000000000000000 : ℝ)+(24901292219/17610000000000 : ℝ)*((14721/100000 : ℝ)+(11199/100000 : ℝ))=(10000956644760419/10000000000000000 : ℝ) by norm_num, show 1+(6142255105305353/20000000000000000000 : ℝ)+(9681426008764859/100000000000000000000 : ℝ)=(12505049087691911453/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6142255105305353/20000000000000000000 : ℝ) ≤ ((5868410078826644353/5870000000000000000 : ℝ)+2*(24901292219/17610000000000 : ℝ)*(14721/100000 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (5868410078826644353/5870000000000000000 : ℝ)+2*(24901292219/17610000000000 : ℝ)*(14721/100000 : ℝ)=(10001454670604799/10000000000000000 : ℝ) by norm_num, show 1+2*(6142255105305353/20000000000000000000 : ℝ)=(10006142255105305353/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5868410078826644353/5870000000000000000 : ℝ)*(X 1 0+X 2 0)+(24901292219/17610000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (11199/100000 : ℝ)) (hi := (14721/100000 : ℝ)) (c := (5868410078826644353/5870000000000000000 : ℝ)) (alpha := (24901292219/17610000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5868410078826644353/5870000000000000000 : ℝ)*(X 0 1+X 2 1)+(24901292219/17610000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (11199/100000 : ℝ)) (hi := (14721/100000 : ℝ)) (c := (5868410078826644353/5870000000000000000 : ℝ)) (alpha := (24901292219/17610000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5868410078826644353/5870000000000000000 : ℝ)*(X 0 2+X 1 2)+(24901292219/17610000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (11199/100000 : ℝ)) (hi := (14721/100000 : ℝ)) (c := (5868410078826644353/5870000000000000000 : ℝ)) (alpha := (24901292219/17610000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2025120241/10000000000 : ℝ)*X 0 0+(2705766047/5000000000 : ℝ)*X 0 1+(32783103/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674298547/5000000000 : ℝ)*X 1 0+(-527450149/2500000000 : ℝ)*X 1 1+(5245296477/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069719419/2000000000 : ℝ)*X 2 0+(5245296477/10000000000 : ℝ)*X 2 1+(-421960119/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((540112737/1250000000 : ℝ)*X 0 0+(1037165863/2500000000 : ℝ)*X 0 1+(4499740283/10000000000 : ℝ)*X 0 2+(540112737/1250000000 : ℝ)*X 1 0+(1037165863/2500000000 : ℝ)*X 1 1+(4499740283/10000000000 : ℝ)*X 1 2+(540112737/1250000000 : ℝ)*X 2 0+(1037165863/2500000000 : ℝ)*X 2 1+(4499740283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1012566121/5000000000 : ℝ)*X 0 0+(655736541/1250000000 : ℝ)*X 0 1+(8454583/15625000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305672059/10000000000 : ℝ)*X 1 0+(-486040999/2500000000 : ℝ)*X 1 1+(5410932999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652835991/5000000000 : ℝ)*X 2 0+(5410933117/10000000000 : ℝ)*X 2 1+(-1944163941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((270057941/625000000 : ℝ)*X 0 0+(899696339/2000000000 : ℝ)*X 0 1+(2074964287/5000000000 : ℝ)*X 0 2+(270057941/625000000 : ℝ)*X 1 0+(899696339/2000000000 : ℝ)*X 1 1+(2074964287/5000000000 : ℝ)*X 1 2+(270057941/625000000 : ℝ)*X 2 0+(899696339/2000000000 : ℝ)*X 2 1+(2074964287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (319408820426372522090424853/29350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2041488589/100000000000000 : ℝ)*(base19) + (1904425371/100000000000000 : ℝ)*(base23) + (18477789/25000000000000 : ℝ)*(lower2) + (137097293/50000000000000 : ℝ)*(upper3) + (6971103/4000000000000 : ℝ)*(upper5) + (443203220285389/10000000000000 : ℝ)*(major0) + (443203220285389/10000000000000 : ℝ)*(major1) + (443203220285389/10000000000000 : ℝ)*(major2) + (375975116396353/6250000000000 : ℝ)*(sp0) + (375977610007853/6250000000000 : ℝ)*(sp1) + (3007820948594433/50000000000000 : ℝ)*(sp2) + (2848398704672987/100000000000000 : ℝ)*(sp3) + (41939272589/100000000000000 : ℝ)*(sp4) + (21536662093/100000000000000 : ℝ)*(sp7) + (71210506033377/2500000000000 : ℝ)*(f.failure) + (6015643801614237/100000000000000 : ℝ)*(f.sum) + (1699722169537/880500000000000000000000000 : ℝ)*base66 + (1386827888787525049/176100000000000000000000000000000 : ℝ)*base68 + (2034492089403525049/176100000000000000000000000000000 : ℝ)*base70 + (568901785132425049/176100000000000000000000000000000 : ℝ)*base72 + (6769603901509/1761000000000000000000000000 : ℝ)*base73 + (1892149645117125049/176100000000000000000000000000000 : ℝ)*base76 + (2574025227876225049/176100000000000000000000000000000 : ℝ)*base78 + (1448951914613325049/176100000000000000000000000000000 : ℝ)*base80 + (3950537196307/1761000000000000000000000000 : ℝ)*base81 + (1665173/250000000000000000000 : ℝ)*base89 + (1665173/250000000000000000000 : ℝ)*base91 + (1665173/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1748268308029924940689154219/293500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32607859/2500000000000 : ℝ)*(base19) + (30951189/2500000000000 : ℝ)*(base23) + (26368159/6250000000000 : ℝ)*(lower1) + (3118193/25000000000000 : ℝ)*(upper2) + (12447979/12500000000000 : ℝ)*(upper3) + (89210179/50000000000000 : ℝ)*(upper5) + (4464037134793241/100000000000000 : ℝ)*(major0) + (4464037134793241/100000000000000 : ℝ)*(major1) + (4464037134793241/100000000000000 : ℝ)*(major2) + (227564649/100000000000000 : ℝ)*(sp1) + (1211816919659207/20000000000000 : ℝ)*(sp4) + (3029541533208513/50000000000000 : ℝ)*(sp5) + (242363334409939/4000000000000 : ℝ)*(sp6) + (1434494736368199/50000000000000 : ℝ)*(sp7) + (1434494736368199/50000000000000 : ℝ)*(f.failure) + (1211816919659207/20000000000000 : ℝ)*(f.sum) + (175931332997/88050000000000000000000000 : ℝ)*base66 + (3173292469225345781/1761000000000000000000000000000000 : ℝ)*base68 + (40630223079907345781/1761000000000000000000000000000000 : ℝ)*base70 + (3233583364843345781/1761000000000000000000000000000000 : ℝ)*base72 + (5045913371/3439453125000000000000000 : ℝ)*base74 + (3355852926025654219/1761000000000000000000000000000000 : ℝ)*base75 + (14487146712646654219/1761000000000000000000000000000000 : ℝ)*base77 + (8186731083520345781/1761000000000000000000000000000000 : ℝ)*base80 + (38041197587561/1761000000000000000000000000 : ℝ)*base81 + (39534349/5000000000000000000000 : ℝ)*base90 + (39534349/5000000000000000000000 : ℝ)*base92 + (39534349/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1364_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11199/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (92/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1364_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1364_s8_0 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-253140103/1250000000 : ℝ)*x 0 + (1082304829/2000000000 : ℝ)*x 1 + (5245304071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (253140103/1250000000 : ℝ)^1081 ≤ (12337880636431/100000000000000 : ℝ)^825 := by
    have hnat : (253140103 : ℕ)^1081*100000000000000^825 ≤ 12337880636431^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253140103 1250000000 12337880636431 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082304829/2000000000 : ℝ)^1081 ≤ (44726803805051/100000000000000 : ℝ)^825 := by
    have hnat : (1082304829 : ℕ)^1081*100000000000000^825 ≤ 44726803805051^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082304829 2000000000 44726803805051 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245304071/10000000000 : ℝ)^1081 ≤ (10733828883391/25000000000000 : ℝ)^825 := by
    have hnat : (5245304071 : ℕ)^1081*25000000000000^825 ≤ 10733828883391^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245304071 10000000000 10733828883391 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-253140103/1250000000 : ℝ), (1082304829/2000000000 : ℝ), (5245304071/10000000000 : ℝ)] ![(12337880636431/100000000000000 : ℝ), (44726803805051/100000000000000 : ℝ), (10733828883391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-253140103/1250000000 : ℝ)|^1081 ≤ (12337880636431/100000000000000 : ℝ)^825
        have hw : |(-253140103/1250000000 : ℝ)|=(253140103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082304829/2000000000 : ℝ)|^1081 ≤ (44726803805051/100000000000000 : ℝ)^825
        have hw : |(1082304829/2000000000 : ℝ)|=(1082304829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245304071/10000000000 : ℝ)|^1081 ≤ (10733828883391/25000000000000 : ℝ)^825
        have hw : |(5245304071/10000000000 : ℝ)|=(5245304071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s8_1 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348594631/10000000000 : ℝ)*x 0 + (-1054896917/5000000000 : ℝ)*x 1 + (5245304053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348594631/10000000000 : ℝ)^1081 ≤ (11011630832933/25000000000000 : ℝ)^825 := by
    have hnat : (5348594631 : ℕ)^1081*25000000000000^825 ≤ 11011630832933^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348594631 10000000000 11011630832933 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054896917/5000000000 : ℝ)^1081 ≤ (2603632262921/20000000000000 : ℝ)^825 := by
    have hnat : (1054896917 : ℕ)^1081*20000000000000^825 ≤ 2603632262921^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054896917 5000000000 2603632262921 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245304053/10000000000 : ℝ)^1081 ≤ (21467657670253/50000000000000 : ℝ)^825 := by
    have hnat : (5245304053 : ℕ)^1081*50000000000000^825 ≤ 21467657670253^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245304053 10000000000 21467657670253 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348594631/10000000000 : ℝ), (-1054896917/5000000000 : ℝ), (5245304053/10000000000 : ℝ)] ![(11011630832933/25000000000000 : ℝ), (2603632262921/20000000000000 : ℝ), (21467657670253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348594631/10000000000 : ℝ)|^1081 ≤ (11011630832933/25000000000000 : ℝ)^825
        have hw : |(5348594631/10000000000 : ℝ)|=(5348594631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1054896917/5000000000 : ℝ)|^1081 ≤ (2603632262921/20000000000000 : ℝ)^825
        have hw : |(-1054896917/5000000000 : ℝ)|=(1054896917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245304053/10000000000 : ℝ)|^1081 ≤ (21467657670253/50000000000000 : ℝ)^825
        have hw : |(5245304053/10000000000 : ℝ)|=(5245304053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s8_2 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348595393/10000000000 : ℝ)*x 0 + (1049060723/2000000000 : ℝ)*x 1 + (-2109793397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348595393/10000000000 : ℝ)^1081 ≤ (44046531554133/100000000000000 : ℝ)^825 := by
    have hnat : (5348595393 : ℕ)^1081*100000000000000^825 ≤ 44046531554133^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348595393 10000000000 44046531554133 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049060723/2000000000 : ℝ)^1081 ≤ (10733827660689/25000000000000 : ℝ)^825 := by
    have hnat : (1049060723 : ℕ)^1081*25000000000000^825 ≤ 10733827660689^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049060723 2000000000 10733827660689 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109793397/10000000000 : ℝ)^1081 ≤ (13018157781449/100000000000000 : ℝ)^825 := by
    have hnat : (2109793397 : ℕ)^1081*100000000000000^825 ≤ 13018157781449^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109793397 10000000000 13018157781449 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348595393/10000000000 : ℝ), (1049060723/2000000000 : ℝ), (-2109793397/10000000000 : ℝ)] ![(44046531554133/100000000000000 : ℝ), (10733827660689/25000000000000 : ℝ), (13018157781449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348595393/10000000000 : ℝ)|^1081 ≤ (44046531554133/100000000000000 : ℝ)^825
        have hw : |(5348595393/10000000000 : ℝ)|=(5348595393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049060723/2000000000 : ℝ)|^1081 ≤ (10733827660689/25000000000000 : ℝ)^825
        have hw : |(1049060723/2000000000 : ℝ)|=(1049060723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2109793397/10000000000 : ℝ)|^1081 ≤ (13018157781449/100000000000000 : ℝ)^825
        have hw : |(-2109793397/10000000000 : ℝ)|=(2109793397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s8_3 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4320902363/10000000000 : ℝ)*x 0 + (4148680103/10000000000 : ℝ)*x 1 + (4499723587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320902363/10000000000 : ℝ)^1081 ≤ (8325917629947/25000000000000 : ℝ)^825 := by
    have hnat : (4320902363 : ℕ)^1081*25000000000000^825 ≤ 8325917629947^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320902363 10000000000 8325917629947 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4148680103/10000000000 : ℝ)^1081 ≤ (24668132813/78125000000 : ℝ)^825 := by
    have hnat : (4148680103 : ℕ)^1081*78125000000^825 ≤ 24668132813^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148680103 10000000000 24668132813 78125000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499723587/10000000000 : ℝ)^1081 ≤ (17560559736827/50000000000000 : ℝ)^825 := by
    have hnat : (4499723587 : ℕ)^1081*50000000000000^825 ≤ 17560559736827^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499723587 10000000000 17560559736827 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320902363/10000000000 : ℝ), (4148680103/10000000000 : ℝ), (4499723587/10000000000 : ℝ)] ![(8325917629947/25000000000000 : ℝ), (24668132813/78125000000 : ℝ), (17560559736827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320902363/10000000000 : ℝ)|^1081 ≤ (8325917629947/25000000000000 : ℝ)^825
        have hw : |(4320902363/10000000000 : ℝ)|=(4320902363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4148680103/10000000000 : ℝ)|^1081 ≤ (24668132813/78125000000 : ℝ)^825
        have hw : |(4148680103/10000000000 : ℝ)|=(4148680103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499723587/10000000000 : ℝ)|^1081 ≤ (17560559736827/50000000000000 : ℝ)^825
        have hw : |(4499723587/10000000000 : ℝ)|=(4499723587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s8_4 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2025133357/10000000000 : ℝ)*x 0 + (2622949879/5000000000 : ℝ)*x 1 + (5410924939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025133357/10000000000 : ℝ)^1081 ≤ (1233798068637/10000000000000 : ℝ)^825 := by
    have hnat : (2025133357 : ℕ)^1081*10000000000000^825 ≤ 1233798068637^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025133357 10000000000 1233798068637 10000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622949879/5000000000 : ℝ)^1081 ≤ (5367713082549/12500000000000 : ℝ)^825 := by
    have hnat : (2622949879 : ℕ)^1081*12500000000000^825 ≤ 5367713082549^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622949879 5000000000 5367713082549 12500000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410924939/10000000000 : ℝ)^1081 ≤ (44720314641779/100000000000000 : ℝ)^825 := by
    have hnat : (5410924939 : ℕ)^1081*100000000000000^825 ≤ 44720314641779^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410924939 10000000000 44720314641779 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2025133357/10000000000 : ℝ), (2622949879/5000000000 : ℝ), (5410924939/10000000000 : ℝ)] ![(1233798068637/10000000000000 : ℝ), (5367713082549/12500000000000 : ℝ), (44720314641779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2025133357/10000000000 : ℝ)|^1081 ≤ (1233798068637/10000000000000 : ℝ)^825
        have hw : |(-2025133357/10000000000 : ℝ)|=(2025133357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622949879/5000000000 : ℝ)|^1081 ≤ (5367713082549/12500000000000 : ℝ)^825
        have hw : |(2622949879/5000000000 : ℝ)|=(2622949879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410924939/10000000000 : ℝ)|^1081 ≤ (44720314641779/100000000000000 : ℝ)^825
        have hw : |(5410924939/10000000000 : ℝ)|=(5410924939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s8_5 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (663209251/1250000000 : ℝ)*x 0 + (-1944171713/10000000000 : ℝ)*x 1 + (2705462723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663209251/1250000000 : ℝ)^1081 ≤ (43583963771793/100000000000000 : ℝ)^825 := by
    have hnat : (663209251 : ℕ)^1081*100000000000000^825 ≤ 43583963771793^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663209251 1250000000 43583963771793 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1944171713/10000000000 : ℝ)^1081 ≤ (2923929021679/25000000000000 : ℝ)^825 := by
    have hnat : (1944171713 : ℕ)^1081*25000000000000^825 ≤ 2923929021679^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944171713 10000000000 2923929021679 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705462723/5000000000 : ℝ)^1081 ≤ (44720320132293/100000000000000 : ℝ)^825 := by
    have hnat : (2705462723 : ℕ)^1081*100000000000000^825 ≤ 44720320132293^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705462723 5000000000 44720320132293 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663209251/1250000000 : ℝ), (-1944171713/10000000000 : ℝ), (2705462723/5000000000 : ℝ)] ![(43583963771793/100000000000000 : ℝ), (2923929021679/25000000000000 : ℝ), (44720320132293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663209251/1250000000 : ℝ)|^1081 ≤ (43583963771793/100000000000000 : ℝ)^825
        have hw : |(663209251/1250000000 : ℝ)|=(663209251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1944171713/10000000000 : ℝ)|^1081 ≤ (2923929021679/25000000000000 : ℝ)^825
        have hw : |(-1944171713/10000000000 : ℝ)|=(1944171713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705462723/5000000000 : ℝ)|^1081 ≤ (44720320132293/100000000000000 : ℝ)^825
        have hw : |(2705462723/5000000000 : ℝ)|=(2705462723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1364_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h) :
    (11201/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (92/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (92/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (14/125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (92/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (14/125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (92/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (14/125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (92/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (14/125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (92/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (14/125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (92/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (14/125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (14/125 : ℝ) ^ (4323/1024 : ℝ) ≤ (1937015226913047/20000000000000000000 : ℝ) := by
    have hpowers : (14/125 : ℝ)^4323 ≤ (1937015226913047/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14 : ℕ)^4323*20000000000000000000^1024 ≤ 1937015226913047^1024*125^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14 125 1937015226913047 20000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14/125 : ℝ)) (X := (1937015226913047/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (92/625 : ℝ) ^ (4323/1024 : ℝ) ≤ (30702469128759461/100000000000000000000 : ℝ) := by
    have hpowers : (92/625 : ℝ)^4323 ≤ (30702469128759461/100000000000000000000 : ℝ)^1024 := by
      have hnat : (92 : ℕ)^4323*100000000000000000000^1024 ≤ 30702469128759461^1024*625^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92 625 30702469128759461 100000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92/625 : ℝ)) (X := (30702469128759461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001937015226913047/10000000000000000000 : ℝ) ≤ (5000229395906701/5000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (10001937015226913047/10000000000000000000 : ℝ)^1024 ≤ (5000229395906701/5000000000000000 : ℝ)^4323 := by
      have hnat : (10001937015226913047 : ℕ)^1024*5000000000000000^4323 ≤ 5000229395906701^4323*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001937015226913047 10000000000000000000 5000229395906701 5000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000229395906701/5000000000000000 : ℝ)) (X := (10001937015226913047/10000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505048443157915587/12500000000000000000 : ℝ) ≤ (10000956522660127/10000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (12505048443157915587/12500000000000000000 : ℝ)^1024 ≤ (10000956522660127/10000000000000000 : ℝ)^4323 := by
      have hnat : (12505048443157915587 : ℕ)^1024*10000000000000000^4323 ≤ 10000956522660127^4323*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505048443157915587 12500000000000000000 10000956522660127 10000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000956522660127/10000000000000000 : ℝ)) (X := (12505048443157915587/12500000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030702469128759461/50000000000000000000 : ℝ) ≤ (2500363563376713/2500000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (50030702469128759461/50000000000000000000 : ℝ)^1024 ≤ (2500363563376713/2500000000000000 : ℝ)^4323 := by
      have hnat : (50030702469128759461 : ℕ)^1024*2500000000000000^4323 ≤ 2500363563376713^4323*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030702469128759461 50000000000000000000 2500363563376713 2500000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500363563376713/2500000000000000 : ℝ)) (X := (50030702469128759461/50000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1937015226913047/20000000000000000000 : ℝ) ≤ ((1718284461729323/1718750000000000 : ℝ)+2*(19909233869/14080000000000 : ℝ)*(14/125 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (1718284461729323/1718750000000000 : ℝ)+2*(19909233869/14080000000000 : ℝ)*(14/125 : ℝ)=(5000229395906701/5000000000000000 : ℝ) by norm_num, show 1+2*(1937015226913047/20000000000000000000 : ℝ)=(10001937015226913047/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30702469128759461/100000000000000000000 : ℝ)+(1937015226913047/20000000000000000000 : ℝ) ≤ ((1718284461729323/1718750000000000 : ℝ)+(19909233869/14080000000000 : ℝ)*((92/625 : ℝ)+(14/125 : ℝ)))^(4323/1024 : ℝ) := by
    rw [show (1718284461729323/1718750000000000 : ℝ)+(19909233869/14080000000000 : ℝ)*((92/625 : ℝ)+(14/125 : ℝ))=(10000956522660127/10000000000000000 : ℝ) by norm_num, show 1+(30702469128759461/100000000000000000000 : ℝ)+(1937015226913047/20000000000000000000 : ℝ)=(12505048443157915587/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30702469128759461/100000000000000000000 : ℝ) ≤ ((1718284461729323/1718750000000000 : ℝ)+2*(19909233869/14080000000000 : ℝ)*(92/625 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (1718284461729323/1718750000000000 : ℝ)+2*(19909233869/14080000000000 : ℝ)*(92/625 : ℝ)=(2500363563376713/2500000000000000 : ℝ) by norm_num, show 1+2*(30702469128759461/100000000000000000000 : ℝ)=(50030702469128759461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1718284461729323/1718750000000000 : ℝ)*(X 1 0+X 2 0)+(19909233869/14080000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (14/125 : ℝ)) (hi := (92/625 : ℝ)) (c := (1718284461729323/1718750000000000 : ℝ)) (alpha := (19909233869/14080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1718284461729323/1718750000000000 : ℝ)*(X 0 1+X 2 1)+(19909233869/14080000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (14/125 : ℝ)) (hi := (92/625 : ℝ)) (c := (1718284461729323/1718750000000000 : ℝ)) (alpha := (19909233869/14080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1718284461729323/1718750000000000 : ℝ)*(X 0 2+X 1 2)+(19909233869/14080000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (14/125 : ℝ)) (hi := (92/625 : ℝ)) (c := (1718284461729323/1718750000000000 : ℝ)) (alpha := (19909233869/14080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-253140103/1250000000 : ℝ)*X 0 0+(1082304829/2000000000 : ℝ)*X 0 1+(5245304071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348594631/10000000000 : ℝ)*X 1 0+(-1054896917/5000000000 : ℝ)*X 1 1+(5245304053/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348595393/10000000000 : ℝ)*X 2 0+(1049060723/2000000000 : ℝ)*X 2 1+(-2109793397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320902363/10000000000 : ℝ)*X 0 0+(4148680103/10000000000 : ℝ)*X 0 1+(4499723587/10000000000 : ℝ)*X 0 2+(4320902363/10000000000 : ℝ)*X 1 0+(4148680103/10000000000 : ℝ)*X 1 1+(4499723587/10000000000 : ℝ)*X 1 2+(4320902363/10000000000 : ℝ)*X 2 0+(4148680103/10000000000 : ℝ)*X 2 1+(4499723587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2025133357/10000000000 : ℝ)*X 0 0+(2622949879/5000000000 : ℝ)*X 0 1+(5410924939/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663209251/1250000000 : ℝ)*X 1 0+(-1944171713/10000000000 : ℝ)*X 1 1+(2705462723/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (255014954066513638203429/62500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48275159/20000000000000 : ℝ)*(base23) + (3734033/1562500000000 : ℝ)*(lower2) + (597689/1562500000000 : ℝ)*(upper3) + (121733521/100000000000000 : ℝ)*(upper4) + (204177/100000000000000 : ℝ)*(upper5) + (277023711144271/6250000000000 : ℝ)*(major0) + (277023711144271/6250000000000 : ℝ)*(major1) + (277023711144271/6250000000000 : ℝ)*(major2) + (3008055452097821/50000000000000 : ℝ)*(sp0) + (6016107940757463/100000000000000 : ℝ)*(sp1) + (752014376487947/12500000000000 : ℝ)*(sp2) + (1424321683664657/50000000000000 : ℝ)*(sp3) + (434908373/10000000000000 : ℝ)*(sp4) + (7312521909/100000000000000 : ℝ)*(sp5) + (1424321683664657/50000000000000 : ℝ)*(f.failure) + (6016115253279371/100000000000000 : ℝ)*(f.sum) + (1493122826483/44000000000000000000000000 : ℝ)*base65 + (14886127840160901/1375000000000000000000000000000 : ℝ)*base68 + (9085797037410901/1375000000000000000000000000000 : ℝ)*base70 + (16099994036714099/1375000000000000000000000000000 : ℝ)*base71 + (6153313153/44000000000000000000000000 : ℝ)*base74 + (20065574776285901/1375000000000000000000000000000 : ℝ)*base76 + (9429635009910901/1375000000000000000000000000000 : ℝ)*base78 + (1148109328910901/1375000000000000000000000000000 : ℝ)*base80 + (3790500717/1760000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (36605893/5000000000000000000000 : ℝ)*base89 + (36605893/5000000000000000000000 : ℝ)*base91 + (36605893/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1364_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (92/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1364_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1364_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11193/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (92/625 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1364_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1364_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1364_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11193/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (92/625 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1364_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

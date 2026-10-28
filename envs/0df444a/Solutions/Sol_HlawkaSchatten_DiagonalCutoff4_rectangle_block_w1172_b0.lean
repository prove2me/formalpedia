-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1172_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:45:29.772897+00:00
-- url     : https://prove2.me/submissions/6d5e181e-2302-46e4-ae1a-1d59cd3cf581

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
theorem support_rectangle_w1172_s0_0 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-58823499/312500000 : ℝ)*x 0 + (6047422317/10000000000 : ℝ)*x 1 + (4784254777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58823499/312500000 : ℝ)^8365 ≤ (2190713346827/20000000000000 : ℝ)^6317 := by
    have hnat : (58823499 : ℕ)^8365*20000000000000^6317 ≤ 2190713346827^6317*312500000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58823499 312500000 2190713346827 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6047422317/10000000000 : ℝ)^8365 ≤ (51375303447903/100000000000000 : ℝ)^6317 := by
    have hnat : (6047422317 : ℕ)^8365*100000000000000^6317 ≤ 51375303447903^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6047422317 10000000000 51375303447903 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4784254777/10000000000 : ℝ)^8365 ≤ (9417782449099/25000000000000 : ℝ)^6317 := by
    have hnat : (4784254777 : ℕ)^8365*25000000000000^6317 ≤ 9417782449099^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4784254777 10000000000 9417782449099 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-58823499/312500000 : ℝ), (6047422317/10000000000 : ℝ), (4784254777/10000000000 : ℝ)] ![(2190713346827/20000000000000 : ℝ), (51375303447903/100000000000000 : ℝ), (9417782449099/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-58823499/312500000 : ℝ)|^8365 ≤ (2190713346827/20000000000000 : ℝ)^6317
        have hw : |(-58823499/312500000 : ℝ)|=(58823499/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6047422317/10000000000 : ℝ)|^8365 ≤ (51375303447903/100000000000000 : ℝ)^6317
        have hw : |(6047422317/10000000000 : ℝ)|=(6047422317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4784254777/10000000000 : ℝ)|^8365 ≤ (9417782449099/25000000000000 : ℝ)^6317
        have hw : |(4784254777/10000000000 : ℝ)|=(4784254777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s0_1 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (137877587/250000000 : ℝ)*x 0 + (-104256667/400000000 : ℝ)*x 1 + (598031847/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137877587/250000000 : ℝ)^8365 ≤ (45474108512657/100000000000000 : ℝ)^6317 := by
    have hnat : (137877587 : ℕ)^8365*100000000000000^6317 ≤ 45474108512657^6317*250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137877587 250000000 45474108512657 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104256667/400000000 : ℝ)^8365 ≤ (16854761686217/100000000000000 : ℝ)^6317 := by
    have hnat : (104256667 : ℕ)^8365*100000000000000^6317 ≤ 16854761686217^6317*400000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104256667 400000000 16854761686217 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598031847/1250000000 : ℝ)^8365 ≤ (37671129785969/100000000000000 : ℝ)^6317 := by
    have hnat : (598031847 : ℕ)^8365*100000000000000^6317 ≤ 37671129785969^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598031847 1250000000 37671129785969 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(137877587/250000000 : ℝ), (-104256667/400000000 : ℝ), (598031847/1250000000 : ℝ)] ![(45474108512657/100000000000000 : ℝ), (16854761686217/100000000000000 : ℝ), (37671129785969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(137877587/250000000 : ℝ)|^8365 ≤ (45474108512657/100000000000000 : ℝ)^6317
        have hw : |(137877587/250000000 : ℝ)|=(137877587/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104256667/400000000 : ℝ)|^8365 ≤ (16854761686217/100000000000000 : ℝ)^6317
        have hw : |(-104256667/400000000 : ℝ)|=(104256667/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(598031847/1250000000 : ℝ)|^8365 ≤ (37671129785969/100000000000000 : ℝ)^6317
        have hw : |(598031847/1250000000 : ℝ)|=(598031847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s0_2 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1103020709/2000000000 : ℝ)*x 0 + (4784254713/10000000000 : ℝ)*x 1 + (-651604167/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103020709/2000000000 : ℝ)^8365 ≤ (45474109222363/100000000000000 : ℝ)^6317 := by
    have hnat : (1103020709 : ℕ)^8365*100000000000000^6317 ≤ 45474109222363^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103020709 2000000000 45474109222363 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4784254713/10000000000 : ℝ)^8365 ≤ (37671129129083/100000000000000 : ℝ)^6317 := by
    have hnat : (4784254713 : ℕ)^8365*100000000000000^6317 ≤ 37671129129083^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4784254713 10000000000 37671129129083 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651604167/2500000000 : ℝ)^8365 ≤ (674190465051/4000000000000 : ℝ)^6317 := by
    have hnat : (651604167 : ℕ)^8365*4000000000000^6317 ≤ 674190465051^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651604167 2500000000 674190465051 4000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103020709/2000000000 : ℝ), (4784254713/10000000000 : ℝ), (-651604167/2500000000 : ℝ)] ![(45474109222363/100000000000000 : ℝ), (37671129129083/100000000000000 : ℝ), (674190465051/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103020709/2000000000 : ℝ)|^8365 ≤ (45474109222363/100000000000000 : ℝ)^6317
        have hw : |(1103020709/2000000000 : ℝ)|=(1103020709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4784254713/10000000000 : ℝ)|^8365 ≤ (37671129129083/100000000000000 : ℝ)^6317
        have hw : |(4784254713/10000000000 : ℝ)|=(4784254713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-651604167/2500000000 : ℝ)|^8365 ≤ (674190465051/4000000000000 : ℝ)^6317
        have hw : |(-651604167/2500000000 : ℝ)|=(651604167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s0_3 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2099287663/5000000000 : ℝ)*x 0 + (1559864657/5000000000 : ℝ)*x 1 + (2823782343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099287663/5000000000 : ℝ)^8365 ≤ (15844549625841/50000000000000 : ℝ)^6317 := by
    have hnat : (2099287663 : ℕ)^8365*50000000000000^6317 ≤ 15844549625841^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099287663 5000000000 15844549625841 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1559864657/5000000000 : ℝ)^8365 ≤ (21384905073087/100000000000000 : ℝ)^6317 := by
    have hnat : (1559864657 : ℕ)^8365*100000000000000^6317 ≤ 21384905073087^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559864657 5000000000 21384905073087 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2823782343/5000000000 : ℝ)^8365 ≤ (46925995654631/100000000000000 : ℝ)^6317 := by
    have hnat : (2823782343 : ℕ)^8365*100000000000000^6317 ≤ 46925995654631^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2823782343 5000000000 46925995654631 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2099287663/5000000000 : ℝ), (1559864657/5000000000 : ℝ), (2823782343/5000000000 : ℝ)] ![(15844549625841/50000000000000 : ℝ), (21384905073087/100000000000000 : ℝ), (46925995654631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2099287663/5000000000 : ℝ)|^8365 ≤ (15844549625841/50000000000000 : ℝ)^6317
        have hw : |(2099287663/5000000000 : ℝ)|=(2099287663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1559864657/5000000000 : ℝ)|^8365 ≤ (21384905073087/100000000000000 : ℝ)^6317
        have hw : |(1559864657/5000000000 : ℝ)|=(1559864657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2823782343/5000000000 : ℝ)|^8365 ≤ (46925995654631/100000000000000 : ℝ)^6317
        have hw : |(2823782343/5000000000 : ℝ)|=(2823782343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s0_4 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-235926241/1250000000 : ℝ)*x 0 + (963365051/2000000000 : ℝ)*x 1 + (6013704487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235926241/1250000000 : ℝ)^8365 ≤ (10992558616139/100000000000000 : ℝ)^6317 := by
    have hnat : (235926241 : ℕ)^8365*100000000000000^6317 ≤ 10992558616139^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235926241 1250000000 10992558616139 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (963365051/2000000000 : ℝ)^8365 ≤ (38011108586291/100000000000000 : ℝ)^6317 := by
    have hnat : (963365051 : ℕ)^8365*100000000000000^6317 ≤ 38011108586291^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963365051 2000000000 38011108586291 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6013704487/10000000000 : ℝ)^8365 ≤ (25498166391399/50000000000000 : ℝ)^6317 := by
    have hnat : (6013704487 : ℕ)^8365*50000000000000^6317 ≤ 25498166391399^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6013704487 10000000000 25498166391399 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235926241/1250000000 : ℝ), (963365051/2000000000 : ℝ), (6013704487/10000000000 : ℝ)] ![(10992558616139/100000000000000 : ℝ), (38011108586291/100000000000000 : ℝ), (25498166391399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235926241/1250000000 : ℝ)|^8365 ≤ (10992558616139/100000000000000 : ℝ)^6317
        have hw : |(-235926241/1250000000 : ℝ)|=(235926241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(963365051/2000000000 : ℝ)|^8365 ≤ (38011108586291/100000000000000 : ℝ)^6317
        have hw : |(963365051/2000000000 : ℝ)|=(963365051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6013704487/10000000000 : ℝ)|^8365 ≤ (25498166391399/50000000000000 : ℝ)^6317
        have hw : |(6013704487/10000000000 : ℝ)|=(6013704487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s0_5 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5171728883/10000000000 : ℝ)*x 0 + (-1376967147/10000000000 : ℝ)*x 1 + (3006852123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171728883/10000000000 : ℝ)^8365 ≤ (41763334189611/100000000000000 : ℝ)^6317 := by
    have hnat : (5171728883 : ℕ)^8365*100000000000000^6317 ≤ 41763334189611^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171728883 10000000000 41763334189611 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376967147/10000000000 : ℝ)^8365 ≤ (3620167861729/50000000000000 : ℝ)^6317 := by
    have hnat : (1376967147 : ℕ)^8365*50000000000000^6317 ≤ 3620167861729^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376967147 10000000000 3620167861729 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3006852123/5000000000 : ℝ)^8365 ≤ (25498165038271/50000000000000 : ℝ)^6317 := by
    have hnat : (3006852123 : ℕ)^8365*50000000000000^6317 ≤ 25498165038271^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3006852123 5000000000 25498165038271 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171728883/10000000000 : ℝ), (-1376967147/10000000000 : ℝ), (3006852123/5000000000 : ℝ)] ![(41763334189611/100000000000000 : ℝ), (3620167861729/50000000000000 : ℝ), (25498165038271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171728883/10000000000 : ℝ)|^8365 ≤ (41763334189611/100000000000000 : ℝ)^6317
        have hw : |(5171728883/10000000000 : ℝ)|=(5171728883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1376967147/10000000000 : ℝ)|^8365 ≤ (3620167861729/50000000000000 : ℝ)^6317
        have hw : |(-1376967147/10000000000 : ℝ)|=(1376967147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3006852123/5000000000 : ℝ)|^8365 ≤ (25498165038271/50000000000000 : ℝ)^6317
        have hw : |(3006852123/5000000000 : ℝ)|=(3006852123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s0_6 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2585864421/5000000000 : ℝ)*x 0 + (6013704357/10000000000 : ℝ)*x 1 + (-1376967031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585864421/5000000000 : ℝ)^8365 ≤ (41763333751183/100000000000000 : ℝ)^6317 := by
    have hnat : (2585864421 : ℕ)^8365*100000000000000^6317 ≤ 41763333751183^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585864421 5000000000 41763333751183 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6013704357/10000000000 : ℝ)^8365 ≤ (3187270707687/6250000000000 : ℝ)^6317 := by
    have hnat : (6013704357 : ℕ)^8365*6250000000000^6317 ≤ 3187270707687^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6013704357 10000000000 3187270707687 6250000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1376967031/10000000000 : ℝ)^8365 ≤ (3620167457881/50000000000000 : ℝ)^6317 := by
    have hnat : (1376967031 : ℕ)^8365*50000000000000^6317 ≤ 3620167457881^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376967031 10000000000 3620167457881 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585864421/5000000000 : ℝ), (6013704357/10000000000 : ℝ), (-1376967031/10000000000 : ℝ)] ![(41763333751183/100000000000000 : ℝ), (3187270707687/6250000000000 : ℝ), (3620167457881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585864421/5000000000 : ℝ)|^8365 ≤ (41763333751183/100000000000000 : ℝ)^6317
        have hw : |(2585864421/5000000000 : ℝ)|=(2585864421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6013704357/10000000000 : ℝ)|^8365 ≤ (3187270707687/6250000000000 : ℝ)^6317
        have hw : |(6013704357/10000000000 : ℝ)|=(6013704357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1376967031/10000000000 : ℝ)|^8365 ≤ (3620167457881/50000000000000 : ℝ)^6317
        have hw : |(-1376967031/10000000000 : ℝ)|=(1376967031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s0_7 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4208697301/10000000000 : ℝ)*x 0 + (2791192301/5000000000 : ℝ)*x 1 + (3187205297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208697301/10000000000 : ℝ)^8365 ≤ (31790303296553/100000000000000 : ℝ)^6317 := by
    have hnat : (4208697301 : ℕ)^8365*100000000000000^6317 ≤ 31790303296553^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208697301 10000000000 31790303296553 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2791192301/5000000000 : ℝ)^8365 ≤ (23105085319249/50000000000000 : ℝ)^6317 := by
    have hnat : (2791192301 : ℕ)^8365*50000000000000^6317 ≤ 23105085319249^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2791192301 5000000000 23105085319249 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3187205297/10000000000 : ℝ)^8365 ≤ (21999526054157/100000000000000 : ℝ)^6317 := by
    have hnat : (3187205297 : ℕ)^8365*100000000000000^6317 ≤ 21999526054157^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3187205297 10000000000 21999526054157 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208697301/10000000000 : ℝ), (2791192301/5000000000 : ℝ), (3187205297/10000000000 : ℝ)] ![(31790303296553/100000000000000 : ℝ), (23105085319249/50000000000000 : ℝ), (21999526054157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208697301/10000000000 : ℝ)|^8365 ≤ (31790303296553/100000000000000 : ℝ)^6317
        have hw : |(4208697301/10000000000 : ℝ)|=(4208697301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2791192301/5000000000 : ℝ)|^8365 ≤ (23105085319249/50000000000000 : ℝ)^6317
        have hw : |(2791192301/5000000000 : ℝ)|=(2791192301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3187205297/10000000000 : ℝ)|^8365 ≤ (21999526054157/100000000000000 : ℝ)^6317
        have hw : |(3187205297/10000000000 : ℝ)|=(3187205297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1172_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (67/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (277/1000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2091/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2091 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2091*1^512 ≤ 0^512*1^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2091/512 : ℝ) ≤ (2370386812978829753/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2091 ≤ (2370386812978829753/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2091*100000000000000000000^512 ≤ 2370386812978829753^512*5^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2370386812978829753 100000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2370386812978829753/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2091 := by
      have hnat : (1 : ℕ)^512*1^2091 ≤ 1^2091*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102370386812978829753/100000000000000000000 : ℝ) ≤ (5028764331562249/5000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (102370386812978829753/100000000000000000000 : ℝ)^512 ≤ (5028764331562249/5000000000000000 : ℝ)^2091 := by
      have hnat : (102370386812978829753 : ℕ)^512*5000000000000000^2091 ≤ 5028764331562249^2091*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102370386812978829753 100000000000000000000 5028764331562249 5000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028764331562249/5000000000000000 : ℝ)) (X := (102370386812978829753/100000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52370386812978829753/50000000000000000000 : ℝ) ≤ (2528764331562249/2500000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (52370386812978829753/50000000000000000000 : ℝ)^512 ≤ (2528764331562249/2500000000000000 : ℝ)^2091 := by
      have hnat : (52370386812978829753 : ℕ)^512*2500000000000000^2091 ≤ 2528764331562249^2091*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52370386812978829753 50000000000000000000 2528764331562249 2500000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528764331562249/2500000000000000 : ℝ)) (X := (52370386812978829753/50000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28764331562249/2000000000000000 : ℝ)*(0 : ℝ))^(2091/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(28764331562249/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2370386812978829753/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28764331562249/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2091/512 : ℝ) := by
    rw [show (1 : ℝ)+(28764331562249/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028764331562249/5000000000000000 : ℝ) by norm_num, show 1+(2370386812978829753/100000000000000000000 : ℝ)+(0 : ℝ)=(102370386812978829753/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2370386812978829753/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28764331562249/2000000000000000 : ℝ)*(2/5 : ℝ))^(2091/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(28764331562249/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528764331562249/2500000000000000 : ℝ) by norm_num, show 1+2*(2370386812978829753/100000000000000000000 : ℝ)=(52370386812978829753/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28764331562249/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28764331562249/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28764331562249/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28764331562249/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28764331562249/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28764331562249/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-58823499/312500000 : ℝ)*X 0 0+(6047422317/10000000000 : ℝ)*X 0 1+(4784254777/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((137877587/250000000 : ℝ)*X 1 0+(-104256667/400000000 : ℝ)*X 1 1+(598031847/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1103020709/2000000000 : ℝ)*X 2 0+(4784254713/10000000000 : ℝ)*X 2 1+(-651604167/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2099287663/5000000000 : ℝ)*X 0 0+(1559864657/5000000000 : ℝ)*X 0 1+(2823782343/5000000000 : ℝ)*X 0 2+(2099287663/5000000000 : ℝ)*X 1 0+(1559864657/5000000000 : ℝ)*X 1 1+(2823782343/5000000000 : ℝ)*X 1 2+(2099287663/5000000000 : ℝ)*X 2 0+(1559864657/5000000000 : ℝ)*X 2 1+(2823782343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-235926241/1250000000 : ℝ)*X 0 0+(963365051/2000000000 : ℝ)*X 0 1+(6013704487/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5171728883/10000000000 : ℝ)*X 1 0+(-1376967147/10000000000 : ℝ)*X 1 1+(3006852123/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2585864421/5000000000 : ℝ)*X 2 0+(6013704357/10000000000 : ℝ)*X 2 1+(-1376967031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4208697301/10000000000 : ℝ)*X 0 0+(2791192301/5000000000 : ℝ)*X 0 1+(3187205297/10000000000 : ℝ)*X 0 2+(4208697301/10000000000 : ℝ)*X 1 0+(2791192301/5000000000 : ℝ)*X 1 1+(3187205297/10000000000 : ℝ)*X 1 2+(4208697301/10000000000 : ℝ)*X 2 0+(2791192301/5000000000 : ℝ)*X 2 1+(3187205297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (684670503146142621946461/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78443297/100000000000000 : ℝ)*(base1) + (166185669/10000000000000 : ℝ)*(base19) + (389213573/25000000000000 : ℝ)*(base23) + (114332853/100000000000000 : ℝ)*(base24) + (188167179/50000000000000 : ℝ)*(upper3) + (593635057785421/100000000000000 : ℝ)*(major0) + (593635057785421/100000000000000 : ℝ)*(major1) + (593635057785421/100000000000000 : ℝ)*(major2) + (791666184861393/100000000000000 : ℝ)*(sp0) + (79166812782969/10000000000000 : ℝ)*(sp1) + (158333623699847/20000000000000 : ℝ)*(sp2) + (395597099945829/100000000000000 : ℝ)*(sp3) + (736653657/20000000000000 : ℝ)*(sp4) + (2919271827/100000000000000 : ℝ)*(sp7) + (49450012207619/12500000000000 : ℝ)*(f.failure) + (39583489484319/5000000000000 : ℝ)*(f.sum) + (229671781528171/100000000000000000000000000000 : ℝ)*base66 + (575573737028171/200000000000000000000000000000 : ℝ)*base68 + (34393147628171/200000000000000000000000000000 : ℝ)*base70 + (509708069971829/200000000000000000000000000000 : ℝ)*base71 + (412222694828171/100000000000000000000000000000 : ℝ)*base74 + (760670795571829/200000000000000000000000000000 : ℝ)*base75 + (62685305028171/200000000000000000000000000000 : ℝ)*base78 + (258986403171829/200000000000000000000000000000 : ℝ)*base79 + (457918187128171/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (11876161/1250000000000000000000 : ℝ)*base90 + (11876161/1250000000000000000000 : ℝ)*base92 + (11876161/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43197145695495339323817/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27441763/100000000000000 : ℝ)*(base1) + (223328969/50000000000000 : ℝ)*(base19) + (110282193/25000000000000 : ℝ)*(base23) + (19390811/50000000000000 : ℝ)*(upper3) + (14673401/25000000000000 : ℝ)*(upper5) + (156626448623189/25000000000000 : ℝ)*(major0) + (156626448623189/25000000000000 : ℝ)*(major1) + (156626448623189/25000000000000 : ℝ)*(major2) + (417386309/50000000000000 : ℝ)*(sp1) + (170251391/20000000000000 : ℝ)*(sp2) + (208876577091107/25000000000000 : ℝ)*(sp4) + (835504999492109/100000000000000 : ℝ)*(sp5) + (417752494268469/50000000000000 : ℝ)*(sp6) + (52188152878111/12500000000000 : ℝ)*(sp7) + (417505250466651/100000000000000 : ℝ)*(f.failure) + (167101256184533/20000000000000 : ℝ)*(f.sum) + (8478845792061/25000000000000000000000000000 : ℝ)*base65 + (108383312592061/50000000000000000000000000000 : ℝ)*base67 + (17777510207939/50000000000000000000000000000 : ℝ)*base70 + (41607610357939/50000000000000000000000000000 : ℝ)*base72 + (130117838317061/25000000000000000000000000000 : ℝ)*base73 + (116904007507939/50000000000000000000000000000 : ℝ)*base76 + (85456429557939/50000000000000000000000000000 : ℝ)*base78 + (66856119457939/50000000000000000000000000000 : ℝ)*base80 + (52238130442061/25000000000000000000000000000 : ℝ)*base81 + (10203031/10000000000000000000000 : ℝ)*base89 + (10203031/10000000000000000000000 : ℝ)*base91 + (10203031/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1172_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (67/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (277/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1172_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1172_s1_0 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2084849983/10000000000 : ℝ)*x 0 + (71169453/125000000 : ℝ)*x 1 + (1252122819/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084849983/10000000000 : ℝ)^8365 ≤ (627026340693/5000000000000 : ℝ)^6317 := by
    have hnat : (2084849983 : ℕ)^8365*5000000000000^6317 ≤ 627026340693^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084849983 10000000000 627026340693 5000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71169453/125000000 : ℝ)^8365 ≤ (47432703140923/100000000000000 : ℝ)^6317 := by
    have hnat : (71169453 : ℕ)^8365*100000000000000^6317 ≤ 47432703140923^6317*125000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71169453 125000000 47432703140923 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1252122819/2500000000 : ℝ)^8365 ≤ (4002677003437/10000000000000 : ℝ)^6317 := by
    have hnat : (1252122819 : ℕ)^8365*10000000000000^6317 ≤ 4002677003437^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252122819 2500000000 4002677003437 10000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2084849983/10000000000 : ℝ), (71169453/125000000 : ℝ), (1252122819/2500000000 : ℝ)] ![(627026340693/5000000000000 : ℝ), (47432703140923/100000000000000 : ℝ), (4002677003437/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2084849983/10000000000 : ℝ)|^8365 ≤ (627026340693/5000000000000 : ℝ)^6317
        have hw : |(-2084849983/10000000000 : ℝ)|=(2084849983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(71169453/125000000 : ℝ)|^8365 ≤ (47432703140923/100000000000000 : ℝ)^6317
        have hw : |(71169453/125000000 : ℝ)|=(71169453/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1252122819/2500000000 : ℝ)|^8365 ≤ (4002677003437/10000000000000 : ℝ)^6317
        have hw : |(1252122819/2500000000 : ℝ)|=(1252122819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s1_1 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5417474049/10000000000 : ℝ)*x 0 + (-2453988163/10000000000 : ℝ)*x 1 + (5008490317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417474049/10000000000 : ℝ)^8365 ≤ (22205603156843/50000000000000 : ℝ)^6317 := by
    have hnat : (5417474049 : ℕ)^8365*50000000000000^6317 ≤ 22205603156843^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417474049 10000000000 22205603156843 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2453988163/10000000000 : ℝ)^8365 ≤ (1556203378729/10000000000000 : ℝ)^6317 := by
    have hnat : (2453988163 : ℕ)^8365*10000000000000^6317 ≤ 1556203378729^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2453988163 10000000000 1556203378729 10000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5008490317/10000000000 : ℝ)^8365 ≤ (40026759885509/100000000000000 : ℝ)^6317 := by
    have hnat : (5008490317 : ℕ)^8365*100000000000000^6317 ≤ 40026759885509^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5008490317 10000000000 40026759885509 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417474049/10000000000 : ℝ), (-2453988163/10000000000 : ℝ), (5008490317/10000000000 : ℝ)] ![(22205603156843/50000000000000 : ℝ), (1556203378729/10000000000000 : ℝ), (40026759885509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417474049/10000000000 : ℝ)|^8365 ≤ (22205603156843/50000000000000 : ℝ)^6317
        have hw : |(5417474049/10000000000 : ℝ)|=(5417474049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2453988163/10000000000 : ℝ)|^8365 ≤ (1556203378729/10000000000000 : ℝ)^6317
        have hw : |(-2453988163/10000000000 : ℝ)|=(2453988163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5008490317/10000000000 : ℝ)|^8365 ≤ (40026759885509/100000000000000 : ℝ)^6317
        have hw : |(5008490317/10000000000 : ℝ)|=(5008490317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s1_2 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1354369041/2500000000 : ℝ)*x 0 + (5008488341/10000000000 : ℝ)*x 1 + (-2453987919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354369041/2500000000 : ℝ)^8365 ≤ (44411229273121/100000000000000 : ℝ)^6317 := by
    have hnat : (1354369041 : ℕ)^8365*100000000000000^6317 ≤ 44411229273121^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354369041 2500000000 44411229273121 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5008488341/10000000000 : ℝ)^8365 ≤ (4002673897399/10000000000000 : ℝ)^6317 := by
    have hnat : (5008488341 : ℕ)^8365*10000000000000^6317 ≤ 4002673897399^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5008488341 10000000000 4002673897399 10000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2453987919/10000000000 : ℝ)^8365 ≤ (3112406347661/20000000000000 : ℝ)^6317 := by
    have hnat : (2453987919 : ℕ)^8365*20000000000000^6317 ≤ 3112406347661^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2453987919 10000000000 3112406347661 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354369041/2500000000 : ℝ), (5008488341/10000000000 : ℝ), (-2453987919/10000000000 : ℝ)] ![(44411229273121/100000000000000 : ℝ), (4002673897399/10000000000000 : ℝ), (3112406347661/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354369041/2500000000 : ℝ)|^8365 ≤ (44411229273121/100000000000000 : ℝ)^6317
        have hw : |(1354369041/2500000000 : ℝ)|=(1354369041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5008488341/10000000000 : ℝ)|^8365 ≤ (4002673897399/10000000000000 : ℝ)^6317
        have hw : |(5008488341/10000000000 : ℝ)|=(5008488341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2453987919/10000000000 : ℝ)|^8365 ≤ (3112406347661/20000000000000 : ℝ)^6317
        have hw : |(-2453987919/10000000000 : ℝ)|=(2453987919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s1_3 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1078722613/2500000000 : ℝ)*x 0 + (920663839/2500000000 : ℝ)*x 1 + (2526796753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078722613/2500000000 : ℝ)^8365 ≤ (16428402196937/50000000000000 : ℝ)^6317 := by
    have hnat : (1078722613 : ℕ)^8365*50000000000000^6317 ≤ 16428402196937^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078722613 2500000000 16428402196937 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (920663839/2500000000 : ℝ)^8365 ≤ (26638424411977/100000000000000 : ℝ)^6317 := by
    have hnat : (920663839 : ℕ)^8365*100000000000000^6317 ≤ 26638424411977^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920663839 2500000000 26638424411977 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2526796753/5000000000 : ℝ)^8365 ≤ (20252385586099/50000000000000 : ℝ)^6317 := by
    have hnat : (2526796753 : ℕ)^8365*50000000000000^6317 ≤ 20252385586099^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2526796753 5000000000 20252385586099 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078722613/2500000000 : ℝ), (920663839/2500000000 : ℝ), (2526796753/5000000000 : ℝ)] ![(16428402196937/50000000000000 : ℝ), (26638424411977/100000000000000 : ℝ), (20252385586099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078722613/2500000000 : ℝ)|^8365 ≤ (16428402196937/50000000000000 : ℝ)^6317
        have hw : |(1078722613/2500000000 : ℝ)|=(1078722613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(920663839/2500000000 : ℝ)|^8365 ≤ (26638424411977/100000000000000 : ℝ)^6317
        have hw : |(920663839/2500000000 : ℝ)|=(920663839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2526796753/5000000000 : ℝ)|^8365 ≤ (20252385586099/50000000000000 : ℝ)^6317
        have hw : |(2526796753/5000000000 : ℝ)|=(2526796753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s1_4 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1042809499/5000000000 : ℝ)*x 0 + (2508869133/5000000000 : ℝ)*x 1 + (1136825049/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042809499/5000000000 : ℝ)^8365 ≤ (12546652529249/100000000000000 : ℝ)^6317 := by
    have hnat : (1042809499 : ℕ)^8365*100000000000000^6317 ≤ 12546652529249^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042809499 5000000000 12546652529249 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2508869133/5000000000 : ℝ)^8365 ≤ (10031164482061/25000000000000 : ℝ)^6317 := by
    have hnat : (2508869133 : ℕ)^8365*25000000000000^6317 ≤ 10031164482061^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508869133 5000000000 10031164482061 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136825049/2000000000 : ℝ)^8365 ≤ (47328689530571/100000000000000 : ℝ)^6317 := by
    have hnat : (1136825049 : ℕ)^8365*100000000000000^6317 ≤ 47328689530571^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136825049 2000000000 47328689530571 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1042809499/5000000000 : ℝ), (2508869133/5000000000 : ℝ), (1136825049/2000000000 : ℝ)] ![(12546652529249/100000000000000 : ℝ), (10031164482061/25000000000000 : ℝ), (47328689530571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1042809499/5000000000 : ℝ)|^8365 ≤ (12546652529249/100000000000000 : ℝ)^6317
        have hw : |(-1042809499/5000000000 : ℝ)|=(1042809499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2508869133/5000000000 : ℝ)|^8365 ≤ (10031164482061/25000000000000 : ℝ)^6317
        have hw : |(2508869133/5000000000 : ℝ)|=(2508869133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1136825049/2000000000 : ℝ)|^8365 ≤ (47328689530571/100000000000000 : ℝ)^6317
        have hw : |(1136825049/2000000000 : ℝ)|=(1136825049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s1_5 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5241574159/10000000000 : ℝ)*x 0 + (-1778350409/10000000000 : ℝ)*x 1 + (5684127941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241574159/10000000000 : ℝ)^8365 ≤ (42511845520347/100000000000000 : ℝ)^6317 := by
    have hnat : (5241574159 : ℕ)^8365*100000000000000^6317 ≤ 42511845520347^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241574159 10000000000 42511845520347 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1778350409/10000000000 : ℝ)^8365 ≤ (5079717604277/50000000000000 : ℝ)^6317 := by
    have hnat : (1778350409 : ℕ)^8365*50000000000000^6317 ≤ 5079717604277^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778350409 10000000000 5079717604277 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5684127941/10000000000 : ℝ)^8365 ≤ (47328719256527/100000000000000 : ℝ)^6317 := by
    have hnat : (5684127941 : ℕ)^8365*100000000000000^6317 ≤ 47328719256527^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5684127941 10000000000 47328719256527 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241574159/10000000000 : ℝ), (-1778350409/10000000000 : ℝ), (5684127941/10000000000 : ℝ)] ![(42511845520347/100000000000000 : ℝ), (5079717604277/50000000000000 : ℝ), (47328719256527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241574159/10000000000 : ℝ)|^8365 ≤ (42511845520347/100000000000000 : ℝ)^6317
        have hw : |(5241574159/10000000000 : ℝ)|=(5241574159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1778350409/10000000000 : ℝ)|^8365 ≤ (5079717604277/50000000000000 : ℝ)^6317
        have hw : |(-1778350409/10000000000 : ℝ)|=(1778350409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5684127941/10000000000 : ℝ)|^8365 ≤ (47328719256527/100000000000000 : ℝ)^6317
        have hw : |(5684127941/10000000000 : ℝ)|=(5684127941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s1_6 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2620786759/5000000000 : ℝ)*x 0 + (710516141/1250000000 : ℝ)*x 1 + (-1778349589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620786759/5000000000 : ℝ)^8365 ≤ (42511838636023/100000000000000 : ℝ)^6317 := by
    have hnat : (2620786759 : ℕ)^8365*100000000000000^6317 ≤ 42511838636023^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620786759 5000000000 42511838636023 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (710516141/1250000000 : ℝ)^8365 ≤ (5916091543041/12500000000000 : ℝ)^6317 := by
    have hnat : (710516141 : ℕ)^8365*12500000000000^6317 ≤ 5916091543041^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710516141 1250000000 5916091543041 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1778349589/10000000000 : ℝ)^8365 ≤ (5079714502639/50000000000000 : ℝ)^6317 := by
    have hnat : (1778349589 : ℕ)^8365*50000000000000^6317 ≤ 5079714502639^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778349589 10000000000 5079714502639 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620786759/5000000000 : ℝ), (710516141/1250000000 : ℝ), (-1778349589/10000000000 : ℝ)] ![(42511838636023/100000000000000 : ℝ), (5916091543041/12500000000000 : ℝ), (5079714502639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620786759/5000000000 : ℝ)|^8365 ≤ (42511838636023/100000000000000 : ℝ)^6317
        have hw : |(2620786759/5000000000 : ℝ)|=(2620786759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(710516141/1250000000 : ℝ)|^8365 ≤ (5916091543041/12500000000000 : ℝ)^6317
        have hw : |(710516141/1250000000 : ℝ)|=(710516141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1778349589/10000000000 : ℝ)|^8365 ≤ (5079714502639/50000000000000 : ℝ)^6317
        have hw : |(-1778349589/10000000000 : ℝ)|=(1778349589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s1_7 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2158208899/5000000000 : ℝ)*x 0 + (201403667/400000000 : ℝ)*x 1 + (7403041/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158208899/5000000000 : ℝ)^8365 ≤ (8218051561641/25000000000000 : ℝ)^6317 := by
    have hnat : (2158208899 : ℕ)^8365*25000000000000^6317 ≤ 8218051561641^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158208899 5000000000 8218051561641 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201403667/400000000 : ℝ)^8365 ≤ (322468140613/800000000000 : ℝ)^6317 := by
    have hnat : (201403667 : ℕ)^8365*800000000000^6317 ≤ 322468140613^6317*400000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201403667 400000000 322468140613 800000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7403041/20000000 : ℝ)^8365 ≤ (6704819041391/25000000000000 : ℝ)^6317 := by
    have hnat : (7403041 : ℕ)^8365*25000000000000^6317 ≤ 6704819041391^6317*20000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7403041 20000000 6704819041391 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158208899/5000000000 : ℝ), (201403667/400000000 : ℝ), (7403041/20000000 : ℝ)] ![(8218051561641/25000000000000 : ℝ), (322468140613/800000000000 : ℝ), (6704819041391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158208899/5000000000 : ℝ)|^8365 ≤ (8218051561641/25000000000000 : ℝ)^6317
        have hw : |(2158208899/5000000000 : ℝ)|=(2158208899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201403667/400000000 : ℝ)|^8365 ≤ (322468140613/800000000000 : ℝ)^6317
        have hw : |(201403667/400000000 : ℝ)|=(201403667/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7403041/20000000 : ℝ)|^8365 ≤ (6704819041391/25000000000000 : ℝ)^6317
        have hw : |(7403041/20000000 : ℝ)|=(7403041/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s1_8 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (524993/1000000000 : ℝ)*x 0 + (1098119627/2000000000 : ℝ)*x 1 + (3174222291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524993/1000000000 : ℝ)^8365 ≤ (2268728029/50000000000000 : ℝ)^6317 := by
    have hnat : (524993 : ℕ)^8365*50000000000000^6317 ≤ 2268728029^6317*1000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524993 1000000000 2268728029 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098119627/2000000000 : ℝ)^8365 ≤ (22603369100823/50000000000000 : ℝ)^6317 := by
    have hnat : (1098119627 : ℕ)^8365*50000000000000^6317 ≤ 22603369100823^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098119627 2000000000 22603369100823 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3174222291/5000000000 : ℝ)^8365 ≤ (13697181083131/25000000000000 : ℝ)^6317 := by
    have hnat : (3174222291 : ℕ)^8365*25000000000000^6317 ≤ 13697181083131^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3174222291 5000000000 13697181083131 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524993/1000000000 : ℝ), (1098119627/2000000000 : ℝ), (3174222291/5000000000 : ℝ)] ![(2268728029/50000000000000 : ℝ), (22603369100823/50000000000000 : ℝ), (13697181083131/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524993/1000000000 : ℝ)|^8365 ≤ (2268728029/50000000000000 : ℝ)^6317
        have hw : |(524993/1000000000 : ℝ)|=(524993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098119627/2000000000 : ℝ)|^8365 ≤ (22603369100823/50000000000000 : ℝ)^6317
        have hw : |(1098119627/2000000000 : ℝ)|=(1098119627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3174222291/5000000000 : ℝ)|^8365 ≤ (13697181083131/25000000000000 : ℝ)^6317
        have hw : |(3174222291/5000000000 : ℝ)|=(3174222291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s1_9 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (986048867/10000000000 : ℝ)*x 0 + (-878020699/2000000000 : ℝ)*x 1 + (1736713343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (986048867/10000000000 : ℝ)^8365 ≤ (4652814701179/100000000000000 : ℝ)^6317 := by
    have hnat : (986048867 : ℕ)^8365*100000000000000^6317 ≤ 4652814701179^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986048867 10000000000 4652814701179 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (878020699/2000000000 : ℝ)^8365 ≤ (33617348531841/100000000000000 : ℝ)^6317 := by
    have hnat : (878020699 : ℕ)^8365*100000000000000^6317 ≤ 33617348531841^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878020699 2000000000 33617348531841 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1736713343/2500000000 : ℝ)^8365 ≤ (30864918375999/50000000000000 : ℝ)^6317 := by
    have hnat : (1736713343 : ℕ)^8365*50000000000000^6317 ≤ 30864918375999^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736713343 2500000000 30864918375999 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(986048867/10000000000 : ℝ), (-878020699/2000000000 : ℝ), (1736713343/2500000000 : ℝ)] ![(4652814701179/100000000000000 : ℝ), (33617348531841/100000000000000 : ℝ), (30864918375999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(986048867/10000000000 : ℝ)|^8365 ≤ (4652814701179/100000000000000 : ℝ)^6317
        have hw : |(986048867/10000000000 : ℝ)|=(986048867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-878020699/2000000000 : ℝ)|^8365 ≤ (33617348531841/100000000000000 : ℝ)^6317
        have hw : |(-878020699/2000000000 : ℝ)|=(878020699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1736713343/2500000000 : ℝ)|^8365 ≤ (30864918375999/50000000000000 : ℝ)^6317
        have hw : |(1736713343/2500000000 : ℝ)|=(1736713343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s1_10 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (493021381/5000000000 : ℝ)*x 0 + (173670957/250000000 : ℝ)*x 1 + (-4390124771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (493021381/5000000000 : ℝ)^8365 ≤ (2326388277211/50000000000000 : ℝ)^6317 := by
    have hnat : (493021381 : ℕ)^8365*50000000000000^6317 ≤ 2326388277211^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493021381 5000000000 2326388277211 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173670957/250000000 : ℝ)^8365 ≤ (12345931833201/20000000000000 : ℝ)^6317 := by
    have hnat : (173670957 : ℕ)^8365*20000000000000^6317 ≤ 12345931833201^6317*250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173670957 250000000 12345931833201 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4390124771/10000000000 : ℝ)^8365 ≤ (33617564273537/100000000000000 : ℝ)^6317 := by
    have hnat : (4390124771 : ℕ)^8365*100000000000000^6317 ≤ 33617564273537^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4390124771 10000000000 33617564273537 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(493021381/5000000000 : ℝ), (173670957/250000000 : ℝ), (-4390124771/10000000000 : ℝ)] ![(2326388277211/50000000000000 : ℝ), (12345931833201/20000000000000 : ℝ), (33617564273537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(493021381/5000000000 : ℝ)|^8365 ≤ (2326388277211/50000000000000 : ℝ)^6317
        have hw : |(493021381/5000000000 : ℝ)|=(493021381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(173670957/250000000 : ℝ)|^8365 ≤ (12345931833201/20000000000000 : ℝ)^6317
        have hw : |(173670957/250000000 : ℝ)|=(173670957/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4390124771/10000000000 : ℝ)|^8365 ≤ (33617564273537/100000000000000 : ℝ)^6317
        have hw : |(-4390124771/10000000000 : ℝ)|=(4390124771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s1_11 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1912395867/10000000000 : ℝ)*x 0 + (725584011/1250000000 : ℝ)*x 1 + (2510157621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1912395867/10000000000 : ℝ)^8365 ≤ (5592835808831/50000000000000 : ℝ)^6317 := by
    have hnat : (1912395867 : ℕ)^8365*50000000000000^6317 ≤ 5592835808831^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912395867 10000000000 5592835808831 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (725584011/1250000000 : ℝ)^8365 ≤ (48662380357139/100000000000000 : ℝ)^6317 := by
    have hnat : (725584011 : ℕ)^8365*100000000000000^6317 ≤ 48662380357139^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      725584011 1250000000 48662380357139 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510157621/5000000000 : ℝ)^8365 ≤ (20075974007967/50000000000000 : ℝ)^6317 := by
    have hnat : (2510157621 : ℕ)^8365*50000000000000^6317 ≤ 20075974007967^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510157621 5000000000 20075974007967 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1912395867/10000000000 : ℝ), (725584011/1250000000 : ℝ), (2510157621/5000000000 : ℝ)] ![(5592835808831/50000000000000 : ℝ), (48662380357139/100000000000000 : ℝ), (20075974007967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1912395867/10000000000 : ℝ)|^8365 ≤ (5592835808831/50000000000000 : ℝ)^6317
        have hw : |(1912395867/10000000000 : ℝ)|=(1912395867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(725584011/1250000000 : ℝ)|^8365 ≤ (48662380357139/100000000000000 : ℝ)^6317
        have hw : |(725584011/1250000000 : ℝ)|=(725584011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2510157621/5000000000 : ℝ)|^8365 ≤ (20075974007967/50000000000000 : ℝ)^6317
        have hw : |(2510157621/5000000000 : ℝ)|=(2510157621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1172_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (277/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (67/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (727/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10151/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (277/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (67/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (277/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (67/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (277/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (67/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (277/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (67/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (277/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (67/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (277/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (67/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (67/12500 : ℝ) ^ (2091/512 : ℝ) ≤ (53204024271/100000000000000000000 : ℝ) := by
    have hpowers : (67/12500 : ℝ)^2091 ≤ (53204024271/100000000000000000000 : ℝ)^512 := by
      have hnat : (67 : ℕ)^2091*100000000000000000000^512 ≤ 53204024271^512*12500^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67 12500 53204024271 100000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67/12500 : ℝ)) (X := (53204024271/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hpowhi : (277/1000 : ℝ) ^ (2091/512 : ℝ) ≤ (66070272972557407/12500000000000000000 : ℝ) := by
    have hpowers : (277/1000 : ℝ)^2091 ≤ (66070272972557407/12500000000000000000 : ℝ)^512 := by
      have hnat : (277 : ℕ)^2091*12500000000000000000^512 ≤ 66070272972557407^512*1000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        277 1000 66070272972557407 12500000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (277/1000 : ℝ)) (X := (66070272972557407/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000053204024271/50000000000000000000 : ℝ) ≤ (1250000000325687/1250000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (50000000053204024271/50000000000000000000 : ℝ)^512 ≤ (1250000000325687/1250000000000000 : ℝ)^2091 := by
      have hnat : (50000000053204024271 : ℕ)^512*1250000000000000^2091 ≤ 1250000000325687^2091*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000053204024271 50000000000000000000 1250000000325687 1250000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000000325687/1250000000000000 : ℝ)) (X := (50000000053204024271/50000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100528562236984483527/100000000000000000000 : ℝ) ≤ (10012916568465969/10000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (100528562236984483527/100000000000000000000 : ℝ)^512 ≤ (10012916568465969/10000000000000000 : ℝ)^2091 := by
      have hnat : (100528562236984483527 : ℕ)^512*10000000000000000^2091 ≤ 10012916568465969^2091*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100528562236984483527 100000000000000000000 10012916568465969 10000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012916568465969/10000000000000000 : ℝ)) (X := (100528562236984483527/100000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6316070272972557407/6250000000000000000 : ℝ) ≤ (5012916567163221/5000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (6316070272972557407/6250000000000000000 : ℝ)^512 ≤ (5012916567163221/5000000000000000 : ℝ)^2091 := by
      have hnat : (6316070272972557407 : ℕ)^512*5000000000000000^2091 ≤ 5012916567163221^2091*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6316070272972557407 6250000000000000000 5012916567163221 5000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012916567163221/5000000000000000 : ℝ)) (X := (6316070272972557407/6250000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(53204024271/100000000000000000000 : ℝ) ≤ ((16976634594510829143/16977500000000000000 : ℝ)+2*(12916565860473/2716400000000000 : ℝ)*(67/12500 : ℝ))^(2091/512 : ℝ) := by
    rw [show (16976634594510829143/16977500000000000000 : ℝ)+2*(12916565860473/2716400000000000 : ℝ)*(67/12500 : ℝ)=(1250000000325687/1250000000000000 : ℝ) by norm_num, show 1+2*(53204024271/100000000000000000000 : ℝ)=(50000000053204024271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(66070272972557407/12500000000000000000 : ℝ)+(53204024271/100000000000000000000 : ℝ) ≤ ((16976634594510829143/16977500000000000000 : ℝ)+(12916565860473/2716400000000000 : ℝ)*((277/1000 : ℝ)+(67/12500 : ℝ)))^(2091/512 : ℝ) := by
    rw [show (16976634594510829143/16977500000000000000 : ℝ)+(12916565860473/2716400000000000 : ℝ)*((277/1000 : ℝ)+(67/12500 : ℝ))=(10012916568465969/10000000000000000 : ℝ) by norm_num, show 1+(66070272972557407/12500000000000000000 : ℝ)+(53204024271/100000000000000000000 : ℝ)=(100528562236984483527/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(66070272972557407/12500000000000000000 : ℝ) ≤ ((16976634594510829143/16977500000000000000 : ℝ)+2*(12916565860473/2716400000000000 : ℝ)*(277/1000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (16976634594510829143/16977500000000000000 : ℝ)+2*(12916565860473/2716400000000000 : ℝ)*(277/1000 : ℝ)=(5012916567163221/5000000000000000 : ℝ) by norm_num, show 1+2*(66070272972557407/12500000000000000000 : ℝ)=(6316070272972557407/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16976634594510829143/16977500000000000000 : ℝ)*(X 1 0+X 2 0)+(12916565860473/2716400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (67/12500 : ℝ)) (hi := (277/1000 : ℝ)) (c := (16976634594510829143/16977500000000000000 : ℝ)) (alpha := (12916565860473/2716400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16976634594510829143/16977500000000000000 : ℝ)*(X 0 1+X 2 1)+(12916565860473/2716400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (67/12500 : ℝ)) (hi := (277/1000 : ℝ)) (c := (16976634594510829143/16977500000000000000 : ℝ)) (alpha := (12916565860473/2716400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16976634594510829143/16977500000000000000 : ℝ)*(X 0 2+X 1 2)+(12916565860473/2716400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (67/12500 : ℝ)) (hi := (277/1000 : ℝ)) (c := (16976634594510829143/16977500000000000000 : ℝ)) (alpha := (12916565860473/2716400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2084849983/10000000000 : ℝ)*X 0 0+(71169453/125000000 : ℝ)*X 0 1+(1252122819/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5417474049/10000000000 : ℝ)*X 1 0+(-2453988163/10000000000 : ℝ)*X 1 1+(5008490317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1354369041/2500000000 : ℝ)*X 2 0+(5008488341/10000000000 : ℝ)*X 2 1+(-2453987919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1078722613/2500000000 : ℝ)*X 0 0+(920663839/2500000000 : ℝ)*X 0 1+(2526796753/5000000000 : ℝ)*X 0 2+(1078722613/2500000000 : ℝ)*X 1 0+(920663839/2500000000 : ℝ)*X 1 1+(2526796753/5000000000 : ℝ)*X 1 2+(1078722613/2500000000 : ℝ)*X 2 0+(920663839/2500000000 : ℝ)*X 2 1+(2526796753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1042809499/5000000000 : ℝ)*X 0 0+(2508869133/5000000000 : ℝ)*X 0 1+(1136825049/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5241574159/10000000000 : ℝ)*X 1 0+(-1778350409/10000000000 : ℝ)*X 1 1+(5684127941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2620786759/5000000000 : ℝ)*X 2 0+(710516141/1250000000 : ℝ)*X 2 1+(-1778349589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2158208899/5000000000 : ℝ)*X 0 0+(201403667/400000000 : ℝ)*X 0 1+(7403041/20000000 : ℝ)*X 0 2+(2158208899/5000000000 : ℝ)*X 1 0+(201403667/400000000 : ℝ)*X 1 1+(7403041/20000000 : ℝ)*X 1 2+(2158208899/5000000000 : ℝ)*X 2 0+(201403667/400000000 : ℝ)*X 2 1+(7403041/20000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((524993/1000000000 : ℝ)*X 0 0+(1098119627/2000000000 : ℝ)*X 0 1+(3174222291/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((986048867/10000000000 : ℝ)*X 1 0+(-878020699/2000000000 : ℝ)*X 1 1+(1736713343/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((493021381/5000000000 : ℝ)*X 2 0+(173670957/250000000 : ℝ)*X 2 1+(-4390124771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1912395867/10000000000 : ℝ)*X 0 0+(725584011/1250000000 : ℝ)*X 0 1+(2510157621/5000000000 : ℝ)*X 0 2+(1912395867/10000000000 : ℝ)*X 1 0+(725584011/1250000000 : ℝ)*X 1 1+(2510157621/5000000000 : ℝ)*X 1 2+(1912395867/10000000000 : ℝ)*X 2 0+(725584011/1250000000 : ℝ)*X 2 1+(2510157621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (186329646204631494475676799/26527343750000000000000000000000 : ℝ) := by norm_num
    linear_combination (284719839/100000000000000 : ℝ)*(lower2) + (1094575348457121/100000000000000 : ℝ)*(major0) + (1094575348457121/100000000000000 : ℝ)*(major1) + (1094575348457121/100000000000000 : ℝ)*(major2) + (729858836107177/50000000000000 : ℝ)*(sp0) + (729858609947761/50000000000000 : ℝ)*(sp1) + (1459715379790889/100000000000000 : ℝ)*(sp2) + (5835415776623/800000000000 : ℝ)*(sp3) + (930548299/20000000000000 : ℝ)*(sp4) + (847695989/20000000000000 : ℝ)*(sp5) + (1219645157/20000000000000 : ℝ)*(sp6) + (433290191/50000000000000 : ℝ)*(sp9) + (33877567/4000000000000 : ℝ)*(sp10) + (145718149/12500000000000 : ℝ)*(sp11) + (729428137823067/100000000000000 : ℝ)*(f.failure) + (1459722324955849/100000000000000 : ℝ)*(f.sum) + (110656590178807/135820000000000000000000000000 : ℝ)*base66 + (7359544161159866447/1697750000000000000000000000000000 : ℝ)*base68 + (2094731713934116447/1697750000000000000000000000000000 : ℝ)*base70 + (3684689757761383553/1697750000000000000000000000000000 : ℝ)*base71 + (67244137033067/135820000000000000000000000000 : ℝ)*base74 + (7930806495335116447/1697750000000000000000000000000000 : ℝ)*base76 + (12192762890103366447/1697750000000000000000000000000000 : ℝ)*base78 + (5379106900212116447/1697750000000000000000000000000000 : ℝ)*base80 + (22153149021827/135820000000000000000000000000 : ℝ)*base82 + (21541527/10000000000000000000000 : ℝ)*base89 + (21541527/10000000000000000000000 : ℝ)*base91 + (21541527/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1678800219029800627596740253/424437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (562624517683581/50000000000000 : ℝ)*(major0) + (562624517683581/50000000000000 : ℝ)*(major1) + (562624517683581/50000000000000 : ℝ)*(major2) + (3945356299/100000000000000 : ℝ)*(sp1) + (6302548677/100000000000000 : ℝ)*(sp2) + (627813361/50000000000000 : ℝ)*(sp3) + (1500626145951569/100000000000000 : ℝ)*(sp4) + (750312268177979/50000000000000 : ℝ)*(sp5) + (187577788470333/12500000000000 : ℝ)*(sp6) + (187466732423527/25000000000000 : ℝ)*(sp7) + (2622567573/100000000000000 : ℝ)*(sp8) + (57361377/20000000000000 : ℝ)*(sp9) + (158207801/100000000000000 : ℝ)*(sp10) + (985049239/100000000000000 : ℝ)*(sp11) + (74986917037007/10000000000000 : ℝ)*(f.failure) + (750314384259571/50000000000000 : ℝ)*(f.sum) + (79670833681023/67910000000000000000000000000 : ℝ)*base65 + (5504683024695857333/848875000000000000000000000000000 : ℝ)*base67 + (4861193001582357333/848875000000000000000000000000000 : ℝ)*base69 + (5486024466973857333/848875000000000000000000000000000 : ℝ)*base71 + (200871402423513/67910000000000000000000000000 : ℝ)*base73 + (4538496064996107333/848875000000000000000000000000000 : ℝ)*base75 + (6126899562907107333/848875000000000000000000000000000 : ℝ)*base77 + (5084610083418357333/848875000000000000000000000000000 : ℝ)*base79 + (83360684754413/67910000000000000000000000000 : ℝ)*base81 + (4512667/1000000000000000000000 : ℝ)*base89 + (4512667/1000000000000000000000 : ℝ)*base91 + (4512667/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1172_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (277/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (67/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (727/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10151/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1172_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1172_s2_0 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2136485467/10000000000 : ℝ)*x 0 + (5505182081/10000000000 : ℝ)*x 1 + (1291000599/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136485467/10000000000 : ℝ)^8365 ≤ (12953455268279/100000000000000 : ℝ)^6317 := by
    have hnat : (2136485467 : ℕ)^8365*100000000000000^6317 ≤ 12953455268279^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136485467 10000000000 12953455268279 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5505182081/10000000000 : ℝ)^8365 ≤ (45365812667213/100000000000000 : ℝ)^6317 := by
    have hnat : (5505182081 : ℕ)^8365*100000000000000^6317 ≤ 45365812667213^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505182081 10000000000 45365812667213 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291000599/2500000000 : ℝ)^8365 ≤ (1042018301067/2500000000000 : ℝ)^6317 := by
    have hnat : (1291000599 : ℕ)^8365*2500000000000^6317 ≤ 1042018301067^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291000599 2500000000 1042018301067 2500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2136485467/10000000000 : ℝ), (5505182081/10000000000 : ℝ), (1291000599/2500000000 : ℝ)] ![(12953455268279/100000000000000 : ℝ), (45365812667213/100000000000000 : ℝ), (1042018301067/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2136485467/10000000000 : ℝ)|^8365 ≤ (12953455268279/100000000000000 : ℝ)^6317
        have hw : |(-2136485467/10000000000 : ℝ)|=(2136485467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5505182081/10000000000 : ℝ)|^8365 ≤ (45365812667213/100000000000000 : ℝ)^6317
        have hw : |(5505182081/10000000000 : ℝ)|=(5505182081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1291000599/2500000000 : ℝ)|^8365 ≤ (1042018301067/2500000000000 : ℝ)^6317
        have hw : |(1291000599/2500000000 : ℝ)|=(1291000599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s2_1 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (537258231/1000000000 : ℝ)*x 0 + (-1156829979/5000000000 : ℝ)*x 1 + (1032801061/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537258231/1000000000 : ℝ)^8365 ≤ (5490567347753/12500000000000 : ℝ)^6317 := by
    have hnat : (537258231 : ℕ)^8365*12500000000000^6317 ≤ 5490567347753^6317*1000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537258231 1000000000 5490567347753 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1156829979/5000000000 : ℝ)^8365 ≤ (1439469807359/10000000000000 : ℝ)^6317 := by
    have hnat : (1156829979 : ℕ)^8365*10000000000000^6317 ≤ 1439469807359^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156829979 5000000000 1439469807359 10000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032801061/2000000000 : ℝ)^8365 ≤ (20840381567307/50000000000000 : ℝ)^6317 := by
    have hnat : (1032801061 : ℕ)^8365*50000000000000^6317 ≤ 20840381567307^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032801061 2000000000 20840381567307 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537258231/1000000000 : ℝ), (-1156829979/5000000000 : ℝ), (1032801061/2000000000 : ℝ)] ![(5490567347753/12500000000000 : ℝ), (1439469807359/10000000000000 : ℝ), (20840381567307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537258231/1000000000 : ℝ)|^8365 ≤ (5490567347753/12500000000000 : ℝ)^6317
        have hw : |(537258231/1000000000 : ℝ)|=(537258231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1156829979/5000000000 : ℝ)|^8365 ≤ (1439469807359/10000000000000 : ℝ)^6317
        have hw : |(-1156829979/5000000000 : ℝ)|=(1156829979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032801061/2000000000 : ℝ)|^8365 ≤ (20840381567307/50000000000000 : ℝ)^6317
        have hw : |(1032801061/2000000000 : ℝ)|=(1032801061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s2_2 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (671572869/1250000000 : ℝ)*x 0 + (1032800853/2000000000 : ℝ)*x 1 + (-2313660463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671572869/1250000000 : ℝ)^8365 ≤ (8784909146499/20000000000000 : ℝ)^6317 := by
    have hnat : (671572869 : ℕ)^8365*20000000000000^6317 ≤ 8784909146499^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671572869 1250000000 8784909146499 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032800853/2000000000 : ℝ)^8365 ≤ (41680752018899/100000000000000 : ℝ)^6317 := by
    have hnat : (1032800853 : ℕ)^8365*100000000000000^6317 ≤ 41680752018899^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032800853 2000000000 41680752018899 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2313660463/10000000000 : ℝ)^8365 ≤ (899668889633/6250000000000 : ℝ)^6317 := by
    have hnat : (2313660463 : ℕ)^8365*6250000000000^6317 ≤ 899668889633^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313660463 10000000000 899668889633 6250000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671572869/1250000000 : ℝ), (1032800853/2000000000 : ℝ), (-2313660463/10000000000 : ℝ)] ![(8784909146499/20000000000000 : ℝ), (41680752018899/100000000000000 : ℝ), (899668889633/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671572869/1250000000 : ℝ)|^8365 ≤ (8784909146499/20000000000000 : ℝ)^6317
        have hw : |(671572869/1250000000 : ℝ)|=(671572869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032800853/2000000000 : ℝ)|^8365 ≤ (41680752018899/100000000000000 : ℝ)^6317
        have hw : |(1032800853/2000000000 : ℝ)|=(1032800853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2313660463/10000000000 : ℝ)|^8365 ≤ (899668889633/6250000000000 : ℝ)^6317
        have hw : |(-2313660463/10000000000 : ℝ)|=(2313660463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s2_3 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4350387081/10000000000 : ℝ)*x 0 + (804437931/2000000000 : ℝ)*x 1 + (4704949569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350387081/10000000000 : ℝ)^8365 ≤ (16607605259701/50000000000000 : ℝ)^6317 := by
    have hnat : (4350387081 : ℕ)^8365*50000000000000^6317 ≤ 16607605259701^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350387081 10000000000 16607605259701 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804437931/2000000000 : ℝ)^8365 ≤ (14969162922219/50000000000000 : ℝ)^6317 := by
    have hnat : (804437931 : ℕ)^8365*50000000000000^6317 ≤ 14969162922219^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804437931 2000000000 14969162922219 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4704949569/10000000000 : ℝ)^8365 ≤ (36846463625457/100000000000000 : ℝ)^6317 := by
    have hnat : (4704949569 : ℕ)^8365*100000000000000^6317 ≤ 36846463625457^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4704949569 10000000000 36846463625457 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350387081/10000000000 : ℝ), (804437931/2000000000 : ℝ), (4704949569/10000000000 : ℝ)] ![(16607605259701/50000000000000 : ℝ), (14969162922219/50000000000000 : ℝ), (36846463625457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350387081/10000000000 : ℝ)|^8365 ≤ (16607605259701/50000000000000 : ℝ)^6317
        have hw : |(4350387081/10000000000 : ℝ)|=(4350387081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(804437931/2000000000 : ℝ)|^8365 ≤ (14969162922219/50000000000000 : ℝ)^6317
        have hw : |(804437931/2000000000 : ℝ)|=(804437931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4704949569/10000000000 : ℝ)|^8365 ≤ (36846463625457/100000000000000 : ℝ)^6317
        have hw : |(4704949569/10000000000 : ℝ)|=(4704949569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s2_4 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-534144841/2500000000 : ℝ)*x 0 + (516630667/1000000000 : ℝ)*x 1 + (687856963/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534144841/2500000000 : ℝ)^8365 ≤ (6477104568363/50000000000000 : ℝ)^6317 := by
    have hnat : (534144841 : ℕ)^8365*50000000000000^6317 ≤ 6477104568363^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534144841 2500000000 6477104568363 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516630667/1000000000 : ℝ)^8365 ≤ (41705362331263/100000000000000 : ℝ)^6317 := by
    have hnat : (516630667 : ℕ)^8365*100000000000000^6317 ≤ 41705362331263^6317*1000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516630667 1000000000 41705362331263 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (687856963/1250000000 : ℝ)^8365 ≤ (9068085705869/20000000000000 : ℝ)^6317 := by
    have hnat : (687856963 : ℕ)^8365*20000000000000^6317 ≤ 9068085705869^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687856963 1250000000 9068085705869 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534144841/2500000000 : ℝ), (516630667/1000000000 : ℝ), (687856963/1250000000 : ℝ)] ![(6477104568363/50000000000000 : ℝ), (41705362331263/100000000000000 : ℝ), (9068085705869/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534144841/2500000000 : ℝ)|^8365 ≤ (6477104568363/50000000000000 : ℝ)^6317
        have hw : |(-534144841/2500000000 : ℝ)|=(534144841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(516630667/1000000000 : ℝ)|^8365 ≤ (41705362331263/100000000000000 : ℝ)^6317
        have hw : |(516630667/1000000000 : ℝ)|=(516630667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(687856963/1250000000 : ℝ)|^8365 ≤ (9068085705869/20000000000000 : ℝ)^6317
        have hw : |(687856963/1250000000 : ℝ)|=(687856963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s2_5 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5285844393/10000000000 : ℝ)*x 0 + (-1974808341/10000000000 : ℝ)*x 1 + (5502855703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285844393/10000000000 : ℝ)^8365 ≤ (10746989119223/25000000000000 : ℝ)^6317 := by
    have hnat : (5285844393 : ℕ)^8365*25000000000000^6317 ≤ 10746989119223^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285844393 10000000000 10746989119223 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1974808341/10000000000 : ℝ)^8365 ≤ (11671614990303/100000000000000 : ℝ)^6317 := by
    have hnat : (1974808341 : ℕ)^8365*100000000000000^6317 ≤ 11671614990303^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974808341 10000000000 11671614990303 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5502855703/10000000000 : ℝ)^8365 ≤ (22670214259217/50000000000000 : ℝ)^6317 := by
    have hnat : (5502855703 : ℕ)^8365*50000000000000^6317 ≤ 22670214259217^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502855703 10000000000 22670214259217 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285844393/10000000000 : ℝ), (-1974808341/10000000000 : ℝ), (5502855703/10000000000 : ℝ)] ![(10746989119223/25000000000000 : ℝ), (11671614990303/100000000000000 : ℝ), (22670214259217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285844393/10000000000 : ℝ)|^8365 ≤ (10746989119223/25000000000000 : ℝ)^6317
        have hw : |(5285844393/10000000000 : ℝ)|=(5285844393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1974808341/10000000000 : ℝ)|^8365 ≤ (11671614990303/100000000000000 : ℝ)^6317
        have hw : |(-1974808341/10000000000 : ℝ)|=(1974808341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5502855703/10000000000 : ℝ)|^8365 ≤ (22670214259217/50000000000000 : ℝ)^6317
        have hw : |(5502855703/10000000000 : ℝ)|=(5502855703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s2_6 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (330365283/625000000 : ℝ)*x 0 + (5502855701/10000000000 : ℝ)*x 1 + (-987404079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330365283/625000000 : ℝ)^8365 ≤ (10746989482687/25000000000000 : ℝ)^6317 := by
    have hnat : (330365283 : ℕ)^8365*25000000000000^6317 ≤ 10746989482687^6317*625000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330365283 625000000 10746989482687 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5502855701/10000000000 : ℝ)^8365 ≤ (45340428496613/100000000000000 : ℝ)^6317 := by
    have hnat : (5502855701 : ℕ)^8365*100000000000000^6317 ≤ 45340428496613^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502855701 10000000000 45340428496613 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (987404079/5000000000 : ℝ)^8365 ≤ (466864542323/4000000000000 : ℝ)^6317 := by
    have hnat : (987404079 : ℕ)^8365*4000000000000^6317 ≤ 466864542323^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987404079 5000000000 466864542323 4000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330365283/625000000 : ℝ), (5502855701/10000000000 : ℝ), (-987404079/5000000000 : ℝ)] ![(10746989482687/25000000000000 : ℝ), (45340428496613/100000000000000 : ℝ), (466864542323/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330365283/625000000 : ℝ)|^8365 ≤ (10746989482687/25000000000000 : ℝ)^6317
        have hw : |(330365283/625000000 : ℝ)|=(330365283/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5502855701/10000000000 : ℝ)|^8365 ≤ (45340428496613/100000000000000 : ℝ)^6317
        have hw : |(5502855701/10000000000 : ℝ)|=(5502855701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-987404079/5000000000 : ℝ)|^8365 ≤ (466864542323/4000000000000 : ℝ)^6317
        have hw : |(-987404079/5000000000 : ℝ)|=(987404079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s2_7 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175288327/5000000000 : ℝ)*x 0 + (4700340779/10000000000 : ℝ)*x 1 + (2013421337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175288327/5000000000 : ℝ)^8365 ≤ (33217127173437/100000000000000 : ℝ)^6317 := by
    have hnat : (2175288327 : ℕ)^8365*100000000000000^6317 ≤ 33217127173437^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175288327 5000000000 33217127173437 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4700340779/10000000000 : ℝ)^8365 ≤ (36798676176629/100000000000000 : ℝ)^6317 := by
    have hnat : (4700340779 : ℕ)^8365*100000000000000^6317 ≤ 36798676176629^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4700340779 10000000000 36798676176629 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2013421337/5000000000 : ℝ)^8365 ≤ (29984196640081/100000000000000 : ℝ)^6317 := by
    have hnat : (2013421337 : ℕ)^8365*100000000000000^6317 ≤ 29984196640081^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013421337 5000000000 29984196640081 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175288327/5000000000 : ℝ), (4700340779/10000000000 : ℝ), (2013421337/5000000000 : ℝ)] ![(33217127173437/100000000000000 : ℝ), (36798676176629/100000000000000 : ℝ), (29984196640081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175288327/5000000000 : ℝ)|^8365 ≤ (33217127173437/100000000000000 : ℝ)^6317
        have hw : |(2175288327/5000000000 : ℝ)|=(2175288327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4700340779/10000000000 : ℝ)|^8365 ≤ (36798676176629/100000000000000 : ℝ)^6317
        have hw : |(4700340779/10000000000 : ℝ)|=(4700340779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2013421337/5000000000 : ℝ)|^8365 ≤ (29984196640081/100000000000000 : ℝ)^6317
        have hw : |(2013421337/5000000000 : ℝ)|=(2013421337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1172_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10151/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (727/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2301/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3283/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10151/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (727/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10151/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (727/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10151/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (727/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10151/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (727/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10151/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (727/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10151/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (727/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (727/12500 : ℝ) ^ (2091/512 : ℝ) ≤ (112630330000971/12500000000000000000 : ℝ) := by
    have hpowers : (727/12500 : ℝ)^2091 ≤ (112630330000971/12500000000000000000 : ℝ)^512 := by
      have hnat : (727 : ℕ)^2091*12500000000000000000^512 ≤ 112630330000971^512*12500^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        727 12500 112630330000971 12500000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (727/12500 : ℝ)) (X := (112630330000971/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hpowhi : (10151/50000 : ℝ) ^ (2091/512 : ℝ) ≤ (29718670051913941/20000000000000000000 : ℝ) := by
    have hpowers : (10151/50000 : ℝ)^2091 ≤ (29718670051913941/20000000000000000000 : ℝ)^512 := by
      have hnat : (10151 : ℕ)^2091*20000000000000000000^512 ≤ 29718670051913941^512*50000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10151 50000 29718670051913941 20000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10151/50000 : ℝ)) (X := (29718670051913941/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250112630330000971/6250000000000000000 : ℝ) ≤ (10000044125365159/10000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (6250112630330000971/6250000000000000000 : ℝ)^512 ≤ (10000044125365159/10000000000000000 : ℝ)^2091 := by
      have hnat : (6250112630330000971 : ℕ)^512*10000000000000000^2091 ≤ 10000044125365159^2091*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250112630330000971 6250000000000000000 10000044125365159 10000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000044125365159/10000000000000000 : ℝ)) (X := (6250112630330000971/6250000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100149494392899577473/100000000000000000000 : ℝ) ≤ (2500914609798153/2500000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (100149494392899577473/100000000000000000000 : ℝ)^512 ≤ (2500914609798153/2500000000000000 : ℝ)^2091 := by
      have hnat : (100149494392899577473 : ℕ)^512*2500000000000000^2091 ≤ 2500914609798153^2091*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100149494392899577473 100000000000000000000 2500914609798153 2500000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500914609798153/2500000000000000 : ℝ)) (X := (100149494392899577473/100000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10029718670051913941/10000000000000000000 : ℝ) ≤ (2001454550604013/2000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (10029718670051913941/10000000000000000000 : ℝ)^512 ≤ (2001454550604013/2000000000000000 : ℝ)^2091 := by
      have hnat : (10029718670051913941 : ℕ)^512*2000000000000000^2091 ≤ 2001454550604013^2091*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10029718670051913941 10000000000000000000 2001454550604013 2000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001454550604013/2000000000000000 : ℝ)) (X := (10029718670051913941/10000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(112630330000971/12500000000000000000 : ℝ) ≤ ((72409298750799379989/72430000000000000000 : ℝ)+2*(3614313827453/1448600000000000 : ℝ)*(727/12500 : ℝ))^(2091/512 : ℝ) := by
    rw [show (72409298750799379989/72430000000000000000 : ℝ)+2*(3614313827453/1448600000000000 : ℝ)*(727/12500 : ℝ)=(10000044125365159/10000000000000000 : ℝ) by norm_num, show 1+2*(112630330000971/12500000000000000000 : ℝ)=(6250112630330000971/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29718670051913941/20000000000000000000 : ℝ)+(112630330000971/12500000000000000000 : ℝ) ≤ ((72409298750799379989/72430000000000000000 : ℝ)+(3614313827453/1448600000000000 : ℝ)*((10151/50000 : ℝ)+(727/12500 : ℝ)))^(2091/512 : ℝ) := by
    rw [show (72409298750799379989/72430000000000000000 : ℝ)+(3614313827453/1448600000000000 : ℝ)*((10151/50000 : ℝ)+(727/12500 : ℝ))=(2500914609798153/2500000000000000 : ℝ) by norm_num, show 1+(29718670051913941/20000000000000000000 : ℝ)+(112630330000971/12500000000000000000 : ℝ)=(100149494392899577473/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29718670051913941/20000000000000000000 : ℝ) ≤ ((72409298750799379989/72430000000000000000 : ℝ)+2*(3614313827453/1448600000000000 : ℝ)*(10151/50000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (72409298750799379989/72430000000000000000 : ℝ)+2*(3614313827453/1448600000000000 : ℝ)*(10151/50000 : ℝ)=(2001454550604013/2000000000000000 : ℝ) by norm_num, show 1+2*(29718670051913941/20000000000000000000 : ℝ)=(10029718670051913941/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (72409298750799379989/72430000000000000000 : ℝ)*(X 1 0+X 2 0)+(3614313827453/1448600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (727/12500 : ℝ)) (hi := (10151/50000 : ℝ)) (c := (72409298750799379989/72430000000000000000 : ℝ)) (alpha := (3614313827453/1448600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (72409298750799379989/72430000000000000000 : ℝ)*(X 0 1+X 2 1)+(3614313827453/1448600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (727/12500 : ℝ)) (hi := (10151/50000 : ℝ)) (c := (72409298750799379989/72430000000000000000 : ℝ)) (alpha := (3614313827453/1448600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (72409298750799379989/72430000000000000000 : ℝ)*(X 0 2+X 1 2)+(3614313827453/1448600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (727/12500 : ℝ)) (hi := (10151/50000 : ℝ)) (c := (72409298750799379989/72430000000000000000 : ℝ)) (alpha := (3614313827453/1448600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2136485467/10000000000 : ℝ)*X 0 0+(5505182081/10000000000 : ℝ)*X 0 1+(1291000599/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((537258231/1000000000 : ℝ)*X 1 0+(-1156829979/5000000000 : ℝ)*X 1 1+(1032801061/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((671572869/1250000000 : ℝ)*X 2 0+(1032800853/2000000000 : ℝ)*X 2 1+(-2313660463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350387081/10000000000 : ℝ)*X 0 0+(804437931/2000000000 : ℝ)*X 0 1+(4704949569/10000000000 : ℝ)*X 0 2+(4350387081/10000000000 : ℝ)*X 1 0+(804437931/2000000000 : ℝ)*X 1 1+(4704949569/10000000000 : ℝ)*X 1 2+(4350387081/10000000000 : ℝ)*X 2 0+(804437931/2000000000 : ℝ)*X 2 1+(4704949569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-534144841/2500000000 : ℝ)*X 0 0+(516630667/1000000000 : ℝ)*X 0 1+(687856963/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5285844393/10000000000 : ℝ)*X 1 0+(-1974808341/10000000000 : ℝ)*X 1 1+(5502855703/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330365283/625000000 : ℝ)*X 2 0+(5502855701/10000000000 : ℝ)*X 2 1+(-987404079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175288327/5000000000 : ℝ)*X 0 0+(4700340779/10000000000 : ℝ)*X 0 1+(2013421337/5000000000 : ℝ)*X 0 2+(2175288327/5000000000 : ℝ)*X 1 0+(4700340779/10000000000 : ℝ)*X 1 1+(2013421337/5000000000 : ℝ)*X 1 2+(2175288327/5000000000 : ℝ)*X 2 0+(4700340779/10000000000 : ℝ)*X 2 1+(2013421337/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3160258822821878259354017583/452687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (655461117/100000000000000 : ℝ)*(base19) + (803737637/100000000000000 : ℝ)*(base23) + (13390051/20000000000000 : ℝ)*(upper2) + (203772763/50000000000000 : ℝ)*(upper3) + (175461259/100000000000000 : ℝ)*(upper4) + (274732225170883/12500000000000 : ℝ)*(major0) + (274732225170883/12500000000000 : ℝ)*(major1) + (274732225170883/12500000000000 : ℝ)*(major2) + (2931034165160401/100000000000000 : ℝ)*(sp0) + (366381999956559/12500000000000 : ℝ)*(sp1) + (183190990710997/6250000000000 : ℝ)*(sp2) + (732324492392497/50000000000000 : ℝ)*(sp3) + (5622488297/25000000000000 : ℝ)*(sp4) + (4865066023/50000000000000 : ℝ)*(sp7) + (18308233936463/1250000000000 : ℝ)*(f.failure) + (732764163778397/25000000000000 : ℝ)*(f.sum) + (2253472818289/36215000000000000000000000000 : ℝ)*base66 + (12582688608453764713/905375000000000000000000000000000 : ℝ)*base68 + (11255883630766139713/905375000000000000000000000000000 : ℝ)*base70 + (4944589814858639713/905375000000000000000000000000000 : ℝ)*base72 + (391686269869/9053750000000000000000000000 : ℝ)*base73 + (11072326827680639713/905375000000000000000000000000000 : ℝ)*base76 + (12407595925372639713/905375000000000000000000000000000 : ℝ)*base78 + (8072379109063389713/905375000000000000000000000000000 : ℝ)*base80 + (45655784022493/18107500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1109403/125000000000000000000 : ℝ)*base89 + (1109403/125000000000000000000 : ℝ)*base91 + (1109403/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36325209850928693229411885561/3621500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2238177363/100000000000000 : ℝ)*(base19) + (2406237339/100000000000000 : ℝ)*(base23) + (66505349/25000000000000 : ℝ)*(upper3) + (572661/2500000000000 : ℝ)*(lower4) + (10761989/5000000000000 : ℝ)*(upper5) + (2228060274568339/100000000000000 : ℝ)*(major0) + (2228060274568339/100000000000000 : ℝ)*(major1) + (2228060274568339/100000000000000 : ℝ)*(major2) + (10922550653/50000000000000 : ℝ)*(sp1) + (6205275403/25000000000000 : ℝ)*(sp2) + (297133448548599/10000000000000 : ℝ)*(sp4) + (2971310402207321/100000000000000 : ℝ)*(sp5) + (2971307258147039/100000000000000 : ℝ)*(sp6) + (371196432325737/25000000000000 : ℝ)*(sp7) + (371196432325737/25000000000000 : ℝ)*(f.failure) + (297133448548599/10000000000000 : ℝ)*(f.sum) + (53392560915193/72430000000000000000000000000 : ℝ)*base66 + (13708411862881918271/7243000000000000000000000000000000 : ℝ)*base67 + (7817534233721918271/7243000000000000000000000000000000 : ℝ)*base69 + (37839160148122918271/7243000000000000000000000000000000 : ℝ)*base71 + (324605337925123/72430000000000000000000000000 : ℝ)*base74 + (27257434545702918271/7243000000000000000000000000000000 : ℝ)*base75 + (32743179438793918271/7243000000000000000000000000000000 : ℝ)*base77 + (11569979713664918271/7243000000000000000000000000000000 : ℝ)*base79 + (443980520184053/72430000000000000000000000000 : ℝ)*base82 + (9588797/2500000000000000000000 : ℝ)*base89 + (9588797/2500000000000000000000 : ℝ)*base91 + (9588797/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1172_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10151/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (727/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2301/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3283/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1172_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1172_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2301/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3283/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1172_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1172_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1172_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2301/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3283/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1172_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

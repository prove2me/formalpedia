-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1042_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:48:32.592707+00:00
-- url     : https://prove2.me/submissions/c5bf5dfd-dd3d-4e12-8d42-a5eb1f89a825

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
theorem support_rectangle_w1042_s9_0 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534502319/1000000000 : ℝ)*x 0 + (-2281972807/10000000000 : ℝ)*x 1 + (210561067/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534502319/1000000000 : ℝ)^8235 ≤ (21720328267439/50000000000000 : ℝ)^6187 := by
    have hnat : (534502319 : ℕ)^8235*50000000000000^6187 ≤ 21720328267439^6187*1000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534502319 1000000000 21720328267439 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2281972807/10000000000 : ℝ)^8235 ≤ (1399266851997/10000000000000 : ℝ)^6187 := by
    have hnat : (2281972807 : ℕ)^8235*10000000000000^6187 ≤ 1399266851997^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2281972807 10000000000 1399266851997 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210561067/400000000 : ℝ)^8235 ≤ (42566674929627/100000000000000 : ℝ)^6187 := by
    have hnat : (210561067 : ℕ)^8235*100000000000000^6187 ≤ 42566674929627^6187*400000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210561067 400000000 42566674929627 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534502319/1000000000 : ℝ), (-2281972807/10000000000 : ℝ), (210561067/400000000 : ℝ)] ![(21720328267439/50000000000000 : ℝ), (1399266851997/10000000000000 : ℝ), (42566674929627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534502319/1000000000 : ℝ)|^8235 ≤ (21720328267439/50000000000000 : ℝ)^6187
        have hw : |(534502319/1000000000 : ℝ)|=(534502319/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2281972807/10000000000 : ℝ)|^8235 ≤ (1399266851997/10000000000000 : ℝ)^6187
        have hw : |(-2281972807/10000000000 : ℝ)|=(2281972807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210561067/400000000 : ℝ)|^8235 ≤ (42566674929627/100000000000000 : ℝ)^6187
        have hw : |(210561067/400000000 : ℝ)|=(210561067/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s9_1 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2215647061/10000000000 : ℝ)*x 0 + (1052870787/2000000000 : ℝ)*x 1 + (5394420809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2215647061/10000000000 : ℝ)^8235 ≤ (1681745950033/12500000000000 : ℝ)^6187 := by
    have hnat : (2215647061 : ℕ)^8235*12500000000000^6187 ≤ 1681745950033^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215647061 10000000000 1681745950033 12500000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052870787/2000000000 : ℝ)^8235 ≤ (42570197279789/100000000000000 : ℝ)^6187 := by
    have hnat : (1052870787 : ℕ)^8235*100000000000000^6187 ≤ 42570197279789^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052870787 2000000000 42570197279789 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394420809/10000000000 : ℝ)^8235 ≤ (1759033404219/4000000000000 : ℝ)^6187 := by
    have hnat : (5394420809 : ℕ)^8235*4000000000000^6187 ≤ 1759033404219^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394420809 10000000000 1759033404219 4000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2215647061/10000000000 : ℝ), (1052870787/2000000000 : ℝ), (5394420809/10000000000 : ℝ)] ![(1681745950033/12500000000000 : ℝ), (42570197279789/100000000000000 : ℝ), (1759033404219/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2215647061/10000000000 : ℝ)|^8235 ≤ (1681745950033/12500000000000 : ℝ)^6187
        have hw : |(-2215647061/10000000000 : ℝ)|=(2215647061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052870787/2000000000 : ℝ)|^8235 ≤ (42570197279789/100000000000000 : ℝ)^6187
        have hw : |(1052870787/2000000000 : ℝ)|=(1052870787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394420809/10000000000 : ℝ)|^8235 ≤ (1759033404219/4000000000000 : ℝ)^6187
        have hw : |(5394420809/10000000000 : ℝ)|=(5394420809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s9_2 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328039941/2500000000 : ℝ)*x 0 + (-2151578539/10000000000 : ℝ)*x 1 + (5394421357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328039941/2500000000 : ℝ)^8235 ≤ (336605593183/781250000000 : ℝ)^6187 := by
    have hnat : (1328039941 : ℕ)^8235*781250000000^6187 ≤ 336605593183^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328039941 2500000000 336605593183 781250000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2151578539/10000000000 : ℝ)^8235 ≤ (12938642999219/100000000000000 : ℝ)^6187 := by
    have hnat : (2151578539 : ℕ)^8235*100000000000000^6187 ≤ 12938642999219^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151578539 10000000000 12938642999219 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394421357/10000000000 : ℝ)^8235 ≤ (4397584105159/10000000000000 : ℝ)^6187 := by
    have hnat : (5394421357 : ℕ)^8235*10000000000000^6187 ≤ 4397584105159^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394421357 10000000000 4397584105159 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328039941/2500000000 : ℝ), (-2151578539/10000000000 : ℝ), (5394421357/10000000000 : ℝ)] ![(336605593183/781250000000 : ℝ), (12938642999219/100000000000000 : ℝ), (4397584105159/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328039941/2500000000 : ℝ)|^8235 ≤ (336605593183/781250000000 : ℝ)^6187
        have hw : |(1328039941/2500000000 : ℝ)|=(1328039941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2151578539/10000000000 : ℝ)|^8235 ≤ (12938642999219/100000000000000 : ℝ)^6187
        have hw : |(-2151578539/10000000000 : ℝ)|=(2151578539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394421357/10000000000 : ℝ)|^8235 ≤ (4397584105159/10000000000000 : ℝ)^6187
        have hw : |(5394421357/10000000000 : ℝ)|=(5394421357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s9_3 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328040123/2500000000 : ℝ)*x 0 + (2697210221/5000000000 : ℝ)*x 1 + (-2151578799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328040123/2500000000 : ℝ)^8235 ≤ (10771380946641/25000000000000 : ℝ)^6187 := by
    have hnat : (1328040123 : ℕ)^8235*25000000000000^6187 ≤ 10771380946641^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328040123 2500000000 10771380946641 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697210221/5000000000 : ℝ)^8235 ≤ (21987915561657/50000000000000 : ℝ)^6187 := by
    have hnat : (2697210221 : ℕ)^8235*50000000000000^6187 ≤ 21987915561657^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697210221 5000000000 21987915561657 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2151578799/10000000000 : ℝ)^8235 ≤ (12938645080297/100000000000000 : ℝ)^6187 := by
    have hnat : (2151578799 : ℕ)^8235*100000000000000^6187 ≤ 12938645080297^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151578799 10000000000 12938645080297 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328040123/2500000000 : ℝ), (2697210221/5000000000 : ℝ), (-2151578799/10000000000 : ℝ)] ![(10771380946641/25000000000000 : ℝ), (21987915561657/50000000000000 : ℝ), (12938645080297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328040123/2500000000 : ℝ)|^8235 ≤ (10771380946641/25000000000000 : ℝ)^6187
        have hw : |(1328040123/2500000000 : ℝ)|=(1328040123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697210221/5000000000 : ℝ)|^8235 ≤ (21987915561657/50000000000000 : ℝ)^6187
        have hw : |(2697210221/5000000000 : ℝ)|=(2697210221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2151578799/10000000000 : ℝ)|^8235 ≤ (12938645080297/100000000000000 : ℝ)^6187
        have hw : |(-2151578799/10000000000 : ℝ)|=(2151578799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s9_4 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2189483441/5000000000 : ℝ)*x 0 + (281731123/625000000 : ℝ)*x 1 + (265874907/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189483441/5000000000 : ℝ)^8235 ≤ (33316525988869/100000000000000 : ℝ)^6187 := by
    have hnat : (2189483441 : ℕ)^8235*100000000000000^6187 ≤ 33316525988869^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189483441 5000000000 33316525988869 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281731123/625000000 : ℝ)^8235 ≤ (34626459663617/100000000000000 : ℝ)^6187 := by
    have hnat : (281731123 : ℕ)^8235*100000000000000^6187 ≤ 34626459663617^6187*625000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281731123 625000000 34626459663617 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265874907/625000000 : ℝ)^8235 ≤ (32057014332989/100000000000000 : ℝ)^6187 := by
    have hnat : (265874907 : ℕ)^8235*100000000000000^6187 ≤ 32057014332989^6187*625000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265874907 625000000 32057014332989 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189483441/5000000000 : ℝ), (281731123/625000000 : ℝ), (265874907/625000000 : ℝ)] ![(33316525988869/100000000000000 : ℝ), (34626459663617/100000000000000 : ℝ), (32057014332989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189483441/5000000000 : ℝ)|^8235 ≤ (33316525988869/100000000000000 : ℝ)^6187
        have hw : |(2189483441/5000000000 : ℝ)|=(2189483441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281731123/625000000 : ℝ)|^8235 ≤ (34626459663617/100000000000000 : ℝ)^6187
        have hw : |(281731123/625000000 : ℝ)|=(281731123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(265874907/625000000 : ℝ)|^8235 ≤ (32057014332989/100000000000000 : ℝ)^6187
        have hw : |(265874907/625000000 : ℝ)|=(265874907/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1042_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5609/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13987/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3497/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5609/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3497/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5609/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3497/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5609/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3497/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5609/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3497/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5609/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3497/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5609/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5609/50000 : ℝ) ^ (4117/1024 : ℝ) ≤ (15141802826488547/100000000000000000000 : ℝ) := by
    have hpowers : (5609/50000 : ℝ)^4117 ≤ (15141802826488547/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5609 : ℕ)^4117*100000000000000000000^1024 ≤ 15141802826488547^1024*50000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5609 50000 15141802826488547 100000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5609/50000 : ℝ)) (X := (15141802826488547/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3497/25000 : ℝ) ^ (4117/1024 : ℝ) ≤ (4596357751308379/12500000000000000000 : ℝ) := by
    have hpowers : (3497/25000 : ℝ)^4117 ≤ (4596357751308379/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3497 : ℕ)^4117*12500000000000000000^1024 ≤ 4596357751308379^1024*25000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3497 25000 4596357751308379 12500000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3497/25000 : ℝ)) (X := (4596357751308379/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015141802826488547/50000000000000000000 : ℝ) ≤ (10000753142705193/10000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (50015141802826488547/50000000000000000000 : ℝ)^1024 ≤ (10000753142705193/10000000000000000 : ℝ)^4117 := by
      have hnat : (50015141802826488547 : ℕ)^1024*10000000000000000^4117 ≤ 10000753142705193^4117*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015141802826488547 50000000000000000000 10000753142705193 10000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000753142705193/10000000000000000 : ℝ)) (X := (50015141802826488547/50000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051912664836955579/100000000000000000000 : ℝ) ≤ (10001290945004299/10000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (100051912664836955579/100000000000000000000 : ℝ)^1024 ≤ (10001290945004299/10000000000000000 : ℝ)^4117 := by
      have hnat : (100051912664836955579 : ℕ)^1024*10000000000000000^4117 ≤ 10001290945004299^4117*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051912664836955579 100000000000000000000 10001290945004299 10000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001290945004299/10000000000000000 : ℝ)) (X := (100051912664836955579/100000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254596357751308379/6250000000000000000 : ℝ) ≤ (2000365749460681/2000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (6254596357751308379/6250000000000000000 : ℝ)^1024 ≤ (2000365749460681/2000000000000000 : ℝ)^4117 := by
      have hnat : (6254596357751308379 : ℕ)^1024*2000000000000000^4117 ≤ 2000365749460681^4117*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254596357751308379 6250000000000000000 2000365749460681 2000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000365749460681/2000000000000000 : ℝ)) (X := (6254596357751308379/6250000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15141802826488547/100000000000000000000 : ℝ) ≤ ((13845010036455321197/13850000000000000000 : ℝ)+2*(268901149553/138500000000000 : ℝ)*(5609/50000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (13845010036455321197/13850000000000000000 : ℝ)+2*(268901149553/138500000000000 : ℝ)*(5609/50000 : ℝ)=(10000753142705193/10000000000000000 : ℝ) by norm_num, show 1+2*(15141802826488547/100000000000000000000 : ℝ)=(50015141802826488547/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4596357751308379/12500000000000000000 : ℝ)+(15141802826488547/100000000000000000000 : ℝ) ≤ ((13845010036455321197/13850000000000000000 : ℝ)+(268901149553/138500000000000 : ℝ)*((3497/25000 : ℝ)+(5609/50000 : ℝ)))^(4117/1024 : ℝ) := by
    rw [show (13845010036455321197/13850000000000000000 : ℝ)+(268901149553/138500000000000 : ℝ)*((3497/25000 : ℝ)+(5609/50000 : ℝ))=(10001290945004299/10000000000000000 : ℝ) by norm_num, show 1+(4596357751308379/12500000000000000000 : ℝ)+(15141802826488547/100000000000000000000 : ℝ)=(100051912664836955579/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4596357751308379/12500000000000000000 : ℝ) ≤ ((13845010036455321197/13850000000000000000 : ℝ)+2*(268901149553/138500000000000 : ℝ)*(3497/25000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (13845010036455321197/13850000000000000000 : ℝ)+2*(268901149553/138500000000000 : ℝ)*(3497/25000 : ℝ)=(2000365749460681/2000000000000000 : ℝ) by norm_num, show 1+2*(4596357751308379/12500000000000000000 : ℝ)=(6254596357751308379/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13845010036455321197/13850000000000000000 : ℝ)*(X 1 0+X 2 0)+(268901149553/138500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (3497/25000 : ℝ)) (c := (13845010036455321197/13850000000000000000 : ℝ)) (alpha := (268901149553/138500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13845010036455321197/13850000000000000000 : ℝ)*(X 0 1+X 2 1)+(268901149553/138500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (3497/25000 : ℝ)) (c := (13845010036455321197/13850000000000000000 : ℝ)) (alpha := (268901149553/138500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13845010036455321197/13850000000000000000 : ℝ)*(X 0 2+X 1 2)+(268901149553/138500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (3497/25000 : ℝ)) (c := (13845010036455321197/13850000000000000000 : ℝ)) (alpha := (268901149553/138500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((534502319/1000000000 : ℝ)*X 1 0+(-2281972807/10000000000 : ℝ)*X 1 1+(210561067/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s9_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2215647061/10000000000 : ℝ)*X 0 0+(1052870787/2000000000 : ℝ)*X 0 1+(5394420809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1328039941/2500000000 : ℝ)*X 1 0+(-2151578539/10000000000 : ℝ)*X 1 1+(5394421357/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1328040123/2500000000 : ℝ)*X 2 0+(2697210221/5000000000 : ℝ)*X 2 1+(-2151578799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2189483441/5000000000 : ℝ)*X 0 0+(281731123/625000000 : ℝ)*X 0 1+(265874907/625000000 : ℝ)*X 0 2+(2189483441/5000000000 : ℝ)*X 1 0+(281731123/625000000 : ℝ)*X 1 1+(265874907/625000000 : ℝ)*X 1 2+(2189483441/5000000000 : ℝ)*X 2 0+(281731123/625000000 : ℝ)*X 2 1+(265874907/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5418195253950556908290421/1352539062500000000000000000000 : ℝ) := by norm_num
    linear_combination (62973681/6250000000000 : ℝ)*(base23) + (11118099/5000000000000 : ℝ)*(lower1) + (55082713/25000000000000 : ℝ)*(lower2) + (9632747/6250000000000 : ℝ)*(upper3) + (207161659/100000000000000 : ℝ)*(lower4) + (679873/50000000000000 : ℝ)*(upper5) + (363437826971471/6250000000000 : ℝ)*(major0) + (363437826971471/6250000000000 : ℝ)*(major1) + (363437826971471/6250000000000 : ℝ)*(major2) + (137536389/4000000000000 : ℝ)*(sp0) + (3844169402937459/50000000000000 : ℝ)*(sp1) + (7688335367465193/100000000000000 : ℝ)*(sp2) + (7688337798296021/100000000000000 : ℝ)*(sp3) + (985417880920173/25000000000000 : ℝ)*(sp4) + (985417880920173/25000000000000 : ℝ)*(f.failure) + (3844169402937459/50000000000000 : ℝ)*(f.sum) + (14025464253321/3462500000000000000000000000 : ℝ)*base66 + (680838375793754213/86562500000000000000000000000000 : ℝ)*base68 + (64762283562495787/86562500000000000000000000000000 : ℝ)*base69 + (1315352179143754213/86562500000000000000000000000000 : ℝ)*base72 + (13895905808979/3462500000000000000000000000 : ℝ)*base73 + (189936845836879213/86562500000000000000000000000000 : ℝ)*base76 + (268412079459379213/86562500000000000000000000000000 : ℝ)*base78 + (919626135076254213/86562500000000000000000000000000 : ℝ)*base80 + (27273276128783/6925000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (14911697/1250000000000000000000 : ℝ)*base89 + (14911697/1250000000000000000000 : ℝ)*base91 + (14911697/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1042_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1042_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1042_box_0 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1668277/8000000 : ℝ)*x 0 + (336105601/625000000 : ℝ)*x 1 + (2688844789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1668277/8000000 : ℝ)^8235 ≤ (775701863137/6250000000000 : ℝ)^6187 := by
    have hnat : (1668277 : ℕ)^8235*6250000000000^6187 ≤ 775701863137^6187*8000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1668277 8000000 775701863137 6250000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336105601/625000000 : ℝ)^8235 ≤ (8758877058977/20000000000000 : ℝ)^6187 := by
    have hnat : (336105601 : ℕ)^8235*20000000000000^6187 ≤ 8758877058977^6187*625000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336105601 625000000 8758877058977 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688844789/5000000000 : ℝ)^8235 ≤ (43794384882987/100000000000000 : ℝ)^6187 := by
    have hnat : (2688844789 : ℕ)^8235*100000000000000^6187 ≤ 43794384882987^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688844789 5000000000 43794384882987 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1668277/8000000 : ℝ), (336105601/625000000 : ℝ), (2688844789/5000000000 : ℝ)] ![(775701863137/6250000000000 : ℝ), (8758877058977/20000000000000 : ℝ), (43794384882987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1668277/8000000 : ℝ)|^8235 ≤ (775701863137/6250000000000 : ℝ)^6187
        have hw : |(-1668277/8000000 : ℝ)|=(1668277/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336105601/625000000 : ℝ)|^8235 ≤ (8758877058977/20000000000000 : ℝ)^6187
        have hw : |(336105601/625000000 : ℝ)|=(336105601/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688844789/5000000000 : ℝ)|^8235 ≤ (43794384882987/100000000000000 : ℝ)^6187
        have hw : |(2688844789/5000000000 : ℝ)|=(2688844789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_box_1 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5294923363/10000000000 : ℝ)*x 0 + (-549330847/2500000000 : ℝ)*x 1 + (5377689697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294923363/10000000000 : ℝ)^8235 ≤ (1715981599071/4000000000000 : ℝ)^6187 := by
    have hnat : (5294923363 : ℕ)^8235*4000000000000^6187 ≤ 1715981599071^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294923363 10000000000 1715981599071 4000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549330847/2500000000 : ℝ)^8235 ≤ (6653036919039/50000000000000 : ℝ)^6187 := by
    have hnat : (549330847 : ℕ)^8235*50000000000000^6187 ≤ 6653036919039^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549330847 2500000000 6653036919039 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377689697/10000000000 : ℝ)^8235 ≤ (21897193086439/50000000000000 : ℝ)^6187 := by
    have hnat : (5377689697 : ℕ)^8235*50000000000000^6187 ≤ 21897193086439^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377689697 10000000000 21897193086439 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294923363/10000000000 : ℝ), (-549330847/2500000000 : ℝ), (5377689697/10000000000 : ℝ)] ![(1715981599071/4000000000000 : ℝ), (6653036919039/50000000000000 : ℝ), (21897193086439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294923363/10000000000 : ℝ)|^8235 ≤ (1715981599071/4000000000000 : ℝ)^6187
        have hw : |(5294923363/10000000000 : ℝ)|=(5294923363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-549330847/2500000000 : ℝ)|^8235 ≤ (6653036919039/50000000000000 : ℝ)^6187
        have hw : |(-549330847/2500000000 : ℝ)|=(549330847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377689697/10000000000 : ℝ)|^8235 ≤ (21897193086439/50000000000000 : ℝ)^6187
        have hw : |(5377689697/10000000000 : ℝ)|=(5377689697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_box_2 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647461677/5000000000 : ℝ)*x 0 + (5377689749/10000000000 : ℝ)*x 1 + (-219732333/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647461677/5000000000 : ℝ)^8235 ≤ (1072488496993/2500000000000 : ℝ)^6187 := by
    have hnat : (2647461677 : ℕ)^8235*2500000000000^6187 ≤ 1072488496993^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647461677 5000000000 1072488496993 2500000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377689749/10000000000 : ℝ)^8235 ≤ (43794386736529/100000000000000 : ℝ)^6187 := by
    have hnat : (5377689749 : ℕ)^8235*100000000000000^6187 ≤ 43794386736529^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377689749 10000000000 43794386736529 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219732333/1000000000 : ℝ)^8235 ≤ (6653036685297/50000000000000 : ℝ)^6187 := by
    have hnat : (219732333 : ℕ)^8235*50000000000000^6187 ≤ 6653036685297^6187*1000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219732333 1000000000 6653036685297 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647461677/5000000000 : ℝ), (5377689749/10000000000 : ℝ), (-219732333/1000000000 : ℝ)] ![(1072488496993/2500000000000 : ℝ), (43794386736529/100000000000000 : ℝ), (6653036685297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647461677/5000000000 : ℝ)|^8235 ≤ (1072488496993/2500000000000 : ℝ)^6187
        have hw : |(2647461677/5000000000 : ℝ)|=(2647461677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377689749/10000000000 : ℝ)|^8235 ≤ (43794386736529/100000000000000 : ℝ)^6187
        have hw : |(5377689749/10000000000 : ℝ)|=(5377689749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219732333/1000000000 : ℝ)|^8235 ≤ (6653036685297/50000000000000 : ℝ)^6187
        have hw : |(-219732333/1000000000 : ℝ)|=(219732333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_box_3 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4487623247/10000000000 : ℝ)*x 0 + (173072131/400000000 : ℝ)*x 1 + (4326803173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4487623247/10000000000 : ℝ)^8235 ≤ (8605339906497/25000000000000 : ℝ)^6187 := by
    have hnat : (4487623247 : ℕ)^8235*25000000000000^6187 ≤ 8605339906497^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487623247 10000000000 8605339906497 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173072131/400000000 : ℝ)^8235 ≤ (256166567893/781250000000 : ℝ)^6187 := by
    have hnat : (173072131 : ℕ)^8235*781250000000^6187 ≤ 256166567893^6187*400000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173072131 400000000 256166567893 781250000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4326803173/10000000000 : ℝ)^8235 ≤ (32789319661461/100000000000000 : ℝ)^6187 := by
    have hnat : (4326803173 : ℕ)^8235*100000000000000^6187 ≤ 32789319661461^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326803173 10000000000 32789319661461 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4487623247/10000000000 : ℝ), (173072131/400000000 : ℝ), (4326803173/10000000000 : ℝ)] ![(8605339906497/25000000000000 : ℝ), (256166567893/781250000000 : ℝ), (32789319661461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4487623247/10000000000 : ℝ)|^8235 ≤ (8605339906497/25000000000000 : ℝ)^6187
        have hw : |(4487623247/10000000000 : ℝ)|=(4487623247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(173072131/400000000 : ℝ)|^8235 ≤ (256166567893/781250000000 : ℝ)^6187
        have hw : |(173072131/400000000 : ℝ)|=(173072131/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4326803173/10000000000 : ℝ)|^8235 ≤ (32789319661461/100000000000000 : ℝ)^6187
        have hw : |(4326803173/10000000000 : ℝ)|=(4326803173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_box_4 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2347332209/10000000000 : ℝ)*x 0 + (659965331/1250000000 : ℝ)*x 1 + (1055944421/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2347332209/10000000000 : ℝ)^8235 ≤ (908038526931/6250000000000 : ℝ)^6187 := by
    have hnat : (2347332209 : ℕ)^8235*6250000000000^6187 ≤ 908038526931^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2347332209 10000000000 908038526931 6250000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659965331/1250000000 : ℝ)^8235 ≤ (5341961837461/12500000000000 : ℝ)^6187 := by
    have hnat : (659965331 : ℕ)^8235*12500000000000^6187 ≤ 5341961837461^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659965331 1250000000 5341961837461 12500000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055944421/2000000000 : ℝ)^8235 ≤ (5341961106199/12500000000000 : ℝ)^6187 := by
    have hnat : (1055944421 : ℕ)^8235*12500000000000^6187 ≤ 5341961106199^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055944421 2000000000 5341961106199 12500000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2347332209/10000000000 : ℝ), (659965331/1250000000 : ℝ), (1055944421/2000000000 : ℝ)] ![(908038526931/6250000000000 : ℝ), (5341961837461/12500000000000 : ℝ), (5341961106199/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2347332209/10000000000 : ℝ)|^8235 ≤ (908038526931/6250000000000 : ℝ)^6187
        have hw : |(-2347332209/10000000000 : ℝ)|=(2347332209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(659965331/1250000000 : ℝ)|^8235 ≤ (5341961837461/12500000000000 : ℝ)^6187
        have hw : |(659965331/1250000000 : ℝ)|=(659965331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055944421/2000000000 : ℝ)|^8235 ≤ (5341961106199/12500000000000 : ℝ)^6187
        have hw : |(1055944421/2000000000 : ℝ)|=(1055944421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_box_5 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5364294853/10000000000 : ℝ)*x 0 + (-1117774271/5000000000 : ℝ)*x 1 + (5279722299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364294853/10000000000 : ℝ)^8235 ≤ (43649253672551/100000000000000 : ℝ)^6187 := by
    have hnat : (5364294853 : ℕ)^8235*100000000000000^6187 ≤ 43649253672551^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364294853 10000000000 43649253672551 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1117774271/5000000000 : ℝ)^8235 ≤ (850940960239/6250000000000 : ℝ)^6187 := by
    have hnat : (1117774271 : ℕ)^8235*6250000000000^6187 ≤ 850940960239^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117774271 5000000000 850940960239 6250000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279722299/10000000000 : ℝ)^8235 ≤ (21367845469841/50000000000000 : ℝ)^6187 := by
    have hnat : (5279722299 : ℕ)^8235*50000000000000^6187 ≤ 21367845469841^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279722299 10000000000 21367845469841 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364294853/10000000000 : ℝ), (-1117774271/5000000000 : ℝ), (5279722299/10000000000 : ℝ)] ![(43649253672551/100000000000000 : ℝ), (850940960239/6250000000000 : ℝ), (21367845469841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364294853/10000000000 : ℝ)|^8235 ≤ (43649253672551/100000000000000 : ℝ)^6187
        have hw : |(5364294853/10000000000 : ℝ)|=(5364294853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1117774271/5000000000 : ℝ)|^8235 ≤ (850940960239/6250000000000 : ℝ)^6187
        have hw : |(-1117774271/5000000000 : ℝ)|=(1117774271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279722299/10000000000 : ℝ)|^8235 ≤ (21367845469841/50000000000000 : ℝ)^6187
        have hw : |(5279722299/10000000000 : ℝ)|=(5279722299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_box_6 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2682147323/5000000000 : ℝ)*x 0 + (2639861197/5000000000 : ℝ)*x 1 + (-1117774347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682147323/5000000000 : ℝ)^8235 ≤ (21824625715321/50000000000000 : ℝ)^6187 := by
    have hnat : (2682147323 : ℕ)^8235*50000000000000^6187 ≤ 21824625715321^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682147323 5000000000 21824625715321 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639861197/5000000000 : ℝ)^8235 ≤ (42735691963179/100000000000000 : ℝ)^6187 := by
    have hnat : (2639861197 : ℕ)^8235*100000000000000^6187 ≤ 42735691963179^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639861197 5000000000 42735691963179 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1117774347/5000000000 : ℝ)^8235 ≤ (13615056595971/100000000000000 : ℝ)^6187 := by
    have hnat : (1117774347 : ℕ)^8235*100000000000000^6187 ≤ 13615056595971^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117774347 5000000000 13615056595971 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682147323/5000000000 : ℝ), (2639861197/5000000000 : ℝ), (-1117774347/5000000000 : ℝ)] ![(21824625715321/50000000000000 : ℝ), (42735691963179/100000000000000 : ℝ), (13615056595971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682147323/5000000000 : ℝ)|^8235 ≤ (21824625715321/50000000000000 : ℝ)^6187
        have hw : |(2682147323/5000000000 : ℝ)|=(2682147323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639861197/5000000000 : ℝ)|^8235 ≤ (42735691963179/100000000000000 : ℝ)^6187
        have hw : |(2639861197/5000000000 : ℝ)|=(2639861197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1117774347/5000000000 : ℝ)|^8235 ≤ (13615056595971/100000000000000 : ℝ)^6187
        have hw : |(-1117774347/5000000000 : ℝ)|=(1117774347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_box_7 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4269971243/10000000000 : ℝ)*x 0 + (2217803861/5000000000 : ℝ)*x 1 + (22178037/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4269971243/10000000000 : ℝ)^8235 ≤ (32217323361809/100000000000000 : ℝ)^6187 := by
    have hnat : (4269971243 : ℕ)^8235*100000000000000^6187 ≤ 32217323361809^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4269971243 10000000000 32217323361809 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217803861/5000000000 : ℝ)^8235 ≤ (8472834987641/25000000000000 : ℝ)^6187 := by
    have hnat : (2217803861 : ℕ)^8235*25000000000000^6187 ≤ 8472834987641^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217803861 5000000000 8472834987641 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22178037/50000000 : ℝ)^8235 ≤ (16945668337919/50000000000000 : ℝ)^6187 := by
    have hnat : (22178037 : ℕ)^8235*50000000000000^6187 ≤ 16945668337919^6187*50000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22178037 50000000 16945668337919 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4269971243/10000000000 : ℝ), (2217803861/5000000000 : ℝ), (22178037/50000000 : ℝ)] ![(32217323361809/100000000000000 : ℝ), (8472834987641/25000000000000 : ℝ), (16945668337919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4269971243/10000000000 : ℝ)|^8235 ≤ (32217323361809/100000000000000 : ℝ)^6187
        have hw : |(4269971243/10000000000 : ℝ)|=(4269971243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2217803861/5000000000 : ℝ)|^8235 ≤ (8472834987641/25000000000000 : ℝ)^6187
        have hw : |(2217803861/5000000000 : ℝ)|=(2217803861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22178037/50000000 : ℝ)|^8235 ≤ (16945668337919/50000000000000 : ℝ)^6187
        have hw : |(22178037/50000000 : ℝ)|=(22178037/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_box_8 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2292671067/10000000000 : ℝ)*x 0 + (5213293317/10000000000 : ℝ)*x 1 + (5387287061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2292671067/10000000000 : ℝ)^8235 ≤ (880003173047/6250000000000 : ℝ)^6187 := by
    have hnat : (2292671067 : ℕ)^8235*6250000000000^6187 ≤ 880003173047^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292671067 10000000000 880003173047 6250000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213293317/10000000000 : ℝ)^8235 ≤ (10505375608737/25000000000000 : ℝ)^6187 := by
    have hnat : (5213293317 : ℕ)^8235*25000000000000^6187 ≤ 10505375608737^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213293317 10000000000 10505375608737 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387287061/10000000000 : ℝ)^8235 ≤ (43898446783317/100000000000000 : ℝ)^6187 := by
    have hnat : (5387287061 : ℕ)^8235*100000000000000^6187 ≤ 43898446783317^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387287061 10000000000 43898446783317 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2292671067/10000000000 : ℝ), (5213293317/10000000000 : ℝ), (5387287061/10000000000 : ℝ)] ![(880003173047/6250000000000 : ℝ), (10505375608737/25000000000000 : ℝ), (43898446783317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2292671067/10000000000 : ℝ)|^8235 ≤ (880003173047/6250000000000 : ℝ)^6187
        have hw : |(-2292671067/10000000000 : ℝ)|=(2292671067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213293317/10000000000 : ℝ)|^8235 ≤ (10505375608737/25000000000000 : ℝ)^6187
        have hw : |(5213293317/10000000000 : ℝ)|=(5213293317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387287061/10000000000 : ℝ)|^8235 ≤ (43898446783317/100000000000000 : ℝ)^6187
        have hw : |(5387287061/10000000000 : ℝ)|=(5387287061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_box_9 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644061679/5000000000 : ℝ)*x 0 + (-1096754007/5000000000 : ℝ)*x 1 + (336705429/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644061679/5000000000 : ℝ)^8235 ≤ (4282622489409/10000000000000 : ℝ)^6187 := by
    have hnat : (2644061679 : ℕ)^8235*10000000000000^6187 ≤ 4282622489409^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644061679 5000000000 4282622489409 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096754007/5000000000 : ℝ)^8235 ≤ (13275330453457/100000000000000 : ℝ)^6187 := by
    have hnat : (1096754007 : ℕ)^8235*100000000000000^6187 ≤ 13275330453457^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096754007 5000000000 13275330453457 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336705429/625000000 : ℝ)^8235 ≤ (4389844464669/10000000000000 : ℝ)^6187 := by
    have hnat : (336705429 : ℕ)^8235*10000000000000^6187 ≤ 4389844464669^6187*625000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336705429 625000000 4389844464669 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644061679/5000000000 : ℝ), (-1096754007/5000000000 : ℝ), (336705429/625000000 : ℝ)] ![(4282622489409/10000000000000 : ℝ), (13275330453457/100000000000000 : ℝ), (4389844464669/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644061679/5000000000 : ℝ)|^8235 ≤ (4282622489409/10000000000000 : ℝ)^6187
        have hw : |(2644061679/5000000000 : ℝ)|=(2644061679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1096754007/5000000000 : ℝ)|^8235 ≤ (13275330453457/100000000000000 : ℝ)^6187
        have hw : |(-1096754007/5000000000 : ℝ)|=(1096754007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336705429/625000000 : ℝ)|^8235 ≤ (4389844464669/10000000000000 : ℝ)^6187
        have hw : |(336705429/625000000 : ℝ)|=(336705429/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_box_10 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644061809/5000000000 : ℝ)*x 0 + (2693643487/5000000000 : ℝ)*x 1 + (-2193507517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644061809/5000000000 : ℝ)^8235 ≤ (8565245539343/20000000000000 : ℝ)^6187 := by
    have hnat : (2644061809 : ℕ)^8235*20000000000000^6187 ≤ 8565245539343^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644061809 5000000000 8565245539343 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693643487/5000000000 : ℝ)^8235 ≤ (43898445839731/100000000000000 : ℝ)^6187 := by
    have hnat : (2693643487 : ℕ)^8235*100000000000000^6187 ≤ 43898445839731^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693643487 5000000000 43898445839731 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2193507517/10000000000 : ℝ)^8235 ≤ (13275326449901/100000000000000 : ℝ)^6187 := by
    have hnat : (2193507517 : ℕ)^8235*100000000000000^6187 ≤ 13275326449901^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193507517 10000000000 13275326449901 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644061809/5000000000 : ℝ), (2693643487/5000000000 : ℝ), (-2193507517/10000000000 : ℝ)] ![(8565245539343/20000000000000 : ℝ), (43898445839731/100000000000000 : ℝ), (13275326449901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644061809/5000000000 : ℝ)|^8235 ≤ (8565245539343/20000000000000 : ℝ)^6187
        have hw : |(2644061809/5000000000 : ℝ)|=(2644061809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693643487/5000000000 : ℝ)|^8235 ≤ (43898445839731/100000000000000 : ℝ)^6187
        have hw : |(2693643487/5000000000 : ℝ)|=(2693643487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2193507517/10000000000 : ℝ)|^8235 ≤ (13275326449901/100000000000000 : ℝ)^6187
        have hw : |(-2193507517/10000000000 : ℝ)|=(2193507517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_box_11 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4508671627/10000000000 : ℝ)*x 0 + (2158069193/5000000000 : ℝ)*x 1 + (863227729/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4508671627/10000000000 : ℝ)^8235 ≤ (34636415074197/100000000000000 : ℝ)^6187 := by
    have hnat : (4508671627 : ℕ)^8235*100000000000000^6187 ≤ 34636415074197^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508671627 10000000000 34636415074197 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2158069193/5000000000 : ℝ)^8235 ≤ (32681791149359/100000000000000 : ℝ)^6187 := by
    have hnat : (2158069193 : ℕ)^8235*100000000000000^6187 ≤ 32681791149359^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158069193 5000000000 32681791149359 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (863227729/2000000000 : ℝ)^8235 ≤ (32681793759679/100000000000000 : ℝ)^6187 := by
    have hnat : (863227729 : ℕ)^8235*100000000000000^6187 ≤ 32681793759679^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863227729 2000000000 32681793759679 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4508671627/10000000000 : ℝ), (2158069193/5000000000 : ℝ), (863227729/2000000000 : ℝ)] ![(34636415074197/100000000000000 : ℝ), (32681791149359/100000000000000 : ℝ), (32681793759679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4508671627/10000000000 : ℝ)|^8235 ≤ (34636415074197/100000000000000 : ℝ)^6187
        have hw : |(4508671627/10000000000 : ℝ)|=(4508671627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2158069193/5000000000 : ℝ)|^8235 ≤ (32681791149359/100000000000000 : ℝ)^6187
        have hw : |(2158069193/5000000000 : ℝ)|=(2158069193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(863227729/2000000000 : ℝ)|^8235 ≤ (32681793759679/100000000000000 : ℝ)^6187
        have hw : |(863227729/2000000000 : ℝ)|=(863227729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_box_12 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2140392059/10000000000 : ℝ)*x 0 + (5442763973/10000000000 : ℝ)*x 1 + (32948341/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140392059/10000000000 : ℝ)^8235 ≤ (1284918191569/10000000000000 : ℝ)^6187 := by
    have hnat : (2140392059 : ℕ)^8235*10000000000000^6187 ≤ 1284918191569^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140392059 10000000000 1284918191569 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442763973/10000000000 : ℝ)^8235 ≤ (22250581362727/50000000000000 : ℝ)^6187 := by
    have hnat : (5442763973 : ℕ)^8235*50000000000000^6187 ≤ 22250581362727^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442763973 10000000000 22250581362727 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32948341/62500000 : ℝ)^8235 ≤ (42649655336919/100000000000000 : ℝ)^6187 := by
    have hnat : (32948341 : ℕ)^8235*100000000000000^6187 ≤ 42649655336919^6187*62500000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32948341 62500000 42649655336919 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2140392059/10000000000 : ℝ), (5442763973/10000000000 : ℝ), (32948341/62500000 : ℝ)] ![(1284918191569/10000000000000 : ℝ), (22250581362727/50000000000000 : ℝ), (42649655336919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2140392059/10000000000 : ℝ)|^8235 ≤ (1284918191569/10000000000000 : ℝ)^6187
        have hw : |(-2140392059/10000000000 : ℝ)|=(2140392059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442763973/10000000000 : ℝ)|^8235 ≤ (22250581362727/50000000000000 : ℝ)^6187
        have hw : |(5442763973/10000000000 : ℝ)|=(5442763973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32948341/62500000 : ℝ)|^8235 ≤ (42649655336919/100000000000000 : ℝ)^6187
        have hw : |(32948341/62500000 : ℝ)|=(32948341/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_box_13 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684974347/5000000000 : ℝ)*x 0 + (-1119303067/5000000000 : ℝ)*x 1 + (2635867279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684974347/5000000000 : ℝ)^8235 ≤ (2185524907929/5000000000000 : ℝ)^6187 := by
    have hnat : (2684974347 : ℕ)^8235*5000000000000^6187 ≤ 2185524907929^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684974347 5000000000 2185524907929 5000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119303067/5000000000 : ℝ)^8235 ≤ (13639846509509/100000000000000 : ℝ)^6187 := by
    have hnat : (1119303067 : ℕ)^8235*100000000000000^6187 ≤ 13639846509509^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119303067 5000000000 13639846509509 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2635867279/5000000000 : ℝ)^8235 ≤ (21324827657691/50000000000000 : ℝ)^6187 := by
    have hnat : (2635867279 : ℕ)^8235*50000000000000^6187 ≤ 21324827657691^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635867279 5000000000 21324827657691 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684974347/5000000000 : ℝ), (-1119303067/5000000000 : ℝ), (2635867279/5000000000 : ℝ)] ![(2185524907929/5000000000000 : ℝ), (13639846509509/100000000000000 : ℝ), (21324827657691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684974347/5000000000 : ℝ)|^8235 ≤ (2185524907929/5000000000000 : ℝ)^6187
        have hw : |(2684974347/5000000000 : ℝ)|=(2684974347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1119303067/5000000000 : ℝ)|^8235 ≤ (13639846509509/100000000000000 : ℝ)^6187
        have hw : |(-1119303067/5000000000 : ℝ)|=(1119303067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2635867279/5000000000 : ℝ)|^8235 ≤ (21324827657691/50000000000000 : ℝ)^6187
        have hw : |(2635867279/5000000000 : ℝ)|=(2635867279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_box_14 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1073989747/2000000000 : ℝ)*x 0 + (329483409/625000000 : ℝ)*x 1 + (-2238606097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073989747/2000000000 : ℝ)^8235 ≤ (1365953081337/3125000000000 : ℝ)^6187 := by
    have hnat : (1073989747 : ℕ)^8235*3125000000000^6187 ≤ 1365953081337^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073989747 2000000000 1365953081337 3125000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329483409/625000000 : ℝ)^8235 ≤ (21324827582313/50000000000000 : ℝ)^6187 := by
    have hnat : (329483409 : ℕ)^8235*50000000000000^6187 ≤ 21324827582313^6187*625000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329483409 625000000 21324827582313 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238606097/10000000000 : ℝ)^8235 ≤ (6819923104721/50000000000000 : ℝ)^6187 := by
    have hnat : (2238606097 : ℕ)^8235*50000000000000^6187 ≤ 6819923104721^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238606097 10000000000 6819923104721 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073989747/2000000000 : ℝ), (329483409/625000000 : ℝ), (-2238606097/10000000000 : ℝ)] ![(1365953081337/3125000000000 : ℝ), (21324827582313/50000000000000 : ℝ), (6819923104721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073989747/2000000000 : ℝ)|^8235 ≤ (1365953081337/3125000000000 : ℝ)^6187
        have hw : |(1073989747/2000000000 : ℝ)|=(1073989747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329483409/625000000 : ℝ)|^8235 ≤ (21324827582313/50000000000000 : ℝ)^6187
        have hw : |(329483409/625000000 : ℝ)|=(329483409/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2238606097/10000000000 : ℝ)|^8235 ≤ (6819923104721/50000000000000 : ℝ)^6187
        have hw : |(-2238606097/10000000000 : ℝ)|=(2238606097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_box_15 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4251995061/10000000000 : ℝ)*x 0 + (88889481/200000000 : ℝ)*x 1 + (4444473971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251995061/10000000000 : ℝ)^8235 ≤ (6407384180459/20000000000000 : ℝ)^6187 := by
    have hnat : (4251995061 : ℕ)^8235*20000000000000^6187 ≤ 6407384180459^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251995061 10000000000 6407384180459 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88889481/200000000 : ℝ)^8235 ≤ (679630798779/2000000000000 : ℝ)^6187 := by
    have hnat : (88889481 : ℕ)^8235*2000000000000^6187 ≤ 679630798779^6187*200000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88889481 200000000 679630798779 2000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4444473971/10000000000 : ℝ)^8235 ≤ (2123846195937/6250000000000 : ℝ)^6187 := by
    have hnat : (4444473971 : ℕ)^8235*6250000000000^6187 ≤ 2123846195937^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4444473971 10000000000 2123846195937 6250000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251995061/10000000000 : ℝ), (88889481/200000000 : ℝ), (4444473971/10000000000 : ℝ)] ![(6407384180459/20000000000000 : ℝ), (679630798779/2000000000000 : ℝ), (2123846195937/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251995061/10000000000 : ℝ)|^8235 ≤ (6407384180459/20000000000000 : ℝ)^6187
        have hw : |(4251995061/10000000000 : ℝ)|=(4251995061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(88889481/200000000 : ℝ)|^8235 ≤ (679630798779/2000000000000 : ℝ)^6187
        have hw : |(88889481/200000000 : ℝ)|=(88889481/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4444473971/10000000000 : ℝ)|^8235 ≤ (2123846195937/6250000000000 : ℝ)^6187
        have hw : |(4444473971/10000000000 : ℝ)|=(4444473971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1042_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59223/100000 : ℝ) ∧ (9937/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82897/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5609/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5609/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5609/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5609/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5609/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5609/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5609/50000 : ℝ) ^ (4117/1024 : ℝ) ≤ (15141802826488547/100000000000000000000 : ℝ) := by
    have hpowers : (5609/50000 : ℝ)^4117 ≤ (15141802826488547/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5609 : ℕ)^4117*100000000000000000000^1024 ≤ 15141802826488547^1024*50000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5609 50000 15141802826488547 100000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5609/50000 : ℝ)) (X := (15141802826488547/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13987/100000 : ℝ) ^ (4117/1024 : ℝ) ≤ (36760294268326851/100000000000000000000 : ℝ) := by
    have hpowers : (13987/100000 : ℝ)^4117 ≤ (36760294268326851/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13987 : ℕ)^4117*100000000000000000000^1024 ≤ 36760294268326851^1024*100000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13987 100000 36760294268326851 100000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13987/100000 : ℝ)) (X := (36760294268326851/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015141802826488547/50000000000000000000 : ℝ) ≤ (10000753142705193/10000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (50015141802826488547/50000000000000000000 : ℝ)^1024 ≤ (10000753142705193/10000000000000000 : ℝ)^4117 := by
      have hnat : (50015141802826488547 : ℕ)^1024*10000000000000000^4117 ≤ 10000753142705193^4117*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015141802826488547 50000000000000000000 10000753142705193 10000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000753142705193/10000000000000000 : ℝ)) (X := (50015141802826488547/50000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025951048547407699/50000000000000000000 : ℝ) ≤ (10001290682260799/10000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (50025951048547407699/50000000000000000000 : ℝ)^1024 ≤ (10001290682260799/10000000000000000 : ℝ)^4117 := by
      have hnat : (50025951048547407699 : ℕ)^1024*10000000000000000^4117 ≤ 10001290682260799^4117*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025951048547407699 50000000000000000000 10001290682260799 10000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001290682260799/10000000000000000 : ℝ)) (X := (50025951048547407699/50000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036760294268326851/50000000000000000000 : ℝ) ≤ (2000365644363281/2000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (50036760294268326851/50000000000000000000 : ℝ)^1024 ≤ (2000365644363281/2000000000000000 : ℝ)^4117 := by
      have hnat : (50036760294268326851 : ℕ)^1024*2000000000000000^4117 ≤ 2000365644363281^4117*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036760294268326851 50000000000000000000 2000365644363281 2000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000365644363281/2000000000000000 : ℝ)) (X := (50036760294268326851/50000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15141802826488547/100000000000000000000 : ℝ) ≤ ((389859510065931031/390000000000000000 : ℝ)+2*(268769777803/138450000000000 : ℝ)*(5609/50000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (389859510065931031/390000000000000000 : ℝ)+2*(268769777803/138450000000000 : ℝ)*(5609/50000 : ℝ)=(10000753142705193/10000000000000000 : ℝ) by norm_num, show 1+2*(15141802826488547/100000000000000000000 : ℝ)=(50015141802826488547/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36760294268326851/100000000000000000000 : ℝ)+(15141802826488547/100000000000000000000 : ℝ) ≤ ((389859510065931031/390000000000000000 : ℝ)+(268769777803/138450000000000 : ℝ)*((13987/100000 : ℝ)+(5609/50000 : ℝ)))^(4117/1024 : ℝ) := by
    rw [show (389859510065931031/390000000000000000 : ℝ)+(268769777803/138450000000000 : ℝ)*((13987/100000 : ℝ)+(5609/50000 : ℝ))=(10001290682260799/10000000000000000 : ℝ) by norm_num, show 1+(36760294268326851/100000000000000000000 : ℝ)+(15141802826488547/100000000000000000000 : ℝ)=(50025951048547407699/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36760294268326851/100000000000000000000 : ℝ) ≤ ((389859510065931031/390000000000000000 : ℝ)+2*(268769777803/138450000000000 : ℝ)*(13987/100000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (389859510065931031/390000000000000000 : ℝ)+2*(268769777803/138450000000000 : ℝ)*(13987/100000 : ℝ)=(2000365644363281/2000000000000000 : ℝ) by norm_num, show 1+2*(36760294268326851/100000000000000000000 : ℝ)=(50036760294268326851/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (389859510065931031/390000000000000000 : ℝ)*(X 1 0+X 2 0)+(268769777803/138450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (389859510065931031/390000000000000000 : ℝ)) (alpha := (268769777803/138450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (389859510065931031/390000000000000000 : ℝ)*(X 0 1+X 2 1)+(268769777803/138450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (389859510065931031/390000000000000000 : ℝ)) (alpha := (268769777803/138450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (389859510065931031/390000000000000000 : ℝ)*(X 0 2+X 1 2)+(268769777803/138450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (389859510065931031/390000000000000000 : ℝ)) (alpha := (268769777803/138450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1668277/8000000 : ℝ)*X 0 0+(336105601/625000000 : ℝ)*X 0 1+(2688844789/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5294923363/10000000000 : ℝ)*X 1 0+(-549330847/2500000000 : ℝ)*X 1 1+(5377689697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647461677/5000000000 : ℝ)*X 2 0+(5377689749/10000000000 : ℝ)*X 2 1+(-219732333/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4487623247/10000000000 : ℝ)*X 0 0+(173072131/400000000 : ℝ)*X 0 1+(4326803173/10000000000 : ℝ)*X 0 2+(4487623247/10000000000 : ℝ)*X 1 0+(173072131/400000000 : ℝ)*X 1 1+(4326803173/10000000000 : ℝ)*X 1 2+(4487623247/10000000000 : ℝ)*X 2 0+(173072131/400000000 : ℝ)*X 2 1+(4326803173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2347332209/10000000000 : ℝ)*X 0 0+(659965331/1250000000 : ℝ)*X 0 1+(1055944421/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5364294853/10000000000 : ℝ)*X 1 0+(-1117774271/5000000000 : ℝ)*X 1 1+(5279722299/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2682147323/5000000000 : ℝ)*X 2 0+(2639861197/5000000000 : ℝ)*X 2 1+(-1117774347/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4269971243/10000000000 : ℝ)*X 0 0+(2217803861/5000000000 : ℝ)*X 0 1+(22178037/50000000 : ℝ)*X 0 2+(4269971243/10000000000 : ℝ)*X 1 0+(2217803861/5000000000 : ℝ)*X 1 1+(22178037/50000000 : ℝ)*X 1 2+(4269971243/10000000000 : ℝ)*X 2 0+(2217803861/5000000000 : ℝ)*X 2 1+(22178037/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2292671067/10000000000 : ℝ)*X 0 0+(5213293317/10000000000 : ℝ)*X 0 1+(5387287061/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644061679/5000000000 : ℝ)*X 1 0+(-1096754007/5000000000 : ℝ)*X 1 1+(336705429/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644061809/5000000000 : ℝ)*X 2 0+(2693643487/5000000000 : ℝ)*X 2 1+(-2193507517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4508671627/10000000000 : ℝ)*X 0 0+(2158069193/5000000000 : ℝ)*X 0 1+(863227729/2000000000 : ℝ)*X 0 2+(4508671627/10000000000 : ℝ)*X 1 0+(2158069193/5000000000 : ℝ)*X 1 1+(863227729/2000000000 : ℝ)*X 1 2+(4508671627/10000000000 : ℝ)*X 2 0+(2158069193/5000000000 : ℝ)*X 2 1+(863227729/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2140392059/10000000000 : ℝ)*X 0 0+(5442763973/10000000000 : ℝ)*X 0 1+(32948341/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684974347/5000000000 : ℝ)*X 1 0+(-1119303067/5000000000 : ℝ)*X 1 1+(2635867279/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1073989747/2000000000 : ℝ)*X 2 0+(329483409/625000000 : ℝ)*X 2 1+(-2238606097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4251995061/10000000000 : ℝ)*X 0 0+(88889481/200000000 : ℝ)*X 0 1+(4444473971/10000000000 : ℝ)*X 0 2+(4251995061/10000000000 : ℝ)*X 1 0+(88889481/200000000 : ℝ)*X 1 1+(4444473971/10000000000 : ℝ)*X 1 2+(4251995061/10000000000 : ℝ)*X 2 0+(88889481/200000000 : ℝ)*X 2 1+(4444473971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-71787502239327772340467049644461/115375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2134849/3125000000000 : ℝ)*(upper0) + (6587363/50000000000000 : ℝ)*(upper1) + (137185363/50000000000000 : ℝ)*(upper3) + (959050045846913/25000000000000 : ℝ)*(major0) + (959050045846913/25000000000000 : ℝ)*(major1) + (959050045846913/25000000000000 : ℝ)*(major2) + (19575362689/100000000000000 : ℝ)*(sp1) + (437881593/10000000000000 : ℝ)*(sp2) + (7425562647/50000000000000 : ℝ)*(sp3) + (254639466122911/5000000000000 : ℝ)*(sp4) + (254638623918313/5000000000000 : ℝ)*(sp5) + (5092787674913019/100000000000000 : ℝ)*(sp6) + (1300166901020377/50000000000000 : ℝ)*(sp7) + (273127073/10000000000000 : ℝ)*(sp8) + (81260895411439/3125000000000 : ℝ)*(f.failure) + (5092792053728949/100000000000000 : ℝ)*(f.sum) + (13971507090319/6922500000000000000000000000 : ℝ)*base66 + (5632222273859931487/692250000000000000000000000000000 : ℝ)*base68 + (14963611666808931487/692250000000000000000000000000000 : ℝ)*base70 + (6267632677887681487/692250000000000000000000000000000 : ℝ)*base72 + (21087885797029/6922500000000000000000000000 : ℝ)*base74 + (4437790744500681487/692250000000000000000000000000000 : ℝ)*base76 + (8628317742583431487/692250000000000000000000000000000 : ℝ)*base78 + (2268490283143431487/692250000000000000000000000000000 : ℝ)*base80 + (54043867845451/1730625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1468971/156250000000000000000 : ℝ)*base89 + (1468971/156250000000000000000 : ℝ)*base91 + (1468971/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59223/100000 : ℝ) ≤ (34165697190996329598985198585577/57687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34126199/100000000000000 : ℝ)*(lower0) + (6824049/12500000000000 : ℝ)*(lower1) + (47973589/100000000000000 : ℝ)*(lower2) + (23310271/50000000000000 : ℝ)*(lower5) + (974678623031677/25000000000000 : ℝ)*(major0) + (974678623031677/25000000000000 : ℝ)*(major1) + (974678623031677/25000000000000 : ℝ)*(major2) + (5134963501227173/100000000000000 : ℝ)*(sp0) + (2567481418172691/50000000000000 : ℝ)*(sp1) + (641869406833587/12500000000000 : ℝ)*(sp2) + (660679678077787/25000000000000 : ℝ)*(sp3) + (664881791/100000000000000 : ℝ)*(sp5) + (8246558477/100000000000000 : ℝ)*(sp6) + (988992739/20000000000000 : ℝ)*(sp7) + (1321361828637421/50000000000000 : ℝ)*(f.failure) + (5134963501227173/100000000000000 : ℝ)*(f.sum) + (55380343424347/13845000000000000000000000000 : ℝ)*base66 + (32876789563004798077/692250000000000000000000000000000 : ℝ)*base67 + (7200830730810201923/692250000000000000000000000000000 : ℝ)*base70 + (1321858308162201923/692250000000000000000000000000000 : ℝ)*base72 + (29719789777799/1730625000000000000000000000 : ℝ)*base74 + (5542326944900451923/692250000000000000000000000000000 : ℝ)*base76 + (11066287145750451923/692250000000000000000000000000000 : ℝ)*base78 + (4379202517321701923/692250000000000000000000000000000 : ℝ)*base80 + (9468910474189/6922500000000000000000000000 : ℝ)*base81 + (2304431/2500000000000000000000 : ℝ)*base90 + (2304431/2500000000000000000000 : ℝ)*base92 + (2304431/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (9937/12500 : ℝ) ≤ (14111038330791336012747848671731/17750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (158880433/100000000000000 : ℝ)*(upper0) + (1935619/1562500000000 : ℝ)*(lower3) + (9099157/3125000000000 : ℝ)*(upper4) + (2183497945514301/50000000000000 : ℝ)*(major0) + (2183497945514301/50000000000000 : ℝ)*(major1) + (2183497945514301/50000000000000 : ℝ)*(major2) + (47268509351/50000000000000 : ℝ)*(sp1) + (60598599157/20000000000000 : ℝ)*(sp2) + (820219291/781250000000 : ℝ)*(sp3) + (3722023669/50000000000000 : ℝ)*(sp4) + (5747338929566367/100000000000000 : ℝ)*(sp8) + (5747251836595003/100000000000000 : ℝ)*(sp9) + (17959510564431/312500000000 : ℝ)*(sp10) + (2960040817875099/100000000000000 : ℝ)*(sp11) + (1480072902972173/50000000000000 : ℝ)*(f.failure) + (1149469274722741/20000000000000 : ℝ)*(f.sum) + (106693541141/177500000000000000000000000 : ℝ)*base66 + (600127900310603141/35500000000000000000000000000000 : ℝ)*base68 + (725162125805103141/35500000000000000000000000000000 : ℝ)*base70 + (443981911856603141/35500000000000000000000000000000 : ℝ)*base72 + (412441674509/44375000000000000000000000 : ℝ)*base74 + (462702461124603141/35500000000000000000000000000000 : ℝ)*base76 + (389595292381603141/35500000000000000000000000000000 : ℝ)*base78 + (1603709410021603141/35500000000000000000000000000000 : ℝ)*base80 + (353166546987/355000000000000000000000000 : ℝ)*base82 + (8739697/2500000000000000000000 : ℝ)*base89 + (8739697/2500000000000000000000 : ℝ)*base91 + (8739697/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-82897/100000 : ℝ) ≤ (-747188209627430164328567924517/901367187500000000000000000000 : ℝ) := by norm_num
    linear_combination (743311/3125000000000 : ℝ)*(lower0) + (3421971/20000000000000 : ℝ)*(lower1) + (419/1280000000 : ℝ)*(lower2) + (34385843352891/781250000000 : ℝ)*(major0) + (34385843352891/781250000000 : ℝ)*(major1) + (34385843352891/781250000000 : ℝ)*(major2) + (419961203/12500000000000 : ℝ)*(sp0) + (539595283/800000000000 : ℝ)*(sp5) + (51949909589/100000000000000 : ℝ)*(sp6) + (4013761101/25000000000000 : ℝ)*(sp7) + (1169389182878551/20000000000000 : ℝ)*(sp12) + (1461720456168001/25000000000000 : ℝ)*(sp13) + (5846897324172789/100000000000000 : ℝ)*(sp14) + (372930278928199/12500000000000 : ℝ)*(sp15) + (745864571617499/25000000000000 : ℝ)*(f.failure) + (5846949274082379/100000000000000 : ℝ)*(f.sum) + (928889860789/4615000000000000000000000000 : ℝ)*base66 + (137964495957333731/14421875000000000000000000000000 : ℝ)*base68 + (92856015185627803/7210937500000000000000000000000 : ℝ)*base70 + (303455549771458731/14421875000000000000000000000000 : ℝ)*base72 + (47665051413983/2307500000000000000000000000 : ℝ)*base73 + (150302215353364981/14421875000000000000000000000000 : ℝ)*base76 + (221442237062614981/14421875000000000000000000000000 : ℝ)*base78 + (224162322345787661/3605468750000000000000000000000 : ℝ)*base79 + (2658136794099/4615000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (14444311/1250000000000000000000 : ℝ)*base89 + (14444311/1250000000000000000000 : ℝ)*base91 + (14444311/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1042_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59223/100000 : ℝ) else (9937/12500 : ℝ) ≤ X j i ∧ X j i ≤ (82897/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1042_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1042_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59223/100000 : ℝ) else (9937/12500 : ℝ) ≤ X j i ∧ X j i ≤ (82897/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1042_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1042_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59223/100000 : ℝ) else (9937/12500 : ℝ) ≤ X j i ∧ X j i ≤ (82897/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1042_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

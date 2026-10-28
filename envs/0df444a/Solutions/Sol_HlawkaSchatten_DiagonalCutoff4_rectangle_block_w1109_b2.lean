-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1109_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:04:14.322746+00:00
-- url     : https://prove2.me/submissions/f297b96d-d2e4-4cb7-8cd2-249a8cfd5e53

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
theorem support_rectangle_w1109_s6_0 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2182731599/10000000000 : ℝ)*x 0 + (2697020339/5000000000 : ℝ)*x 1 + (105295981/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182731599/10000000000 : ℝ)^4151 ≤ (3314992173343/25000000000000 : ℝ)^3127 := by
    have hnat : (2182731599 : ℕ)^4151*25000000000000^3127 ≤ 3314992173343^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182731599 10000000000 3314992173343 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697020339/5000000000 : ℝ)^4151 ≤ (11017018085241/25000000000000 : ℝ)^3127 := by
    have hnat : (2697020339 : ℕ)^4151*25000000000000^3127 ≤ 11017018085241^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697020339 5000000000 11017018085241 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105295981/200000000 : ℝ)^4151 ≤ (42671958950321/100000000000000 : ℝ)^3127 := by
    have hnat : (105295981 : ℕ)^4151*100000000000000^3127 ≤ 42671958950321^3127*200000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105295981 200000000 42671958950321 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2182731599/10000000000 : ℝ), (2697020339/5000000000 : ℝ), (105295981/200000000 : ℝ)] ![(3314992173343/25000000000000 : ℝ), (11017018085241/25000000000000 : ℝ), (42671958950321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2182731599/10000000000 : ℝ)|^4151 ≤ (3314992173343/25000000000000 : ℝ)^3127
        have hw : |(-2182731599/10000000000 : ℝ)|=(2182731599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697020339/5000000000 : ℝ)|^4151 ≤ (11017018085241/25000000000000 : ℝ)^3127
        have hw : |(2697020339/5000000000 : ℝ)|=(2697020339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105295981/200000000 : ℝ)|^4151 ≤ (42671958950321/100000000000000 : ℝ)^3127
        have hw : |(105295981/200000000 : ℝ)|=(105295981/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s6_1 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267248681/500000000 : ℝ)*x 0 + (-2248299587/10000000000 : ℝ)*x 1 + (5264799103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267248681/500000000 : ℝ)^4151 ≤ (43536728010009/100000000000000 : ℝ)^3127 := by
    have hnat : (267248681 : ℕ)^4151*100000000000000^3127 ≤ 43536728010009^3127*500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267248681 500000000 43536728010009 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248299587/10000000000 : ℝ)^4151 ≤ (3447828112163/25000000000000 : ℝ)^3127 := by
    have hnat : (2248299587 : ℕ)^4151*25000000000000^3127 ≤ 3447828112163^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248299587 10000000000 3447828112163 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264799103/10000000000 : ℝ)^4151 ≤ (21335979760283/50000000000000 : ℝ)^3127 := by
    have hnat : (5264799103 : ℕ)^4151*50000000000000^3127 ≤ 21335979760283^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264799103 10000000000 21335979760283 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267248681/500000000 : ℝ), (-2248299587/10000000000 : ℝ), (5264799103/10000000000 : ℝ)] ![(43536728010009/100000000000000 : ℝ), (3447828112163/25000000000000 : ℝ), (21335979760283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267248681/500000000 : ℝ)|^4151 ≤ (43536728010009/100000000000000 : ℝ)^3127
        have hw : |(267248681/500000000 : ℝ)|=(267248681/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2248299587/10000000000 : ℝ)|^4151 ≤ (3447828112163/25000000000000 : ℝ)^3127
        have hw : |(-2248299587/10000000000 : ℝ)|=(2248299587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264799103/10000000000 : ℝ)|^4151 ≤ (21335979760283/50000000000000 : ℝ)^3127
        have hw : |(5264799103/10000000000 : ℝ)|=(5264799103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s6_2 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068994703/2000000000 : ℝ)*x 0 + (5264799091/10000000000 : ℝ)*x 1 + (-2248299743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068994703/2000000000 : ℝ)^4151 ≤ (43536726874673/100000000000000 : ℝ)^3127 := by
    have hnat : (1068994703 : ℕ)^4151*100000000000000^3127 ≤ 43536726874673^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068994703 2000000000 43536726874673 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264799091/10000000000 : ℝ)^4151 ≤ (42671959391453/100000000000000 : ℝ)^3127 := by
    have hnat : (5264799091 : ℕ)^4151*100000000000000^3127 ≤ 42671959391453^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264799091 10000000000 42671959391453 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248299743/10000000000 : ℝ)^4151 ≤ (13791313718937/100000000000000 : ℝ)^3127 := by
    have hnat : (2248299743 : ℕ)^4151*100000000000000^3127 ≤ 13791313718937^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248299743 10000000000 13791313718937 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068994703/2000000000 : ℝ), (5264799091/10000000000 : ℝ), (-2248299743/10000000000 : ℝ)] ![(43536726874673/100000000000000 : ℝ), (42671959391453/100000000000000 : ℝ), (13791313718937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068994703/2000000000 : ℝ)|^4151 ≤ (43536726874673/100000000000000 : ℝ)^3127
        have hw : |(1068994703/2000000000 : ℝ)|=(1068994703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264799091/10000000000 : ℝ)|^4151 ≤ (42671959391453/100000000000000 : ℝ)^3127
        have hw : |(5264799091/10000000000 : ℝ)|=(5264799091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2248299743/10000000000 : ℝ)|^4151 ≤ (13791313718937/100000000000000 : ℝ)^3127
        have hw : |(-2248299743/10000000000 : ℝ)|=(2248299743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s6_3 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (873864419/2000000000 : ℝ)*x 0 + (2121732487/5000000000 : ℝ)*x 1 + (224946217/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873864419/2000000000 : ℝ)^4151 ≤ (130142857313/390625000000 : ℝ)^3127 := by
    have hnat : (873864419 : ℕ)^4151*390625000000^3127 ≤ 130142857313^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873864419 2000000000 130142857313 390625000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121732487/5000000000 : ℝ)^4151 ≤ (16024339671429/50000000000000 : ℝ)^3127 := by
    have hnat : (2121732487 : ℕ)^4151*50000000000000^3127 ≤ 16024339671429^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121732487 5000000000 16024339671429 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224946217/500000000 : ℝ)^4151 ≤ (8658687293/25000000000 : ℝ)^3127 := by
    have hnat : (224946217 : ℕ)^4151*25000000000^3127 ≤ 8658687293^3127*500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224946217 500000000 8658687293 25000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873864419/2000000000 : ℝ), (2121732487/5000000000 : ℝ), (224946217/500000000 : ℝ)] ![(130142857313/390625000000 : ℝ), (16024339671429/50000000000000 : ℝ), (8658687293/25000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873864419/2000000000 : ℝ)|^4151 ≤ (130142857313/390625000000 : ℝ)^3127
        have hw : |(873864419/2000000000 : ℝ)|=(873864419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2121732487/5000000000 : ℝ)|^4151 ≤ (16024339671429/50000000000000 : ℝ)^3127
        have hw : |(2121732487/5000000000 : ℝ)|=(2121732487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224946217/500000000 : ℝ)|^4151 ≤ (8658687293/25000000000 : ℝ)^3127
        have hw : |(224946217/500000000 : ℝ)|=(224946217/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s6_4 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2182736771/10000000000 : ℝ)*x 0 + (5265125393/10000000000 : ℝ)*x 1 + (1078742613/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182736771/10000000000 : ℝ)^4151 ≤ (663000520099/5000000000000 : ℝ)^3127 := by
    have hnat : (2182736771 : ℕ)^4151*5000000000000^3127 ≤ 663000520099^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182736771 10000000000 663000520099 5000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265125393/10000000000 : ℝ)^4151 ≤ (42675470221263/100000000000000 : ℝ)^3127 := by
    have hnat : (5265125393 : ℕ)^4151*100000000000000^3127 ≤ 42675470221263^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265125393 10000000000 42675470221263 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078742613/2000000000 : ℝ)^4151 ≤ (22032259685663/50000000000000 : ℝ)^3127 := by
    have hnat : (1078742613 : ℕ)^4151*50000000000000^3127 ≤ 22032259685663^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078742613 2000000000 22032259685663 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2182736771/10000000000 : ℝ), (5265125393/10000000000 : ℝ), (1078742613/2000000000 : ℝ)] ![(663000520099/5000000000000 : ℝ), (42675470221263/100000000000000 : ℝ), (22032259685663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2182736771/10000000000 : ℝ)|^4151 ≤ (663000520099/5000000000000 : ℝ)^3127
        have hw : |(-2182736771/10000000000 : ℝ)|=(2182736771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265125393/10000000000 : ℝ)|^4151 ≤ (42675470221263/100000000000000 : ℝ)^3127
        have hw : |(5265125393/10000000000 : ℝ)|=(5265125393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078742613/2000000000 : ℝ)|^4151 ≤ (22032259685663/50000000000000 : ℝ)^3127
        have hw : |(1078742613/2000000000 : ℝ)|=(1078742613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s6_5 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312310999/10000000000 : ℝ)*x 0 + (-2119385643/10000000000 : ℝ)*x 1 + (2696856519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312310999/10000000000 : ℝ)^4151 ≤ (43183909999069/100000000000000 : ℝ)^3127 := by
    have hnat : (5312310999 : ℕ)^4151*100000000000000^3127 ≤ 43183909999069^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312310999 10000000000 43183909999069 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119385643/10000000000 : ℝ)^4151 ≤ (12751570917387/100000000000000 : ℝ)^3127 := by
    have hnat : (2119385643 : ℕ)^4151*100000000000000^3127 ≤ 12751570917387^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119385643 10000000000 12751570917387 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696856519/5000000000 : ℝ)^4151 ≤ (22032259539257/50000000000000 : ℝ)^3127 := by
    have hnat : (2696856519 : ℕ)^4151*50000000000000^3127 ≤ 22032259539257^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696856519 5000000000 22032259539257 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312310999/10000000000 : ℝ), (-2119385643/10000000000 : ℝ), (2696856519/5000000000 : ℝ)] ![(43183909999069/100000000000000 : ℝ), (12751570917387/100000000000000 : ℝ), (22032259539257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312310999/10000000000 : ℝ)|^4151 ≤ (43183909999069/100000000000000 : ℝ)^3127
        have hw : |(5312310999/10000000000 : ℝ)|=(5312310999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2119385643/10000000000 : ℝ)|^4151 ≤ (12751570917387/100000000000000 : ℝ)^3127
        have hw : |(-2119385643/10000000000 : ℝ)|=(2119385643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696856519/5000000000 : ℝ)|^4151 ≤ (22032259539257/50000000000000 : ℝ)^3127
        have hw : |(2696856519/5000000000 : ℝ)|=(2696856519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s6_6 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328077753/2500000000 : ℝ)*x 0 + (5393713007/10000000000 : ℝ)*x 1 + (-423877133/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328077753/2500000000 : ℝ)^4151 ≤ (5397988767419/12500000000000 : ℝ)^3127 := by
    have hnat : (1328077753 : ℕ)^4151*12500000000000^3127 ≤ 5397988767419^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328077753 2500000000 5397988767419 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393713007/10000000000 : ℝ)^4151 ≤ (44064518742321/100000000000000 : ℝ)^3127 := by
    have hnat : (5393713007 : ℕ)^4151*100000000000000^3127 ≤ 44064518742321^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393713007 10000000000 44064518742321 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423877133/2000000000 : ℝ)^4151 ≤ (12751571093099/100000000000000 : ℝ)^3127 := by
    have hnat : (423877133 : ℕ)^4151*100000000000000^3127 ≤ 12751571093099^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423877133 2000000000 12751571093099 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328077753/2500000000 : ℝ), (5393713007/10000000000 : ℝ), (-423877133/2000000000 : ℝ)] ![(5397988767419/12500000000000 : ℝ), (44064518742321/100000000000000 : ℝ), (12751571093099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328077753/2500000000 : ℝ)|^4151 ≤ (5397988767419/12500000000000 : ℝ)^3127
        have hw : |(1328077753/2500000000 : ℝ)|=(1328077753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393713007/10000000000 : ℝ)|^4151 ≤ (44064518742321/100000000000000 : ℝ)^3127
        have hw : |(5393713007/10000000000 : ℝ)|=(5393713007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423877133/2000000000 : ℝ)|^4151 ≤ (12751571093099/100000000000000 : ℝ)^3127
        have hw : |(-423877133/2000000000 : ℝ)|=(423877133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s6_7 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4369332307/10000000000 : ℝ)*x 0 + (4498279173/10000000000 : ℝ)*x 1 + (1061028067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369332307/10000000000 : ℝ)^4151 ≤ (6663334967833/20000000000000 : ℝ)^3127 := by
    have hnat : (4369332307 : ℕ)^4151*20000000000000^3127 ≤ 6663334967833^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369332307 10000000000 6663334967833 20000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498279173/10000000000 : ℝ)^4151 ≤ (17314078032251/50000000000000 : ℝ)^3127 := by
    have hnat : (4498279173 : ℕ)^4151*50000000000000^3127 ≤ 17314078032251^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498279173 10000000000 17314078032251 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061028067/2500000000 : ℝ)^4151 ≤ (16027584537679/50000000000000 : ℝ)^3127 := by
    have hnat : (1061028067 : ℕ)^4151*50000000000000^3127 ≤ 16027584537679^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061028067 2500000000 16027584537679 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369332307/10000000000 : ℝ), (4498279173/10000000000 : ℝ), (1061028067/2500000000 : ℝ)] ![(6663334967833/20000000000000 : ℝ), (17314078032251/50000000000000 : ℝ), (16027584537679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369332307/10000000000 : ℝ)|^4151 ≤ (6663334967833/20000000000000 : ℝ)^3127
        have hw : |(4369332307/10000000000 : ℝ)|=(4369332307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498279173/10000000000 : ℝ)|^4151 ≤ (17314078032251/50000000000000 : ℝ)^3127
        have hw : |(4498279173/10000000000 : ℝ)|=(4498279173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061028067/2500000000 : ℝ)|^4151 ≤ (16027584537679/50000000000000 : ℝ)^3127
        have hw : |(1061028067/2500000000 : ℝ)|=(1061028067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1109_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11301/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14039/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5633/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5633/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5633/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5633/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5633/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5633/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5633/50000 : ℝ) ^ (8301/2048 : ℝ) ≤ (1792757994327253/12500000000000000000 : ℝ) := by
    have hpowers : (5633/50000 : ℝ)^8301 ≤ (1792757994327253/12500000000000000000 : ℝ)^2048 := by
      have hnat : (5633 : ℕ)^8301*12500000000000000000^2048 ≤ 1792757994327253^2048*50000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5633 50000 1792757994327253 12500000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5633/50000 : ℝ)) (X := (1792757994327253/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (563/4000 : ℝ) ^ (8301/2048 : ℝ) ≤ (17678352142022769/50000000000000000000 : ℝ) := by
    have hpowers : (563/4000 : ℝ)^8301 ≤ (17678352142022769/50000000000000000000 : ℝ)^2048 := by
      have hnat : (563 : ℕ)^8301*50000000000000000000^2048 ≤ 17678352142022769^2048*4000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        563 4000 17678352142022769 50000000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (563/4000 : ℝ)) (X := (17678352142022769/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251792757994327253/6250000000000000000 : ℝ) ≤ (2000141522101963/2000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (6251792757994327253/6250000000000000000 : ℝ)^2048 ≤ (2000141522101963/2000000000000000 : ℝ)^8301 := by
      have hnat : (6251792757994327253 : ℕ)^2048*2000000000000000^8301 ≤ 2000141522101963^8301*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251792757994327253 6250000000000000000 2000141522101963 2000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000141522101963/2000000000000000 : ℝ)) (X := (6251792757994327253/6250000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024849384119331781/50000000000000000000 : ℝ) ≤ (10001225924954889/10000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (50024849384119331781/50000000000000000000 : ℝ)^2048 ≤ (10001225924954889/10000000000000000 : ℝ)^8301 := by
      have hnat : (50024849384119331781 : ℕ)^2048*10000000000000000^8301 ≤ 10001225924954889^8301*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024849384119331781 50000000000000000000 10001225924954889 10000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001225924954889/10000000000000000 : ℝ)) (X := (50024849384119331781/50000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017678352142022769/25000000000000000000 : ℝ) ≤ (10001744239399963/10000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (25017678352142022769/25000000000000000000 : ℝ)^2048 ≤ (10001744239399963/10000000000000000 : ℝ)^8301 := by
      have hnat : (25017678352142022769 : ℕ)^2048*10000000000000000^8301 ≤ 10001744239399963^8301*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017678352142022769 25000000000000000000 10001744239399963 10000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001744239399963/10000000000000000 : ℝ)) (X := (25017678352142022769/25000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1792757994327253/12500000000000000000 : ℝ) ≤ ((28080309016845662967/28090000000000000000 : ℝ)+2*(259157222537/140450000000000 : ℝ)*(5633/50000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (28080309016845662967/28090000000000000000 : ℝ)+2*(259157222537/140450000000000 : ℝ)*(5633/50000 : ℝ)=(2000141522101963/2000000000000000 : ℝ) by norm_num, show 1+2*(1792757994327253/12500000000000000000 : ℝ)=(6251792757994327253/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17678352142022769/50000000000000000000 : ℝ)+(1792757994327253/12500000000000000000 : ℝ) ≤ ((28080309016845662967/28090000000000000000 : ℝ)+(259157222537/140450000000000 : ℝ)*((563/4000 : ℝ)+(5633/50000 : ℝ)))^(8301/2048 : ℝ) := by
    rw [show (28080309016845662967/28090000000000000000 : ℝ)+(259157222537/140450000000000 : ℝ)*((563/4000 : ℝ)+(5633/50000 : ℝ))=(10001225924954889/10000000000000000 : ℝ) by norm_num, show 1+(17678352142022769/50000000000000000000 : ℝ)+(1792757994327253/12500000000000000000 : ℝ)=(50024849384119331781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17678352142022769/50000000000000000000 : ℝ) ≤ ((28080309016845662967/28090000000000000000 : ℝ)+2*(259157222537/140450000000000 : ℝ)*(563/4000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (28080309016845662967/28090000000000000000 : ℝ)+2*(259157222537/140450000000000 : ℝ)*(563/4000 : ℝ)=(10001744239399963/10000000000000000 : ℝ) by norm_num, show 1+2*(17678352142022769/50000000000000000000 : ℝ)=(25017678352142022769/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28080309016845662967/28090000000000000000 : ℝ)*(X 1 0+X 2 0)+(259157222537/140450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (5633/50000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (28080309016845662967/28090000000000000000 : ℝ)) (alpha := (259157222537/140450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28080309016845662967/28090000000000000000 : ℝ)*(X 0 1+X 2 1)+(259157222537/140450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (5633/50000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (28080309016845662967/28090000000000000000 : ℝ)) (alpha := (259157222537/140450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28080309016845662967/28090000000000000000 : ℝ)*(X 0 2+X 1 2)+(259157222537/140450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (5633/50000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (28080309016845662967/28090000000000000000 : ℝ)) (alpha := (259157222537/140450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2182731599/10000000000 : ℝ)*X 0 0+(2697020339/5000000000 : ℝ)*X 0 1+(105295981/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267248681/500000000 : ℝ)*X 1 0+(-2248299587/10000000000 : ℝ)*X 1 1+(5264799103/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068994703/2000000000 : ℝ)*X 2 0+(5264799091/10000000000 : ℝ)*X 2 1+(-2248299743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873864419/2000000000 : ℝ)*X 0 0+(2121732487/5000000000 : ℝ)*X 0 1+(224946217/500000000 : ℝ)*X 0 2+(873864419/2000000000 : ℝ)*X 1 0+(2121732487/5000000000 : ℝ)*X 1 1+(224946217/500000000 : ℝ)*X 1 2+(873864419/2000000000 : ℝ)*X 2 0+(2121732487/5000000000 : ℝ)*X 2 1+(224946217/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2182736771/10000000000 : ℝ)*X 0 0+(5265125393/10000000000 : ℝ)*X 0 1+(1078742613/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312310999/10000000000 : ℝ)*X 1 0+(-2119385643/10000000000 : ℝ)*X 1 1+(2696856519/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328077753/2500000000 : ℝ)*X 2 0+(5393713007/10000000000 : ℝ)*X 2 1+(-423877133/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369332307/10000000000 : ℝ)*X 0 0+(4498279173/10000000000 : ℝ)*X 0 1+(1061028067/2500000000 : ℝ)*X 0 2+(4369332307/10000000000 : ℝ)*X 1 0+(4498279173/10000000000 : ℝ)*X 1 1+(1061028067/2500000000 : ℝ)*X 1 2+(4369332307/10000000000 : ℝ)*X 2 0+(4498279173/10000000000 : ℝ)*X 2 1+(1061028067/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5571319570791432060902111811/702250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56376769/5000000000000 : ℝ)*(base19) + (260505917/25000000000000 : ℝ)*(base23) + (89902039/50000000000000 : ℝ)*(upper3) + (40577887/100000000000000 : ℝ)*(lower4) + (5826033854526089/100000000000000 : ℝ)*(major0) + (5826033854526089/100000000000000 : ℝ)*(major1) + (5826033854526089/100000000000000 : ℝ)*(major2) + (7737487184380441/100000000000000 : ℝ)*(sp0) + (3868758353188401/50000000000000 : ℝ)*(sp1) + (1934378812228137/25000000000000 : ℝ)*(sp2) + (978633007605617/25000000000000 : ℝ)*(sp3) + (1532476587/5000000000000 : ℝ)*(sp4) + (771487983/50000000000000 : ℝ)*(sp6) + (17580266607/100000000000000 : ℝ)*(sp7) + (978637402672269/25000000000000 : ℝ)*(f.failure) + (3868758916956091/50000000000000 : ℝ)*(f.sum) + (11713201217659/3511250000000000000000000000 : ℝ)*base65 + (27878051923612246063/2809000000000000000000000000000000 : ℝ)*base67 + (24897407178047246063/2809000000000000000000000000000000 : ℝ)*base69 + (18723517024720246063/2809000000000000000000000000000000 : ℝ)*base71 + (10113964671481/14045000000000000000000000000 : ℝ)*base73 + (27810793698856753937/2809000000000000000000000000000000 : ℝ)*base76 + (33964194357972246063/2809000000000000000000000000000000 : ℝ)*base77 + (11202617772704246063/2809000000000000000000000000000000 : ℝ)*base79 + (179174867161/219453125000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (30320443/2500000000000000000000 : ℝ)*base89 + (30320443/2500000000000000000000 : ℝ)*base91 + (30320443/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3401656235433370799471054769/351125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1018407409/50000000000000 : ℝ)*(base19) + (536319789/25000000000000 : ℝ)*(base23) + (191259557/100000000000000 : ℝ)*(upper3) + (48925007/100000000000000 : ℝ)*(lower4) + (117384807/50000000000000 : ℝ)*(upper5) + (2927804453955669/50000000000000 : ℝ)*(major0) + (2927804453955669/50000000000000 : ℝ)*(major1) + (2927804453955669/50000000000000 : ℝ)*(major2) + (5631341931/10000000000000 : ℝ)*(sp1) + (55880339819/100000000000000 : ℝ)*(sp2) + (3888398106827409/50000000000000 : ℝ)*(sp4) + (7776737863420689/100000000000000 : ℝ)*(sp5) + (7776738188035843/100000000000000 : ℝ)*(sp6) + (196721063961929/5000000000000 : ℝ)*(sp7) + (196721063961929/5000000000000 : ℝ)*(f.failure) + (3888398106827409/50000000000000 : ℝ)*(f.sum) + (223581694411/7022500000000000000000000000 : ℝ)*base65 + (2931365527620609923/1404500000000000000000000000000000 : ℝ)*base67 + (17689094476361390077/1404500000000000000000000000000000 : ℝ)*base70 + (4117927777585890077/1404500000000000000000000000000000 : ℝ)*base72 + (15326296486577/14045000000000000000000000000 : ℝ)*base73 + (4265339857400390077/1404500000000000000000000000000000 : ℝ)*base76 + (307570387340890077/1404500000000000000000000000000000 : ℝ)*base78 + (6092576405081390077/1404500000000000000000000000000000 : ℝ)*base80 + (16395476536937/3511250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1666463/500000000000000000000 : ℝ)*base89 + (1666463/500000000000000000000 : ℝ)*base91 + (1666463/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1109_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1109_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1109_s7_0 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1091380967/5000000000 : ℝ)*x 0 + (5393669423/10000000000 : ℝ)*x 1 + (5265150521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091380967/5000000000 : ℝ)^4151 ≤ (663010666233/5000000000000 : ℝ)^3127 := by
    have hnat : (1091380967 : ℕ)^4151*5000000000000^3127 ≤ 663010666233^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091380967 5000000000 663010666233 5000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393669423/10000000000 : ℝ)^4151 ≤ (11016011519571/25000000000000 : ℝ)^3127 := by
    have hnat : (5393669423 : ℕ)^4151*25000000000000^3127 ≤ 11016011519571^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393669423 10000000000 11016011519571 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265150521/10000000000 : ℝ)^4151 ≤ (42675740587659/100000000000000 : ℝ)^3127 := by
    have hnat : (5265150521 : ℕ)^4151*100000000000000^3127 ≤ 42675740587659^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265150521 10000000000 42675740587659 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1091380967/5000000000 : ℝ), (5393669423/10000000000 : ℝ), (5265150521/10000000000 : ℝ)] ![(663010666233/5000000000000 : ℝ), (11016011519571/25000000000000 : ℝ), (42675740587659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1091380967/5000000000 : ℝ)|^4151 ≤ (663010666233/5000000000000 : ℝ)^3127
        have hw : |(-1091380967/5000000000 : ℝ)|=(1091380967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393669423/10000000000 : ℝ)|^4151 ≤ (11016011519571/25000000000000 : ℝ)^3127
        have hw : |(5393669423/10000000000 : ℝ)|=(5393669423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265150521/10000000000 : ℝ)|^4151 ≤ (42675740587659/100000000000000 : ℝ)^3127
        have hw : |(5265150521/10000000000 : ℝ)|=(5265150521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s7_1 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344881139/10000000000 : ℝ)*x 0 + (-56198951/250000000 : ℝ)*x 1 + (5265150521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344881139/10000000000 : ℝ)^4151 ≤ (43535728041417/100000000000000 : ℝ)^3127 := by
    have hnat : (5344881139 : ℕ)^4151*100000000000000^3127 ≤ 43535728041417^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344881139 10000000000 43535728041417 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56198951/250000000 : ℝ)^4151 ≤ (1723566419113/12500000000000 : ℝ)^3127 := by
    have hnat : (56198951 : ℕ)^4151*12500000000000^3127 ≤ 1723566419113^3127*250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56198951 250000000 1723566419113 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265150521/10000000000 : ℝ)^4151 ≤ (42675740587659/100000000000000 : ℝ)^3127 := by
    have hnat : (5265150521 : ℕ)^4151*100000000000000^3127 ≤ 42675740587659^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265150521 10000000000 42675740587659 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344881139/10000000000 : ℝ), (-56198951/250000000 : ℝ), (5265150521/10000000000 : ℝ)] ![(43535728041417/100000000000000 : ℝ), (1723566419113/12500000000000 : ℝ), (42675740587659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344881139/10000000000 : ℝ)|^4151 ≤ (43535728041417/100000000000000 : ℝ)^3127
        have hw : |(5344881139/10000000000 : ℝ)|=(5344881139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-56198951/250000000 : ℝ)|^4151 ≤ (1723566419113/12500000000000 : ℝ)^3127
        have hw : |(-56198951/250000000 : ℝ)|=(56198951/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265150521/10000000000 : ℝ)|^4151 ≤ (42675740587659/100000000000000 : ℝ)^3127
        have hw : |(5265150521/10000000000 : ℝ)|=(5265150521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s7_2 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344881139/10000000000 : ℝ)*x 0 + (5265150523/10000000000 : ℝ)*x 1 + (-1123979019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344881139/10000000000 : ℝ)^4151 ≤ (43535728041417/100000000000000 : ℝ)^3127 := by
    have hnat : (5344881139 : ℕ)^4151*100000000000000^3127 ≤ 43535728041417^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344881139 10000000000 43535728041417 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265150523/10000000000 : ℝ)^4151 ≤ (21337870304589/50000000000000 : ℝ)^3127 := by
    have hnat : (5265150523 : ℕ)^4151*50000000000000^3127 ≤ 21337870304589^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265150523 10000000000 21337870304589 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123979019/5000000000 : ℝ)^4151 ≤ (13788531336619/100000000000000 : ℝ)^3127 := by
    have hnat : (1123979019 : ℕ)^4151*100000000000000^3127 ≤ 13788531336619^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123979019 5000000000 13788531336619 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344881139/10000000000 : ℝ), (5265150523/10000000000 : ℝ), (-1123979019/5000000000 : ℝ)] ![(43535728041417/100000000000000 : ℝ), (21337870304589/50000000000000 : ℝ), (13788531336619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344881139/10000000000 : ℝ)|^4151 ≤ (43535728041417/100000000000000 : ℝ)^3127
        have hw : |(5344881139/10000000000 : ℝ)|=(5344881139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265150523/10000000000 : ℝ)|^4151 ≤ (21337870304589/50000000000000 : ℝ)^3127
        have hw : |(5265150523/10000000000 : ℝ)|=(5265150523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1123979019/5000000000 : ℝ)|^4151 ≤ (13788531336619/100000000000000 : ℝ)^3127
        have hw : |(-1123979019/5000000000 : ℝ)|=(1123979019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s7_3 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4369340747/10000000000 : ℝ)*x 0 + (4244176603/10000000000 : ℝ)*x 1 + (1124551923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369340747/10000000000 : ℝ)^4151 ≤ (33316760269873/100000000000000 : ℝ)^3127 := by
    have hnat : (4369340747 : ℕ)^4151*100000000000000^3127 ≤ 33316760269873^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369340747 10000000000 33316760269873 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4244176603/10000000000 : ℝ)^4151 ≤ (16027907056043/50000000000000 : ℝ)^3127 := by
    have hnat : (4244176603 : ℕ)^4151*50000000000000^3127 ≤ 16027907056043^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244176603 10000000000 16027907056043 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124551923/2500000000 : ℝ)^4151 ≤ (34627425603049/100000000000000 : ℝ)^3127 := by
    have hnat : (1124551923 : ℕ)^4151*100000000000000^3127 ≤ 34627425603049^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124551923 2500000000 34627425603049 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369340747/10000000000 : ℝ), (4244176603/10000000000 : ℝ), (1124551923/2500000000 : ℝ)] ![(33316760269873/100000000000000 : ℝ), (16027907056043/50000000000000 : ℝ), (34627425603049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369340747/10000000000 : ℝ)|^4151 ≤ (33316760269873/100000000000000 : ℝ)^3127
        have hw : |(4369340747/10000000000 : ℝ)|=(4369340747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4244176603/10000000000 : ℝ)|^4151 ≤ (16027907056043/50000000000000 : ℝ)^3127
        have hw : |(4244176603/10000000000 : ℝ)|=(4244176603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124551923/2500000000 : ℝ)|^4151 ≤ (34627425603049/100000000000000 : ℝ)^3127
        have hw : |(1124551923/2500000000 : ℝ)|=(1124551923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s7_4 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1091383463/5000000000 : ℝ)*x 0 + (2632736599/5000000000 : ℝ)*x 1 + (1078669113/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091383463/5000000000 : ℝ)^4151 ≤ (21216405731/160000000000 : ℝ)^3127 := by
    have hnat : (1091383463 : ℕ)^4151*160000000000^3127 ≤ 21216405731^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091383463 5000000000 21216405731 160000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632736599/5000000000 : ℝ)^4151 ≤ (1066980312249/2500000000000 : ℝ)^3127 := by
    have hnat : (2632736599 : ℕ)^4151*2500000000000^3127 ≤ 1066980312249^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632736599 5000000000 1066980312249 2500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078669113/2000000000 : ℝ)^4151 ≤ (44060533910463/100000000000000 : ℝ)^3127 := by
    have hnat : (1078669113 : ℕ)^4151*100000000000000^3127 ≤ 44060533910463^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078669113 2000000000 44060533910463 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1091383463/5000000000 : ℝ), (2632736599/5000000000 : ℝ), (1078669113/2000000000 : ℝ)] ![(21216405731/160000000000 : ℝ), (1066980312249/2500000000000 : ℝ), (44060533910463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1091383463/5000000000 : ℝ)|^4151 ≤ (21216405731/160000000000 : ℝ)^3127
        have hw : |(-1091383463/5000000000 : ℝ)|=(1091383463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632736599/5000000000 : ℝ)|^4151 ≤ (1066980312249/2500000000000 : ℝ)^3127
        have hw : |(2632736599/5000000000 : ℝ)|=(2632736599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078669113/2000000000 : ℝ)|^4151 ≤ (44060533910463/100000000000000 : ℝ)^3127
        have hw : |(1078669113/2000000000 : ℝ)|=(1078669113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s7_5 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656200499/5000000000 : ℝ)*x 0 + (-2119762961/10000000000 : ℝ)*x 1 + (5393345591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656200499/5000000000 : ℝ)^4151 ≤ (5398110148077/12500000000000 : ℝ)^3127 := by
    have hnat : (2656200499 : ℕ)^4151*12500000000000^3127 ≤ 5398110148077^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656200499 5000000000 5398110148077 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119762961/10000000000 : ℝ)^4151 ≤ (12754584608501/100000000000000 : ℝ)^3127 := by
    have hnat : (2119762961 : ℕ)^4151*100000000000000^3127 ≤ 12754584608501^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119762961 10000000000 12754584608501 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393345591/10000000000 : ℝ)^4151 ≤ (5507566774053/12500000000000 : ℝ)^3127 := by
    have hnat : (5393345591 : ℕ)^4151*12500000000000^3127 ≤ 5507566774053^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393345591 10000000000 5507566774053 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656200499/5000000000 : ℝ), (-2119762961/10000000000 : ℝ), (5393345591/10000000000 : ℝ)] ![(5398110148077/12500000000000 : ℝ), (12754584608501/100000000000000 : ℝ), (5507566774053/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656200499/5000000000 : ℝ)|^4151 ≤ (5398110148077/12500000000000 : ℝ)^3127
        have hw : |(2656200499/5000000000 : ℝ)|=(2656200499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2119762961/10000000000 : ℝ)|^4151 ≤ (12754584608501/100000000000000 : ℝ)^3127
        have hw : |(-2119762961/10000000000 : ℝ)|=(2119762961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393345591/10000000000 : ℝ)|^4151 ≤ (5507566774053/12500000000000 : ℝ)^3127
        have hw : |(5393345591/10000000000 : ℝ)|=(5393345591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s7_6 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312400993/10000000000 : ℝ)*x 0 + (5393345587/10000000000 : ℝ)*x 1 + (-2119762973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312400993/10000000000 : ℝ)^4151 ≤ (2159244056533/5000000000000 : ℝ)^3127 := by
    have hnat : (5312400993 : ℕ)^4151*5000000000000^3127 ≤ 2159244056533^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312400993 10000000000 2159244056533 5000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393345587/10000000000 : ℝ)^4151 ≤ (22030267074523/50000000000000 : ℝ)^3127 := by
    have hnat : (5393345587 : ℕ)^4151*50000000000000^3127 ≤ 22030267074523^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393345587 10000000000 22030267074523 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119762973/10000000000 : ℝ)^4151 ≤ (12754584704349/100000000000000 : ℝ)^3127 := by
    have hnat : (2119762973 : ℕ)^4151*100000000000000^3127 ≤ 12754584704349^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119762973 10000000000 12754584704349 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312400993/10000000000 : ℝ), (5393345587/10000000000 : ℝ), (-2119762973/10000000000 : ℝ)] ![(2159244056533/5000000000000 : ℝ), (22030267074523/50000000000000 : ℝ), (12754584704349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312400993/10000000000 : ℝ)|^4151 ≤ (2159244056533/5000000000000 : ℝ)^3127
        have hw : |(5312400993/10000000000 : ℝ)|=(5312400993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393345587/10000000000 : ℝ)|^4151 ≤ (22030267074523/50000000000000 : ℝ)^3127
        have hw : |(5393345587/10000000000 : ℝ)|=(5393345587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2119762973/10000000000 : ℝ)|^4151 ≤ (12754584704349/100000000000000 : ℝ)^3127
        have hw : |(-2119762973/10000000000 : ℝ)|=(2119762973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s7_7 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2184675293/5000000000 : ℝ)*x 0 + (2248784947/5000000000 : ℝ)*x 1 + (848963339/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184675293/5000000000 : ℝ)^4151 ≤ (33316859861499/100000000000000 : ℝ)^3127 := by
    have hnat : (2184675293 : ℕ)^4151*100000000000000^3127 ≤ 33316859861499^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184675293 5000000000 33316859861499 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248784947/5000000000 : ℝ)^4151 ≤ (8655227034829/25000000000000 : ℝ)^3127 := by
    have hnat : (2248784947 : ℕ)^4151*25000000000000^3127 ≤ 8655227034829^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248784947 5000000000 8655227034829 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848963339/2000000000 : ℝ)^4151 ≤ (8015557997087/25000000000000 : ℝ)^3127 := by
    have hnat : (848963339 : ℕ)^4151*25000000000000^3127 ≤ 8015557997087^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848963339 2000000000 8015557997087 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184675293/5000000000 : ℝ), (2248784947/5000000000 : ℝ), (848963339/2000000000 : ℝ)] ![(33316859861499/100000000000000 : ℝ), (8655227034829/25000000000000 : ℝ), (8015557997087/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184675293/5000000000 : ℝ)|^4151 ≤ (33316859861499/100000000000000 : ℝ)^3127
        have hw : |(2184675293/5000000000 : ℝ)|=(2184675293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248784947/5000000000 : ℝ)|^4151 ≤ (8655227034829/25000000000000 : ℝ)^3127
        have hw : |(2248784947/5000000000 : ℝ)|=(2248784947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848963339/2000000000 : ℝ)|^4151 ≤ (8015557997087/25000000000000 : ℝ)^3127
        have hw : |(848963339/2000000000 : ℝ)|=(848963339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1109_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11309/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14031/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11301/100000 : ℝ) ^ (8301/2048 : ℝ) ≤ (14523519247615069/100000000000000000000 : ℝ) := by
    have hpowers : (11301/100000 : ℝ)^8301 ≤ (14523519247615069/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11301 : ℕ)^8301*100000000000000000000^2048 ≤ 14523519247615069^2048*100000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11301 100000 14523519247615069 100000000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11301/100000 : ℝ)) (X := (14523519247615069/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14039/100000 : ℝ) ^ (8301/2048 : ℝ) ≤ (3499158882284837/10000000000000000000 : ℝ) := by
    have hpowers : (14039/100000 : ℝ)^8301 ≤ (3499158882284837/10000000000000000000 : ℝ)^2048 := by
      have hnat : (14039 : ℕ)^8301*10000000000000000000^2048 ≤ 3499158882284837^2048*100000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14039 100000 3499158882284837 10000000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14039/100000 : ℝ)) (X := (3499158882284837/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014523519247615069/50000000000000000000 : ℝ) ≤ (10000716562194083/10000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (50014523519247615069/50000000000000000000 : ℝ)^2048 ≤ (10000716562194083/10000000000000000 : ℝ)^8301 := by
      have hnat : (50014523519247615069 : ℕ)^2048*10000000000000000^8301 ≤ 10000716562194083^8301*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014523519247615069 50000000000000000000 10000716562194083 10000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000716562194083/10000000000000000 : ℝ)) (X := (50014523519247615069/50000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049515108070463439/100000000000000000000 : ℝ) ≤ (10001221395433977/10000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (100049515108070463439/100000000000000000000 : ℝ)^2048 ≤ (10001221395433977/10000000000000000 : ℝ)^8301 := by
      have hnat : (100049515108070463439 : ℕ)^2048*10000000000000000^8301 ≤ 10001221395433977^8301*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049515108070463439 100000000000000000000 10001221395433977 10000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001221395433977/10000000000000000 : ℝ)) (X := (100049515108070463439/100000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003499158882284837/5000000000000000000 : ℝ) ≤ (10001726228673871/10000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (5003499158882284837/5000000000000000000 : ℝ)^2048 ≤ (10001726228673871/10000000000000000 : ℝ)^8301 := by
      have hnat : (5003499158882284837 : ℕ)^2048*10000000000000000^8301 ≤ 10001726228673871^8301*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003499158882284837 5000000000000000000 10001726228673871 10000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001726228673871/10000000000000000 : ℝ)) (X := (5003499158882284837/5000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14523519247615069/100000000000000000000 : ℝ) ≤ ((13685275853199657533/13690000000000000000 : ℝ)+2*(252416619947/136900000000000 : ℝ)*(11301/100000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (13685275853199657533/13690000000000000000 : ℝ)+2*(252416619947/136900000000000 : ℝ)*(11301/100000 : ℝ)=(10000716562194083/10000000000000000 : ℝ) by norm_num, show 1+2*(14523519247615069/100000000000000000000 : ℝ)=(50014523519247615069/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3499158882284837/10000000000000000000 : ℝ)+(14523519247615069/100000000000000000000 : ℝ) ≤ ((13685275853199657533/13690000000000000000 : ℝ)+(252416619947/136900000000000 : ℝ)*((14039/100000 : ℝ)+(11301/100000 : ℝ)))^(8301/2048 : ℝ) := by
    rw [show (13685275853199657533/13690000000000000000 : ℝ)+(252416619947/136900000000000 : ℝ)*((14039/100000 : ℝ)+(11301/100000 : ℝ))=(10001221395433977/10000000000000000 : ℝ) by norm_num, show 1+(3499158882284837/10000000000000000000 : ℝ)+(14523519247615069/100000000000000000000 : ℝ)=(100049515108070463439/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3499158882284837/10000000000000000000 : ℝ) ≤ ((13685275853199657533/13690000000000000000 : ℝ)+2*(252416619947/136900000000000 : ℝ)*(14039/100000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (13685275853199657533/13690000000000000000 : ℝ)+2*(252416619947/136900000000000 : ℝ)*(14039/100000 : ℝ)=(10001726228673871/10000000000000000 : ℝ) by norm_num, show 1+2*(3499158882284837/10000000000000000000 : ℝ)=(5003499158882284837/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13685275853199657533/13690000000000000000 : ℝ)*(X 1 0+X 2 0)+(252416619947/136900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (11301/100000 : ℝ)) (hi := (14039/100000 : ℝ)) (c := (13685275853199657533/13690000000000000000 : ℝ)) (alpha := (252416619947/136900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13685275853199657533/13690000000000000000 : ℝ)*(X 0 1+X 2 1)+(252416619947/136900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (11301/100000 : ℝ)) (hi := (14039/100000 : ℝ)) (c := (13685275853199657533/13690000000000000000 : ℝ)) (alpha := (252416619947/136900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13685275853199657533/13690000000000000000 : ℝ)*(X 0 2+X 1 2)+(252416619947/136900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (11301/100000 : ℝ)) (hi := (14039/100000 : ℝ)) (c := (13685275853199657533/13690000000000000000 : ℝ)) (alpha := (252416619947/136900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1091380967/5000000000 : ℝ)*X 0 0+(5393669423/10000000000 : ℝ)*X 0 1+(5265150521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344881139/10000000000 : ℝ)*X 1 0+(-56198951/250000000 : ℝ)*X 1 1+(5265150521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344881139/10000000000 : ℝ)*X 2 0+(5265150523/10000000000 : ℝ)*X 2 1+(-1123979019/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369340747/10000000000 : ℝ)*X 0 0+(4244176603/10000000000 : ℝ)*X 0 1+(1124551923/2500000000 : ℝ)*X 0 2+(4369340747/10000000000 : ℝ)*X 1 0+(4244176603/10000000000 : ℝ)*X 1 1+(1124551923/2500000000 : ℝ)*X 1 2+(4369340747/10000000000 : ℝ)*X 2 0+(4244176603/10000000000 : ℝ)*X 2 1+(1124551923/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1091383463/5000000000 : ℝ)*X 0 0+(2632736599/5000000000 : ℝ)*X 0 1+(1078669113/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656200499/5000000000 : ℝ)*X 1 0+(-2119762961/10000000000 : ℝ)*X 1 1+(5393345591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312400993/10000000000 : ℝ)*X 2 0+(5393345587/10000000000 : ℝ)*X 2 1+(-2119762973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184675293/5000000000 : ℝ)*X 0 0+(2248784947/5000000000 : ℝ)*X 0 1+(848963339/2000000000 : ℝ)*X 0 2+(2184675293/5000000000 : ℝ)*X 1 0+(2248784947/5000000000 : ℝ)*X 1 1+(848963339/2000000000 : ℝ)*X 1 2+(2184675293/5000000000 : ℝ)*X 2 0+(2248784947/5000000000 : ℝ)*X 2 1+(848963339/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1480731780451879211135433219/684500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (220150121/50000000000000 : ℝ)*(base19) + (206689981/50000000000000 : ℝ)*(base23) + (3597143/25000000000000 : ℝ)*(lower2) + (13336743/25000000000000 : ℝ)*(upper3) + (1155979/3125000000000 : ℝ)*(upper5) + (5858759806627381/100000000000000 : ℝ)*(major0) + (5858759806627381/100000000000000 : ℝ)*(major1) + (5858759806627381/100000000000000 : ℝ)*(major2) + (1556193810363913/20000000000000 : ℝ)*(sp0) + (7780980712499311/100000000000000 : ℝ)*(sp1) + (7780980739419591/100000000000000 : ℝ)*(sp2) + (393653197085383/10000000000000 : ℝ)*(sp3) + (3025244997/25000000000000 : ℝ)*(sp4) + (1283498731/20000000000000 : ℝ)*(sp7) + (787307677669497/20000000000000 : ℝ)*(f.failure) + (3890490576399777/50000000000000 : ℝ)*(f.sum) + (25393918497317/6845000000000000000000000000 : ℝ)*base65 + (4814351755729588927/1369000000000000000000000000000000 : ℝ)*base68 + (9265891974091411073/1369000000000000000000000000000000 : ℝ)*base69 + (43322341346639588927/1369000000000000000000000000000000 : ℝ)*base72 + (37624397629907/6845000000000000000000000000 : ℝ)*base73 + (23732807077517411073/1369000000000000000000000000000000 : ℝ)*base75 + (11600693268119588927/1369000000000000000000000000000000 : ℝ)*base78 + (59119944341635588927/1369000000000000000000000000000000 : ℝ)*base80 + (88246459873/1711250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2875759/2000000000000000000000 : ℝ)*base89 + (2875759/2000000000000000000000 : ℝ)*base91 + (2875759/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (685117910460314714935044597/85562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1564798521/100000000000000 : ℝ)*(base19) + (331427803/20000000000000 : ℝ)*(base23) + (18050851/10000000000000 : ℝ)*(upper3) + (45739917/100000000000000 : ℝ)*(lower4) + (165847041/100000000000000 : ℝ)*(upper5) + (1472090582168203/25000000000000 : ℝ)*(major0) + (1472090582168203/25000000000000 : ℝ)*(major1) + (1472090582168203/25000000000000 : ℝ)*(major2) + (10933978569/25000000000000 : ℝ)*(sp1) + (22980202923/50000000000000 : ℝ)*(sp2) + (7820295877171819/100000000000000 : ℝ)*(sp4) + (7820250576459023/100000000000000 : ℝ)*(sp5) + (3910124129813479/50000000000000 : ℝ)*(sp6) + (3956428513266401/100000000000000 : ℝ)*(sp7) + (3956428513266401/100000000000000 : ℝ)*(f.failure) + (7820295877171819/100000000000000 : ℝ)*(f.sum) + (6650850759681/1711250000000000000000000000 : ℝ)*base65 + (2414378264289876801/342250000000000000000000000000000 : ℝ)*base68 + (6350273379691376801/342250000000000000000000000000000 : ℝ)*base70 + (8318966866817876801/342250000000000000000000000000000 : ℝ)*base72 + (8028107653369/6845000000000000000000000000 : ℝ)*base73 + (10469362558022876801/342250000000000000000000000000000 : ℝ)*base76 + (5154852806400376801/342250000000000000000000000000000 : ℝ)*base78 + (1497784066985623199/342250000000000000000000000000000 : ℝ)*base79 + (45239286393979/6845000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (37631047/10000000000000000000000 : ℝ)*base89 + (37631047/10000000000000000000000 : ℝ)*base91 + (37631047/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1109_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1109_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1109_s8_0 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2182767881/10000000000 : ℝ)*x 0 + (1348396811/2500000000 : ℝ)*x 1 + (5265228893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182767881/10000000000 : ℝ)^4151 ≤ (13260261283329/100000000000000 : ℝ)^3127 := by
    have hnat : (2182767881 : ℕ)^4151*100000000000000^3127 ≤ 13260261283329^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182767881 10000000000 13260261283329 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348396811/2500000000 : ℝ)^4151 ≤ (5507894357351/12500000000000 : ℝ)^3127 := by
    have hnat : (1348396811 : ℕ)^4151*12500000000000^3127 ≤ 5507894357351^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348396811 2500000000 5507894357351 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265228893/10000000000 : ℝ)^4151 ≤ (21338291919573/50000000000000 : ℝ)^3127 := by
    have hnat : (5265228893 : ℕ)^4151*50000000000000^3127 ≤ 21338291919573^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265228893 10000000000 21338291919573 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2182767881/10000000000 : ℝ), (1348396811/2500000000 : ℝ), (5265228893/10000000000 : ℝ)] ![(13260261283329/100000000000000 : ℝ), (5507894357351/12500000000000 : ℝ), (21338291919573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2182767881/10000000000 : ℝ)|^4151 ≤ (13260261283329/100000000000000 : ℝ)^3127
        have hw : |(-2182767881/10000000000 : ℝ)|=(2182767881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348396811/2500000000 : ℝ)|^4151 ≤ (5507894357351/12500000000000 : ℝ)^3127
        have hw : |(1348396811/2500000000 : ℝ)|=(1348396811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265228893/10000000000 : ℝ)|^4151 ≤ (21338291919573/50000000000000 : ℝ)^3127
        have hw : |(5265228893/10000000000 : ℝ)|=(5265228893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s8_1 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344860861/10000000000 : ℝ)*x 0 + (-1123940679/5000000000 : ℝ)*x 1 + (5265228929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344860861/10000000000 : ℝ)^4151 ≤ (43535508782401/100000000000000 : ℝ)^3127 := by
    have hnat : (5344860861 : ℕ)^4151*100000000000000^3127 ≤ 43535508782401^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344860861 10000000000 43535508782401 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123940679/5000000000 : ℝ)^4151 ≤ (13787906977669/100000000000000 : ℝ)^3127 := by
    have hnat : (1123940679 : ℕ)^4151*100000000000000^3127 ≤ 13787906977669^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123940679 5000000000 13787906977669 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265228929/10000000000 : ℝ)^4151 ≤ (10669146056623/25000000000000 : ℝ)^3127 := by
    have hnat : (5265228929 : ℕ)^4151*25000000000000^3127 ≤ 10669146056623^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265228929 10000000000 10669146056623 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344860861/10000000000 : ℝ), (-1123940679/5000000000 : ℝ), (5265228929/10000000000 : ℝ)] ![(43535508782401/100000000000000 : ℝ), (13787906977669/100000000000000 : ℝ), (10669146056623/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344860861/10000000000 : ℝ)|^4151 ≤ (43535508782401/100000000000000 : ℝ)^3127
        have hw : |(5344860861/10000000000 : ℝ)|=(5344860861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1123940679/5000000000 : ℝ)|^4151 ≤ (13787906977669/100000000000000 : ℝ)^3127
        have hw : |(-1123940679/5000000000 : ℝ)|=(1123940679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265228929/10000000000 : ℝ)|^4151 ≤ (10669146056623/25000000000000 : ℝ)^3127
        have hw : |(5265228929/10000000000 : ℝ)|=(5265228929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s8_2 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344860897/10000000000 : ℝ)*x 0 + (1053045781/2000000000 : ℝ)*x 1 + (-1123940671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344860897/10000000000 : ℝ)^4151 ≤ (5441938646457/12500000000000 : ℝ)^3127 := by
    have hnat : (5344860897 : ℕ)^4151*12500000000000^3127 ≤ 5441938646457^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344860897 10000000000 5441938646457 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053045781/2000000000 : ℝ)^4151 ≤ (42676583968261/100000000000000 : ℝ)^3127 := by
    have hnat : (1053045781 : ℕ)^4151*100000000000000^3127 ≤ 42676583968261^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053045781 2000000000 42676583968261 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123940671/5000000000 : ℝ)^4151 ≤ (430872088981/3125000000000 : ℝ)^3127 := by
    have hnat : (1123940671 : ℕ)^4151*3125000000000^3127 ≤ 430872088981^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123940671 5000000000 430872088981 3125000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344860897/10000000000 : ℝ), (1053045781/2000000000 : ℝ), (-1123940671/5000000000 : ℝ)] ![(5441938646457/12500000000000 : ℝ), (42676583968261/100000000000000 : ℝ), (430872088981/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344860897/10000000000 : ℝ)|^4151 ≤ (5441938646457/12500000000000 : ℝ)^3127
        have hw : |(5344860897/10000000000 : ℝ)|=(5344860897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053045781/2000000000 : ℝ)|^4151 ≤ (42676583968261/100000000000000 : ℝ)^3127
        have hw : |(1053045781/2000000000 : ℝ)|=(1053045781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1123940671/5000000000 : ℝ)|^4151 ≤ (430872088981/3125000000000 : ℝ)^3127
        have hw : |(-1123940671/5000000000 : ℝ)|=(1123940671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s8_3 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4369344829/10000000000 : ℝ)*x 0 + (2122167409/5000000000 : ℝ)*x 1 + (899609683/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369344829/10000000000 : ℝ)^4151 ≤ (6663360317679/20000000000000 : ℝ)^3127 := by
    have hnat : (4369344829 : ℕ)^4151*20000000000000^3127 ≤ 6663360317679^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369344829 10000000000 6663360317679 20000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122167409/5000000000 : ℝ)^4151 ≤ (32057400423769/100000000000000 : ℝ)^3127 := by
    have hnat : (2122167409 : ℕ)^4151*100000000000000^3127 ≤ 32057400423769^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122167409 5000000000 32057400423769 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899609683/2000000000 : ℝ)^4151 ≤ (34625797971489/100000000000000 : ℝ)^3127 := by
    have hnat : (899609683 : ℕ)^4151*100000000000000^3127 ≤ 34625797971489^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899609683 2000000000 34625797971489 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369344829/10000000000 : ℝ), (2122167409/5000000000 : ℝ), (899609683/2000000000 : ℝ)] ![(6663360317679/20000000000000 : ℝ), (32057400423769/100000000000000 : ℝ), (34625797971489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369344829/10000000000 : ℝ)|^4151 ≤ (6663360317679/20000000000000 : ℝ)^3127
        have hw : |(4369344829/10000000000 : ℝ)|=(4369344829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2122167409/5000000000 : ℝ)|^4151 ≤ (32057400423769/100000000000000 : ℝ)^3127
        have hw : |(2122167409/5000000000 : ℝ)|=(2122167409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899609683/2000000000 : ℝ)|^4151 ≤ (34625797971489/100000000000000 : ℝ)^3127
        have hw : |(899609683/2000000000 : ℝ)|=(899609683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s8_4 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-545693153/2500000000 : ℝ)*x 0 + (1316387713/2500000000 : ℝ)*x 1 + (5393264291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545693153/2500000000 : ℝ)^4151 ≤ (1657537429473/12500000000000 : ℝ)^3127 := by
    have hnat : (545693153 : ℕ)^4151*12500000000000^3127 ≤ 1657537429473^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545693153 2500000000 1657537429473 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316387713/2500000000 : ℝ)^4151 ≤ (21340024016401/50000000000000 : ℝ)^3127 := by
    have hnat : (1316387713 : ℕ)^4151*50000000000000^3127 ≤ 21340024016401^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316387713 2500000000 21340024016401 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393264291/10000000000 : ℝ)^4151 ≤ (44059652522889/100000000000000 : ℝ)^3127 := by
    have hnat : (5393264291 : ℕ)^4151*100000000000000^3127 ≤ 44059652522889^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393264291 10000000000 44059652522889 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-545693153/2500000000 : ℝ), (1316387713/2500000000 : ℝ), (5393264291/10000000000 : ℝ)] ![(1657537429473/12500000000000 : ℝ), (21340024016401/50000000000000 : ℝ), (44059652522889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-545693153/2500000000 : ℝ)|^4151 ≤ (1657537429473/12500000000000 : ℝ)^3127
        have hw : |(-545693153/2500000000 : ℝ)|=(545693153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316387713/2500000000 : ℝ)|^4151 ≤ (21340024016401/50000000000000 : ℝ)^3127
        have hw : |(1316387713/2500000000 : ℝ)|=(1316387713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393264291/10000000000 : ℝ)|^4151 ≤ (44059652522889/100000000000000 : ℝ)^3127
        have hw : |(5393264291/10000000000 : ℝ)|=(5393264291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s8_5 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312421147/10000000000 : ℝ)*x 0 + (-529961627/2500000000 : ℝ)*x 1 + (5393264007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312421147/10000000000 : ℝ)^4151 ≤ (5398137326829/12500000000000 : ℝ)^3127 := by
    have hnat : (5312421147 : ℕ)^4151*12500000000000^3127 ≤ 5398137326829^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312421147 10000000000 5398137326829 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529961627/2500000000 : ℝ)^4151 ≤ (6377625966857/50000000000000 : ℝ)^3127 := by
    have hnat : (529961627 : ℕ)^4151*50000000000000^3127 ≤ 6377625966857^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529961627 2500000000 6377625966857 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393264007/10000000000 : ℝ)^4151 ≤ (22029824721509/50000000000000 : ℝ)^3127 := by
    have hnat : (5393264007 : ℕ)^4151*50000000000000^3127 ≤ 22029824721509^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393264007 10000000000 22029824721509 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312421147/10000000000 : ℝ), (-529961627/2500000000 : ℝ), (5393264007/10000000000 : ℝ)] ![(5398137326829/12500000000000 : ℝ), (6377625966857/50000000000000 : ℝ), (22029824721509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312421147/10000000000 : ℝ)|^4151 ≤ (5398137326829/12500000000000 : ℝ)^3127
        have hw : |(5312421147/10000000000 : ℝ)|=(5312421147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-529961627/2500000000 : ℝ)|^4151 ≤ (6377625966857/50000000000000 : ℝ)^3127
        have hw : |(-529961627/2500000000 : ℝ)|=(529961627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393264007/10000000000 : ℝ)|^4151 ≤ (22029824721509/50000000000000 : ℝ)^3127
        have hw : |(5393264007/10000000000 : ℝ)|=(5393264007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s8_6 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656210791/5000000000 : ℝ)*x 0 + (2696631977/5000000000 : ℝ)*x 1 + (-211984599/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656210791/5000000000 : ℝ)^4151 ≤ (43185103308767/100000000000000 : ℝ)^3127 := by
    have hnat : (2656210791 : ℕ)^4151*100000000000000^3127 ≤ 43185103308767^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656210791 5000000000 43185103308767 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696631977/5000000000 : ℝ)^4151 ≤ (22029824434127/50000000000000 : ℝ)^3127 := by
    have hnat : (2696631977 : ℕ)^4151*50000000000000^3127 ≤ 22029824434127^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696631977 5000000000 22029824434127 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211984599/1000000000 : ℝ)^4151 ≤ (12755247796203/100000000000000 : ℝ)^3127 := by
    have hnat : (211984599 : ℕ)^4151*100000000000000^3127 ≤ 12755247796203^3127*1000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211984599 1000000000 12755247796203 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656210791/5000000000 : ℝ), (2696631977/5000000000 : ℝ), (-211984599/1000000000 : ℝ)] ![(43185103308767/100000000000000 : ℝ), (22029824434127/50000000000000 : ℝ), (12755247796203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656210791/5000000000 : ℝ)|^4151 ≤ (43185103308767/100000000000000 : ℝ)^3127
        have hw : |(2656210791/5000000000 : ℝ)|=(2656210791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696631977/5000000000 : ℝ)|^4151 ≤ (22029824434127/50000000000000 : ℝ)^3127
        have hw : |(2696631977/5000000000 : ℝ)|=(2696631977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-211984599/1000000000 : ℝ)|^4151 ≤ (12755247796203/100000000000000 : ℝ)^3127
        have hw : |(-211984599/1000000000 : ℝ)|=(211984599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s8_7 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1092338711/2500000000 : ℝ)*x 0 + (4497412091/10000000000 : ℝ)*x 1 + (848994643/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092338711/2500000000 : ℝ)^4151 ≤ (33316902961547/100000000000000 : ℝ)^3127 := by
    have hnat : (1092338711 : ℕ)^4151*100000000000000^3127 ≤ 33316902961547^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092338711 2500000000 33316902961547 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497412091/10000000000 : ℝ)^4151 ≤ (34619295645169/100000000000000 : ℝ)^3127 := by
    have hnat : (4497412091 : ℕ)^4151*100000000000000^3127 ≤ 34619295645169^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497412091 10000000000 34619295645169 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848994643/2000000000 : ℝ)^4151 ≤ (32063801382843/100000000000000 : ℝ)^3127 := by
    have hnat : (848994643 : ℕ)^4151*100000000000000^3127 ≤ 32063801382843^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848994643 2000000000 32063801382843 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092338711/2500000000 : ℝ), (4497412091/10000000000 : ℝ), (848994643/2000000000 : ℝ)] ![(33316902961547/100000000000000 : ℝ), (34619295645169/100000000000000 : ℝ), (32063801382843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092338711/2500000000 : ℝ)|^4151 ≤ (33316902961547/100000000000000 : ℝ)^3127
        have hw : |(1092338711/2500000000 : ℝ)|=(1092338711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497412091/10000000000 : ℝ)|^4151 ≤ (34619295645169/100000000000000 : ℝ)^3127
        have hw : |(4497412091/10000000000 : ℝ)|=(4497412091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848994643/2000000000 : ℝ)|^4151 ≤ (32063801382843/100000000000000 : ℝ)^3127
        have hw : |(848994643/2000000000 : ℝ)|=(848994643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1109_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1131/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14029/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11309/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11309/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11309/100000 : ℝ) ^ (8301/2048 : ℝ) ≤ (14565236409068551/100000000000000000000 : ℝ) := by
    have hpowers : (11309/100000 : ℝ)^8301 ≤ (14565236409068551/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11309 : ℕ)^8301*100000000000000000000^2048 ≤ 14565236409068551^2048*100000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11309 100000 14565236409068551 100000000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11309/100000 : ℝ)) (X := (14565236409068551/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14031/100000 : ℝ) ^ (8301/2048 : ℝ) ≤ (6982167854378087/20000000000000000000 : ℝ) := by
    have hpowers : (14031/100000 : ℝ)^8301 ≤ (6982167854378087/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14031 : ℕ)^8301*20000000000000000000^2048 ≤ 6982167854378087^2048*100000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14031 100000 6982167854378087 20000000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14031/100000 : ℝ)) (X := (6982167854378087/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014565236409068551/50000000000000000000 : ℝ) ≤ (2500179655052981/2500000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (50014565236409068551/50000000000000000000 : ℝ)^2048 ≤ (2500179655052981/2500000000000000 : ℝ)^8301 := by
      have hnat : (50014565236409068551 : ℕ)^2048*2500000000000000^8301 ≤ 2500179655052981^8301*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014565236409068551 50000000000000000000 2500179655052981 2500000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500179655052981/2500000000000000 : ℝ)) (X := (50014565236409068551/50000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024738037840479493/50000000000000000000 : ℝ) ≤ (2500305108199109/2500000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (50024738037840479493/50000000000000000000 : ℝ)^2048 ≤ (2500305108199109/2500000000000000 : ℝ)^8301 := by
      have hnat : (50024738037840479493 : ℕ)^2048*2500000000000000^8301 ≤ 2500305108199109^8301*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024738037840479493 50000000000000000000 2500305108199109 2500000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500305108199109/2500000000000000 : ℝ)) (X := (50024738037840479493/50000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006982167854378087/10000000000000000000 : ℝ) ≤ (2500430561345237/2500000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (10006982167854378087/10000000000000000000 : ℝ)^2048 ≤ (2500430561345237/2500000000000000 : ℝ)^8301 := by
      have hnat : (10006982167854378087 : ℕ)^2048*2500000000000000^8301 ≤ 2500430561345237^8301*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006982167854378087 10000000000000000000 2500430561345237 2500000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500430561345237/2500000000000000 : ℝ)) (X := (10006982167854378087/10000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14565236409068551/100000000000000000000 : ℝ) ≤ ((3401325760897545589/3402500000000000000 : ℝ)+2*(7840821633/4253125000000 : ℝ)*(11309/100000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (3401325760897545589/3402500000000000000 : ℝ)+2*(7840821633/4253125000000 : ℝ)*(11309/100000 : ℝ)=(2500179655052981/2500000000000000 : ℝ) by norm_num, show 1+2*(14565236409068551/100000000000000000000 : ℝ)=(50014565236409068551/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6982167854378087/20000000000000000000 : ℝ)+(14565236409068551/100000000000000000000 : ℝ) ≤ ((3401325760897545589/3402500000000000000 : ℝ)+(7840821633/4253125000000 : ℝ)*((14031/100000 : ℝ)+(11309/100000 : ℝ)))^(8301/2048 : ℝ) := by
    rw [show (3401325760897545589/3402500000000000000 : ℝ)+(7840821633/4253125000000 : ℝ)*((14031/100000 : ℝ)+(11309/100000 : ℝ))=(2500305108199109/2500000000000000 : ℝ) by norm_num, show 1+(6982167854378087/20000000000000000000 : ℝ)+(14565236409068551/100000000000000000000 : ℝ)=(50024738037840479493/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6982167854378087/20000000000000000000 : ℝ) ≤ ((3401325760897545589/3402500000000000000 : ℝ)+2*(7840821633/4253125000000 : ℝ)*(14031/100000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (3401325760897545589/3402500000000000000 : ℝ)+2*(7840821633/4253125000000 : ℝ)*(14031/100000 : ℝ)=(2500430561345237/2500000000000000 : ℝ) by norm_num, show 1+2*(6982167854378087/20000000000000000000 : ℝ)=(10006982167854378087/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3401325760897545589/3402500000000000000 : ℝ)*(X 1 0+X 2 0)+(7840821633/4253125000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (14031/100000 : ℝ)) (c := (3401325760897545589/3402500000000000000 : ℝ)) (alpha := (7840821633/4253125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3401325760897545589/3402500000000000000 : ℝ)*(X 0 1+X 2 1)+(7840821633/4253125000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (14031/100000 : ℝ)) (c := (3401325760897545589/3402500000000000000 : ℝ)) (alpha := (7840821633/4253125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3401325760897545589/3402500000000000000 : ℝ)*(X 0 2+X 1 2)+(7840821633/4253125000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (14031/100000 : ℝ)) (c := (3401325760897545589/3402500000000000000 : ℝ)) (alpha := (7840821633/4253125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2182767881/10000000000 : ℝ)*X 0 0+(1348396811/2500000000 : ℝ)*X 0 1+(5265228893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344860861/10000000000 : ℝ)*X 1 0+(-1123940679/5000000000 : ℝ)*X 1 1+(5265228929/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344860897/10000000000 : ℝ)*X 2 0+(1053045781/2000000000 : ℝ)*X 2 1+(-1123940671/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369344829/10000000000 : ℝ)*X 0 0+(2122167409/5000000000 : ℝ)*X 0 1+(899609683/2000000000 : ℝ)*X 0 2+(4369344829/10000000000 : ℝ)*X 1 0+(2122167409/5000000000 : ℝ)*X 1 1+(899609683/2000000000 : ℝ)*X 1 2+(4369344829/10000000000 : ℝ)*X 2 0+(2122167409/5000000000 : ℝ)*X 2 1+(899609683/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-545693153/2500000000 : ℝ)*X 0 0+(1316387713/2500000000 : ℝ)*X 0 1+(5393264291/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312421147/10000000000 : ℝ)*X 1 0+(-529961627/2500000000 : ℝ)*X 1 1+(5393264007/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656210791/5000000000 : ℝ)*X 2 0+(2696631977/5000000000 : ℝ)*X 2 1+(-211984599/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092338711/2500000000 : ℝ)*X 0 0+(4497412091/10000000000 : ℝ)*X 0 1+(848994643/2000000000 : ℝ)*X 0 2+(1092338711/2500000000 : ℝ)*X 1 0+(4497412091/10000000000 : ℝ)*X 1 1+(848994643/2000000000 : ℝ)*X 1 2+(1092338711/2500000000 : ℝ)*X 2 0+(4497412091/10000000000 : ℝ)*X 2 1+(848994643/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1423249961910461188819567887/170125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (829849119/50000000000000 : ℝ)*(base19) + (62726159/4000000000000 : ℝ)*(base23) + (38487979/50000000000000 : ℝ)*(lower2) + (195771211/100000000000000 : ℝ)*(upper3) + (12429243/10000000000000 : ℝ)*(upper5) + (5866142683863213/100000000000000 : ℝ)*(major0) + (5866142683863213/100000000000000 : ℝ)*(major1) + (5866142683863213/100000000000000 : ℝ)*(major2) + (1558147564348703/20000000000000 : ℝ)*(sp0) + (3895392219063691/50000000000000 : ℝ)*(sp1) + (1558156905934329/20000000000000 : ℝ)*(sp2) + (985368563729633/25000000000000 : ℝ)*(sp3) + (9655216421/20000000000000 : ℝ)*(sp4) + (4947223739/20000000000000 : ℝ)*(sp7) + (3941498991037227/100000000000000 : ℝ)*(f.failure) + (389539304891281/5000000000000 : ℝ)*(f.sum) + (22392277974037/6805000000000000000000000000 : ℝ)*base66 + (534452185195467457/340250000000000000000000000000000 : ℝ)*base67 + (3939756486906967457/340250000000000000000000000000000 : ℝ)*base69 + (4334989915493217457/340250000000000000000000000000000 : ℝ)*base71 + (18099418038203/6805000000000000000000000000 : ℝ)*base73 + (1490146200779967457/340250000000000000000000000000000 : ℝ)*base75 + (447303737657467457/340250000000000000000000000000000 : ℝ)*base77 + (1261065381344217457/340250000000000000000000000000000 : ℝ)*base79 + (45506623928453/6805000000000000000000000000 : ℝ)*base81 + (19394931/10000000000000000000000 : ℝ)*base90 + (19394931/10000000000000000000000 : ℝ)*base92 + (19394931/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12410120693971250319435957/2126562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (28945543/5000000000000 : ℝ)*(base19) + (1408752267/100000000000000 : ℝ)*(base23) + (41681377/25000000000000 : ℝ)*(lower2) + (5539473/12500000000000 : ℝ)*(upper3) + (9676811/6250000000000 : ℝ)*(lower4) + (5565471/6250000000000 : ℝ)*(upper5) + (147392499060411/2500000000000 : ℝ)*(major0) + (147392499060411/2500000000000 : ℝ)*(major1) + (147392499060411/2500000000000 : ℝ)*(major2) + (34568089377/100000000000000 : ℝ)*(sp2) + (1566008202748909/20000000000000 : ℝ)*(sp4) + (1566008086966737/20000000000000 : ℝ)*(sp5) + (7830005036902901/100000000000000 : ℝ)*(sp6) + (990339679140699/25000000000000 : ℝ)*(sp7) + (990339679140699/25000000000000 : ℝ)*(f.failure) + (1566008202748909/20000000000000 : ℝ)*(f.sum) + (1047285382301/340250000000000000000000000 : ℝ)*base65 + (221237564192127079/8506250000000000000000000000000 : ℝ)*base67 + (67837697897133329/8506250000000000000000000000000 : ℝ)*base69 + (173928764053233329/8506250000000000000000000000000 : ℝ)*base71 + (265866973361/170125000000000000000000000 : ℝ)*base74 + (3214583614633329/8506250000000000000000000000000 : ℝ)*base75 + (95524413378133329/8506250000000000000000000000000 : ℝ)*base77 + (123159902860633329/8506250000000000000000000000000 : ℝ)*base79 + (65631156969/170125000000000000000000000 : ℝ)*base81 + (20077347/2500000000000000000000 : ℝ)*base90 + (20077347/2500000000000000000000 : ℝ)*base92 + (20077347/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1109_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1131/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1109_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1109_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1131/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1109_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1109_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1109_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1131/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1109_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

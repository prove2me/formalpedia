-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1575_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:28:36.027273+00:00
-- url     : https://prove2.me/submissions/a83c56d7-ac07-49bd-a0e0-4e3d1e4700c9

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
theorem support_rectangle_w1575_s3_0 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-889285557/5000000000 : ℝ)*x 0 + (339171011/625000000 : ℝ)*x 1 + (2609402691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (889285557/5000000000 : ℝ)^4647 ≤ (10917227119213/100000000000000 : ℝ)^3623 := by
    have hnat : (889285557 : ℕ)^4647*100000000000000^3623 ≤ 10917227119213^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889285557 5000000000 10917227119213 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339171011/625000000 : ℝ)^4647 ≤ (45657179066041/100000000000000 : ℝ)^3623 := by
    have hnat : (339171011 : ℕ)^4647*100000000000000^3623 ≤ 45657179066041^3623*625000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339171011 625000000 45657179066041 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609402691/5000000000 : ℝ)^4647 ≤ (43425593799931/100000000000000 : ℝ)^3623 := by
    have hnat : (2609402691 : ℕ)^4647*100000000000000^3623 ≤ 43425593799931^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609402691 5000000000 43425593799931 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-889285557/5000000000 : ℝ), (339171011/625000000 : ℝ), (2609402691/5000000000 : ℝ)] ![(10917227119213/100000000000000 : ℝ), (45657179066041/100000000000000 : ℝ), (43425593799931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-889285557/5000000000 : ℝ)|^4647 ≤ (10917227119213/100000000000000 : ℝ)^3623
        have hw : |(-889285557/5000000000 : ℝ)|=(889285557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339171011/625000000 : ℝ)|^4647 ≤ (45657179066041/100000000000000 : ℝ)^3623
        have hw : |(339171011/625000000 : ℝ)|=(339171011/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609402691/5000000000 : ℝ)|^4647 ≤ (43425593799931/100000000000000 : ℝ)^3623
        have hw : |(2609402691/5000000000 : ℝ)|=(2609402691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s3_1 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674150719/5000000000 : ℝ)*x 0 + (-1884971037/10000000000 : ℝ)*x 1 + (1304701343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674150719/5000000000 : ℝ)^4647 ≤ (22406249649831/50000000000000 : ℝ)^3623 := by
    have hnat : (2674150719 : ℕ)^4647*50000000000000^3623 ≤ 22406249649831^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674150719 5000000000 22406249649831 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1884971037/10000000000 : ℝ)^4647 ≤ (367559593511/3125000000000 : ℝ)^3623 := by
    have hnat : (1884971037 : ℕ)^4647*3125000000000^3623 ≤ 367559593511^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884971037 10000000000 367559593511 3125000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304701343/2500000000 : ℝ)^4647 ≤ (43425593693203/100000000000000 : ℝ)^3623 := by
    have hnat : (1304701343 : ℕ)^4647*100000000000000^3623 ≤ 43425593693203^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304701343 2500000000 43425593693203 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674150719/5000000000 : ℝ), (-1884971037/10000000000 : ℝ), (1304701343/2500000000 : ℝ)] ![(22406249649831/50000000000000 : ℝ), (367559593511/3125000000000 : ℝ), (43425593693203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674150719/5000000000 : ℝ)|^4647 ≤ (22406249649831/50000000000000 : ℝ)^3623
        have hw : |(2674150719/5000000000 : ℝ)|=(2674150719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1884971037/10000000000 : ℝ)|^4647 ≤ (367559593511/3125000000000 : ℝ)^3623
        have hw : |(-1884971037/10000000000 : ℝ)|=(1884971037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304701343/2500000000 : ℝ)|^4647 ≤ (43425593693203/100000000000000 : ℝ)^3623
        have hw : |(1304701343/2500000000 : ℝ)|=(1304701343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s3_2 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348301421/10000000000 : ℝ)*x 0 + (652350673/1250000000 : ℝ)*x 1 + (-1884971043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348301421/10000000000 : ℝ)^4647 ≤ (44812499116963/100000000000000 : ℝ)^3623 := by
    have hnat : (5348301421 : ℕ)^4647*100000000000000^3623 ≤ 44812499116963^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348301421 10000000000 44812499116963 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652350673/1250000000 : ℝ)^4647 ≤ (43425593821277/100000000000000 : ℝ)^3623 := by
    have hnat : (652350673 : ℕ)^4647*100000000000000^3623 ≤ 43425593821277^3623*1250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652350673 1250000000 43425593821277 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1884971043/10000000000 : ℝ)^4647 ≤ (2940476760093/25000000000000 : ℝ)^3623 := by
    have hnat : (1884971043 : ℕ)^4647*25000000000000^3623 ≤ 2940476760093^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884971043 10000000000 2940476760093 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348301421/10000000000 : ℝ), (652350673/1250000000 : ℝ), (-1884971043/10000000000 : ℝ)] ![(44812499116963/100000000000000 : ℝ), (43425593821277/100000000000000 : ℝ), (2940476760093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348301421/10000000000 : ℝ)|^4647 ≤ (44812499116963/100000000000000 : ℝ)^3623
        have hw : |(5348301421/10000000000 : ℝ)|=(5348301421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652350673/1250000000 : ℝ)|^4647 ≤ (43425593821277/100000000000000 : ℝ)^3623
        have hw : |(652350673/1250000000 : ℝ)|=(652350673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1884971043/10000000000 : ℝ)|^4647 ≤ (2940476760093/25000000000000 : ℝ)^3623
        have hw : |(-1884971043/10000000000 : ℝ)|=(1884971043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s3_3 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4241160349/10000000000 : ℝ)*x 0 + (80013477/200000000 : ℝ)*x 1 + (898635941/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4241160349/10000000000 : ℝ)^4647 ≤ (6656216616263/20000000000000 : ℝ)^3623 := by
    have hnat : (4241160349 : ℕ)^4647*20000000000000^3623 ≤ 6656216616263^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241160349 10000000000 6656216616263 20000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80013477/200000000 : ℝ)^4647 ≤ (30880233717893/100000000000000 : ℝ)^3623 := by
    have hnat : (80013477 : ℕ)^4647*100000000000000^3623 ≤ 30880233717893^3623*200000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80013477 200000000 30880233717893 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898635941/2000000000 : ℝ)^4647 ≤ (7167736636273/20000000000000 : ℝ)^3623 := by
    have hnat : (898635941 : ℕ)^4647*20000000000000^3623 ≤ 7167736636273^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898635941 2000000000 7167736636273 20000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4241160349/10000000000 : ℝ), (80013477/200000000 : ℝ), (898635941/2000000000 : ℝ)] ![(6656216616263/20000000000000 : ℝ), (30880233717893/100000000000000 : ℝ), (7167736636273/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4241160349/10000000000 : ℝ)|^4647 ≤ (6656216616263/20000000000000 : ℝ)^3623
        have hw : |(4241160349/10000000000 : ℝ)|=(4241160349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80013477/200000000 : ℝ)|^4647 ≤ (30880233717893/100000000000000 : ℝ)^3623
        have hw : |(80013477/200000000 : ℝ)|=(80013477/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898635941/2000000000 : ℝ)|^4647 ≤ (7167736636273/20000000000000 : ℝ)^3623
        have hw : |(898635941/2000000000 : ℝ)|=(898635941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s3_4 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1778598629/10000000000 : ℝ)*x 0 + (5219905603/10000000000 : ℝ)*x 1 + (5425627899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1778598629/10000000000 : ℝ)^4647 ≤ (5458721873937/50000000000000 : ℝ)^3623 := by
    have hnat : (1778598629 : ℕ)^4647*50000000000000^3623 ≤ 5458721873937^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778598629 10000000000 5458721873937 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219905603/10000000000 : ℝ)^4647 ≤ (21718668302757/50000000000000 : ℝ)^3623 := by
    have hnat : (5219905603 : ℕ)^4647*50000000000000^3623 ≤ 21718668302757^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219905603 10000000000 21718668302757 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425627899/10000000000 : ℝ)^4647 ≤ (11411304908947/25000000000000 : ℝ)^3623 := by
    have hnat : (5425627899 : ℕ)^4647*25000000000000^3623 ≤ 11411304908947^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425627899 10000000000 11411304908947 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1778598629/10000000000 : ℝ), (5219905603/10000000000 : ℝ), (5425627899/10000000000 : ℝ)] ![(5458721873937/50000000000000 : ℝ), (21718668302757/50000000000000 : ℝ), (11411304908947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1778598629/10000000000 : ℝ)|^4647 ≤ (5458721873937/50000000000000 : ℝ)^3623
        have hw : |(-1778598629/10000000000 : ℝ)|=(1778598629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219905603/10000000000 : ℝ)|^4647 ≤ (21718668302757/50000000000000 : ℝ)^3623
        have hw : |(5219905603/10000000000 : ℝ)|=(5219905603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425627899/10000000000 : ℝ)|^4647 ≤ (11411304908947/25000000000000 : ℝ)^3623
        have hw : |(5425627899/10000000000 : ℝ)|=(5425627899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s3_5 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323314083/2500000000 : ℝ)*x 0 + (-839074271/5000000000 : ℝ)*x 1 + (678203511/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323314083/2500000000 : ℝ)^4647 ≤ (22110895788357/50000000000000 : ℝ)^3623 := by
    have hnat : (1323314083 : ℕ)^4647*50000000000000^3623 ≤ 22110895788357^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323314083 2500000000 22110895788357 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (839074271/5000000000 : ℝ)^4647 ≤ (1013298673379/10000000000000 : ℝ)^3623 := by
    have hnat : (839074271 : ℕ)^4647*10000000000000^3623 ≤ 1013298673379^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839074271 5000000000 1013298673379 10000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678203511/1250000000 : ℝ)^4647 ≤ (45645221675231/100000000000000 : ℝ)^3623 := by
    have hnat : (678203511 : ℕ)^4647*100000000000000^3623 ≤ 45645221675231^3623*1250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678203511 1250000000 45645221675231 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323314083/2500000000 : ℝ), (-839074271/5000000000 : ℝ), (678203511/1250000000 : ℝ)] ![(22110895788357/50000000000000 : ℝ), (1013298673379/10000000000000 : ℝ), (45645221675231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323314083/2500000000 : ℝ)|^4647 ≤ (22110895788357/50000000000000 : ℝ)^3623
        have hw : |(1323314083/2500000000 : ℝ)|=(1323314083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-839074271/5000000000 : ℝ)|^4647 ≤ (1013298673379/10000000000000 : ℝ)^3623
        have hw : |(-839074271/5000000000 : ℝ)|=(839074271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678203511/1250000000 : ℝ)|^4647 ≤ (45645221675231/100000000000000 : ℝ)^3623
        have hw : |(678203511/1250000000 : ℝ)|=(678203511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s3_6 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058651351/2000000000 : ℝ)*x 0 + (5425627603/10000000000 : ℝ)*x 1 + (-209768579/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058651351/2000000000 : ℝ)^4647 ≤ (22110898054713/50000000000000 : ℝ)^3623 := by
    have hnat : (1058651351 : ℕ)^4647*50000000000000^3623 ≤ 22110898054713^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058651351 2000000000 22110898054713 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425627603/10000000000 : ℝ)^4647 ≤ (45645216441741/100000000000000 : ℝ)^3623 := by
    have hnat : (5425627603 : ℕ)^4647*100000000000000^3623 ≤ 45645216441741^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425627603 10000000000 45645216441741 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209768579/1250000000 : ℝ)^4647 ≤ (1266623428853/12500000000000 : ℝ)^3623 := by
    have hnat : (209768579 : ℕ)^4647*12500000000000^3623 ≤ 1266623428853^3623*1250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209768579 1250000000 1266623428853 12500000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058651351/2000000000 : ℝ), (5425627603/10000000000 : ℝ), (-209768579/1250000000 : ℝ)] ![(22110898054713/50000000000000 : ℝ), (45645216441741/100000000000000 : ℝ), (1266623428853/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058651351/2000000000 : ℝ)|^4647 ≤ (22110898054713/50000000000000 : ℝ)^3623
        have hw : |(1058651351/2000000000 : ℝ)|=(1058651351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425627603/10000000000 : ℝ)|^4647 ≤ (45645216441741/100000000000000 : ℝ)^3623
        have hw : |(5425627603/10000000000 : ℝ)|=(5425627603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209768579/1250000000 : ℝ)|^4647 ≤ (1266623428853/12500000000000 : ℝ)^3623
        have hw : |(-209768579/1250000000 : ℝ)|=(209768579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s3_7 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4241226721/10000000000 : ℝ)*x 0 + (449057441/1000000000 : ℝ)*x 1 + (4003298113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4241226721/10000000000 : ℝ)^4647 ≤ (8320437780519/25000000000000 : ℝ)^3623 := by
    have hnat : (4241226721 : ℕ)^4647*25000000000000^3623 ≤ 8320437780519^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241226721 10000000000 8320437780519 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449057441/1000000000 : ℝ)^4647 ≤ (8953007885827/25000000000000 : ℝ)^3623 := by
    have hnat : (449057441 : ℕ)^4647*25000000000000^3623 ≤ 8953007885827^3623*1000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449057441 1000000000 8953007885827 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4003298113/10000000000 : ℝ)^4647 ≤ (30906217321213/100000000000000 : ℝ)^3623 := by
    have hnat : (4003298113 : ℕ)^4647*100000000000000^3623 ≤ 30906217321213^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4003298113 10000000000 30906217321213 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4241226721/10000000000 : ℝ), (449057441/1000000000 : ℝ), (4003298113/10000000000 : ℝ)] ![(8320437780519/25000000000000 : ℝ), (8953007885827/25000000000000 : ℝ), (30906217321213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4241226721/10000000000 : ℝ)|^4647 ≤ (8320437780519/25000000000000 : ℝ)^3623
        have hw : |(4241226721/10000000000 : ℝ)|=(4241226721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(449057441/1000000000 : ℝ)|^4647 ≤ (8953007885827/25000000000000 : ℝ)^3623
        have hw : |(449057441/1000000000 : ℝ)|=(449057441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4003298113/10000000000 : ℝ)|^4647 ≤ (30906217321213/100000000000000 : ℝ)^3623
        have hw : |(4003298113/10000000000 : ℝ)|=(4003298113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1575_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15799/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10847/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11107/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15517/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15799/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10847/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15799/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10847/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15799/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10847/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15799/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10847/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15799/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10847/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15799/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10847/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10847/100000 : ℝ) ^ (4645/1024 : ℝ) ≤ (4207618973477169/100000000000000000000 : ℝ) := by
    have hpowers : (10847/100000 : ℝ)^4645 ≤ (4207618973477169/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10847 : ℕ)^4645*100000000000000000000^1024 ≤ 4207618973477169^1024*100000^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10847 100000 4207618973477169 100000000000000000000 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10847/100000 : ℝ)) (X := (4207618973477169/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15799/100000 : ℝ) ^ (4645/1024 : ℝ) ≤ (463348141226329/2000000000000000000 : ℝ) := by
    have hpowers : (15799/100000 : ℝ)^4645 ≤ (463348141226329/2000000000000000000 : ℝ)^1024 := by
      have hnat : (15799 : ℕ)^4645*2000000000000000000^1024 ≤ 463348141226329^1024*100000^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15799 100000 463348141226329 2000000000000000000 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15799/100000 : ℝ)) (X := (463348141226329/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004207618973477169/50000000000000000000 : ℝ) ≤ (31250579717507/31250000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (50004207618973477169/50000000000000000000 : ℝ)^1024 ≤ (31250579717507/31250000000000 : ℝ)^4645 := by
      have hnat : (50004207618973477169 : ℕ)^1024*31250000000000^4645 ≤ 31250579717507^4645*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004207618973477169 50000000000000000000 31250579717507 31250000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31250579717507/31250000000000 : ℝ)) (X := (50004207618973477169/50000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027375026034793619/100000000000000000000 : ℝ) ≤ (1000060342381287/1000000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (100027375026034793619/100000000000000000000 : ℝ)^1024 ≤ (1000060342381287/1000000000000000 : ℝ)^4645 := by
      have hnat : (100027375026034793619 : ℕ)^1024*1000000000000000^4645 ≤ 1000060342381287^4645*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027375026034793619 100000000000000000000 1000060342381287 1000000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000060342381287/1000000000000000 : ℝ)) (X := (100027375026034793619/100000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000463348141226329/1000000000000000000 : ℝ) ≤ (20002042676047/20000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (1000463348141226329/1000000000000000000 : ℝ)^1024 ≤ (20002042676047/20000000000000 : ℝ)^4645 := by
      have hnat : (1000463348141226329 : ℕ)^1024*20000000000000^4645 ≤ 20002042676047^4645*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000463348141226329 1000000000000000000 20002042676047 20000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20002042676047/20000000000000 : ℝ)) (X := (1000463348141226329/1000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4207618973477169/100000000000000000000 : ℝ) ≤ ((2475592620633244263/2476000000000000000 : ℝ)+2*(41791421063/49520000000000 : ℝ)*(10847/100000 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (2475592620633244263/2476000000000000000 : ℝ)+2*(41791421063/49520000000000 : ℝ)*(10847/100000 : ℝ)=(31250579717507/31250000000000 : ℝ) by norm_num, show 1+2*(4207618973477169/100000000000000000000 : ℝ)=(50004207618973477169/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(463348141226329/2000000000000000000 : ℝ)+(4207618973477169/100000000000000000000 : ℝ) ≤ ((2475592620633244263/2476000000000000000 : ℝ)+(41791421063/49520000000000 : ℝ)*((15799/100000 : ℝ)+(10847/100000 : ℝ)))^(4645/1024 : ℝ) := by
    rw [show (2475592620633244263/2476000000000000000 : ℝ)+(41791421063/49520000000000 : ℝ)*((15799/100000 : ℝ)+(10847/100000 : ℝ))=(1000060342381287/1000000000000000 : ℝ) by norm_num, show 1+(463348141226329/2000000000000000000 : ℝ)+(4207618973477169/100000000000000000000 : ℝ)=(100027375026034793619/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(463348141226329/2000000000000000000 : ℝ) ≤ ((2475592620633244263/2476000000000000000 : ℝ)+2*(41791421063/49520000000000 : ℝ)*(15799/100000 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (2475592620633244263/2476000000000000000 : ℝ)+2*(41791421063/49520000000000 : ℝ)*(15799/100000 : ℝ)=(20002042676047/20000000000000 : ℝ) by norm_num, show 1+2*(463348141226329/2000000000000000000 : ℝ)=(1000463348141226329/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2475592620633244263/2476000000000000000 : ℝ)*(X 1 0+X 2 0)+(41791421063/49520000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (10847/100000 : ℝ)) (hi := (15799/100000 : ℝ)) (c := (2475592620633244263/2476000000000000000 : ℝ)) (alpha := (41791421063/49520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2475592620633244263/2476000000000000000 : ℝ)*(X 0 1+X 2 1)+(41791421063/49520000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (10847/100000 : ℝ)) (hi := (15799/100000 : ℝ)) (c := (2475592620633244263/2476000000000000000 : ℝ)) (alpha := (41791421063/49520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2475592620633244263/2476000000000000000 : ℝ)*(X 0 2+X 1 2)+(41791421063/49520000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (10847/100000 : ℝ)) (hi := (15799/100000 : ℝ)) (c := (2475592620633244263/2476000000000000000 : ℝ)) (alpha := (41791421063/49520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-889285557/5000000000 : ℝ)*X 0 0+(339171011/625000000 : ℝ)*X 0 1+(2609402691/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674150719/5000000000 : ℝ)*X 1 0+(-1884971037/10000000000 : ℝ)*X 1 1+(1304701343/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348301421/10000000000 : ℝ)*X 2 0+(652350673/1250000000 : ℝ)*X 2 1+(-1884971043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4241160349/10000000000 : ℝ)*X 0 0+(80013477/200000000 : ℝ)*X 0 1+(898635941/2000000000 : ℝ)*X 0 2+(4241160349/10000000000 : ℝ)*X 1 0+(80013477/200000000 : ℝ)*X 1 1+(898635941/2000000000 : ℝ)*X 1 2+(4241160349/10000000000 : ℝ)*X 2 0+(80013477/200000000 : ℝ)*X 2 1+(898635941/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1778598629/10000000000 : ℝ)*X 0 0+(5219905603/10000000000 : ℝ)*X 0 1+(5425627899/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323314083/2500000000 : ℝ)*X 1 0+(-839074271/5000000000 : ℝ)*X 1 1+(678203511/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058651351/2000000000 : ℝ)*X 2 0+(5425627603/10000000000 : ℝ)*X 2 1+(-209768579/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4241226721/10000000000 : ℝ)*X 0 0+(449057441/1000000000 : ℝ)*X 0 1+(4003298113/10000000000 : ℝ)*X 0 2+(4241226721/10000000000 : ℝ)*X 1 0+(449057441/1000000000 : ℝ)*X 1 1+(4003298113/10000000000 : ℝ)*X 1 2+(4241226721/10000000000 : ℝ)*X 2 0+(449057441/1000000000 : ℝ)*X 2 1+(4003298113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77342736519900528507036471/12380000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (536056101/50000000000000 : ℝ)*(base19) + (990290337/100000000000000 : ℝ)*(base23) + (17792473/50000000000000 : ℝ)*(lower2) + (3195039/2000000000000 : ℝ)*(upper3) + (51492513/50000000000000 : ℝ)*(upper5) + (341988739130661/10000000000000 : ℝ)*(major0) + (341988739130661/10000000000000 : ℝ)*(major1) + (341988739130661/10000000000000 : ℝ)*(major2) + (4809310236293963/100000000000000 : ℝ)*(sp0) + (4809325991964327/100000000000000 : ℝ)*(sp1) + (4809326073786193/100000000000000 : ℝ)*(sp2) + (2030439680315439/100000000000000 : ℝ)*(sp3) + (8413891283/50000000000000 : ℝ)*(sp4) + (3914987389/50000000000000 : ℝ)*(sp7) + (253805938786277/12500000000000 : ℝ)*(f.failure) + (480932706407653/10000000000000 : ℝ)*(f.sum) + (1889399734201/1238000000000000000000000000 : ℝ)*base65 + (193171212157637843/24760000000000000000000000000000 : ℝ)*base67 + (142347912901042157/24760000000000000000000000000000 : ℝ)*base70 + (63821271552797843/24760000000000000000000000000000 : ℝ)*base71 + (2507629227163/1238000000000000000000000000 : ℝ)*base74 + (245243964765517843/24760000000000000000000000000000 : ℝ)*base75 + (55569307604277843/24760000000000000000000000000000 : ℝ)*base77 + (197582202314122157/24760000000000000000000000000000 : ℝ)*base80 + (1115857614593/247600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (7832567/1250000000000000000000 : ℝ)*base90 + (7832567/1250000000000000000000 : ℝ)*base92 + (7832567/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6387302980939136074353/1238000000000000000000000000 : ℝ) := by norm_num
    linear_combination (266331121/100000000000000 : ℝ)*(base19) + (1283670869/100000000000000 : ℝ)*(base23) + (501321/10000000000000 : ℝ)*(lower2) + (213701009/100000000000000 : ℝ)*(upper3) + (33791639/12500000000000 : ℝ)*(lower4) + (1728284793143861/50000000000000 : ℝ)*(major0) + (1728284793143861/50000000000000 : ℝ)*(major1) + (1728284793143861/50000000000000 : ℝ)*(major2) + (12275041323/100000000000000 : ℝ)*(sp2) + (409827931/100000000000000 : ℝ)*(sp3) + (972182524730171/20000000000000 : ℝ)*(sp4) + (2430456178659867/50000000000000 : ℝ)*(sp5) + (4860899064938663/100000000000000 : ℝ)*(sp6) + (2052225967117577/100000000000000 : ℝ)*(sp7) + (513056594236377/25000000000000 : ℝ)*(f.failure) + (972182524730171/20000000000000 : ℝ)*(f.sum) + (898837795937/247600000000000000000000000 : ℝ)*base65 + (474031572681069443/123800000000000000000000000000000 : ℝ)*base67 + (576699474759730557/123800000000000000000000000000000 : ℝ)*base70 + (232833377272869443/123800000000000000000000000000000 : ℝ)*base71 + (1355393552347/1238000000000000000000000000 : ℝ)*base73 + (34391568801669443/123800000000000000000000000000000 : ℝ)*base75 + (222253300795130557/123800000000000000000000000000000 : ℝ)*base78 + (323160855611730557/123800000000000000000000000000000 : ℝ)*base80 + (113944875139/247600000000000000000000000 : ℝ)*base82 + (8240333/2500000000000000000000 : ℝ)*base89 + (8240333/2500000000000000000000 : ℝ)*base91 + (8240333/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1575_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15799/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10847/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15517/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1575_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1575_s4_0 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-71151363/400000000 : ℝ)*x 0 + (5425306359/10000000000 : ℝ)*x 1 + (2610046939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71151363/400000000 : ℝ)^4647 ≤ (10918903809603/100000000000000 : ℝ)^3623 := by
    have hnat : (71151363 : ℕ)^4647*100000000000000^3623 ≤ 10918903809603^3623*400000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71151363 400000000 10918903809603 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425306359/10000000000 : ℝ)^4647 ≤ (22820875011523/50000000000000 : ℝ)^3623 := by
    have hnat : (5425306359 : ℕ)^4647*50000000000000^3623 ≤ 22820875011523^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425306359 10000000000 22820875011523 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610046939/5000000000 : ℝ)^4647 ≤ (43439346159821/100000000000000 : ℝ)^3623 := by
    have hnat : (2610046939 : ℕ)^4647*100000000000000^3623 ≤ 43439346159821^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610046939 5000000000 43439346159821 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-71151363/400000000 : ℝ), (5425306359/10000000000 : ℝ), (2610046939/5000000000 : ℝ)] ![(10918903809603/100000000000000 : ℝ), (22820875011523/50000000000000 : ℝ), (43439346159821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-71151363/400000000 : ℝ)|^4647 ≤ (10918903809603/100000000000000 : ℝ)^3623
        have hw : |(-71151363/400000000 : ℝ)|=(71151363/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425306359/10000000000 : ℝ)|^4647 ≤ (22820875011523/50000000000000 : ℝ)^3623
        have hw : |(5425306359/10000000000 : ℝ)|=(5425306359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610046939/5000000000 : ℝ)|^4647 ≤ (43439346159821/100000000000000 : ℝ)^3623
        have hw : |(2610046939/5000000000 : ℝ)|=(2610046939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s4_1 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673961159/5000000000 : ℝ)*x 0 + (-376752333/2000000000 : ℝ)*x 1 + (2610046947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673961159/5000000000 : ℝ)^4647 ≤ (22404212467141/50000000000000 : ℝ)^3623 := by
    have hnat : (2673961159 : ℕ)^4647*50000000000000^3623 ≤ 22404212467141^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673961159 5000000000 22404212467141 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (376752333/2000000000 : ℝ)^4647 ≤ (2350445743629/20000000000000 : ℝ)^3623 := by
    have hnat : (376752333 : ℕ)^4647*20000000000000^3623 ≤ 2350445743629^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376752333 2000000000 2350445743629 20000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610046947/5000000000 : ℝ)^4647 ≤ (21719673165299/50000000000000 : ℝ)^3623 := by
    have hnat : (2610046947 : ℕ)^4647*50000000000000^3623 ≤ 21719673165299^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610046947 5000000000 21719673165299 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673961159/5000000000 : ℝ), (-376752333/2000000000 : ℝ), (2610046947/5000000000 : ℝ)] ![(22404212467141/50000000000000 : ℝ), (2350445743629/20000000000000 : ℝ), (21719673165299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673961159/5000000000 : ℝ)|^4647 ≤ (22404212467141/50000000000000 : ℝ)^3623
        have hw : |(2673961159/5000000000 : ℝ)|=(2673961159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-376752333/2000000000 : ℝ)|^4647 ≤ (2350445743629/20000000000000 : ℝ)^3623
        have hw : |(-376752333/2000000000 : ℝ)|=(376752333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610046947/5000000000 : ℝ)|^4647 ≤ (21719673165299/50000000000000 : ℝ)^3623
        have hw : |(2610046947/5000000000 : ℝ)|=(2610046947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s4_2 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213916893/400000000 : ℝ)*x 0 + (2610046943/5000000000 : ℝ)*x 1 + (-941880833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213916893/400000000 : ℝ)^4647 ≤ (4480842500951/10000000000000 : ℝ)^3623 := by
    have hnat : (213916893 : ℕ)^4647*10000000000000^3623 ≤ 4480842500951^3623*400000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213916893 400000000 4480842500951 10000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610046943/5000000000 : ℝ)^4647 ≤ (4343934624521/10000000000000 : ℝ)^3623 := by
    have hnat : (2610046943 : ℕ)^4647*10000000000000^3623 ≤ 4343934624521^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610046943 5000000000 4343934624521 10000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (941880833/5000000000 : ℝ)^4647 ≤ (11752228726147/100000000000000 : ℝ)^3623 := by
    have hnat : (941880833 : ℕ)^4647*100000000000000^3623 ≤ 11752228726147^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941880833 5000000000 11752228726147 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213916893/400000000 : ℝ), (2610046943/5000000000 : ℝ), (-941880833/5000000000 : ℝ)] ![(4480842500951/10000000000000 : ℝ), (4343934624521/10000000000000 : ℝ), (11752228726147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213916893/400000000 : ℝ)|^4647 ≤ (4480842500951/10000000000000 : ℝ)^3623
        have hw : |(213916893/400000000 : ℝ)|=(213916893/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610046943/5000000000 : ℝ)|^4647 ≤ (4343934624521/10000000000000 : ℝ)^3623
        have hw : |(2610046943/5000000000 : ℝ)|=(2610046943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-941880833/5000000000 : ℝ)|^4647 ≤ (11752228726147/100000000000000 : ℝ)^3623
        have hw : |(-941880833/5000000000 : ℝ)|=(941880833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s4_3 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4241295079/10000000000 : ℝ)*x 0 + (2001939159/5000000000 : ℝ)*x 1 + (4489945451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4241295079/10000000000 : ℝ)^4647 ≤ (33282439155213/100000000000000 : ℝ)^3623 := by
    have hnat : (4241295079 : ℕ)^4647*100000000000000^3623 ≤ 33282439155213^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241295079 10000000000 33282439155213 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2001939159/5000000000 : ℝ)^4647 ≤ (30911962752333/100000000000000 : ℝ)^3623 := by
    have hnat : (2001939159 : ℕ)^4647*100000000000000^3623 ≤ 30911962752333^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001939159 5000000000 30911962752333 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489945451/10000000000 : ℝ)^4647 ≤ (17902799037699/50000000000000 : ℝ)^3623 := by
    have hnat : (4489945451 : ℕ)^4647*50000000000000^3623 ≤ 17902799037699^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489945451 10000000000 17902799037699 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4241295079/10000000000 : ℝ), (2001939159/5000000000 : ℝ), (4489945451/10000000000 : ℝ)] ![(33282439155213/100000000000000 : ℝ), (30911962752333/100000000000000 : ℝ), (17902799037699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4241295079/10000000000 : ℝ)|^4647 ≤ (33282439155213/100000000000000 : ℝ)^3623
        have hw : |(4241295079/10000000000 : ℝ)|=(4241295079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2001939159/5000000000 : ℝ)|^4647 ≤ (30911962752333/100000000000000 : ℝ)^3623
        have hw : |(2001939159/5000000000 : ℝ)|=(2001939159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489945451/10000000000 : ℝ)|^4647 ≤ (17902799037699/50000000000000 : ℝ)^3623
        have hw : |(4489945451/10000000000 : ℝ)|=(4489945451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s4_4 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-889405183/5000000000 : ℝ)*x 0 + (26105827/50000000 : ℝ)*x 1 + (2712113603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (889405183/5000000000 : ℝ)^4647 ≤ (136488885107/1250000000000 : ℝ)^3623 := by
    have hnat : (889405183 : ℕ)^4647*1250000000000^3623 ≤ 136488885107^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889405183 5000000000 136488885107 1250000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26105827/50000000 : ℝ)^4647 ≤ (43450783446169/100000000000000 : ℝ)^3623 := by
    have hnat : (26105827 : ℕ)^4647*100000000000000^3623 ≤ 43450783446169^3623*50000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26105827 50000000 43450783446169 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712113603/5000000000 : ℝ)^4647 ≤ (45630105728757/100000000000000 : ℝ)^3623 := by
    have hnat : (2712113603 : ℕ)^4647*100000000000000^3623 ≤ 45630105728757^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712113603 5000000000 45630105728757 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-889405183/5000000000 : ℝ), (26105827/50000000 : ℝ), (2712113603/5000000000 : ℝ)] ![(136488885107/1250000000000 : ℝ), (43450783446169/100000000000000 : ℝ), (45630105728757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-889405183/5000000000 : ℝ)|^4647 ≤ (136488885107/1250000000000 : ℝ)^3623
        have hw : |(-889405183/5000000000 : ℝ)|=(889405183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26105827/50000000 : ℝ)|^4647 ≤ (43450783446169/100000000000000 : ℝ)^3623
        have hw : |(26105827/50000000 : ℝ)|=(26105827/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712113603/5000000000 : ℝ)|^4647 ≤ (45630105728757/100000000000000 : ℝ)^3623
        have hw : |(2712113603/5000000000 : ℝ)|=(2712113603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s4_5 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105871943/200000000 : ℝ)*x 0 + (-26244207/156250000 : ℝ)*x 1 + (1084845341/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105871943/200000000 : ℝ)^4647 ≤ (22112721844919/50000000000000 : ℝ)^3623 := by
    have hnat : (105871943 : ℕ)^4647*50000000000000^3623 ≤ 22112721844919^3623*200000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105871943 200000000 22112721844919 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26244207/156250000 : ℝ)^4647 ≤ (1268056995887/12500000000000 : ℝ)^3623 := by
    have hnat : (26244207 : ℕ)^4647*12500000000000^3623 ≤ 1268056995887^3623*156250000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26244207 156250000 1268056995887 12500000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084845341/2000000000 : ℝ)^4647 ≤ (45630100323011/100000000000000 : ℝ)^3623 := by
    have hnat : (1084845341 : ℕ)^4647*100000000000000^3623 ≤ 45630100323011^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084845341 2000000000 45630100323011 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105871943/200000000 : ℝ), (-26244207/156250000 : ℝ), (1084845341/2000000000 : ℝ)] ![(22112721844919/50000000000000 : ℝ), (1268056995887/12500000000000 : ℝ), (45630100323011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105871943/200000000 : ℝ)|^4647 ≤ (22112721844919/50000000000000 : ℝ)^3623
        have hw : |(105871943/200000000 : ℝ)|=(105871943/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26244207/156250000 : ℝ)|^4647 ≤ (1268056995887/12500000000000 : ℝ)^3623
        have hw : |(-26244207/156250000 : ℝ)|=(26244207/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084845341/2000000000 : ℝ)|^4647 ≤ (45630100323011/100000000000000 : ℝ)^3623
        have hw : |(1084845341/2000000000 : ℝ)|=(1084845341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s4_6 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646799019/5000000000 : ℝ)*x 0 + (5424226323/10000000000 : ℝ)*x 1 + (-1679628553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646799019/5000000000 : ℝ)^4647 ≤ (11056363301373/25000000000000 : ℝ)^3623 := by
    have hnat : (2646799019 : ℕ)^4647*25000000000000^3623 ≤ 11056363301373^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646799019 5000000000 11056363301373 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424226323/10000000000 : ℝ)^4647 ≤ (2851881012579/6250000000000 : ℝ)^3623 := by
    have hnat : (5424226323 : ℕ)^4647*6250000000000^3623 ≤ 2851881012579^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424226323 10000000000 2851881012579 6250000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1679628553/10000000000 : ℝ)^4647 ≤ (158507040361/1562500000000 : ℝ)^3623 := by
    have hnat : (1679628553 : ℕ)^4647*1562500000000^3623 ≤ 158507040361^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1679628553 10000000000 158507040361 1562500000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646799019/5000000000 : ℝ), (5424226323/10000000000 : ℝ), (-1679628553/10000000000 : ℝ)] ![(11056363301373/25000000000000 : ℝ), (2851881012579/6250000000000 : ℝ), (158507040361/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646799019/5000000000 : ℝ)|^4647 ≤ (11056363301373/25000000000000 : ℝ)^3623
        have hw : |(2646799019/5000000000 : ℝ)|=(2646799019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424226323/10000000000 : ℝ)|^4647 ≤ (2851881012579/6250000000000 : ℝ)^3623
        have hw : |(5424226323/10000000000 : ℝ)|=(5424226323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1679628553/10000000000 : ℝ)|^4647 ≤ (158507040361/1562500000000 : ℝ)^3623
        have hw : |(-1679628553/10000000000 : ℝ)|=(1679628553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s4_7 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4241358357/10000000000 : ℝ)*x 0 + (560926013/1250000000 : ℝ)*x 1 + (4006434423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4241358357/10000000000 : ℝ)^4647 ≤ (3328307606021/10000000000000 : ℝ)^3623 := by
    have hnat : (4241358357 : ℕ)^4647*10000000000000^3623 ≤ 3328307606021^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241358357 10000000000 3328307606021 10000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560926013/1250000000 : ℝ)^4647 ≤ (3577964675973/10000000000000 : ℝ)^3623 := by
    have hnat : (560926013 : ℕ)^4647*10000000000000^3623 ≤ 3577964675973^3623*1250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560926013 1250000000 3577964675973 10000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4006434423/10000000000 : ℝ)^4647 ≤ (30937277168371/100000000000000 : ℝ)^3623 := by
    have hnat : (4006434423 : ℕ)^4647*100000000000000^3623 ≤ 30937277168371^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4006434423 10000000000 30937277168371 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4241358357/10000000000 : ℝ), (560926013/1250000000 : ℝ), (4006434423/10000000000 : ℝ)] ![(3328307606021/10000000000000 : ℝ), (3577964675973/10000000000000 : ℝ), (30937277168371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4241358357/10000000000 : ℝ)|^4647 ≤ (3328307606021/10000000000000 : ℝ)^3623
        have hw : |(4241358357/10000000000 : ℝ)|=(4241358357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560926013/1250000000 : ℝ)|^4647 ≤ (3577964675973/10000000000000 : ℝ)^3623
        have hw : |(560926013/1250000000 : ℝ)|=(560926013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4006434423/10000000000 : ℝ)|^4647 ≤ (30937277168371/100000000000000 : ℝ)^3623
        have hw : |(4006434423/10000000000 : ℝ)|=(4006434423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1575_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15517/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2227/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15487/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15517/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11107/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15517/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11107/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15517/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11107/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15517/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11107/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15517/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11107/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15517/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11107/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11107/100000 : ℝ) ^ (4645/1024 : ℝ) ≤ (936979730920963/20000000000000000000 : ℝ) := by
    have hpowers : (11107/100000 : ℝ)^4645 ≤ (936979730920963/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11107 : ℕ)^4645*20000000000000000000^1024 ≤ 936979730920963^1024*100000^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11107 100000 936979730920963 20000000000000000000 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11107/100000 : ℝ)) (X := (936979730920963/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15517/100000 : ℝ) ^ (4645/1024 : ℝ) ≤ (10674966810848617/50000000000000000000 : ℝ) := by
    have hpowers : (15517/100000 : ℝ)^4645 ≤ (10674966810848617/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15517 : ℕ)^4645*50000000000000000000^1024 ≤ 10674966810848617^1024*100000^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15517 100000 10674966810848617 50000000000000000000 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15517/100000 : ℝ)) (X := (10674966810848617/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000936979730920963/10000000000000000000 : ℝ) ≤ (5000103275802549/5000000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (10000936979730920963/10000000000000000000 : ℝ)^1024 ≤ (5000103275802549/5000000000000000 : ℝ)^4645 := by
      have hnat : (10000936979730920963 : ℕ)^1024*5000000000000000^4645 ≤ 5000103275802549^4645*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000936979730920963 10000000000000000000 5000103275802549 5000000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000103275802549/5000000000000000 : ℝ)) (X := (10000936979730920963/10000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026034832276302049/100000000000000000000 : ℝ) ≤ (1250071735638659/1250000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (100026034832276302049/100000000000000000000 : ℝ)^1024 ≤ (1250071735638659/1250000000000000 : ℝ)^4645 := by
      have hnat : (100026034832276302049 : ℕ)^1024*1250000000000000^4645 ≤ 1250071735638659^4645*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026034832276302049 100000000000000000000 1250071735638659 1250000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250071735638659/1250000000000000 : ℝ)) (X := (100026034832276302049/100000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010674966810848617/25000000000000000000 : ℝ) ≤ (5000470609306723/5000000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (25010674966810848617/25000000000000000000 : ℝ)^1024 ≤ (5000470609306723/5000000000000000 : ℝ)^4645 := by
      have hnat : (25010674966810848617 : ℕ)^1024*5000000000000000^4645 ≤ 5000470609306723^4645*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010674966810848617 25000000000000000000 5000470609306723 5000000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000470609306723/5000000000000000 : ℝ)) (X := (25010674966810848617/25000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(936979730920963/20000000000000000000 : ℝ) ≤ ((56240753757801991/56250000000000000 : ℝ)+2*(3748301063/4500000000000 : ℝ)*(11107/100000 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (56240753757801991/56250000000000000 : ℝ)+2*(3748301063/4500000000000 : ℝ)*(11107/100000 : ℝ)=(5000103275802549/5000000000000000 : ℝ) by norm_num, show 1+2*(936979730920963/20000000000000000000 : ℝ)=(10000936979730920963/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10674966810848617/50000000000000000000 : ℝ)+(936979730920963/20000000000000000000 : ℝ) ≤ ((56240753757801991/56250000000000000 : ℝ)+(3748301063/4500000000000 : ℝ)*((15517/100000 : ℝ)+(11107/100000 : ℝ)))^(4645/1024 : ℝ) := by
    rw [show (56240753757801991/56250000000000000 : ℝ)+(3748301063/4500000000000 : ℝ)*((15517/100000 : ℝ)+(11107/100000 : ℝ))=(1250071735638659/1250000000000000 : ℝ) by norm_num, show 1+(10674966810848617/50000000000000000000 : ℝ)+(936979730920963/20000000000000000000 : ℝ)=(100026034832276302049/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10674966810848617/50000000000000000000 : ℝ) ≤ ((56240753757801991/56250000000000000 : ℝ)+2*(3748301063/4500000000000 : ℝ)*(15517/100000 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (56240753757801991/56250000000000000 : ℝ)+2*(3748301063/4500000000000 : ℝ)*(15517/100000 : ℝ)=(5000470609306723/5000000000000000 : ℝ) by norm_num, show 1+2*(10674966810848617/50000000000000000000 : ℝ)=(25010674966810848617/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56240753757801991/56250000000000000 : ℝ)*(X 1 0+X 2 0)+(3748301063/4500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (11107/100000 : ℝ)) (hi := (15517/100000 : ℝ)) (c := (56240753757801991/56250000000000000 : ℝ)) (alpha := (3748301063/4500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56240753757801991/56250000000000000 : ℝ)*(X 0 1+X 2 1)+(3748301063/4500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (11107/100000 : ℝ)) (hi := (15517/100000 : ℝ)) (c := (56240753757801991/56250000000000000 : ℝ)) (alpha := (3748301063/4500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56240753757801991/56250000000000000 : ℝ)*(X 0 2+X 1 2)+(3748301063/4500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (11107/100000 : ℝ)) (hi := (15517/100000 : ℝ)) (c := (56240753757801991/56250000000000000 : ℝ)) (alpha := (3748301063/4500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-71151363/400000000 : ℝ)*X 0 0+(5425306359/10000000000 : ℝ)*X 0 1+(2610046939/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673961159/5000000000 : ℝ)*X 1 0+(-376752333/2000000000 : ℝ)*X 1 1+(2610046947/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213916893/400000000 : ℝ)*X 2 0+(2610046943/5000000000 : ℝ)*X 2 1+(-941880833/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4241295079/10000000000 : ℝ)*X 0 0+(2001939159/5000000000 : ℝ)*X 0 1+(4489945451/10000000000 : ℝ)*X 0 2+(4241295079/10000000000 : ℝ)*X 1 0+(2001939159/5000000000 : ℝ)*X 1 1+(4489945451/10000000000 : ℝ)*X 1 2+(4241295079/10000000000 : ℝ)*X 2 0+(2001939159/5000000000 : ℝ)*X 2 1+(4489945451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-889405183/5000000000 : ℝ)*X 0 0+(26105827/50000000 : ℝ)*X 0 1+(2712113603/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((105871943/200000000 : ℝ)*X 1 0+(-26244207/156250000 : ℝ)*X 1 1+(1084845341/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646799019/5000000000 : ℝ)*X 2 0+(5424226323/10000000000 : ℝ)*X 2 1+(-1679628553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4241358357/10000000000 : ℝ)*X 0 0+(560926013/1250000000 : ℝ)*X 0 1+(4006434423/10000000000 : ℝ)*X 0 2+(4241358357/10000000000 : ℝ)*X 1 0+(560926013/1250000000 : ℝ)*X 1 1+(4006434423/10000000000 : ℝ)*X 1 2+(4241358357/10000000000 : ℝ)*X 2 0+(560926013/1250000000 : ℝ)*X 2 1+(4006434423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (345159870690882569365369/156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (370779269/100000000000000 : ℝ)*(base19) + (358369829/100000000000000 : ℝ)*(base23) + (502379/5000000000000 : ℝ)*(lower2) + (27983749/50000000000000 : ℝ)*(upper3) + (42309171/100000000000000 : ℝ)*(upper5) + (3465172408182127/100000000000000 : ℝ)*(major0) + (3465172408182127/100000000000000 : ℝ)*(major1) + (3465172408182127/100000000000000 : ℝ)*(major2) + (1218251099079187/25000000000000 : ℝ)*(sp0) + (4873010347794117/100000000000000 : ℝ)*(sp1) + (4873010360203557/100000000000000 : ℝ)*(sp2) + (1028665688928921/50000000000000 : ℝ)*(sp3) + (3161128319/50000000000000 : ℝ)*(sp4) + (2646298907/100000000000000 : ℝ)*(sp7) + (514333506039187/25000000000000 : ℝ)*(f.failure) + (2436505359286693/50000000000000 : ℝ)*(f.sum) + (116751054119/56250000000000000000000000 : ℝ)*base65 + (67096317421272643/5625000000000000000000000000000 : ℝ)*base68 + (108187936690647643/5625000000000000000000000000000 : ℝ)*base70 + (21971671398147643/5625000000000000000000000000000 : ℝ)*base72 + (249768531613/112500000000000000000000000 : ℝ)*base73 + (82219895961897643/5625000000000000000000000000000 : ℝ)*base76 + (13739727744977357/5625000000000000000000000000000 : ℝ)*base77 + (113573593002522643/5625000000000000000000000000000 : ℝ)*base80 + (1028310301/219726562500000000000000 : ℝ)*base82 + (25616177/2500000000000000000000 : ℝ)*base90 + (25616177/2500000000000000000000 : ℝ)*base92 + (25616177/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (332403342069005353457491/78125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (253258169/100000000000000 : ℝ)*(base19) + (765873997/100000000000000 : ℝ)*(base23) + (57772637/25000000000000 : ℝ)*(lower2) + (3068029/25000000000000 : ℝ)*(lower3) + (1750939706312247/50000000000000 : ℝ)*(major0) + (1750939706312247/50000000000000 : ℝ)*(major1) + (1750939706312247/50000000000000 : ℝ)*(major2) + (145207429/2500000000000 : ℝ)*(sp0) + (11991237991/100000000000000 : ℝ)*(sp2) + (1021639687/25000000000000 : ℝ)*(sp3) + (61557815681241/1250000000000 : ℝ)*(sp4) + (4924630809538271/100000000000000 : ℝ)*(sp5) + (1231154576421113/25000000000000 : ℝ)*(sp6) + (1039561767034181/50000000000000 : ℝ)*(sp7) + (207912762062711/10000000000000 : ℝ)*(f.failure) + (123115776569911/2500000000000 : ℝ)*(f.sum) + (147373649731/18750000000000000000000000 : ℝ)*base65 + (1419866637098759/937500000000000000000000000000 : ℝ)*base67 + (3830652872723759/937500000000000000000000000000 : ℝ)*base69 + (4849479739598759/937500000000000000000000000000 : ℝ)*base71 + (73619457287/37500000000000000000000000 : ℝ)*base73 + (10136719533661259/937500000000000000000000000000 : ℝ)*base75 + (12696517301161259/937500000000000000000000000000 : ℝ)*base77 + (3539227658526241/937500000000000000000000000000 : ℝ)*base80 + (83722399487/37500000000000000000000000 : ℝ)*base81 + (13909181/1000000000000000000000 : ℝ)*base90 + (13909181/1000000000000000000000 : ℝ)*base92 + (13909181/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1575_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15517/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2227/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15487/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1575_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1575_s5_0 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1778805031/10000000000 : ℝ)*x 0 + (1085032581/2000000000 : ℝ)*x 1 + (1044044689/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1778805031/10000000000 : ℝ)^4647 ≤ (10919068804023/100000000000000 : ℝ)^3623 := by
    have hnat : (1778805031 : ℕ)^4647*100000000000000^3623 ≤ 10919068804023^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778805031 10000000000 10919068804023 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085032581/2000000000 : ℝ)^4647 ≤ (45640202085627/100000000000000 : ℝ)^3623 := by
    have hnat : (1085032581 : ℕ)^4647*100000000000000^3623 ≤ 45640202085627^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085032581 2000000000 45640202085627 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044044689/2000000000 : ℝ)^4647 ≤ (43440729105849/100000000000000 : ℝ)^3623 := by
    have hnat : (1044044689 : ℕ)^4647*100000000000000^3623 ≤ 43440729105849^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044044689 2000000000 43440729105849 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1778805031/10000000000 : ℝ), (1085032581/2000000000 : ℝ), (1044044689/2000000000 : ℝ)] ![(10919068804023/100000000000000 : ℝ), (45640202085627/100000000000000 : ℝ), (43440729105849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1778805031/10000000000 : ℝ)|^4647 ≤ (10919068804023/100000000000000 : ℝ)^3623
        have hw : |(-1778805031/10000000000 : ℝ)|=(1778805031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085032581/2000000000 : ℝ)|^4647 ≤ (45640202085627/100000000000000 : ℝ)^3623
        have hw : |(1085032581/2000000000 : ℝ)|=(1085032581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044044689/2000000000 : ℝ)|^4647 ≤ (43440729105849/100000000000000 : ℝ)^3623
        have hw : |(1044044689/2000000000 : ℝ)|=(1044044689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s5_1 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334242773/625000000 : ℝ)*x 0 + (-117727489/625000000 : ℝ)*x 1 + (5220223447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334242773/625000000 : ℝ)^4647 ≤ (44808017093857/100000000000000 : ℝ)^3623 := by
    have hnat : (334242773 : ℕ)^4647*100000000000000^3623 ≤ 44808017093857^3623*625000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334242773 625000000 44808017093857 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117727489/625000000 : ℝ)^4647 ≤ (5875626877607/50000000000000 : ℝ)^3623 := by
    have hnat : (117727489 : ℕ)^4647*50000000000000^3623 ≤ 5875626877607^3623*625000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117727489 625000000 5875626877607 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220223447/10000000000 : ℝ)^4647 ≤ (43440729127197/100000000000000 : ℝ)^3623 := by
    have hnat : (5220223447 : ℕ)^4647*100000000000000^3623 ≤ 43440729127197^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220223447 10000000000 43440729127197 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334242773/625000000 : ℝ), (-117727489/625000000 : ℝ), (5220223447/10000000000 : ℝ)] ![(44808017093857/100000000000000 : ℝ), (5875626877607/50000000000000 : ℝ), (43440729127197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334242773/625000000 : ℝ)|^4647 ≤ (44808017093857/100000000000000 : ℝ)^3623
        have hw : |(334242773/625000000 : ℝ)|=(334242773/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117727489/625000000 : ℝ)|^4647 ≤ (5875626877607/50000000000000 : ℝ)^3623
        have hw : |(-117727489/625000000 : ℝ)|=(117727489/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220223447/10000000000 : ℝ)|^4647 ≤ (43440729127197/100000000000000 : ℝ)^3623
        have hw : |(5220223447/10000000000 : ℝ)|=(5220223447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s5_2 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334242773/625000000 : ℝ)*x 0 + (5220223449/10000000000 : ℝ)*x 1 + (-1883639823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334242773/625000000 : ℝ)^4647 ≤ (44808017093857/100000000000000 : ℝ)^3623 := by
    have hnat : (334242773 : ℕ)^4647*100000000000000^3623 ≤ 44808017093857^3623*625000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334242773 625000000 44808017093857 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220223449/10000000000 : ℝ)^4647 ≤ (339380696473/781250000000 : ℝ)^3623 := by
    have hnat : (5220223449 : ℕ)^4647*781250000000^3623 ≤ 339380696473^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220223449 10000000000 339380696473 781250000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1883639823/10000000000 : ℝ)^4647 ≤ (2937813436803/25000000000000 : ℝ)^3623 := by
    have hnat : (1883639823 : ℕ)^4647*25000000000000^3623 ≤ 2937813436803^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883639823 10000000000 2937813436803 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334242773/625000000 : ℝ), (5220223449/10000000000 : ℝ), (-1883639823/10000000000 : ℝ)] ![(44808017093857/100000000000000 : ℝ), (339380696473/781250000000 : ℝ), (2937813436803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334242773/625000000 : ℝ)|^4647 ≤ (44808017093857/100000000000000 : ℝ)^3623
        have hw : |(334242773/625000000 : ℝ)|=(334242773/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220223449/10000000000 : ℝ)|^4647 ≤ (339380696473/781250000000 : ℝ)^3623
        have hw : |(5220223449/10000000000 : ℝ)|=(5220223449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1883639823/10000000000 : ℝ)|^4647 ≤ (2937813436803/25000000000000 : ℝ)^3623
        have hw : |(-1883639823/10000000000 : ℝ)|=(1883639823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s5_3 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (848261701/2000000000 : ℝ)*x 0 + (800840027/2000000000 : ℝ)*x 1 + (448962067/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848261701/2000000000 : ℝ)^4647 ≤ (33282574290209/100000000000000 : ℝ)^3623 := by
    have hnat : (848261701 : ℕ)^4647*100000000000000^3623 ≤ 33282574290209^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848261701 2000000000 33282574290209 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (800840027/2000000000 : ℝ)^4647 ≤ (30915149619519/100000000000000 : ℝ)^3623 := by
    have hnat : (800840027 : ℕ)^4647*100000000000000^3623 ≤ 30915149619519^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800840027 2000000000 30915149619519 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448962067/1000000000 : ℝ)^4647 ≤ (35802276069639/100000000000000 : ℝ)^3623 := by
    have hnat : (448962067 : ℕ)^4647*100000000000000^3623 ≤ 35802276069639^3623*1000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448962067 1000000000 35802276069639 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848261701/2000000000 : ℝ), (800840027/2000000000 : ℝ), (448962067/1000000000 : ℝ)] ![(33282574290209/100000000000000 : ℝ), (30915149619519/100000000000000 : ℝ), (35802276069639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848261701/2000000000 : ℝ)|^4647 ≤ (33282574290209/100000000000000 : ℝ)^3623
        have hw : |(848261701/2000000000 : ℝ)|=(848261701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(800840027/2000000000 : ℝ)|^4647 ≤ (30915149619519/100000000000000 : ℝ)^3623
        have hw : |(800840027/2000000000 : ℝ)|=(800840027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448962067/1000000000 : ℝ)|^4647 ≤ (35802276069639/100000000000000 : ℝ)^3623
        have hw : |(448962067/1000000000 : ℝ)|=(448962067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s5_4 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-355766333/2000000000 : ℝ)*x 0 + (5221292159/10000000000 : ℝ)*x 1 + (678010783/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (355766333/2000000000 : ℝ)^4647 ≤ (10919278504253/100000000000000 : ℝ)^3623 := by
    have hnat : (355766333 : ℕ)^4647*100000000000000^3623 ≤ 10919278504253^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355766333 2000000000 10919278504253 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221292159/10000000000 : ℝ)^4647 ≤ (543151706239/1250000000000 : ℝ)^3623 := by
    have hnat : (5221292159 : ℕ)^4647*1250000000000^3623 ≤ 543151706239^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221292159 10000000000 543151706239 1250000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678010783/1250000000 : ℝ)^4647 ≤ (4562858498243/10000000000000 : ℝ)^3623 := by
    have hnat : (678010783 : ℕ)^4647*10000000000000^3623 ≤ 4562858498243^3623*1250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678010783 1250000000 4562858498243 10000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-355766333/2000000000 : ℝ), (5221292159/10000000000 : ℝ), (678010783/1250000000 : ℝ)] ![(10919278504253/100000000000000 : ℝ), (543151706239/1250000000000 : ℝ), (4562858498243/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-355766333/2000000000 : ℝ)|^4647 ≤ (10919278504253/100000000000000 : ℝ)^3623
        have hw : |(-355766333/2000000000 : ℝ)|=(355766333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221292159/10000000000 : ℝ)|^4647 ≤ (543151706239/1250000000000 : ℝ)^3623
        have hw : |(5221292159/10000000000 : ℝ)|=(5221292159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678010783/1250000000 : ℝ)|^4647 ≤ (4562858498243/10000000000000 : ℝ)^3623
        have hw : |(678010783/1250000000 : ℝ)|=(678010783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s5_5 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293631823/10000000000 : ℝ)*x 0 + (-1679776873/10000000000 : ℝ)*x 1 + (135602157/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293631823/10000000000 : ℝ)^4647 ≤ (22112907620007/50000000000000 : ℝ)^3623 := by
    have hnat : (5293631823 : ℕ)^4647*50000000000000^3623 ≤ 22112907620007^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293631823 10000000000 22112907620007 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1679776873/10000000000 : ℝ)^4647 ≤ (10145599595613/100000000000000 : ℝ)^3623 := by
    have hnat : (1679776873 : ℕ)^4647*100000000000000^3623 ≤ 10145599595613^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1679776873 10000000000 10145599595613 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135602157/250000000 : ℝ)^4647 ≤ (11407146288767/25000000000000 : ℝ)^3623 := by
    have hnat : (135602157 : ℕ)^4647*25000000000000^3623 ≤ 11407146288767^3623*250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135602157 250000000 11407146288767 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293631823/10000000000 : ℝ), (-1679776873/10000000000 : ℝ), (135602157/250000000 : ℝ)] ![(22112907620007/50000000000000 : ℝ), (10145599595613/100000000000000 : ℝ), (11407146288767/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293631823/10000000000 : ℝ)|^4647 ≤ (22112907620007/50000000000000 : ℝ)^3623
        have hw : |(5293631823/10000000000 : ℝ)|=(5293631823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1679776873/10000000000 : ℝ)|^4647 ≤ (10145599595613/100000000000000 : ℝ)^3623
        have hw : |(-1679776873/10000000000 : ℝ)|=(1679776873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135602157/250000000 : ℝ)|^4647 ≤ (11407146288767/25000000000000 : ℝ)^3623
        have hw : |(135602157/250000000 : ℝ)|=(135602157/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s5_6 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211745263/400000000 : ℝ)*x 0 + (1084817299/2000000000 : ℝ)*x 1 + (-419944229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211745263/400000000 : ℝ)^4647 ≤ (11056453145621/25000000000000 : ℝ)^3623 := by
    have hnat : (211745263 : ℕ)^4647*25000000000000^3623 ≤ 11056453145621^3623*400000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211745263 400000000 11056453145621 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084817299/2000000000 : ℝ)^4647 ≤ (22814293737441/50000000000000 : ℝ)^3623 := by
    have hnat : (1084817299 : ℕ)^4647*50000000000000^3623 ≤ 22814293737441^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084817299 2000000000 22814293737441 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (419944229/2500000000 : ℝ)^4647 ≤ (2536399982183/25000000000000 : ℝ)^3623 := by
    have hnat : (419944229 : ℕ)^4647*25000000000000^3623 ≤ 2536399982183^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419944229 2500000000 2536399982183 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211745263/400000000 : ℝ), (1084817299/2000000000 : ℝ), (-419944229/2500000000 : ℝ)] ![(11056453145621/25000000000000 : ℝ), (22814293737441/50000000000000 : ℝ), (2536399982183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211745263/400000000 : ℝ)|^4647 ≤ (11056453145621/25000000000000 : ℝ)^3623
        have hw : |(211745263/400000000 : ℝ)|=(211745263/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084817299/2000000000 : ℝ)|^4647 ≤ (22814293737441/50000000000000 : ℝ)^3623
        have hw : |(1084817299/2000000000 : ℝ)|=(1084817299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-419944229/2500000000 : ℝ)|^4647 ≤ (2536399982183/25000000000000 : ℝ)^3623
        have hw : |(-419944229/2500000000 : ℝ)|=(419944229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s5_7 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265085731/625000000 : ℝ)*x 0 + (4487089301/10000000000 : ℝ)*x 1 + (1001687511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265085731/625000000 : ℝ)^4647 ≤ (16641605160051/50000000000000 : ℝ)^3623 := by
    have hnat : (265085731 : ℕ)^4647*50000000000000^3623 ≤ 16641605160051^3623*625000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265085731 625000000 16641605160051 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487089301/10000000000 : ℝ)^4647 ≤ (2236024151249/6250000000000 : ℝ)^3623 := by
    have hnat : (4487089301 : ℕ)^4647*6250000000000^3623 ≤ 2236024151249^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487089301 10000000000 2236024151249 6250000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001687511/2500000000 : ℝ)^4647 ≤ (30940403241363/100000000000000 : ℝ)^3623 := by
    have hnat : (1001687511 : ℕ)^4647*100000000000000^3623 ≤ 30940403241363^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001687511 2500000000 30940403241363 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265085731/625000000 : ℝ), (4487089301/10000000000 : ℝ), (1001687511/2500000000 : ℝ)] ![(16641605160051/50000000000000 : ℝ), (2236024151249/6250000000000 : ℝ), (30940403241363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265085731/625000000 : ℝ)|^4647 ≤ (16641605160051/50000000000000 : ℝ)^3623
        have hw : |(265085731/625000000 : ℝ)|=(265085731/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487089301/10000000000 : ℝ)|^4647 ≤ (2236024151249/6250000000000 : ℝ)^3623
        have hw : |(4487089301/10000000000 : ℝ)|=(4487089301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1001687511/2500000000 : ℝ)|^4647 ≤ (30940403241363/100000000000000 : ℝ)^3623
        have hw : |(1001687511/2500000000 : ℝ)|=(1001687511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1575_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15487/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2227/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11137/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15487/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2227/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15487/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2227/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15487/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2227/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15487/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2227/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15487/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2227/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15487/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2227/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2227/20000 : ℝ) ^ (4645/1024 : ℝ) ≤ (4738711103781891/100000000000000000000 : ℝ) := by
    have hpowers : (2227/20000 : ℝ)^4645 ≤ (4738711103781891/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2227 : ℕ)^4645*100000000000000000000^1024 ≤ 4738711103781891^1024*20000^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2227 20000 4738711103781891 100000000000000000000 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2227/20000 : ℝ)) (X := (4738711103781891/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15487/100000 : ℝ) ^ (4645/1024 : ℝ) ≤ (21163333844928861/100000000000000000000 : ℝ) := by
    have hpowers : (15487/100000 : ℝ)^4645 ≤ (21163333844928861/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15487 : ℕ)^4645*100000000000000000000^1024 ≤ 21163333844928861^1024*100000^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15487 100000 21163333844928861 100000000000000000000 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15487/100000 : ℝ)) (X := (21163333844928861/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004738711103781891/50000000000000000000 : ℝ) ≤ (2500052231011073/2500000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (50004738711103781891/50000000000000000000 : ℝ)^1024 ≤ (2500052231011073/2500000000000000 : ℝ)^4645 := by
      have hnat : (50004738711103781891 : ℕ)^1024*2500000000000000^4645 ≤ 2500052231011073^4645*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004738711103781891 50000000000000000000 2500052231011073 2500000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500052231011073/2500000000000000 : ℝ)) (X := (50004738711103781891/50000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125809438904647211/3125000000000000000 : ℝ) ≤ (10000570958377223/10000000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (3125809438904647211/3125000000000000000 : ℝ)^1024 ≤ (10000570958377223/10000000000000000 : ℝ)^4645 := by
      have hnat : (3125809438904647211 : ℕ)^1024*10000000000000000^4645 ≤ 10000570958377223^4645*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125809438904647211 3125000000000000000 10000570958377223 10000000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000570958377223/10000000000000000 : ℝ)) (X := (3125809438904647211/3125000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021163333844928861/50000000000000000000 : ℝ) ≤ (5000466496355077/5000000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (50021163333844928861/50000000000000000000 : ℝ)^1024 ≤ (5000466496355077/5000000000000000 : ℝ)^4645 := by
      have hnat : (50021163333844928861 : ℕ)^1024*5000000000000000^4645 ≤ 5000466496355077^4645*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021163333844928861 50000000000000000000 5000466496355077 5000000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000466496355077/5000000000000000 : ℝ)) (X := (50021163333844928861/50000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4738711103781891/100000000000000000000 : ℝ) ≤ ((1279789609789599571/1280000000000000000 : ℝ)+2*(362034332931/435200000000000 : ℝ)*(2227/20000 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (1279789609789599571/1280000000000000000 : ℝ)+2*(362034332931/435200000000000 : ℝ)*(2227/20000 : ℝ)=(2500052231011073/2500000000000000 : ℝ) by norm_num, show 1+2*(4738711103781891/100000000000000000000 : ℝ)=(50004738711103781891/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21163333844928861/100000000000000000000 : ℝ)+(4738711103781891/100000000000000000000 : ℝ) ≤ ((1279789609789599571/1280000000000000000 : ℝ)+(362034332931/435200000000000 : ℝ)*((15487/100000 : ℝ)+(2227/20000 : ℝ)))^(4645/1024 : ℝ) := by
    rw [show (1279789609789599571/1280000000000000000 : ℝ)+(362034332931/435200000000000 : ℝ)*((15487/100000 : ℝ)+(2227/20000 : ℝ))=(10000570958377223/10000000000000000 : ℝ) by norm_num, show 1+(21163333844928861/100000000000000000000 : ℝ)+(4738711103781891/100000000000000000000 : ℝ)=(3125809438904647211/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21163333844928861/100000000000000000000 : ℝ) ≤ ((1279789609789599571/1280000000000000000 : ℝ)+2*(362034332931/435200000000000 : ℝ)*(15487/100000 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (1279789609789599571/1280000000000000000 : ℝ)+2*(362034332931/435200000000000 : ℝ)*(15487/100000 : ℝ)=(5000466496355077/5000000000000000 : ℝ) by norm_num, show 1+2*(21163333844928861/100000000000000000000 : ℝ)=(50021163333844928861/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1279789609789599571/1280000000000000000 : ℝ)*(X 1 0+X 2 0)+(362034332931/435200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (2227/20000 : ℝ)) (hi := (15487/100000 : ℝ)) (c := (1279789609789599571/1280000000000000000 : ℝ)) (alpha := (362034332931/435200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1279789609789599571/1280000000000000000 : ℝ)*(X 0 1+X 2 1)+(362034332931/435200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (2227/20000 : ℝ)) (hi := (15487/100000 : ℝ)) (c := (1279789609789599571/1280000000000000000 : ℝ)) (alpha := (362034332931/435200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1279789609789599571/1280000000000000000 : ℝ)*(X 0 2+X 1 2)+(362034332931/435200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (2227/20000 : ℝ)) (hi := (15487/100000 : ℝ)) (c := (1279789609789599571/1280000000000000000 : ℝ)) (alpha := (362034332931/435200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1778805031/10000000000 : ℝ)*X 0 0+(1085032581/2000000000 : ℝ)*X 0 1+(1044044689/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334242773/625000000 : ℝ)*X 1 0+(-117727489/625000000 : ℝ)*X 1 1+(5220223447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334242773/625000000 : ℝ)*X 2 0+(5220223449/10000000000 : ℝ)*X 2 1+(-1883639823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((848261701/2000000000 : ℝ)*X 0 0+(800840027/2000000000 : ℝ)*X 0 1+(448962067/1000000000 : ℝ)*X 0 2+(848261701/2000000000 : ℝ)*X 1 0+(800840027/2000000000 : ℝ)*X 1 1+(448962067/1000000000 : ℝ)*X 1 2+(848261701/2000000000 : ℝ)*X 2 0+(800840027/2000000000 : ℝ)*X 2 1+(448962067/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-355766333/2000000000 : ℝ)*X 0 0+(5221292159/10000000000 : ℝ)*X 0 1+(678010783/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293631823/10000000000 : ℝ)*X 1 0+(-1679776873/10000000000 : ℝ)*X 1 1+(135602157/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211745263/400000000 : ℝ)*X 2 0+(1084817299/2000000000 : ℝ)*X 2 1+(-419944229/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((265085731/625000000 : ℝ)*X 0 0+(4487089301/10000000000 : ℝ)*X 0 1+(1001687511/2500000000 : ℝ)*X 0 2+(265085731/625000000 : ℝ)*X 1 0+(4487089301/10000000000 : ℝ)*X 1 1+(1001687511/2500000000 : ℝ)*X 1 2+(265085731/625000000 : ℝ)*X 2 0+(4487089301/10000000000 : ℝ)*X 2 1+(1001687511/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5650765781828002508474379429/544000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69925787/4000000000000 : ℝ)*(base19) + (1020189/62500000000 : ℝ)*(base23) + (6195111/10000000000000 : ℝ)*(lower2) + (127616369/50000000000000 : ℝ)*(upper3) + (6951661/4000000000000 : ℝ)*(upper5) + (3469821106696549/100000000000000 : ℝ)*(major0) + (3469821106696549/100000000000000 : ℝ)*(major1) + (3469821106696549/100000000000000 : ℝ)*(major2) + (2439759656752223/50000000000000 : ℝ)*(sp0) + (4879546080479339/100000000000000 : ℝ)*(sp1) + (975909239264323/20000000000000 : ℝ)*(sp2) + (2060081042105379/100000000000000 : ℝ)*(sp3) + (1782194973/6250000000000 : ℝ)*(sp4) + (3249103947/25000000000000 : ℝ)*(sp7) + (1030047019260583/50000000000000 : ℝ)*(f.failure) + (975909565724803/20000000000000 : ℝ)*(f.sum) + (3225215332399/21760000000000000000000000000 : ℝ)*base65 + (16035383449765181857/2176000000000000000000000000000000 : ℝ)*base68 + (22144233036069181857/2176000000000000000000000000000000 : ℝ)*base70 + (26424487206565181857/2176000000000000000000000000000000 : ℝ)*base72 + (103055362254801/21760000000000000000000000000 : ℝ)*base74 + (10018110786394818143/2176000000000000000000000000000000 : ℝ)*base75 + (19839784058533181857/2176000000000000000000000000000000 : ℝ)*base78 + (22195437501733181857/2176000000000000000000000000000000 : ℝ)*base80 + (84548274229201/21760000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (44636493/5000000000000000000000 : ℝ)*base90 + (44636493/5000000000000000000000 : ℝ)*base92 + (44636493/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (816644942609826630822084807/217600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (192226699/25000000000000 : ℝ)*(base19) + (627620977/100000000000000 : ℝ)*(base23) + (29539943/12500000000000 : ℝ)*(lower1) + (12341533/10000000000000 : ℝ)*(upper3) + (8918461/20000000000000 : ℝ)*(lower4) + (8746361/10000000000000 : ℝ)*(upper5) + (701295157446767/20000000000000 : ℝ)*(major0) + (701295157446767/20000000000000 : ℝ)*(major1) + (701295157446767/20000000000000 : ℝ)*(major2) + (107176407/20000000000000 : ℝ)*(sp2) + (2465547440001679/50000000000000 : ℝ)*(sp4) + (2465547055548281/50000000000000 : ℝ)*(sp5) + (4931093716500347/100000000000000 : ℝ)*(sp6) + (130116035585343/6250000000000 : ℝ)*(sp7) + (130116035585343/6250000000000 : ℝ)*(f.failure) + (2465547440001679/50000000000000 : ℝ)*(f.sum) + (1921276076621/4352000000000000000000000000 : ℝ)*base65 + (24969167820373021731/435200000000000000000000000000000 : ℝ)*base68 + (2754489985502178269/435200000000000000000000000000000 : ℝ)*base69 + (50534559389985821731/435200000000000000000000000000000 : ℝ)*base72 + (20188349172147/4352000000000000000000000000 : ℝ)*base74 + (30912933187652578269/435200000000000000000000000000000 : ℝ)*base75 + (668078210926621731/435200000000000000000000000000000 : ℝ)*base78 + (1821437989614621731/435200000000000000000000000000000 : ℝ)*base80 + (8425670234803/4352000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1783547/625000000000000000000 : ℝ)*base89 + (1783547/625000000000000000000 : ℝ)*base91 + (1783547/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1575_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15487/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2227/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1575_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1575_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15799/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10847/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1575_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1575_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1575_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15799/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10847/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1575_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

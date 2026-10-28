-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1203_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:03:58.189589+00:00
-- url     : https://prove2.me/submissions/a1a56f14-2a75-4e17-85e8-2357e46328e3

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
theorem support_rectangle_w1203_s3_0 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-426973013/2000000000 : ℝ)*x 0 + (1084638947/2000000000 : ℝ)*x 1 + (523748621/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426973013/2000000000 : ℝ)^2099 ≤ (12972122710201/100000000000000 : ℝ)^1587 := by
    have hnat : (426973013 : ℕ)^2099*100000000000000^1587 ≤ 12972122710201^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426973013 2000000000 12972122710201 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084638947/2000000000 : ℝ)^2099 ≤ (44516423639823/100000000000000 : ℝ)^1587 := by
    have hnat : (1084638947 : ℕ)^2099*100000000000000^1587 ≤ 44516423639823^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084638947 2000000000 44516423639823 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523748621/1000000000 : ℝ)^2099 ≤ (42511453637117/100000000000000 : ℝ)^1587 := by
    have hnat : (523748621 : ℕ)^2099*100000000000000^1587 ≤ 42511453637117^1587*1000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523748621 1000000000 42511453637117 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-426973013/2000000000 : ℝ), (1084638947/2000000000 : ℝ), (523748621/1000000000 : ℝ)] ![(12972122710201/100000000000000 : ℝ), (44516423639823/100000000000000 : ℝ), (42511453637117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-426973013/2000000000 : ℝ)|^2099 ≤ (12972122710201/100000000000000 : ℝ)^1587
        have hw : |(-426973013/2000000000 : ℝ)|=(426973013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084638947/2000000000 : ℝ)|^2099 ≤ (44516423639823/100000000000000 : ℝ)^1587
        have hw : |(1084638947/2000000000 : ℝ)|=(1084638947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523748621/1000000000 : ℝ)|^2099 ≤ (42511453637117/100000000000000 : ℝ)^1587
        have hw : |(523748621/1000000000 : ℝ)|=(523748621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s3_1 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5352366383/10000000000 : ℝ)*x 0 + (-1114836263/5000000000 : ℝ)*x 1 + (5237486341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352366383/10000000000 : ℝ)^2099 ≤ (21874540723983/50000000000000 : ℝ)^1587 := by
    have hnat : (5352366383 : ℕ)^2099*50000000000000^1587 ≤ 21874540723983^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352366383 10000000000 21874540723983 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114836263/5000000000 : ℝ)^2099 ≤ (13739463495591/100000000000000 : ℝ)^1587 := by
    have hnat : (1114836263 : ℕ)^2099*100000000000000^1587 ≤ 13739463495591^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114836263 5000000000 13739463495591 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237486341/10000000000 : ℝ)^2099 ≤ (8502291008691/20000000000000 : ℝ)^1587 := by
    have hnat : (5237486341 : ℕ)^2099*20000000000000^1587 ≤ 8502291008691^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237486341 10000000000 8502291008691 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352366383/10000000000 : ℝ), (-1114836263/5000000000 : ℝ), (5237486341/10000000000 : ℝ)] ![(21874540723983/50000000000000 : ℝ), (13739463495591/100000000000000 : ℝ), (8502291008691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352366383/10000000000 : ℝ)|^2099 ≤ (21874540723983/50000000000000 : ℝ)^1587
        have hw : |(5352366383/10000000000 : ℝ)|=(5352366383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1114836263/5000000000 : ℝ)|^2099 ≤ (13739463495591/100000000000000 : ℝ)^1587
        have hw : |(-1114836263/5000000000 : ℝ)|=(1114836263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237486341/10000000000 : ℝ)|^2099 ≤ (8502291008691/20000000000000 : ℝ)^1587
        have hw : |(5237486341/10000000000 : ℝ)|=(5237486341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s3_2 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5352366299/10000000000 : ℝ)*x 0 + (5237486549/10000000000 : ℝ)*x 1 + (-2229672363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352366299/10000000000 : ℝ)^2099 ≤ (43749080539857/100000000000000 : ℝ)^1587 := by
    have hnat : (5352366299 : ℕ)^2099*100000000000000^1587 ≤ 43749080539857^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352366299 10000000000 43749080539857 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237486549/10000000000 : ℝ)^2099 ≤ (2125572863821/5000000000000 : ℝ)^1587 := by
    have hnat : (5237486549 : ℕ)^2099*5000000000000^1587 ≤ 2125572863821^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237486549 10000000000 2125572863821 5000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2229672363/10000000000 : ℝ)^2099 ≤ (13739462167121/100000000000000 : ℝ)^1587 := by
    have hnat : (2229672363 : ℕ)^2099*100000000000000^1587 ≤ 13739462167121^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229672363 10000000000 13739462167121 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352366299/10000000000 : ℝ), (5237486549/10000000000 : ℝ), (-2229672363/10000000000 : ℝ)] ![(43749080539857/100000000000000 : ℝ), (2125572863821/5000000000000 : ℝ), (13739462167121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352366299/10000000000 : ℝ)|^2099 ≤ (43749080539857/100000000000000 : ℝ)^1587
        have hw : |(5352366299/10000000000 : ℝ)|=(5352366299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237486549/10000000000 : ℝ)|^2099 ≤ (2125572863821/5000000000000 : ℝ)^1587
        have hw : |(5237486549/10000000000 : ℝ)|=(5237486549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2229672363/10000000000 : ℝ)|^2099 ≤ (13739462167121/100000000000000 : ℝ)^1587
        have hw : |(-2229672363/10000000000 : ℝ)|=(2229672363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s3_3 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4354251151/10000000000 : ℝ)*x 0 + (4171239977/10000000000 : ℝ)*x 1 + (1136281859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354251151/10000000000 : ℝ)^2099 ≤ (6659617221069/20000000000000 : ℝ)^1587 := by
    have hnat : (4354251151 : ℕ)^2099*20000000000000^1587 ≤ 6659617221069^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354251151 10000000000 6659617221069 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171239977/10000000000 : ℝ)^2099 ≤ (6291940832123/20000000000000 : ℝ)^1587 := by
    have hnat : (4171239977 : ℕ)^2099*20000000000000^1587 ≤ 6291940832123^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171239977 10000000000 6291940832123 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136281859/2500000000 : ℝ)^2099 ≤ (35242209717741/100000000000000 : ℝ)^1587 := by
    have hnat : (1136281859 : ℕ)^2099*100000000000000^1587 ≤ 35242209717741^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136281859 2500000000 35242209717741 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354251151/10000000000 : ℝ), (4171239977/10000000000 : ℝ), (1136281859/2500000000 : ℝ)] ![(6659617221069/20000000000000 : ℝ), (6291940832123/20000000000000 : ℝ), (35242209717741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354251151/10000000000 : ℝ)|^2099 ≤ (6659617221069/20000000000000 : ℝ)^1587
        have hw : |(4354251151/10000000000 : ℝ)|=(4354251151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171239977/10000000000 : ℝ)|^2099 ≤ (6291940832123/20000000000000 : ℝ)^1587
        have hw : |(4171239977/10000000000 : ℝ)|=(4171239977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1136281859/2500000000 : ℝ)|^2099 ≤ (35242209717741/100000000000000 : ℝ)^1587
        have hw : |(1136281859/2500000000 : ℝ)|=(1136281859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s3_4 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1067440463/5000000000 : ℝ)*x 0 + (654772307/1250000000 : ℝ)*x 1 + (5422498457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067440463/5000000000 : ℝ)^2099 ≤ (6486125089987/50000000000000 : ℝ)^1587 := by
    have hnat : (1067440463 : ℕ)^2099*50000000000000^1587 ≤ 6486125089987^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067440463 5000000000 6486125089987 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654772307/1250000000 : ℝ)^2099 ≤ (2657430333697/6250000000000 : ℝ)^1587 := by
    have hnat : (654772307 : ℕ)^2099*6250000000000^1587 ≤ 2657430333697^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654772307 1250000000 2657430333697 6250000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422498457/10000000000 : ℝ)^2099 ≤ (1390902014603/3125000000000 : ℝ)^1587 := by
    have hnat : (5422498457 : ℕ)^2099*3125000000000^1587 ≤ 1390902014603^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422498457 10000000000 1390902014603 3125000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1067440463/5000000000 : ℝ), (654772307/1250000000 : ℝ), (5422498457/10000000000 : ℝ)] ![(6486125089987/50000000000000 : ℝ), (2657430333697/6250000000000 : ℝ), (1390902014603/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1067440463/5000000000 : ℝ)|^2099 ≤ (6486125089987/50000000000000 : ℝ)^1587
        have hw : |(-1067440463/5000000000 : ℝ)|=(1067440463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654772307/1250000000 : ℝ)|^2099 ≤ (2657430333697/6250000000000 : ℝ)^1587
        have hw : |(654772307/1250000000 : ℝ)|=(654772307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422498457/10000000000 : ℝ)|^2099 ≤ (1390902014603/3125000000000 : ℝ)^1587
        have hw : |(5422498457/10000000000 : ℝ)|=(5422498457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s3_5 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652556421/5000000000 : ℝ)*x 0 + (-1597391/7812500 : ℝ)*x 1 + (1355624781/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652556421/5000000000 : ℝ)^2099 ≤ (10809740230051/25000000000000 : ℝ)^1587 := by
    have hnat : (2652556421 : ℕ)^2099*25000000000000^1587 ≤ 10809740230051^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652556421 5000000000 10809740230051 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1597391/7812500 : ℝ)^2099 ≤ (3063041839997/25000000000000 : ℝ)^1587 := by
    have hnat : (1597391 : ℕ)^2099*25000000000000^1587 ≤ 3063041839997^1587*7812500^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1597391 7812500 3063041839997 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355624781/2500000000 : ℝ)^2099 ≤ (2225443585423/5000000000000 : ℝ)^1587 := by
    have hnat : (1355624781 : ℕ)^2099*5000000000000^1587 ≤ 2225443585423^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355624781 2500000000 2225443585423 5000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652556421/5000000000 : ℝ), (-1597391/7812500 : ℝ), (1355624781/2500000000 : ℝ)] ![(10809740230051/25000000000000 : ℝ), (3063041839997/25000000000000 : ℝ), (2225443585423/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652556421/5000000000 : ℝ)|^2099 ≤ (10809740230051/25000000000000 : ℝ)^1587
        have hw : |(2652556421/5000000000 : ℝ)|=(2652556421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1597391/7812500 : ℝ)|^2099 ≤ (3063041839997/25000000000000 : ℝ)^1587
        have hw : |(-1597391/7812500 : ℝ)|=(1597391/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355624781/2500000000 : ℝ)|^2099 ≤ (2225443585423/5000000000000 : ℝ)^1587
        have hw : |(1355624781/2500000000 : ℝ)|=(1355624781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s3_6 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305114753/10000000000 : ℝ)*x 0 + (1084499659/2000000000 : ℝ)*x 1 + (-255582377/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305114753/10000000000 : ℝ)^2099 ≤ (43238981520661/100000000000000 : ℝ)^1587 := by
    have hnat : (5305114753 : ℕ)^2099*100000000000000^1587 ≤ 43238981520661^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305114753 10000000000 43238981520661 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084499659/2000000000 : ℝ)^2099 ≤ (11127215677143/25000000000000 : ℝ)^1587 := by
    have hnat : (1084499659 : ℕ)^2099*25000000000000^1587 ≤ 11127215677143^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084499659 2000000000 11127215677143 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255582377/1250000000 : ℝ)^2099 ≤ (12252155757043/100000000000000 : ℝ)^1587 := by
    have hnat : (255582377 : ℕ)^2099*100000000000000^1587 ≤ 12252155757043^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255582377 1250000000 12252155757043 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305114753/10000000000 : ℝ), (1084499659/2000000000 : ℝ), (-255582377/1250000000 : ℝ)] ![(43238981520661/100000000000000 : ℝ), (11127215677143/25000000000000 : ℝ), (12252155757043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305114753/10000000000 : ℝ)|^2099 ≤ (43238981520661/100000000000000 : ℝ)^1587
        have hw : |(5305114753/10000000000 : ℝ)|=(5305114753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084499659/2000000000 : ℝ)|^2099 ≤ (11127215677143/25000000000000 : ℝ)^1587
        have hw : |(1084499659/2000000000 : ℝ)|=(1084499659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-255582377/1250000000 : ℝ)|^2099 ≤ (12252155757043/100000000000000 : ℝ)^1587
        have hw : |(-255582377/1250000000 : ℝ)|=(255582377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s3_7 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4354282401/10000000000 : ℝ)*x 0 + (1135933799/2500000000 : ℝ)*x 1 + (4172639481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354282401/10000000000 : ℝ)^2099 ≤ (8324600545393/25000000000000 : ℝ)^1587 := by
    have hnat : (4354282401 : ℕ)^2099*25000000000000^1587 ≤ 8324600545393^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354282401 10000000000 8324600545393 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135933799/2500000000 : ℝ)^2099 ≤ (7045586489207/20000000000000 : ℝ)^1587 := by
    have hnat : (1135933799 : ℕ)^2099*20000000000000^1587 ≤ 7045586489207^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135933799 2500000000 7045586489207 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172639481/10000000000 : ℝ)^2099 ≤ (1967104084773/6250000000000 : ℝ)^1587 := by
    have hnat : (4172639481 : ℕ)^2099*6250000000000^1587 ≤ 1967104084773^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172639481 10000000000 1967104084773 6250000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354282401/10000000000 : ℝ), (1135933799/2500000000 : ℝ), (4172639481/10000000000 : ℝ)] ![(8324600545393/25000000000000 : ℝ), (7045586489207/20000000000000 : ℝ), (1967104084773/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354282401/10000000000 : ℝ)|^2099 ≤ (8324600545393/25000000000000 : ℝ)^1587
        have hw : |(4354282401/10000000000 : ℝ)|=(4354282401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1135933799/2500000000 : ℝ)|^2099 ≤ (7045586489207/20000000000000 : ℝ)^1587
        have hw : |(1135933799/2500000000 : ℝ)|=(1135933799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172639481/10000000000 : ℝ)|^2099 ≤ (1967104084773/6250000000000 : ℝ)^1587
        have hw : |(4172639481/10000000000 : ℝ)|=(4172639481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s3_8 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-7424559/5000000000 : ℝ)*x 0 + (1119442559/2000000000 : ℝ)*x 1 + (1247534951/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7424559/5000000000 : ℝ)^2099 ≤ (9082409057/50000000000000 : ℝ)^1587 := by
    have hnat : (7424559 : ℕ)^2099*50000000000000^1587 ≤ 9082409057^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7424559 5000000000 9082409057 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119442559/2000000000 : ℝ)^2099 ≤ (2900962911579/6250000000000 : ℝ)^1587 := by
    have hnat : (1119442559 : ℕ)^2099*6250000000000^1587 ≤ 2900962911579^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119442559 2000000000 2900962911579 6250000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1247534951/2000000000 : ℝ)^2099 ≤ (53566428589287/100000000000000 : ℝ)^1587 := by
    have hnat : (1247534951 : ℕ)^2099*100000000000000^1587 ≤ 53566428589287^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1247534951 2000000000 53566428589287 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7424559/5000000000 : ℝ), (1119442559/2000000000 : ℝ), (1247534951/2000000000 : ℝ)] ![(9082409057/50000000000000 : ℝ), (2900962911579/6250000000000 : ℝ), (53566428589287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7424559/5000000000 : ℝ)|^2099 ≤ (9082409057/50000000000000 : ℝ)^1587
        have hw : |(-7424559/5000000000 : ℝ)|=(7424559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119442559/2000000000 : ℝ)|^2099 ≤ (2900962911579/6250000000000 : ℝ)^1587
        have hw : |(1119442559/2000000000 : ℝ)|=(1119442559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1247534951/2000000000 : ℝ)|^2099 ≤ (53566428589287/100000000000000 : ℝ)^1587
        have hw : |(1247534951/2000000000 : ℝ)|=(1247534951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s3_9 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1051348503/10000000000 : ℝ)*x 0 + (-2179221449/5000000000 : ℝ)*x 1 + (6930759319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051348503/10000000000 : ℝ)^2099 ≤ (5083248619763/100000000000000 : ℝ)^1587 := by
    have hnat : (1051348503 : ℕ)^2099*100000000000000^1587 ≤ 5083248619763^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051348503 10000000000 5083248619763 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2179221449/5000000000 : ℝ)^2099 ≤ (1041890306537/3125000000000 : ℝ)^1587 := by
    have hnat : (2179221449 : ℕ)^2099*3125000000000^1587 ≤ 1041890306537^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179221449 5000000000 1041890306537 3125000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6930759319/10000000000 : ℝ)^2099 ≤ (6157626155309/10000000000000 : ℝ)^1587 := by
    have hnat : (6930759319 : ℕ)^2099*10000000000000^1587 ≤ 6157626155309^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6930759319 10000000000 6157626155309 10000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051348503/10000000000 : ℝ), (-2179221449/5000000000 : ℝ), (6930759319/10000000000 : ℝ)] ![(5083248619763/100000000000000 : ℝ), (1041890306537/3125000000000 : ℝ), (6157626155309/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051348503/10000000000 : ℝ)|^2099 ≤ (5083248619763/100000000000000 : ℝ)^1587
        have hw : |(1051348503/10000000000 : ℝ)|=(1051348503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2179221449/5000000000 : ℝ)|^2099 ≤ (1041890306537/3125000000000 : ℝ)^1587
        have hw : |(-2179221449/5000000000 : ℝ)|=(2179221449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6930759319/10000000000 : ℝ)|^2099 ≤ (6157626155309/10000000000000 : ℝ)^1587
        have hw : |(6930759319/10000000000 : ℝ)|=(6930759319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s3_10 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (6035619/62500000 : ℝ)*x 0 + (6927671443/10000000000 : ℝ)*x 1 + (-1103829927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6035619/62500000 : ℝ)^2099 ≤ (2271434133143/50000000000000 : ℝ)^1587 := by
    have hnat : (6035619 : ℕ)^2099*50000000000000^1587 ≤ 2271434133143^1587*62500000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6035619 62500000 2271434133143 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6927671443/10000000000 : ℝ)^2099 ≤ (3076998954977/5000000000000 : ℝ)^1587 := by
    have hnat : (6927671443 : ℕ)^2099*5000000000000^1587 ≤ 3076998954977^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6927671443 10000000000 3076998954977 5000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103829927/2500000000 : ℝ)^2099 ≤ (6783430523943/20000000000000 : ℝ)^1587 := by
    have hnat : (1103829927 : ℕ)^2099*20000000000000^1587 ≤ 6783430523943^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103829927 2500000000 6783430523943 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6035619/62500000 : ℝ), (6927671443/10000000000 : ℝ), (-1103829927/2500000000 : ℝ)] ![(2271434133143/50000000000000 : ℝ), (3076998954977/5000000000000 : ℝ), (6783430523943/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6035619/62500000 : ℝ)|^2099 ≤ (2271434133143/50000000000000 : ℝ)^1587
        have hw : |(6035619/62500000 : ℝ)|=(6035619/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6927671443/10000000000 : ℝ)|^2099 ≤ (3076998954977/5000000000000 : ℝ)^1587
        have hw : |(6927671443/10000000000 : ℝ)|=(6927671443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1103829927/2500000000 : ℝ)|^2099 ≤ (6783430523943/20000000000000 : ℝ)^1587
        have hw : |(-1103829927/2500000000 : ℝ)|=(1103829927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s3_11 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (156660163/1000000000 : ℝ)*x 0 + (5530548473/10000000000 : ℝ)*x 1 + (5531840243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156660163/1000000000 : ℝ)^2099 ≤ (8614598959027/100000000000000 : ℝ)^1587 := by
    have hnat : (156660163 : ℕ)^2099*100000000000000^1587 ≤ 8614598959027^1587*1000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156660163 1000000000 8614598959027 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5530548473/10000000000 : ℝ)^2099 ≤ (45685643539777/100000000000000 : ℝ)^1587 := by
    have hnat : (5530548473 : ℕ)^2099*100000000000000^1587 ≤ 45685643539777^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5530548473 10000000000 45685643539777 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5531840243/10000000000 : ℝ)^2099 ≤ (22849878745493/50000000000000 : ℝ)^1587 := by
    have hnat : (5531840243 : ℕ)^2099*50000000000000^1587 ≤ 22849878745493^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5531840243 10000000000 22849878745493 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(156660163/1000000000 : ℝ), (5530548473/10000000000 : ℝ), (5531840243/10000000000 : ℝ)] ![(8614598959027/100000000000000 : ℝ), (45685643539777/100000000000000 : ℝ), (22849878745493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(156660163/1000000000 : ℝ)|^2099 ≤ (8614598959027/100000000000000 : ℝ)^1587
        have hw : |(156660163/1000000000 : ℝ)|=(156660163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5530548473/10000000000 : ℝ)|^2099 ≤ (45685643539777/100000000000000 : ℝ)^1587
        have hw : |(5530548473/10000000000 : ℝ)|=(5530548473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5531840243/10000000000 : ℝ)|^2099 ≤ (22849878745493/50000000000000 : ℝ)^1587
        have hw : |(5531840243/10000000000 : ℝ)|=(5531840243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1203_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2041/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1351/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7369/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2041/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2041/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2041/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2041/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2041/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2041/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9337/100000 : ℝ) ^ (8395/2048 : ℝ) ≤ (3004175269266563/50000000000000000000 : ℝ) := by
    have hpowers : (9337/100000 : ℝ)^8395 ≤ (3004175269266563/50000000000000000000 : ℝ)^2048 := by
      have hnat : (9337 : ℕ)^8395*50000000000000000000^2048 ≤ 3004175269266563^2048*100000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9337 100000 3004175269266563 50000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9337/100000 : ℝ)) (X := (3004175269266563/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2041/12500 : ℝ) ^ (8395/2048 : ℝ) ≤ (14847626455071761/25000000000000000000 : ℝ) := by
    have hpowers : (2041/12500 : ℝ)^8395 ≤ (14847626455071761/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2041 : ℕ)^8395*25000000000000000000^2048 ≤ 14847626455071761^2048*12500^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2041 12500 14847626455071761 25000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2041/12500 : ℝ)) (X := (14847626455071761/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003004175269266563/25000000000000000000 : ℝ) ≤ (2500073284949211/2500000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (25003004175269266563/25000000000000000000 : ℝ)^2048 ≤ (2500073284949211/2500000000000000 : ℝ)^8395 := by
      have hnat : (25003004175269266563 : ℕ)^2048*2500000000000000^8395 ≤ 2500073284949211^8395*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003004175269266563 25000000000000000000 2500073284949211 2500000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500073284949211/2500000000000000 : ℝ)) (X := (25003004175269266563/25000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10006539885635882017/10000000000000000000 : ℝ) ≤ (2500398760447561/2500000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (10006539885635882017/10000000000000000000 : ℝ)^2048 ≤ (2500398760447561/2500000000000000 : ℝ)^8395 := by
      have hnat : (10006539885635882017 : ℕ)^2048*2500000000000000^8395 ≤ 2500398760447561^8395*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006539885635882017 10000000000000000000 2500398760447561 2500000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500398760447561/2500000000000000 : ℝ)) (X := (10006539885635882017/10000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12514847626455071761/12500000000000000000 : ℝ) ≤ (2500724235945911/2500000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (12514847626455071761/12500000000000000000 : ℝ)^2048 ≤ (2500724235945911/2500000000000000 : ℝ)^8395 := by
      have hnat : (12514847626455071761 : ℕ)^2048*2500000000000000^8395 ≤ 2500724235945911^8395*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12514847626455071761 12500000000000000000 2500724235945911 2500000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500724235945911/2500000000000000 : ℝ)) (X := (12514847626455071761/12500000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3004175269266563/50000000000000000000 : ℝ) ≤ ((17471934405623746201/17477500000000000000 : ℝ)+2*(6509509967/3495500000000 : ℝ)*(9337/100000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (17471934405623746201/17477500000000000000 : ℝ)+2*(6509509967/3495500000000 : ℝ)*(9337/100000 : ℝ)=(2500073284949211/2500000000000000 : ℝ) by norm_num, show 1+2*(3004175269266563/50000000000000000000 : ℝ)=(25003004175269266563/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14847626455071761/25000000000000000000 : ℝ)+(3004175269266563/50000000000000000000 : ℝ) ≤ ((17471934405623746201/17477500000000000000 : ℝ)+(6509509967/3495500000000 : ℝ)*((2041/12500 : ℝ)+(9337/100000 : ℝ)))^(8395/2048 : ℝ) := by
    rw [show (17471934405623746201/17477500000000000000 : ℝ)+(6509509967/3495500000000 : ℝ)*((2041/12500 : ℝ)+(9337/100000 : ℝ))=(2500398760447561/2500000000000000 : ℝ) by norm_num, show 1+(14847626455071761/25000000000000000000 : ℝ)+(3004175269266563/50000000000000000000 : ℝ)=(10006539885635882017/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14847626455071761/25000000000000000000 : ℝ) ≤ ((17471934405623746201/17477500000000000000 : ℝ)+2*(6509509967/3495500000000 : ℝ)*(2041/12500 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (17471934405623746201/17477500000000000000 : ℝ)+2*(6509509967/3495500000000 : ℝ)*(2041/12500 : ℝ)=(2500724235945911/2500000000000000 : ℝ) by norm_num, show 1+2*(14847626455071761/25000000000000000000 : ℝ)=(12514847626455071761/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17471934405623746201/17477500000000000000 : ℝ)*(X 1 0+X 2 0)+(6509509967/3495500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (9337/100000 : ℝ)) (hi := (2041/12500 : ℝ)) (c := (17471934405623746201/17477500000000000000 : ℝ)) (alpha := (6509509967/3495500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17471934405623746201/17477500000000000000 : ℝ)*(X 0 1+X 2 1)+(6509509967/3495500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (9337/100000 : ℝ)) (hi := (2041/12500 : ℝ)) (c := (17471934405623746201/17477500000000000000 : ℝ)) (alpha := (6509509967/3495500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17471934405623746201/17477500000000000000 : ℝ)*(X 0 2+X 1 2)+(6509509967/3495500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (9337/100000 : ℝ)) (hi := (2041/12500 : ℝ)) (c := (17471934405623746201/17477500000000000000 : ℝ)) (alpha := (6509509967/3495500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-426973013/2000000000 : ℝ)*X 0 0+(1084638947/2000000000 : ℝ)*X 0 1+(523748621/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352366383/10000000000 : ℝ)*X 1 0+(-1114836263/5000000000 : ℝ)*X 1 1+(5237486341/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352366299/10000000000 : ℝ)*X 2 0+(5237486549/10000000000 : ℝ)*X 2 1+(-2229672363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354251151/10000000000 : ℝ)*X 0 0+(4171239977/10000000000 : ℝ)*X 0 1+(1136281859/2500000000 : ℝ)*X 0 2+(4354251151/10000000000 : ℝ)*X 1 0+(4171239977/10000000000 : ℝ)*X 1 1+(1136281859/2500000000 : ℝ)*X 1 2+(4354251151/10000000000 : ℝ)*X 2 0+(4171239977/10000000000 : ℝ)*X 2 1+(1136281859/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1067440463/5000000000 : ℝ)*X 0 0+(654772307/1250000000 : ℝ)*X 0 1+(5422498457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652556421/5000000000 : ℝ)*X 1 0+(-1597391/7812500 : ℝ)*X 1 1+(1355624781/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305114753/10000000000 : ℝ)*X 2 0+(1084499659/2000000000 : ℝ)*X 2 1+(-255582377/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354282401/10000000000 : ℝ)*X 0 0+(1135933799/2500000000 : ℝ)*X 0 1+(4172639481/10000000000 : ℝ)*X 0 2+(4354282401/10000000000 : ℝ)*X 1 0+(1135933799/2500000000 : ℝ)*X 1 1+(4172639481/10000000000 : ℝ)*X 1 2+(4354282401/10000000000 : ℝ)*X 2 0+(1135933799/2500000000 : ℝ)*X 2 1+(4172639481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-7424559/5000000000 : ℝ)*X 0 0+(1119442559/2000000000 : ℝ)*X 0 1+(1247534951/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1051348503/10000000000 : ℝ)*X 1 0+(-2179221449/5000000000 : ℝ)*X 1 1+(6930759319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((6035619/62500000 : ℝ)*X 2 0+(6927671443/10000000000 : ℝ)*X 2 1+(-1103829927/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((156660163/1000000000 : ℝ)*X 0 0+(5530548473/10000000000 : ℝ)*X 0 1+(5531840243/10000000000 : ℝ)*X 0 2+(156660163/1000000000 : ℝ)*X 1 0+(5530548473/10000000000 : ℝ)*X 1 1+(5531840243/10000000000 : ℝ)*X 1 2+(156660163/1000000000 : ℝ)*X 2 0+(5530548473/10000000000 : ℝ)*X 2 1+(5531840243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36352008736270847442561/3333568572998046875000000000 : ℝ) := by norm_num
    linear_combination (1007427286001041/25000000000000 : ℝ)*(major0) + (1007427286001041/25000000000000 : ℝ)*(major1) + (1007427286001041/25000000000000 : ℝ)*(major2) + (5384795928179921/100000000000000 : ℝ)*(sp0) + (2692400760318189/50000000000000 : ℝ)*(sp1) + (5384806952351267/100000000000000 : ℝ)*(sp2) + (334325692669947/12500000000000 : ℝ)*(sp3) + (10836917739/100000000000000 : ℝ)*(sp4) + (5374237451/100000000000000 : ℝ)*(sp5) + (3891950233/100000000000000 : ℝ)*(sp7) + (757478509/100000000000000 : ℝ)*(sp8) + (31385117/5000000000000 : ℝ)*(sp9) + (570224901/100000000000000 : ℝ)*(sp10) + (193725581/20000000000000 : ℝ)*(sp11) + (167163150121107/6250000000000 : ℝ)*(f.failure) + (673100940322021/12500000000000 : ℝ)*(f.sum) + (10714097082309/3495500000000000000000000000 : ℝ)*base66 + (5393166958301017259/436937500000000000000000000000000 : ℝ)*base68 + (5936339909711204759/436937500000000000000000000000000 : ℝ)*base70 + (1410285476593267259/436937500000000000000000000000000 : ℝ)*base72 + (7779885472233/6991000000000000000000000000 : ℝ)*base73 + (3352795696793329759/436937500000000000000000000000000 : ℝ)*base76 + (48901238533795241/436937500000000000000000000000000 : ℝ)*base77 + (802937595965517259/436937500000000000000000000000000 : ℝ)*base80 + (1394338291713/279640000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1354867/156250000000000000000 : ℝ)*base90 + (1354867/156250000000000000000 : ℝ)*base92 + (1354867/156250000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48390099411017525718165201/27308593750000000000000000000000 : ℝ) := by norm_num
    linear_combination (3186509/800000000000 : ℝ)*(lower2) + (31755589/20000000000000 : ℝ)*(upper4) + (1015015128111793/25000000000000 : ℝ)*(major0) + (1015015128111793/25000000000000 : ℝ)*(major1) + (1015015128111793/25000000000000 : ℝ)*(major2) + (11683640559/100000000000000 : ℝ)*(sp1) + (19904826483/100000000000000 : ℝ)*(sp2) + (11485463923/100000000000000 : ℝ)*(sp3) + (5425363876922027/100000000000000 : ℝ)*(sp4) + (5425353980742713/100000000000000 : ℝ)*(sp5) + (678168070575453/12500000000000 : ℝ)*(sp6) + (673685953995341/25000000000000 : ℝ)*(sp7) + (893730623/50000000000000 : ℝ)*(sp8) + (238990633/20000000000000 : ℝ)*(sp10) + (1347377650722643/50000000000000 : ℝ)*(f.failure) + (5425365664383273/100000000000000 : ℝ)*(f.sum) + (1849125944723/6991000000000000000000000000 : ℝ)*base65 + (3717036872222139107/436937500000000000000000000000000 : ℝ)*base68 + (911308511768639107/436937500000000000000000000000000 : ℝ)*base70 + (9013907310469201607/436937500000000000000000000000000 : ℝ)*base72 + (27569075698471/6991000000000000000000000000 : ℝ)*base74 + (838132016022485893/436937500000000000000000000000000 : ℝ)*base75 + (334525951218326607/436937500000000000000000000000000 : ℝ)*base78 + (2045389351463389107/436937500000000000000000000000000 : ℝ)*base80 + (27513927460629/6991000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1761117/1250000000000000000000 : ℝ)*base89 + (1761117/1250000000000000000000 : ℝ)*base91 + (1761117/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1203_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2041/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1351/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1203_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1203_s4_0 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-66794213/312500000 : ℝ)*x 0 + (2699559151/5000000000 : ℝ)*x 1 + (5259892771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66794213/312500000 : ℝ)^2099 ≤ (12992618164097/100000000000000 : ℝ)^1587 := by
    have hnat : (66794213 : ℕ)^2099*100000000000000^1587 ≤ 12992618164097^1587*312500000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66794213 312500000 12992618164097 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699559151/5000000000 : ℝ)^2099 ≤ (44255218761659/100000000000000 : ℝ)^1587 := by
    have hnat : (2699559151 : ℕ)^2099*100000000000000^1587 ≤ 44255218761659^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699559151 5000000000 44255218761659 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259892771/10000000000 : ℝ)^2099 ≤ (21376081531463/50000000000000 : ℝ)^1587 := by
    have hnat : (5259892771 : ℕ)^2099*50000000000000^1587 ≤ 21376081531463^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259892771 10000000000 21376081531463 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66794213/312500000 : ℝ), (2699559151/5000000000 : ℝ), (5259892771/10000000000 : ℝ)] ![(12992618164097/100000000000000 : ℝ), (44255218761659/100000000000000 : ℝ), (21376081531463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66794213/312500000 : ℝ)|^2099 ≤ (12992618164097/100000000000000 : ℝ)^1587
        have hw : |(-66794213/312500000 : ℝ)|=(66794213/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699559151/5000000000 : ℝ)|^2099 ≤ (44255218761659/100000000000000 : ℝ)^1587
        have hw : |(2699559151/5000000000 : ℝ)|=(2699559151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259892771/10000000000 : ℝ)|^2099 ≤ (21376081531463/50000000000000 : ℝ)^1587
        have hw : |(5259892771/10000000000 : ℝ)|=(5259892771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s4_1 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673159101/5000000000 : ℝ)*x 0 + (-1104062831/5000000000 : ℝ)*x 1 + (2629946437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673159101/5000000000 : ℝ)^2099 ≤ (8736741515297/20000000000000 : ℝ)^1587 := by
    have hnat : (2673159101 : ℕ)^2099*20000000000000^1587 ≤ 8736741515297^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673159101 5000000000 8736741515297 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104062831/5000000000 : ℝ)^2099 ≤ (135641282371/1000000000000 : ℝ)^1587 := by
    have hnat : (1104062831 : ℕ)^2099*1000000000000^1587 ≤ 135641282371^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104062831 5000000000 135641282371 1000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629946437/5000000000 : ℝ)^2099 ≤ (42752164170197/100000000000000 : ℝ)^1587 := by
    have hnat : (2629946437 : ℕ)^2099*100000000000000^1587 ≤ 42752164170197^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629946437 5000000000 42752164170197 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673159101/5000000000 : ℝ), (-1104062831/5000000000 : ℝ), (2629946437/5000000000 : ℝ)] ![(8736741515297/20000000000000 : ℝ), (135641282371/1000000000000 : ℝ), (42752164170197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673159101/5000000000 : ℝ)|^2099 ≤ (8736741515297/20000000000000 : ℝ)^1587
        have hw : |(2673159101/5000000000 : ℝ)|=(2673159101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1104062831/5000000000 : ℝ)|^2099 ≤ (135641282371/1000000000000 : ℝ)^1587
        have hw : |(-1104062831/5000000000 : ℝ)|=(1104062831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629946437/5000000000 : ℝ)|^2099 ≤ (42752164170197/100000000000000 : ℝ)^1587
        have hw : |(2629946437/5000000000 : ℝ)|=(2629946437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s4_2 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5346318193/10000000000 : ℝ)*x 0 + (210395711/400000000 : ℝ)*x 1 + (-441625161/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346318193/10000000000 : ℝ)^2099 ≤ (43683707479223/100000000000000 : ℝ)^1587 := by
    have hnat : (5346318193 : ℕ)^2099*100000000000000^1587 ≤ 43683707479223^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346318193 10000000000 43683707479223 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210395711/400000000 : ℝ)^2099 ≤ (42752163105927/100000000000000 : ℝ)^1587 := by
    have hnat : (210395711 : ℕ)^2099*100000000000000^1587 ≤ 42752163105927^1587*400000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210395711 400000000 42752163105927 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441625161/2000000000 : ℝ)^2099 ≤ (6782064699461/50000000000000 : ℝ)^1587 := by
    have hnat : (441625161 : ℕ)^2099*50000000000000^1587 ≤ 6782064699461^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441625161 2000000000 6782064699461 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346318193/10000000000 : ℝ), (210395711/400000000 : ℝ), (-441625161/2000000000 : ℝ)] ![(43683707479223/100000000000000 : ℝ), (42752163105927/100000000000000 : ℝ), (6782064699461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346318193/10000000000 : ℝ)|^2099 ≤ (43683707479223/100000000000000 : ℝ)^1587
        have hw : |(5346318193/10000000000 : ℝ)|=(5346318193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210395711/400000000 : ℝ)|^2099 ≤ (42752163105927/100000000000000 : ℝ)^1587
        have hw : |(210395711/400000000 : ℝ)|=(210395711/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441625161/2000000000 : ℝ)|^2099 ≤ (6782064699461/50000000000000 : ℝ)^1587
        have hw : |(-441625161/2000000000 : ℝ)|=(441625161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s4_3 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (34846211/80000000 : ℝ)*x 0 + (1054459027/2500000000 : ℝ)*x 1 + (1124534927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34846211/80000000 : ℝ)^2099 ≤ (33313513744627/100000000000000 : ℝ)^1587 := by
    have hnat : (34846211 : ℕ)^2099*100000000000000^1587 ≤ 33313513744627^1587*80000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34846211 80000000 33313513744627 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054459027/2500000000 : ℝ)^2099 ≤ (31925348950603/100000000000000 : ℝ)^1587 := by
    have hnat : (1054459027 : ℕ)^2099*100000000000000^1587 ≤ 31925348950603^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054459027 2500000000 31925348950603 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124534927/2500000000 : ℝ)^2099 ≤ (6952227456323/20000000000000 : ℝ)^1587 := by
    have hnat : (1124534927 : ℕ)^2099*20000000000000^1587 ≤ 6952227456323^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124534927 2500000000 6952227456323 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34846211/80000000 : ℝ), (1054459027/2500000000 : ℝ), (1124534927/2500000000 : ℝ)] ![(33313513744627/100000000000000 : ℝ), (31925348950603/100000000000000 : ℝ), (6952227456323/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34846211/80000000 : ℝ)|^2099 ≤ (33313513744627/100000000000000 : ℝ)^1587
        have hw : |(34846211/80000000 : ℝ)|=(34846211/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054459027/2500000000 : ℝ)|^2099 ≤ (31925348950603/100000000000000 : ℝ)^1587
        have hw : |(1054459027/2500000000 : ℝ)|=(1054459027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124534927/2500000000 : ℝ)|^2099 ≤ (6952227456323/20000000000000 : ℝ)^1587
        have hw : |(1124534927/2500000000 : ℝ)|=(1124534927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s4_4 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-267177597/1250000000 : ℝ)*x 0 + (2630141097/5000000000 : ℝ)*x 1 + (2699363859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267177597/1250000000 : ℝ)^2099 ≤ (12992666081119/100000000000000 : ℝ)^1587 := by
    have hnat : (267177597 : ℕ)^2099*100000000000000^1587 ≤ 12992666081119^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267177597 1250000000 12992666081119 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630141097/5000000000 : ℝ)^2099 ≤ (1336135921553/3125000000000 : ℝ)^1587 := by
    have hnat : (2630141097 : ℕ)^2099*3125000000000^1587 ≤ 1336135921553^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630141097 5000000000 1336135921553 3125000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699363859/5000000000 : ℝ)^2099 ≤ (22125492206863/50000000000000 : ℝ)^1587 := by
    have hnat : (2699363859 : ℕ)^2099*50000000000000^1587 ≤ 22125492206863^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699363859 5000000000 22125492206863 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267177597/1250000000 : ℝ), (2630141097/5000000000 : ℝ), (2699363859/5000000000 : ℝ)] ![(12992666081119/100000000000000 : ℝ), (1336135921553/3125000000000 : ℝ), (22125492206863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267177597/1250000000 : ℝ)|^2099 ≤ (12992666081119/100000000000000 : ℝ)^1587
        have hw : |(-267177597/1250000000 : ℝ)|=(267177597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630141097/5000000000 : ℝ)|^2099 ≤ (1336135921553/3125000000000 : ℝ)^1587
        have hw : |(2630141097/5000000000 : ℝ)|=(2630141097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699363859/5000000000 : ℝ)|^2099 ≤ (22125492206863/50000000000000 : ℝ)^1587
        have hw : |(2699363859/5000000000 : ℝ)|=(2699363859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s4_5 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2655445521/5000000000 : ℝ)*x 0 + (-2069291519/10000000000 : ℝ)*x 1 + (674840917/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655445521/5000000000 : ℝ)^2099 ≤ (5412657560087/12500000000000 : ℝ)^1587 := by
    have hnat : (2655445521 : ℕ)^2099*12500000000000^1587 ≤ 5412657560087^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655445521 5000000000 5412657560087 12500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069291519/10000000000 : ℝ)^2099 ≤ (1244775922941/10000000000000 : ℝ)^1587 := by
    have hnat : (2069291519 : ℕ)^2099*10000000000000^1587 ≤ 1244775922941^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069291519 10000000000 1244775922941 10000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674840917/1250000000 : ℝ)^2099 ≤ (22125490136243/50000000000000 : ℝ)^1587 := by
    have hnat : (674840917 : ℕ)^2099*50000000000000^1587 ≤ 22125490136243^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674840917 1250000000 22125490136243 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655445521/5000000000 : ℝ), (-2069291519/10000000000 : ℝ), (674840917/1250000000 : ℝ)] ![(5412657560087/12500000000000 : ℝ), (1244775922941/10000000000000 : ℝ), (22125490136243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655445521/5000000000 : ℝ)|^2099 ≤ (5412657560087/12500000000000 : ℝ)^1587
        have hw : |(2655445521/5000000000 : ℝ)|=(2655445521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069291519/10000000000 : ℝ)|^2099 ≤ (1244775922941/10000000000000 : ℝ)^1587
        have hw : |(-2069291519/10000000000 : ℝ)|=(2069291519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674840917/1250000000 : ℝ)|^2099 ≤ (22125490136243/50000000000000 : ℝ)^1587
        have hw : |(674840917/1250000000 : ℝ)|=(674840917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s4_6 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1327722883/2500000000 : ℝ)*x 0 + (5398727029/10000000000 : ℝ)*x 1 + (-1034645637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327722883/2500000000 : ℝ)^2099 ≤ (43301265764719/100000000000000 : ℝ)^1587 := by
    have hnat : (1327722883 : ℕ)^2099*100000000000000^1587 ≤ 43301265764719^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327722883 2500000000 43301265764719 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398727029/10000000000 : ℝ)^2099 ≤ (44250976944317/100000000000000 : ℝ)^1587 := by
    have hnat : (5398727029 : ℕ)^2099*100000000000000^1587 ≤ 44250976944317^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398727029 10000000000 44250976944317 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034645637/5000000000 : ℝ)^2099 ≤ (777984830009/6250000000000 : ℝ)^1587 := by
    have hnat : (1034645637 : ℕ)^2099*6250000000000^1587 ≤ 777984830009^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034645637 5000000000 777984830009 6250000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327722883/2500000000 : ℝ), (5398727029/10000000000 : ℝ), (-1034645637/5000000000 : ℝ)] ![(43301265764719/100000000000000 : ℝ), (44250976944317/100000000000000 : ℝ), (777984830009/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327722883/2500000000 : ℝ)|^2099 ≤ (43301265764719/100000000000000 : ℝ)^1587
        have hw : |(1327722883/2500000000 : ℝ)|=(1327722883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398727029/10000000000 : ℝ)|^2099 ≤ (44250976944317/100000000000000 : ℝ)^1587
        have hw : |(5398727029/10000000000 : ℝ)|=(5398727029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1034645637/5000000000 : ℝ)|^2099 ≤ (777984830009/6250000000000 : ℝ)^1587
        have hw : |(-1034645637/5000000000 : ℝ)|=(1034645637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s4_7 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (435578977/1000000000 : ℝ)*x 0 + (4497355417/10000000000 : ℝ)*x 1 + (421862327/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435578977/1000000000 : ℝ)^2099 ≤ (832841231069/2500000000000 : ℝ)^1587 := by
    have hnat : (435578977 : ℕ)^2099*2500000000000^1587 ≤ 832841231069^1587*1000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435578977 1000000000 832841231069 2500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497355417/10000000000 : ℝ)^2099 ≤ (17376560605223/50000000000000 : ℝ)^1587 := by
    have hnat : (4497355417 : ℕ)^2099*50000000000000^1587 ≤ 17376560605223^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497355417 10000000000 17376560605223 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421862327/1000000000 : ℝ)^2099 ≤ (31933229539247/100000000000000 : ℝ)^1587 := by
    have hnat : (421862327 : ℕ)^2099*100000000000000^1587 ≤ 31933229539247^1587*1000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421862327 1000000000 31933229539247 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435578977/1000000000 : ℝ), (4497355417/10000000000 : ℝ), (421862327/1000000000 : ℝ)] ![(832841231069/2500000000000 : ℝ), (17376560605223/50000000000000 : ℝ), (31933229539247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435578977/1000000000 : ℝ)|^2099 ≤ (832841231069/2500000000000 : ℝ)^1587
        have hw : |(435578977/1000000000 : ℝ)|=(435578977/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497355417/10000000000 : ℝ)|^2099 ≤ (17376560605223/50000000000000 : ℝ)^1587
        have hw : |(4497355417/10000000000 : ℝ)|=(4497355417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(421862327/1000000000 : ℝ)|^2099 ≤ (31933229539247/100000000000000 : ℝ)^1587
        have hw : |(421862327/1000000000 : ℝ)|=(421862327/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1203_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1351/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5643/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1351/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1351/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1351/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1351/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1351/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1351/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1351/12500 : ℝ) ^ (8395/2048 : ℝ) ≤ (5472365915707851/50000000000000000000 : ℝ) := by
    have hpowers : (1351/12500 : ℝ)^8395 ≤ (5472365915707851/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1351 : ℕ)^8395*50000000000000000000^2048 ≤ 5472365915707851^2048*12500^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1351 12500 5472365915707851 50000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1351/12500 : ℝ)) (X := (5472365915707851/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7369/50000 : ℝ) ^ (8395/2048 : ℝ) ≤ (39023743511140299/100000000000000000000 : ℝ) := by
    have hpowers : (7369/50000 : ℝ)^8395 ≤ (39023743511140299/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7369 : ℕ)^8395*100000000000000000000^2048 ≤ 39023743511140299^2048*50000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7369 50000 39023743511140299 100000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7369/50000 : ℝ)) (X := (39023743511140299/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005472365915707851/25000000000000000000 : ℝ) ≤ (1000053395964901/1000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (25005472365915707851/25000000000000000000 : ℝ)^2048 ≤ (1000053395964901/1000000000000000 : ℝ)^8395 := by
      have hnat : (25005472365915707851 : ℕ)^2048*1000000000000000^8395 ≤ 1000053395964901^8395*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005472365915707851 25000000000000000000 1000053395964901 1000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000053395964901/1000000000000000 : ℝ)) (X := (25005472365915707851/25000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049968475342556001/100000000000000000000 : ℝ) ≤ (1000121877442279/1000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (100049968475342556001/100000000000000000000 : ℝ)^2048 ≤ (1000121877442279/1000000000000000 : ℝ)^8395 := by
      have hnat : (100049968475342556001 : ℕ)^2048*1000000000000000^8395 ≤ 1000121877442279^8395*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049968475342556001 100000000000000000000 1000121877442279 1000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000121877442279/1000000000000000 : ℝ)) (X := (100049968475342556001/100000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039023743511140299/50000000000000000000 : ℝ) ≤ (1000190358919657/1000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (50039023743511140299/50000000000000000000 : ℝ)^2048 ≤ (1000190358919657/1000000000000000 : ℝ)^8395 := by
      have hnat : (50039023743511140299 : ℕ)^2048*1000000000000000^8395 ≤ 1000190358919657^8395*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039023743511140299 50000000000000000000 1000190358919657 1000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000190358919657/1000000000000000 : ℝ)) (X := (50039023743511140299/50000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5472365915707851/50000000000000000000 : ℝ) ≤ ((654788258421176347/655000000000000000 : ℝ)+2*(11413579563/6550000000000 : ℝ)*(1351/12500 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (654788258421176347/655000000000000000 : ℝ)+2*(11413579563/6550000000000 : ℝ)*(1351/12500 : ℝ)=(1000053395964901/1000000000000000 : ℝ) by norm_num, show 1+2*(5472365915707851/50000000000000000000 : ℝ)=(25005472365915707851/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39023743511140299/100000000000000000000 : ℝ)+(5472365915707851/50000000000000000000 : ℝ) ≤ ((654788258421176347/655000000000000000 : ℝ)+(11413579563/6550000000000 : ℝ)*((7369/50000 : ℝ)+(1351/12500 : ℝ)))^(8395/2048 : ℝ) := by
    rw [show (654788258421176347/655000000000000000 : ℝ)+(11413579563/6550000000000 : ℝ)*((7369/50000 : ℝ)+(1351/12500 : ℝ))=(1000121877442279/1000000000000000 : ℝ) by norm_num, show 1+(39023743511140299/100000000000000000000 : ℝ)+(5472365915707851/50000000000000000000 : ℝ)=(100049968475342556001/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39023743511140299/100000000000000000000 : ℝ) ≤ ((654788258421176347/655000000000000000 : ℝ)+2*(11413579563/6550000000000 : ℝ)*(7369/50000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (654788258421176347/655000000000000000 : ℝ)+2*(11413579563/6550000000000 : ℝ)*(7369/50000 : ℝ)=(1000190358919657/1000000000000000 : ℝ) by norm_num, show 1+2*(39023743511140299/100000000000000000000 : ℝ)=(50039023743511140299/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (654788258421176347/655000000000000000 : ℝ)*(X 1 0+X 2 0)+(11413579563/6550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (1351/12500 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (654788258421176347/655000000000000000 : ℝ)) (alpha := (11413579563/6550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (654788258421176347/655000000000000000 : ℝ)*(X 0 1+X 2 1)+(11413579563/6550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (1351/12500 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (654788258421176347/655000000000000000 : ℝ)) (alpha := (11413579563/6550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (654788258421176347/655000000000000000 : ℝ)*(X 0 2+X 1 2)+(11413579563/6550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (1351/12500 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (654788258421176347/655000000000000000 : ℝ)) (alpha := (11413579563/6550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66794213/312500000 : ℝ)*X 0 0+(2699559151/5000000000 : ℝ)*X 0 1+(5259892771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673159101/5000000000 : ℝ)*X 1 0+(-1104062831/5000000000 : ℝ)*X 1 1+(2629946437/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346318193/10000000000 : ℝ)*X 2 0+(210395711/400000000 : ℝ)*X 2 1+(-441625161/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34846211/80000000 : ℝ)*X 0 0+(1054459027/2500000000 : ℝ)*X 0 1+(1124534927/2500000000 : ℝ)*X 0 2+(34846211/80000000 : ℝ)*X 1 0+(1054459027/2500000000 : ℝ)*X 1 1+(1124534927/2500000000 : ℝ)*X 1 2+(34846211/80000000 : ℝ)*X 2 0+(1054459027/2500000000 : ℝ)*X 2 1+(1124534927/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-267177597/1250000000 : ℝ)*X 0 0+(2630141097/5000000000 : ℝ)*X 0 1+(2699363859/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655445521/5000000000 : ℝ)*X 1 0+(-2069291519/10000000000 : ℝ)*X 1 1+(674840917/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327722883/2500000000 : ℝ)*X 2 0+(5398727029/10000000000 : ℝ)*X 2 1+(-1034645637/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435578977/1000000000 : ℝ)*X 0 0+(4497355417/10000000000 : ℝ)*X 0 1+(421862327/1000000000 : ℝ)*X 0 2+(435578977/1000000000 : ℝ)*X 1 0+(4497355417/10000000000 : ℝ)*X 1 1+(421862327/1000000000 : ℝ)*X 1 2+(435578977/1000000000 : ℝ)*X 2 0+(4497355417/10000000000 : ℝ)*X 2 1+(421862327/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1007201146701075622389/163750000000000000000000000 : ℝ) := by norm_num
    linear_combination (231880299/12500000000000 : ℝ)*(base19) + (1616415253/100000000000000 : ℝ)*(base23) + (189025749/50000000000000 : ℝ)*(upper3) + (24222649/20000000000000 : ℝ)*(upper4) + (163983/25000000000000 : ℝ)*(upper5) + (5375148314518887/100000000000000 : ℝ)*(major0) + (5375148314518887/100000000000000 : ℝ)*(major1) + (671893539314861/12500000000000 : ℝ)*(major2) + (1795661436582989/25000000000000 : ℝ)*(sp0) + (897835665583993/12500000000000 : ℝ)*(sp1) + (7182685563299083/100000000000000 : ℝ)*(sp2) + (3567580740783187/100000000000000 : ℝ)*(sp3) + (2071669119/5000000000000 : ℝ)*(sp4) + (1425175601/5000000000000 : ℝ)*(sp7) + (3567609244295207/100000000000000 : ℝ)*(f.failure) + (1436537435942867/20000000000000 : ℝ)*(f.sum) + (95890460773/65500000000000000000000000 : ℝ)*base65 + (270166399079565789/65500000000000000000000000000000 : ℝ)*base67 + (6864851101555267/8187500000000000000000000000000 : ℝ)*base69 + (230531205967934211/65500000000000000000000000000000 : ℝ)*base72 + (404676087817/131000000000000000000000000 : ℝ)*base73 + (108610241794694733/8187500000000000000000000000000 : ℝ)*base76 + (12718661604734211/65500000000000000000000000000000 : ℝ)*base78 + (1702071710631765789/65500000000000000000000000000000 : ℝ)*base79 + (2529381564793/655000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (22033033/2500000000000000000000 : ℝ)*base89 + (22033033/2500000000000000000000 : ℝ)*base91 + (2966967/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (159538679758306660641697467/16375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (767934971/100000000000000 : ℝ)*(base19) + (596509869/25000000000000 : ℝ)*(base23) + (404271221/100000000000000 : ℝ)*(lower4) + (232274007/100000000000000 : ℝ)*(upper5) + (5405372200249987/100000000000000 : ℝ)*(major0) + (5405372200249987/100000000000000 : ℝ)*(major1) + (5405372200249987/100000000000000 : ℝ)*(major2) + (2306996123/50000000000000 : ℝ)*(sp0) + (10190892399/100000000000000 : ℝ)*(sp1) + (38744648211/100000000000000 : ℝ)*(sp2) + (3611534965572333/50000000000000 : ℝ)*(sp4) + (3611531793154771/50000000000000 : ℝ)*(sp5) + (288921336577969/4000000000000 : ℝ)*(sp6) + (717533906120477/20000000000000 : ℝ)*(sp7) + (717533906120477/20000000000000 : ℝ)*(f.failure) + (451442159071057/6250000000000 : ℝ)*(f.sum) + (642173655457/163750000000000000000000000 : ℝ)*base66 + (320620154605942511/65500000000000000000000000000000 : ℝ)*base68 + (51465705082442511/65500000000000000000000000000000 : ℝ)*base70 + (428645228606442511/65500000000000000000000000000000 : ℝ)*base72 + (1145320299967/655000000000000000000000000 : ℝ)*base73 + (1293764838534442511/65500000000000000000000000000000 : ℝ)*base76 + (258672729398057489/65500000000000000000000000000000 : ℝ)*base77 + (441704407892942511/65500000000000000000000000000000 : ℝ)*base80 + (520278765113/655000000000000000000000000 : ℝ)*base82 + (4114163/500000000000000000000 : ℝ)*base89 + (4114163/500000000000000000000 : ℝ)*base91 + (4114163/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1203_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1351/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1203_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1203_s5_0 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2137927187/10000000000 : ℝ)*x 0 + (2696680907/5000000000 : ℝ)*x 1 + (5265312881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137927187/10000000000 : ℝ)^2099 ≤ (3249184416493/25000000000000 : ℝ)^1587 := by
    have hnat : (2137927187 : ℕ)^2099*25000000000000^1587 ≤ 3249184416493^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137927187 10000000000 3249184416493 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696680907/5000000000 : ℝ)^2099 ≤ (44192822288023/100000000000000 : ℝ)^1587 := by
    have hnat : (2696680907 : ℕ)^2099*100000000000000^1587 ≤ 44192822288023^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696680907 5000000000 44192822288023 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265312881/10000000000 : ℝ)^2099 ≤ (42810440035441/100000000000000 : ℝ)^1587 := by
    have hnat : (5265312881 : ℕ)^2099*100000000000000^1587 ≤ 42810440035441^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265312881 10000000000 42810440035441 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2137927187/10000000000 : ℝ), (2696680907/5000000000 : ℝ), (5265312881/10000000000 : ℝ)] ![(3249184416493/25000000000000 : ℝ), (44192822288023/100000000000000 : ℝ), (42810440035441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2137927187/10000000000 : ℝ)|^2099 ≤ (3249184416493/25000000000000 : ℝ)^1587
        have hw : |(-2137927187/10000000000 : ℝ)|=(2137927187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696680907/5000000000 : ℝ)|^2099 ≤ (44192822288023/100000000000000 : ℝ)^1587
        have hw : |(2696680907/5000000000 : ℝ)|=(2696680907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265312881/10000000000 : ℝ)|^2099 ≤ (42810440035441/100000000000000 : ℝ)^1587
        have hw : |(5265312881/10000000000 : ℝ)|=(5265312881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s5_1 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672433571/5000000000 : ℝ)*x 0 + (-1101440469/5000000000 : ℝ)*x 1 + (65816411/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672433571/5000000000 : ℝ)^2099 ≤ (43668026836473/100000000000000 : ℝ)^1587 := by
    have hnat : (2672433571 : ℕ)^2099*100000000000000^1587 ≤ 43668026836473^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672433571 5000000000 43668026836473 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101440469/5000000000 : ℝ)^2099 ≤ (3380383282023/25000000000000 : ℝ)^1587 := by
    have hnat : (1101440469 : ℕ)^2099*25000000000000^1587 ≤ 3380383282023^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101440469 5000000000 3380383282023 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65816411/125000000 : ℝ)^2099 ≤ (2675652501543/6250000000000 : ℝ)^1587 := by
    have hnat : (65816411 : ℕ)^2099*6250000000000^1587 ≤ 2675652501543^1587*125000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65816411 125000000 2675652501543 6250000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672433571/5000000000 : ℝ), (-1101440469/5000000000 : ℝ), (65816411/125000000 : ℝ)] ![(43668026836473/100000000000000 : ℝ), (3380383282023/25000000000000 : ℝ), (2675652501543/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672433571/5000000000 : ℝ)|^2099 ≤ (43668026836473/100000000000000 : ℝ)^1587
        have hw : |(2672433571/5000000000 : ℝ)|=(2672433571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1101440469/5000000000 : ℝ)|^2099 ≤ (3380383282023/25000000000000 : ℝ)^1587
        have hw : |(-1101440469/5000000000 : ℝ)|=(1101440469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65816411/125000000 : ℝ)|^2099 ≤ (2675652501543/6250000000000 : ℝ)^1587
        have hw : |(65816411/125000000 : ℝ)|=(65816411/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s5_2 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068973429/2000000000 : ℝ)*x 0 + (1316328219/2500000000 : ℝ)*x 1 + (-2202880939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068973429/2000000000 : ℝ)^2099 ≤ (4366802686889/10000000000000 : ℝ)^1587 := by
    have hnat : (1068973429 : ℕ)^2099*10000000000000^1587 ≤ 4366802686889^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068973429 2000000000 4366802686889 10000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316328219/2500000000 : ℝ)^2099 ≤ (5351304997709/12500000000000 : ℝ)^1587 := by
    have hnat : (1316328219 : ℕ)^2099*12500000000000^1587 ≤ 5351304997709^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316328219 2500000000 5351304997709 12500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202880939/10000000000 : ℝ)^2099 ≤ (13521533136211/100000000000000 : ℝ)^1587 := by
    have hnat : (2202880939 : ℕ)^2099*100000000000000^1587 ≤ 13521533136211^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202880939 10000000000 13521533136211 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068973429/2000000000 : ℝ), (1316328219/2500000000 : ℝ), (-2202880939/10000000000 : ℝ)] ![(4366802686889/10000000000000 : ℝ), (5351304997709/12500000000000 : ℝ), (13521533136211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068973429/2000000000 : ℝ)|^2099 ≤ (4366802686889/10000000000000 : ℝ)^1587
        have hw : |(1068973429/2000000000 : ℝ)|=(1068973429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316328219/2500000000 : ℝ)|^2099 ≤ (5351304997709/12500000000000 : ℝ)^1587
        have hw : |(1316328219/2500000000 : ℝ)|=(1316328219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2202880939/10000000000 : ℝ)|^2099 ≤ (13521533136211/100000000000000 : ℝ)^1587
        have hw : |(-2202880939/10000000000 : ℝ)|=(2202880939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s5_3 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4356078171/10000000000 : ℝ)*x 0 + (105726207/250000000 : ℝ)*x 1 + (1121712479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356078171/10000000000 : ℝ)^2099 ≤ (33316566617447/100000000000000 : ℝ)^1587 := by
    have hnat : (4356078171 : ℕ)^2099*100000000000000^1587 ≤ 33316566617447^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356078171 10000000000 33316566617447 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105726207/250000000 : ℝ)^2099 ≤ (32037643142263/100000000000000 : ℝ)^1587 := by
    have hnat : (105726207 : ℕ)^2099*100000000000000^1587 ≤ 32037643142263^1587*250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105726207 250000000 32037643142263 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121712479/2500000000 : ℝ)^2099 ≤ (1385831608957/4000000000000 : ℝ)^1587 := by
    have hnat : (1121712479 : ℕ)^2099*4000000000000^1587 ≤ 1385831608957^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121712479 2500000000 1385831608957 4000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356078171/10000000000 : ℝ), (105726207/250000000 : ℝ), (1121712479/2500000000 : ℝ)] ![(33316566617447/100000000000000 : ℝ), (32037643142263/100000000000000 : ℝ), (1385831608957/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356078171/10000000000 : ℝ)|^2099 ≤ (33316566617447/100000000000000 : ℝ)^1587
        have hw : |(4356078171/10000000000 : ℝ)|=(4356078171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105726207/250000000 : ℝ)|^2099 ≤ (32037643142263/100000000000000 : ℝ)^1587
        have hw : |(105726207/250000000 : ℝ)|=(105726207/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121712479/2500000000 : ℝ)|^2099 ≤ (1385831608957/4000000000000 : ℝ)^1587
        have hw : |(1121712479/2500000000 : ℝ)|=(1121712479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s5_4 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2137931951/10000000000 : ℝ)*x 0 + (5265643107/10000000000 : ℝ)*x 1 + (5393030597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137931951/10000000000 : ℝ)^2099 ≤ (12996775970389/100000000000000 : ℝ)^1587 := by
    have hnat : (2137931951 : ℕ)^2099*100000000000000^1587 ≤ 12996775970389^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137931951 10000000000 12996775970389 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265643107/10000000000 : ℝ)^2099 ≤ (21406995624041/50000000000000 : ℝ)^1587 := by
    have hnat : (5265643107 : ℕ)^2099*50000000000000^1587 ≤ 21406995624041^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265643107 10000000000 21406995624041 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393030597/10000000000 : ℝ)^2099 ≤ (2761827048191/6250000000000 : ℝ)^1587 := by
    have hnat : (5393030597 : ℕ)^2099*6250000000000^1587 ≤ 2761827048191^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393030597 10000000000 2761827048191 6250000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2137931951/10000000000 : ℝ), (5265643107/10000000000 : ℝ), (5393030597/10000000000 : ℝ)] ![(12996775970389/100000000000000 : ℝ), (21406995624041/50000000000000 : ℝ), (2761827048191/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2137931951/10000000000 : ℝ)|^2099 ≤ (12996775970389/100000000000000 : ℝ)^1587
        have hw : |(-2137931951/10000000000 : ℝ)|=(2137931951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265643107/10000000000 : ℝ)|^2099 ≤ (21406995624041/50000000000000 : ℝ)^1587
        have hw : |(5265643107/10000000000 : ℝ)|=(5265643107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393030597/10000000000 : ℝ)|^2099 ≤ (2761827048191/6250000000000 : ℝ)^1587
        have hw : |(5393030597/10000000000 : ℝ)|=(5393030597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s5_5 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (332017723/625000000 : ℝ)*x 0 + (-2075162451/10000000000 : ℝ)*x 1 + (5393030473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332017723/625000000 : ℝ)^2099 ≤ (5414534716027/12500000000000 : ℝ)^1587 := by
    have hnat : (332017723 : ℕ)^2099*12500000000000^1587 ≤ 5414534716027^1587*625000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332017723 625000000 5414534716027 12500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075162451/10000000000 : ℝ)^2099 ≤ (12494490829631/100000000000000 : ℝ)^1587 := by
    have hnat : (2075162451 : ℕ)^2099*100000000000000^1587 ≤ 12494490829631^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075162451 10000000000 12494490829631 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393030473/10000000000 : ℝ)^2099 ≤ (44189231427237/100000000000000 : ℝ)^1587 := by
    have hnat : (5393030473 : ℕ)^2099*100000000000000^1587 ≤ 44189231427237^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393030473 10000000000 44189231427237 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332017723/625000000 : ℝ), (-2075162451/10000000000 : ℝ), (5393030473/10000000000 : ℝ)] ![(5414534716027/12500000000000 : ℝ), (12494490829631/100000000000000 : ℝ), (44189231427237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332017723/625000000 : ℝ)|^2099 ≤ (5414534716027/12500000000000 : ℝ)^1587
        have hw : |(332017723/625000000 : ℝ)|=(332017723/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2075162451/10000000000 : ℝ)|^2099 ≤ (12494490829631/100000000000000 : ℝ)^1587
        have hw : |(-2075162451/10000000000 : ℝ)|=(2075162451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393030473/10000000000 : ℝ)|^2099 ≤ (44189231427237/100000000000000 : ℝ)^1587
        have hw : |(5393030473/10000000000 : ℝ)|=(5393030473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s5_6 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656141471/5000000000 : ℝ)*x 0 + (5393031203/10000000000 : ℝ)*x 1 + (-415032461/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656141471/5000000000 : ℝ)^2099 ≤ (10829067744259/25000000000000 : ℝ)^1587 := by
    have hnat : (2656141471 : ℕ)^2099*25000000000000^1587 ≤ 10829067744259^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656141471 5000000000 10829067744259 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393031203/10000000000 : ℝ)^2099 ≤ (4418923933843/10000000000000 : ℝ)^1587 := by
    have hnat : (5393031203 : ℕ)^2099*10000000000000^1587 ≤ 4418923933843^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393031203 10000000000 4418923933843 10000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415032461/2000000000 : ℝ)^2099 ≤ (6247244833483/50000000000000 : ℝ)^1587 := by
    have hnat : (415032461 : ℕ)^2099*50000000000000^1587 ≤ 6247244833483^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415032461 2000000000 6247244833483 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656141471/5000000000 : ℝ), (5393031203/10000000000 : ℝ), (-415032461/2000000000 : ℝ)] ![(10829067744259/25000000000000 : ℝ), (4418923933843/10000000000000 : ℝ), (6247244833483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656141471/5000000000 : ℝ)|^2099 ≤ (10829067744259/25000000000000 : ℝ)^1587
        have hw : |(2656141471/5000000000 : ℝ)|=(2656141471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393031203/10000000000 : ℝ)|^2099 ≤ (4418923933843/10000000000000 : ℝ)^1587
        have hw : |(5393031203/10000000000 : ℝ)|=(5393031203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-415032461/2000000000 : ℝ)|^2099 ≤ (6247244833483/50000000000000 : ℝ)^1587
        have hw : |(-415032461/2000000000 : ℝ)|=(415032461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s5_7 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4356088839/10000000000 : ℝ)*x 0 + (2243093023/5000000000 : ℝ)*x 1 + (2114857071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356088839/10000000000 : ℝ)^2099 ≤ (33316674532807/100000000000000 : ℝ)^1587 := by
    have hnat : (4356088839 : ℕ)^2099*100000000000000^1587 ≤ 33316674532807^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356088839 10000000000 33316674532807 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243093023/5000000000 : ℝ)^2099 ≤ (34639010420249/100000000000000 : ℝ)^1587 := by
    have hnat : (2243093023 : ℕ)^2099*100000000000000^1587 ≤ 34639010420249^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243093023 5000000000 34639010420249 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114857071/5000000000 : ℝ)^2099 ≤ (32044315029367/100000000000000 : ℝ)^1587 := by
    have hnat : (2114857071 : ℕ)^2099*100000000000000^1587 ≤ 32044315029367^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114857071 5000000000 32044315029367 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356088839/10000000000 : ℝ), (2243093023/5000000000 : ℝ), (2114857071/5000000000 : ℝ)] ![(33316674532807/100000000000000 : ℝ), (34639010420249/100000000000000 : ℝ), (32044315029367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356088839/10000000000 : ℝ)|^2099 ≤ (33316674532807/100000000000000 : ℝ)^1587
        have hw : |(4356088839/10000000000 : ℝ)|=(4356088839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243093023/5000000000 : ℝ)|^2099 ≤ (34639010420249/100000000000000 : ℝ)^1587
        have hw : |(2243093023/5000000000 : ℝ)|=(2243093023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114857071/5000000000 : ℝ)|^2099 ≤ (32044315029367/100000000000000 : ℝ)^1587
        have hw : |(2114857071/5000000000 : ℝ)|=(2114857071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1203_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5701/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7057/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5643/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5643/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5643/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5643/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5643/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (5643/50000 : ℝ) ^ (8395/2048 : ℝ) ≤ (2613827437516977/20000000000000000000 : ℝ) := by
    have hpowers : (5643/50000 : ℝ)^8395 ≤ (2613827437516977/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5643 : ℕ)^8395*20000000000000000000^2048 ≤ 2613827437516977^2048*50000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5643 50000 2613827437516977 20000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5643/50000 : ℝ)) (X := (2613827437516977/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8395/2048 : ℝ) ≤ (16923093612991997/50000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8395 ≤ (16923093612991997/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8395*50000000000000000000^2048 ≤ 16923093612991997^2048*20000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 16923093612991997 50000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (16923093612991997/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002613827437516977/10000000000000000000 : ℝ) ≤ (5000318796291771/5000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (10002613827437516977/10000000000000000000 : ℝ)^2048 ≤ (5000318796291771/5000000000000000 : ℝ)^8395 := by
      have hnat : (10002613827437516977 : ℕ)^2048*5000000000000000^8395 ≤ 5000318796291771^8395*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002613827437516977 10000000000000000000 5000318796291771 5000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000318796291771/5000000000000000 : ℝ)) (X := (10002613827437516977/10000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046915324413568879/100000000000000000000 : ℝ) ≤ (5000572159313749/5000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (100046915324413568879/100000000000000000000 : ℝ)^2048 ≤ (5000572159313749/5000000000000000 : ℝ)^8395 := by
      have hnat : (100046915324413568879 : ℕ)^2048*5000000000000000^8395 ≤ 5000572159313749^8395*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046915324413568879 100000000000000000000 5000572159313749 5000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000572159313749/5000000000000000 : ℝ)) (X := (100046915324413568879/100000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016923093612991997/25000000000000000000 : ℝ) ≤ (5000825522335727/5000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (25016923093612991997/25000000000000000000 : ℝ)^2048 ≤ (5000825522335727/5000000000000000 : ℝ)^8395 := by
      have hnat : (25016923093612991997 : ℕ)^2048*5000000000000000^8395 ≤ 5000825522335727^8395*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016923093612991997 25000000000000000000 5000825522335727 5000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000825522335727/5000000000000000 : ℝ)) (X := (25016923093612991997/25000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2613827437516977/20000000000000000000 : ℝ) ≤ ((4913407073377448421/4915000000000000000 : ℝ)+2*(126681510989/73725000000000 : ℝ)*(5643/50000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (4913407073377448421/4915000000000000000 : ℝ)+2*(126681510989/73725000000000 : ℝ)*(5643/50000 : ℝ)=(5000318796291771/5000000000000000 : ℝ) by norm_num, show 1+2*(2613827437516977/20000000000000000000 : ℝ)=(10002613827437516977/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16923093612991997/50000000000000000000 : ℝ)+(2613827437516977/20000000000000000000 : ℝ) ≤ ((4913407073377448421/4915000000000000000 : ℝ)+(126681510989/73725000000000 : ℝ)*((2847/20000 : ℝ)+(5643/50000 : ℝ)))^(8395/2048 : ℝ) := by
    rw [show (4913407073377448421/4915000000000000000 : ℝ)+(126681510989/73725000000000 : ℝ)*((2847/20000 : ℝ)+(5643/50000 : ℝ))=(5000572159313749/5000000000000000 : ℝ) by norm_num, show 1+(16923093612991997/50000000000000000000 : ℝ)+(2613827437516977/20000000000000000000 : ℝ)=(100046915324413568879/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16923093612991997/50000000000000000000 : ℝ) ≤ ((4913407073377448421/4915000000000000000 : ℝ)+2*(126681510989/73725000000000 : ℝ)*(2847/20000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (4913407073377448421/4915000000000000000 : ℝ)+2*(126681510989/73725000000000 : ℝ)*(2847/20000 : ℝ)=(5000825522335727/5000000000000000 : ℝ) by norm_num, show 1+2*(16923093612991997/50000000000000000000 : ℝ)=(25016923093612991997/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4913407073377448421/4915000000000000000 : ℝ)*(X 1 0+X 2 0)+(126681510989/73725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (4913407073377448421/4915000000000000000 : ℝ)) (alpha := (126681510989/73725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4913407073377448421/4915000000000000000 : ℝ)*(X 0 1+X 2 1)+(126681510989/73725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (4913407073377448421/4915000000000000000 : ℝ)) (alpha := (126681510989/73725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4913407073377448421/4915000000000000000 : ℝ)*(X 0 2+X 1 2)+(126681510989/73725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (4913407073377448421/4915000000000000000 : ℝ)) (alpha := (126681510989/73725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2137927187/10000000000 : ℝ)*X 0 0+(2696680907/5000000000 : ℝ)*X 0 1+(5265312881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672433571/5000000000 : ℝ)*X 1 0+(-1101440469/5000000000 : ℝ)*X 1 1+(65816411/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068973429/2000000000 : ℝ)*X 2 0+(1316328219/2500000000 : ℝ)*X 2 1+(-2202880939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356078171/10000000000 : ℝ)*X 0 0+(105726207/250000000 : ℝ)*X 0 1+(1121712479/2500000000 : ℝ)*X 0 2+(4356078171/10000000000 : ℝ)*X 1 0+(105726207/250000000 : ℝ)*X 1 1+(1121712479/2500000000 : ℝ)*X 1 2+(4356078171/10000000000 : ℝ)*X 2 0+(105726207/250000000 : ℝ)*X 2 1+(1121712479/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2137931951/10000000000 : ℝ)*X 0 0+(5265643107/10000000000 : ℝ)*X 0 1+(5393030597/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((332017723/625000000 : ℝ)*X 1 0+(-2075162451/10000000000 : ℝ)*X 1 1+(5393030473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656141471/5000000000 : ℝ)*X 2 0+(5393031203/10000000000 : ℝ)*X 2 1+(-415032461/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356088839/10000000000 : ℝ)*X 0 0+(2243093023/5000000000 : ℝ)*X 0 1+(2114857071/5000000000 : ℝ)*X 0 2+(4356088839/10000000000 : ℝ)*X 1 0+(2243093023/5000000000 : ℝ)*X 1 1+(2114857071/5000000000 : ℝ)*X 1 2+(4356088839/10000000000 : ℝ)*X 2 0+(2243093023/5000000000 : ℝ)*X 2 1+(2114857071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68398731840941726820562763/24575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (534007759/100000000000000 : ℝ)*(base19) + (100361041/20000000000000 : ℝ)*(base23) + (195547/1000000000000 : ℝ)*(lower2) + (7010169/10000000000000 : ℝ)*(upper3) + (1682931/4000000000000 : ℝ)*(upper5) + (1168850983147501/20000000000000 : ℝ)*(major0) + (1168850983147501/20000000000000 : ℝ)*(major1) + (2922127457868753/50000000000000 : ℝ)*(major2) + (780952943516983/10000000000000 : ℝ)*(sp0) + (3904771573841847/50000000000000 : ℝ)*(sp1) + (976192897485781/12500000000000 : ℝ)*(sp2) + (969739571209527/25000000000000 : ℝ)*(sp3) + (14246521623/100000000000000 : ℝ)*(sp4) + (1943042487/25000000000000 : ℝ)*(sp7) + (3878966057008057/100000000000000 : ℝ)*(f.failure) + (7809543681691453/100000000000000 : ℝ)*(f.sum) + (13309577506793/14745000000000000000000000000 : ℝ)*base65 + (723641272639034079/98300000000000000000000000000000 : ℝ)*base68 + (2538873916518517039/737250000000000000000000000000000 : ℝ)*base69 + (468971457798734079/98300000000000000000000000000000 : ℝ)*base72 + (48460780622569/7372500000000000000000000000 : ℝ)*base73 + (6456681633354232961/737250000000000000000000000000000 : ℝ)*base76 + (2091059486434562237/294900000000000000000000000000000 : ℝ)*base78 + (6070574648124962237/294900000000000000000000000000000 : ℝ)*base80 + (1006348662943/737250000000000000000000000 : ℝ)*base82 + (35532183/2500000000000000000000 : ℝ)*base89 + (35532183/2500000000000000000000 : ℝ)*base91 + (10532183/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25066832095902207127516351/9830000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1041983319/50000000000000 : ℝ)*(base19) + (2158005611/100000000000000 : ℝ)*(base23) + (12235737/25000000000000 : ℝ)*(upper3) + (437655877/100000000000000 : ℝ)*(lower4) + (1468640347380553/25000000000000 : ℝ)*(major0) + (1468640347380553/25000000000000 : ℝ)*(major1) + (5874561389522213/100000000000000 : ℝ)*(major2) + (63718208003/100000000000000 : ℝ)*(sp1) + (92285480689/100000000000000 : ℝ)*(sp2) + (6444117427/50000000000000 : ℝ)*(sp3) + (314001661405691/4000000000000 : ℝ)*(sp4) + (3924987866483817/50000000000000 : ℝ)*(sp5) + (3924973545827987/50000000000000 : ℝ)*(sp6) + (3899068270666161/100000000000000 : ℝ)*(sp7) + (779816231780203/20000000000000 : ℝ)*(f.failure) + (314001661405691/4000000000000 : ℝ)*(f.sum) + (948448576753/491500000000000000000000000 : ℝ)*base65 + (4168196646481654561/368625000000000000000000000000000 : ℝ)*base68 + (6851354824067072981/1474500000000000000000000000000000 : ℝ)*base70 + (3910393481394154561/368625000000000000000000000000000 : ℝ)*base72 + (128703572523/30718750000000000000000000 : ℝ)*base73 + (21266806060218572981/1474500000000000000000000000000000 : ℝ)*base76 + (1225413193259520439/368625000000000000000000000000000 : ℝ)*base77 + (4081032625792229561/368625000000000000000000000000000 : ℝ)*base80 + (79035181532653/14745000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (4082757/500000000000000000000 : ℝ)*base89 + (4082757/500000000000000000000 : ℝ)*base91 + (917243/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1203_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5701/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1203_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1203_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2041/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5701/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1203_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1203_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1203_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2041/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5701/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1203_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

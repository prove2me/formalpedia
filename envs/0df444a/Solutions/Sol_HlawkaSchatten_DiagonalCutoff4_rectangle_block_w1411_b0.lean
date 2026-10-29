-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1411_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:46.815261+00:00
-- url     : https://prove2.me/submissions/c9f39b0a-cca4-41e8-aa09-1256cd8d82eb

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
theorem support_rectangle_w1411_s0_0 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-884524961/5000000000 : ℝ)*x 0 + (1193528909/2000000000 : ℝ)*x 1 + (965420549/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (884524961/5000000000 : ℝ)^4371 ≤ (5206662962989/50000000000000 : ℝ)^3347 := by
    have hnat : (884524961 : ℕ)^4371*50000000000000^3347 ≤ 5206662962989^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884524961 5000000000 5206662962989 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1193528909/2000000000 : ℝ)^4371 ≤ (25478909977803/50000000000000 : ℝ)^3347 := by
    have hnat : (1193528909 : ℕ)^4371*50000000000000^3347 ≤ 25478909977803^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193528909 2000000000 25478909977803 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965420549/2000000000 : ℝ)^4371 ≤ (19314427046979/50000000000000 : ℝ)^3347 := by
    have hnat : (965420549 : ℕ)^4371*50000000000000^3347 ≤ 19314427046979^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965420549 2000000000 19314427046979 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-884524961/5000000000 : ℝ), (1193528909/2000000000 : ℝ), (965420549/2000000000 : ℝ)] ![(5206662962989/50000000000000 : ℝ), (25478909977803/50000000000000 : ℝ), (19314427046979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-884524961/5000000000 : ℝ)|^4371 ≤ (5206662962989/50000000000000 : ℝ)^3347
        have hw : |(-884524961/5000000000 : ℝ)|=(884524961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1193528909/2000000000 : ℝ)|^4371 ≤ (25478909977803/50000000000000 : ℝ)^3347
        have hw : |(1193528909/2000000000 : ℝ)|=(1193528909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(965420549/2000000000 : ℝ)|^4371 ≤ (19314427046979/50000000000000 : ℝ)^3347
        have hw : |(965420549/2000000000 : ℝ)|=(965420549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s0_1 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (686762887/1250000000 : ℝ)*x 0 + (-2414146277/10000000000 : ℝ)*x 1 + (2413551529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (686762887/1250000000 : ℝ)^4371 ≤ (22871222285753/50000000000000 : ℝ)^3347 := by
    have hnat : (686762887 : ℕ)^4371*50000000000000^3347 ≤ 22871222285753^3347*1250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686762887 1250000000 22871222285753 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2414146277/10000000000 : ℝ)^4371 ≤ (15628698046529/100000000000000 : ℝ)^3347 := by
    have hnat : (2414146277 : ℕ)^4371*100000000000000^3347 ≤ 15628698046529^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2414146277 10000000000 15628698046529 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2413551529/5000000000 : ℝ)^4371 ≤ (7725771473013/20000000000000 : ℝ)^3347 := by
    have hnat : (2413551529 : ℕ)^4371*20000000000000^3347 ≤ 7725771473013^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2413551529 5000000000 7725771473013 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(686762887/1250000000 : ℝ), (-2414146277/10000000000 : ℝ), (2413551529/5000000000 : ℝ)] ![(22871222285753/50000000000000 : ℝ), (15628698046529/100000000000000 : ℝ), (7725771473013/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(686762887/1250000000 : ℝ)|^4371 ≤ (22871222285753/50000000000000 : ℝ)^3347
        have hw : |(686762887/1250000000 : ℝ)|=(686762887/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2414146277/10000000000 : ℝ)|^4371 ≤ (15628698046529/100000000000000 : ℝ)^3347
        have hw : |(-2414146277/10000000000 : ℝ)|=(2414146277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2413551529/5000000000 : ℝ)|^4371 ≤ (7725771473013/20000000000000 : ℝ)^3347
        have hw : |(2413551529/5000000000 : ℝ)|=(2413551529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s0_2 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (686762917/1250000000 : ℝ)*x 0 + (4827102927/10000000000 : ℝ)*x 1 + (-2414146131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (686762917/1250000000 : ℝ)^4371 ≤ (5717805897627/12500000000000 : ℝ)^3347 := by
    have hnat : (686762917 : ℕ)^4371*12500000000000^3347 ≤ 5717805897627^3347*1250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686762917 1250000000 5717805897627 12500000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4827102927/10000000000 : ℝ)^4371 ≤ (38628855996007/100000000000000 : ℝ)^3347 := by
    have hnat : (4827102927 : ℕ)^4371*100000000000000^3347 ≤ 38628855996007^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4827102927 10000000000 38628855996007 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2414146131/10000000000 : ℝ)^4371 ≤ (15628696812183/100000000000000 : ℝ)^3347 := by
    have hnat : (2414146131 : ℕ)^4371*100000000000000^3347 ≤ 15628696812183^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2414146131 10000000000 15628696812183 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(686762917/1250000000 : ℝ), (4827102927/10000000000 : ℝ), (-2414146131/10000000000 : ℝ)] ![(5717805897627/12500000000000 : ℝ), (38628855996007/100000000000000 : ℝ), (15628696812183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(686762917/1250000000 : ℝ)|^4371 ≤ (5717805897627/12500000000000 : ℝ)^3347
        have hw : |(686762917/1250000000 : ℝ)|=(686762917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4827102927/10000000000 : ℝ)|^4371 ≤ (38628855996007/100000000000000 : ℝ)^3347
        have hw : |(4827102927/10000000000 : ℝ)|=(4827102927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2414146131/10000000000 : ℝ)|^4371 ≤ (15628696812183/100000000000000 : ℝ)^3347
        have hw : |(-2414146131/10000000000 : ℝ)|=(2414146131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s0_3 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1042148413/2500000000 : ℝ)*x 0 + (193990301/625000000 : ℝ)*x 1 + (5554955637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042148413/2500000000 : ℝ)^4371 ≤ (6379065016617/20000000000000 : ℝ)^3347 := by
    have hnat : (1042148413 : ℕ)^4371*20000000000000^3347 ≤ 6379065016617^3347*2500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042148413 2500000000 6379065016617 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193990301/625000000 : ℝ)^4371 ≤ (2169946509731/10000000000000 : ℝ)^3347 := by
    have hnat : (193990301 : ℕ)^4371*10000000000000^3347 ≤ 2169946509731^3347*625000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193990301 625000000 2169946509731 10000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5554955637/10000000000 : ℝ)^4371 ≤ (5800651225201/12500000000000 : ℝ)^3347 := by
    have hnat : (5554955637 : ℕ)^4371*12500000000000^3347 ≤ 5800651225201^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5554955637 10000000000 5800651225201 12500000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042148413/2500000000 : ℝ), (193990301/625000000 : ℝ), (5554955637/10000000000 : ℝ)] ![(6379065016617/20000000000000 : ℝ), (2169946509731/10000000000000 : ℝ), (5800651225201/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042148413/2500000000 : ℝ)|^4371 ≤ (6379065016617/20000000000000 : ℝ)^3347
        have hw : |(1042148413/2500000000 : ℝ)|=(1042148413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(193990301/625000000 : ℝ)|^4371 ≤ (2169946509731/10000000000000 : ℝ)^3347
        have hw : |(193990301/625000000 : ℝ)|=(193990301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5554955637/10000000000 : ℝ)|^4371 ≤ (5800651225201/12500000000000 : ℝ)^3347
        have hw : |(5554955637/10000000000 : ℝ)|=(5554955637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s0_4 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-443288839/2500000000 : ℝ)*x 0 + (4856323637/10000000000 : ℝ)*x 1 + (2968689869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443288839/2500000000 : ℝ)^4371 ≤ (10444896872887/100000000000000 : ℝ)^3347 := by
    have hnat : (443288839 : ℕ)^4371*100000000000000^3347 ≤ 10444896872887^3347*2500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443288839 2500000000 10444896872887 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4856323637/10000000000 : ℝ)^4371 ≤ (9733629694557/25000000000000 : ℝ)^3347 := by
    have hnat : (4856323637 : ℕ)^4371*25000000000000^3347 ≤ 9733629694557^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4856323637 10000000000 9733629694557 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2968689869/5000000000 : ℝ)^4371 ≤ (2024823373321/4000000000000 : ℝ)^3347 := by
    have hnat : (2968689869 : ℕ)^4371*4000000000000^3347 ≤ 2024823373321^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2968689869 5000000000 2024823373321 4000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-443288839/2500000000 : ℝ), (4856323637/10000000000 : ℝ), (2968689869/5000000000 : ℝ)] ![(10444896872887/100000000000000 : ℝ), (9733629694557/25000000000000 : ℝ), (2024823373321/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-443288839/2500000000 : ℝ)|^4371 ≤ (10444896872887/100000000000000 : ℝ)^3347
        have hw : |(-443288839/2500000000 : ℝ)|=(443288839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4856323637/10000000000 : ℝ)|^4371 ≤ (9733629694557/25000000000000 : ℝ)^3347
        have hw : |(4856323637/10000000000 : ℝ)|=(4856323637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2968689869/5000000000 : ℝ)|^4371 ≤ (2024823373321/4000000000000 : ℝ)^3347
        have hw : |(2968689869/5000000000 : ℝ)|=(2968689869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s0_5 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2591444563/5000000000 : ℝ)*x 0 + (-65193457/500000000 : ℝ)*x 1 + (742172477/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591444563/5000000000 : ℝ)^4371 ≤ (42388343606383/100000000000000 : ℝ)^3347 := by
    have hnat : (2591444563 : ℕ)^4371*100000000000000^3347 ≤ 42388343606383^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591444563 5000000000 42388343606383 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65193457/500000000 : ℝ)^4371 ≤ (1747767793341/25000000000000 : ℝ)^3347 := by
    have hnat : (65193457 : ℕ)^4371*25000000000000^3347 ≤ 1747767793341^3347*500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65193457 500000000 1747767793341 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (742172477/1250000000 : ℝ)^4371 ≤ (5062058520149/10000000000000 : ℝ)^3347 := by
    have hnat : (742172477 : ℕ)^4371*10000000000000^3347 ≤ 5062058520149^3347*1250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742172477 1250000000 5062058520149 10000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591444563/5000000000 : ℝ), (-65193457/500000000 : ℝ), (742172477/1250000000 : ℝ)] ![(42388343606383/100000000000000 : ℝ), (1747767793341/25000000000000 : ℝ), (5062058520149/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591444563/5000000000 : ℝ)|^4371 ≤ (42388343606383/100000000000000 : ℝ)^3347
        have hw : |(2591444563/5000000000 : ℝ)|=(2591444563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-65193457/500000000 : ℝ)|^4371 ≤ (1747767793341/25000000000000 : ℝ)^3347
        have hw : |(-65193457/500000000 : ℝ)|=(65193457/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(742172477/1250000000 : ℝ)|^4371 ≤ (5062058520149/10000000000000 : ℝ)^3347
        have hw : |(742172477/1250000000 : ℝ)|=(742172477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s0_6 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2591444559/5000000000 : ℝ)*x 0 + (2968689879/5000000000 : ℝ)*x 1 + (-260773849/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591444559/5000000000 : ℝ)^4371 ≤ (21194171760469/50000000000000 : ℝ)^3347 := by
    have hnat : (2591444559 : ℕ)^4371*50000000000000^3347 ≤ 21194171760469^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591444559 5000000000 21194171760469 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2968689879/5000000000 : ℝ)^4371 ≤ (50620584555709/100000000000000 : ℝ)^3347 := by
    have hnat : (2968689879 : ℕ)^4371*100000000000000^3347 ≤ 50620584555709^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2968689879 5000000000 50620584555709 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260773849/2000000000 : ℝ)^4371 ≤ (1747767977149/25000000000000 : ℝ)^3347 := by
    have hnat : (260773849 : ℕ)^4371*25000000000000^3347 ≤ 1747767977149^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260773849 2000000000 1747767977149 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591444559/5000000000 : ℝ), (2968689879/5000000000 : ℝ), (-260773849/2000000000 : ℝ)] ![(21194171760469/50000000000000 : ℝ), (50620584555709/100000000000000 : ℝ), (1747767977149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591444559/5000000000 : ℝ)|^4371 ≤ (21194171760469/50000000000000 : ℝ)^3347
        have hw : |(2591444559/5000000000 : ℝ)|=(2591444559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2968689879/5000000000 : ℝ)|^4371 ≤ (50620584555709/100000000000000 : ℝ)^3347
        have hw : |(2968689879/5000000000 : ℝ)|=(2968689879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-260773849/2000000000 : ℝ)|^4371 ≤ (1747767977149/25000000000000 : ℝ)^3347
        have hw : |(-260773849/2000000000 : ℝ)|=(260773849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s0_7 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522177173/1250000000 : ℝ)*x 0 + (5492156839/10000000000 : ℝ)*x 1 + (3168886363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522177173/1250000000 : ℝ)^4371 ≤ (639670448133/2000000000000 : ℝ)^3347 := by
    have hnat : (522177173 : ℕ)^4371*2000000000000^3347 ≤ 639670448133^3347*1250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522177173 1250000000 639670448133 2000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5492156839/10000000000 : ℝ)^4371 ≤ (22860642075091/50000000000000 : ℝ)^3347 := by
    have hnat : (5492156839 : ℕ)^4371*50000000000000^3347 ≤ 22860642075091^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492156839 10000000000 22860642075091 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3168886363/10000000000 : ℝ)^4371 ≤ (11147596711853/50000000000000 : ℝ)^3347 := by
    have hnat : (3168886363 : ℕ)^4371*50000000000000^3347 ≤ 11147596711853^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3168886363 10000000000 11147596711853 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522177173/1250000000 : ℝ), (5492156839/10000000000 : ℝ), (3168886363/10000000000 : ℝ)] ![(639670448133/2000000000000 : ℝ), (22860642075091/50000000000000 : ℝ), (11147596711853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522177173/1250000000 : ℝ)|^4371 ≤ (639670448133/2000000000000 : ℝ)^3347
        have hw : |(522177173/1250000000 : ℝ)|=(522177173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5492156839/10000000000 : ℝ)|^4371 ≤ (22860642075091/50000000000000 : ℝ)^3347
        have hw : |(5492156839/10000000000 : ℝ)|=(5492156839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3168886363/10000000000 : ℝ)|^4371 ≤ (11147596711853/50000000000000 : ℝ)^3347
        have hw : |(3168886363/10000000000 : ℝ)|=(3168886363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1411_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (12/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26383/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (2185/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2185 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2185*1^512 ≤ 0^512*1^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2185/512 : ℝ) ≤ (2003364270293016497/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2185 ≤ (2003364270293016497/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2185*100000000000000000000^512 ≤ 2003364270293016497^512*5^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2003364270293016497 100000000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2003364270293016497/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2185 := by
      have hnat : (1 : ℕ)^512*1^2185 ≤ 1^2185*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102003364270293016497/100000000000000000000 : ℝ) ≤ (10046587967357011/10000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (102003364270293016497/100000000000000000000 : ℝ)^512 ≤ (10046587967357011/10000000000000000 : ℝ)^2185 := by
      have hnat : (102003364270293016497 : ℕ)^512*10000000000000000^2185 ≤ 10046587967357011^2185*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102003364270293016497 100000000000000000000 10046587967357011 10000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10046587967357011/10000000000000000 : ℝ)) (X := (102003364270293016497/100000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52003364270293016497/50000000000000000000 : ℝ) ≤ (5046587967357011/5000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (52003364270293016497/50000000000000000000 : ℝ)^512 ≤ (5046587967357011/5000000000000000 : ℝ)^2185 := by
      have hnat : (52003364270293016497 : ℕ)^512*5000000000000000^2185 ≤ 5046587967357011^2185*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52003364270293016497 50000000000000000000 5046587967357011 5000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5046587967357011/5000000000000000 : ℝ)) (X := (52003364270293016497/50000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(46587967357011/4000000000000000 : ℝ)*(0 : ℝ))^(2185/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(46587967357011/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2003364270293016497/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(46587967357011/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2185/512 : ℝ) := by
    rw [show (1 : ℝ)+(46587967357011/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10046587967357011/10000000000000000 : ℝ) by norm_num, show 1+(2003364270293016497/100000000000000000000 : ℝ)+(0 : ℝ)=(102003364270293016497/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2003364270293016497/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(46587967357011/4000000000000000 : ℝ)*(2/5 : ℝ))^(2185/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(46587967357011/4000000000000000 : ℝ)*(2/5 : ℝ)=(5046587967357011/5000000000000000 : ℝ) by norm_num, show 1+2*(2003364270293016497/100000000000000000000 : ℝ)=(52003364270293016497/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(46587967357011/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46587967357011/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(46587967357011/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46587967357011/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(46587967357011/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46587967357011/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-884524961/5000000000 : ℝ)*X 0 0+(1193528909/2000000000 : ℝ)*X 0 1+(965420549/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((686762887/1250000000 : ℝ)*X 1 0+(-2414146277/10000000000 : ℝ)*X 1 1+(2413551529/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((686762917/1250000000 : ℝ)*X 2 0+(4827102927/10000000000 : ℝ)*X 2 1+(-2414146131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1042148413/2500000000 : ℝ)*X 0 0+(193990301/625000000 : ℝ)*X 0 1+(5554955637/10000000000 : ℝ)*X 0 2+(1042148413/2500000000 : ℝ)*X 1 0+(193990301/625000000 : ℝ)*X 1 1+(5554955637/10000000000 : ℝ)*X 1 2+(1042148413/2500000000 : ℝ)*X 2 0+(193990301/625000000 : ℝ)*X 2 1+(5554955637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-443288839/2500000000 : ℝ)*X 0 0+(4856323637/10000000000 : ℝ)*X 0 1+(2968689869/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2591444563/5000000000 : ℝ)*X 1 0+(-65193457/500000000 : ℝ)*X 1 1+(742172477/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2591444559/5000000000 : ℝ)*X 2 0+(2968689879/5000000000 : ℝ)*X 2 1+(-260773849/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((522177173/1250000000 : ℝ)*X 0 0+(5492156839/10000000000 : ℝ)*X 0 1+(3168886363/10000000000 : ℝ)*X 0 2+(522177173/1250000000 : ℝ)*X 1 0+(5492156839/10000000000 : ℝ)*X 1 1+(3168886363/10000000000 : ℝ)*X 1 2+(522177173/1250000000 : ℝ)*X 2 0+(5492156839/10000000000 : ℝ)*X 2 1+(3168886363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (308836488289122055093263/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (772199841/100000000000000 : ℝ)*(base19) + (386584037/50000000000000 : ℝ)*(base23) + (47423331/50000000000000 : ℝ)*(upper3) + (20510789/100000000000000 : ℝ)*(upper4) + (111936813/100000000000000 : ℝ)*(upper5) + (321190735794311/50000000000000 : ℝ)*(major0) + (321190735794311/50000000000000 : ℝ)*(major1) + (321190735794311/50000000000000 : ℝ)*(major2) + (109597358941041/12500000000000 : ℝ)*(sp0) + (876781090002273/100000000000000 : ℝ)*(sp1) + (21919527225851/2500000000000 : ℝ)*(sp2) + (407979606237941/100000000000000 : ℝ)*(sp3) + (1495336893/50000000000000 : ℝ)*(sp4) + (1371791689/100000000000000 : ℝ)*(sp7) + (40798097802963/10000000000000 : ℝ)*(f.failure) + (438390931101057/50000000000000 : ℝ)*(f.sum) + (389125987835579/100000000000000000000000000000 : ℝ)*base66 + (848632674035579/200000000000000000000000000000 : ℝ)*base68 + (1051778609364421/200000000000000000000000000000 : ℝ)*base69 + (703729463435579/200000000000000000000000000000 : ℝ)*base72 + (452126330835579/100000000000000000000000000000 : ℝ)*base74 + (886370128164421/200000000000000000000000000000 : ℝ)*base75 + (592773509835579/200000000000000000000000000000 : ℝ)*base78 + (716090398364421/200000000000000000000000000000 : ℝ)*base79 + (437756271364421/100000000000000000000000000000 : ℝ)*base81 + (22493/50000000000000000000 : ℝ)*base90 + (22493/50000000000000000000 : ℝ)*base92 + (22493/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (703599248746674333277317/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (454481009/25000000000000 : ℝ)*(base19) + (1819415703/100000000000000 : ℝ)*(base23) + (88759077/100000000000000 : ℝ)*(base32) + (125667117/50000000000000 : ℝ)*(upper3) + (209546197/100000000000000 : ℝ)*(upper5) + (338862213099983/50000000000000 : ℝ)*(major0) + (338862213099983/50000000000000 : ℝ)*(major1) + (338862213099983/50000000000000 : ℝ)*(major2) + (4453253793/100000000000000 : ℝ)*(sp1) + (2250935223/50000000000000 : ℝ)*(sp2) + (925021081481269/100000000000000 : ℝ)*(sp4) + (11562685128793/1250000000000 : ℝ)*(sp5) + (11562684502439/1250000000000 : ℝ)*(sp6) + (860854895253/200000000000 : ℝ)*(sp7) + (430427536385577/100000000000000 : ℝ)*(f.failure) + (925021081481269/100000000000000 : ℝ)*(f.sum) + (96539324569187/100000000000000000000000000000 : ℝ)*base66 + (531247828430813/200000000000000000000000000000 : ℝ)*base67 + (1117643805369187/200000000000000000000000000000 : ℝ)*base70 + (280836914569187/200000000000000000000000000000 : ℝ)*base72 + (319894275130813/100000000000000000000000000000 : ℝ)*base73 + (1546571507769187/200000000000000000000000000000 : ℝ)*base76 + (137172004169187/200000000000000000000000000000 : ℝ)*base78 + (841216381369187/200000000000000000000000000000 : ℝ)*base80 + (79353468369187/100000000000000000000000000000 : ℝ)*base82 + (1806553/500000000000000000000 : ℝ)*base89 + (1806553/500000000000000000000 : ℝ)*base91 + (1806553/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1411_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (12/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26383/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1411_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1411_s1_0 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1943963109/10000000000 : ℝ)*x 0 + (5612522379/10000000000 : ℝ)*x 1 + (316882587/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1943963109/10000000000 : ℝ)^4371 ≤ (11777828653747/100000000000000 : ℝ)^3347 := by
    have hnat : (1943963109 : ℕ)^4371*100000000000000^3347 ≤ 11777828653747^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943963109 10000000000 11777828653747 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5612522379/10000000000 : ℝ)^4371 ≤ (47034236649419/100000000000000 : ℝ)^3347 := by
    have hnat : (5612522379 : ℕ)^4371*100000000000000^3347 ≤ 47034236649419^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5612522379 10000000000 47034236649419 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (316882587/625000000 : ℝ)^4371 ≤ (41187934674749/100000000000000 : ℝ)^3347 := by
    have hnat : (316882587 : ℕ)^4371*100000000000000^3347 ≤ 41187934674749^3347*625000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316882587 625000000 41187934674749 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1943963109/10000000000 : ℝ), (5612522379/10000000000 : ℝ), (316882587/625000000 : ℝ)] ![(11777828653747/100000000000000 : ℝ), (47034236649419/100000000000000 : ℝ), (41187934674749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1943963109/10000000000 : ℝ)|^4371 ≤ (11777828653747/100000000000000 : ℝ)^3347
        have hw : |(-1943963109/10000000000 : ℝ)|=(1943963109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5612522379/10000000000 : ℝ)|^4371 ≤ (47034236649419/100000000000000 : ℝ)^3347
        have hw : |(5612522379/10000000000 : ℝ)|=(5612522379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(316882587/625000000 : ℝ)|^4371 ≤ (41187934674749/100000000000000 : ℝ)^3347
        have hw : |(316882587/625000000 : ℝ)|=(316882587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s1_1 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (674828131/1250000000 : ℝ)*x 0 + (-2231777129/10000000000 : ℝ)*x 1 + (5070118437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674828131/1250000000 : ℝ)^4371 ≤ (44707086829731/100000000000000 : ℝ)^3347 := by
    have hnat : (674828131 : ℕ)^4371*100000000000000^3347 ≤ 44707086829731^3347*1250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674828131 1250000000 44707086829731 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2231777129/10000000000 : ℝ)^4371 ≤ (14105009820111/100000000000000 : ℝ)^3347 := by
    have hnat : (2231777129 : ℕ)^4371*100000000000000^3347 ≤ 14105009820111^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231777129 10000000000 14105009820111 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5070118437/10000000000 : ℝ)^4371 ≤ (4118790332499/10000000000000 : ℝ)^3347 := by
    have hnat : (5070118437 : ℕ)^4371*10000000000000^3347 ≤ 4118790332499^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5070118437 10000000000 4118790332499 10000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674828131/1250000000 : ℝ), (-2231777129/10000000000 : ℝ), (5070118437/10000000000 : ℝ)] ![(44707086829731/100000000000000 : ℝ), (14105009820111/100000000000000 : ℝ), (4118790332499/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674828131/1250000000 : ℝ)|^4371 ≤ (44707086829731/100000000000000 : ℝ)^3347
        have hw : |(674828131/1250000000 : ℝ)|=(674828131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2231777129/10000000000 : ℝ)|^4371 ≤ (14105009820111/100000000000000 : ℝ)^3347
        have hw : |(-2231777129/10000000000 : ℝ)|=(2231777129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5070118437/10000000000 : ℝ)|^4371 ≤ (4118790332499/10000000000000 : ℝ)^3347
        have hw : |(5070118437/10000000000 : ℝ)|=(5070118437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s1_2 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1349655827/2500000000 : ℝ)*x 0 + (2535060817/5000000000 : ℝ)*x 1 + (-1115887651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1349655827/2500000000 : ℝ)^4371 ≤ (11176767002997/25000000000000 : ℝ)^3347 := by
    have hnat : (1349655827 : ℕ)^4371*25000000000000^3347 ≤ 11176767002997^3347*2500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349655827 2500000000 11176767002997 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2535060817/5000000000 : ℝ)^4371 ≤ (2059396862107/5000000000000 : ℝ)^3347 := by
    have hnat : (2535060817 : ℕ)^4371*5000000000000^3347 ≤ 2059396862107^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2535060817 5000000000 2059396862107 5000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115887651/5000000000 : ℝ)^4371 ≤ (7052497370319/50000000000000 : ℝ)^3347 := by
    have hnat : (1115887651 : ℕ)^4371*50000000000000^3347 ≤ 7052497370319^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115887651 5000000000 7052497370319 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1349655827/2500000000 : ℝ), (2535060817/5000000000 : ℝ), (-1115887651/5000000000 : ℝ)] ![(11176767002997/25000000000000 : ℝ), (2059396862107/5000000000000 : ℝ), (7052497370319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1349655827/2500000000 : ℝ)|^4371 ≤ (11176767002997/25000000000000 : ℝ)^3347
        have hw : |(1349655827/2500000000 : ℝ)|=(1349655827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2535060817/5000000000 : ℝ)|^4371 ≤ (2059396862107/5000000000000 : ℝ)^3347
        have hw : |(2535060817/5000000000 : ℝ)|=(2535060817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1115887651/5000000000 : ℝ)|^4371 ≤ (7052497370319/50000000000000 : ℝ)^3347
        have hw : |(-1115887651/5000000000 : ℝ)|=(1115887651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s1_3 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4279907317/10000000000 : ℝ)*x 0 + (1866383489/5000000000 : ℝ)*x 1 + (979687323/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4279907317/10000000000 : ℝ)^4371 ≤ (33012112868647/100000000000000 : ℝ)^3347 := by
    have hnat : (4279907317 : ℕ)^4371*100000000000000^3347 ≤ 33012112868647^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4279907317 10000000000 33012112868647 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1866383489/5000000000 : ℝ)^4371 ≤ (13805928015229/50000000000000 : ℝ)^3347 := by
    have hnat : (1866383489 : ℕ)^4371*50000000000000^3347 ≤ 13805928015229^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866383489 5000000000 13805928015229 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979687323/2000000000 : ℝ)^4371 ≤ (39376031088921/100000000000000 : ℝ)^3347 := by
    have hnat : (979687323 : ℕ)^4371*100000000000000^3347 ≤ 39376031088921^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979687323 2000000000 39376031088921 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4279907317/10000000000 : ℝ), (1866383489/5000000000 : ℝ), (979687323/2000000000 : ℝ)] ![(33012112868647/100000000000000 : ℝ), (13805928015229/50000000000000 : ℝ), (39376031088921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4279907317/10000000000 : ℝ)|^4371 ≤ (33012112868647/100000000000000 : ℝ)^3347
        have hw : |(4279907317/10000000000 : ℝ)|=(4279907317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1866383489/5000000000 : ℝ)|^4371 ≤ (13805928015229/50000000000000 : ℝ)^3347
        have hw : |(1866383489/5000000000 : ℝ)|=(1866383489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(979687323/2000000000 : ℝ)|^4371 ≤ (39376031088921/100000000000000 : ℝ)^3347
        have hw : |(979687323/2000000000 : ℝ)|=(979687323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s1_4 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-194438581/1000000000 : ℝ)*x 0 + (5076569997/10000000000 : ℝ)*x 1 + (5605963209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (194438581/1000000000 : ℝ)^4371 ≤ (2356234659747/20000000000000 : ℝ)^3347 := by
    have hnat : (194438581 : ℕ)^4371*20000000000000^3347 ≤ 2356234659747^3347*1000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194438581 1000000000 2356234659747 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5076569997/10000000000 : ℝ)^4371 ≤ (41256361594769/100000000000000 : ℝ)^3347 := by
    have hnat : (5076569997 : ℕ)^4371*100000000000000^3347 ≤ 41256361594769^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076569997 10000000000 41256361594769 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5605963209/10000000000 : ℝ)^4371 ≤ (23481232549599/50000000000000 : ℝ)^3347 := by
    have hnat : (5605963209 : ℕ)^4371*50000000000000^3347 ≤ 23481232549599^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5605963209 10000000000 23481232549599 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-194438581/1000000000 : ℝ), (5076569997/10000000000 : ℝ), (5605963209/10000000000 : ℝ)] ![(2356234659747/20000000000000 : ℝ), (41256361594769/100000000000000 : ℝ), (23481232549599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-194438581/1000000000 : ℝ)|^4371 ≤ (2356234659747/20000000000000 : ℝ)^3347
        have hw : |(-194438581/1000000000 : ℝ)|=(194438581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5076569997/10000000000 : ℝ)|^4371 ≤ (41256361594769/100000000000000 : ℝ)^3347
        have hw : |(5076569997/10000000000 : ℝ)|=(5076569997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5605963209/10000000000 : ℝ)|^4371 ≤ (23481232549599/50000000000000 : ℝ)^3347
        have hw : |(5605963209/10000000000 : ℝ)|=(5605963209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s1_5 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257100083/10000000000 : ℝ)*x 0 + (-1695932523/10000000000 : ℝ)*x 1 + (2802981513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257100083/10000000000 : ℝ)^4371 ≤ (1079567469959/2500000000000 : ℝ)^3347 := by
    have hnat : (5257100083 : ℕ)^4371*2500000000000^3347 ≤ 1079567469959^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257100083 10000000000 1079567469959 2500000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1695932523/10000000000 : ℝ)^4371 ≤ (9854838086487/100000000000000 : ℝ)^3347 := by
    have hnat : (1695932523 : ℕ)^4371*100000000000000^3347 ≤ 9854838086487^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1695932523 10000000000 9854838086487 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2802981513/5000000000 : ℝ)^4371 ≤ (2348123154857/5000000000000 : ℝ)^3347 := by
    have hnat : (2802981513 : ℕ)^4371*5000000000000^3347 ≤ 2348123154857^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2802981513 5000000000 2348123154857 5000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257100083/10000000000 : ℝ), (-1695932523/10000000000 : ℝ), (2802981513/5000000000 : ℝ)] ![(1079567469959/2500000000000 : ℝ), (9854838086487/100000000000000 : ℝ), (2348123154857/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257100083/10000000000 : ℝ)|^4371 ≤ (1079567469959/2500000000000 : ℝ)^3347
        have hw : |(5257100083/10000000000 : ℝ)|=(5257100083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1695932523/10000000000 : ℝ)|^4371 ≤ (9854838086487/100000000000000 : ℝ)^3347
        have hw : |(-1695932523/10000000000 : ℝ)|=(1695932523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2802981513/5000000000 : ℝ)|^4371 ≤ (2348123154857/5000000000000 : ℝ)^3347
        have hw : |(2802981513/5000000000 : ℝ)|=(2802981513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s1_6 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628550367/5000000000 : ℝ)*x 0 + (5605963537/10000000000 : ℝ)*x 1 + (-847965433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628550367/5000000000 : ℝ)^4371 ≤ (10795676445451/25000000000000 : ℝ)^3347 := by
    have hnat : (2628550367 : ℕ)^4371*25000000000000^3347 ≤ 10795676445451^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628550367 5000000000 10795676445451 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5605963537/10000000000 : ℝ)^4371 ≤ (11740617171897/25000000000000 : ℝ)^3347 := by
    have hnat : (5605963537 : ℕ)^4371*25000000000000^3347 ≤ 11740617171897^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5605963537 10000000000 11740617171897 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847965433/5000000000 : ℝ)^4371 ≤ (2463706378013/25000000000000 : ℝ)^3347 := by
    have hnat : (847965433 : ℕ)^4371*25000000000000^3347 ≤ 2463706378013^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847965433 5000000000 2463706378013 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628550367/5000000000 : ℝ), (5605963537/10000000000 : ℝ), (-847965433/5000000000 : ℝ)] ![(10795676445451/25000000000000 : ℝ), (11740617171897/25000000000000 : ℝ), (2463706378013/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628550367/5000000000 : ℝ)|^4371 ≤ (10795676445451/25000000000000 : ℝ)^3347
        have hw : |(2628550367/5000000000 : ℝ)|=(2628550367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5605963537/10000000000 : ℝ)|^4371 ≤ (11740617171897/25000000000000 : ℝ)^3347
        have hw : |(5605963537/10000000000 : ℝ)|=(5605963537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-847965433/5000000000 : ℝ)|^4371 ≤ (2463706378013/25000000000000 : ℝ)^3347
        have hw : |(-847965433/5000000000 : ℝ)|=(847965433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s1_7 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535102053/1250000000 : ℝ)*x 0 + (4884573367/10000000000 : ℝ)*x 1 + (468358689/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535102053/1250000000 : ℝ)^4371 ≤ (33021270711011/100000000000000 : ℝ)^3347 := by
    have hnat : (535102053 : ℕ)^4371*100000000000000^3347 ≤ 33021270711011^3347*1250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535102053 1250000000 33021270711011 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4884573367/10000000000 : ℝ)^4371 ≤ (39230560114411/100000000000000 : ℝ)^3347 := by
    have hnat : (4884573367 : ℕ)^4371*100000000000000^3347 ≤ 39230560114411^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4884573367 10000000000 39230560114411 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468358689/1250000000 : ℝ)^4371 ≤ (5549633831071/20000000000000 : ℝ)^3347 := by
    have hnat : (468358689 : ℕ)^4371*20000000000000^3347 ≤ 5549633831071^3347*1250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468358689 1250000000 5549633831071 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535102053/1250000000 : ℝ), (4884573367/10000000000 : ℝ), (468358689/1250000000 : ℝ)] ![(33021270711011/100000000000000 : ℝ), (39230560114411/100000000000000 : ℝ), (5549633831071/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535102053/1250000000 : ℝ)|^4371 ≤ (33021270711011/100000000000000 : ℝ)^3347
        have hw : |(535102053/1250000000 : ℝ)|=(535102053/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4884573367/10000000000 : ℝ)|^4371 ≤ (39230560114411/100000000000000 : ℝ)^3347
        have hw : |(4884573367/10000000000 : ℝ)|=(4884573367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(468358689/1250000000 : ℝ)|^4371 ≤ (5549633831071/20000000000000 : ℝ)^3347
        have hw : |(468358689/1250000000 : ℝ)|=(468358689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1411_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (12/625 : ℝ)*pair X i i ≤ pair X i h) :
    (7501/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2371/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26383/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (12/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26383/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (12/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26383/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (12/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26383/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (12/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26383/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (12/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26383/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (12/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (12/625 : ℝ) ^ (2185/512 : ℝ) ≤ (4719042366961/100000000000000000000 : ℝ) := by
    have hpowers : (12/625 : ℝ)^2185 ≤ (4719042366961/100000000000000000000 : ℝ)^512 := by
      have hnat : (12 : ℕ)^2185*100000000000000000000^512 ≤ 4719042366961^512*625^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12 625 4719042366961 100000000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12/625 : ℝ)) (X := (4719042366961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26383/100000 : ℝ) ^ (2185/512 : ℝ) ≤ (10599996941599653/3125000000000000000 : ℝ) := by
    have hpowers : (26383/100000 : ℝ)^2185 ≤ (10599996941599653/3125000000000000000 : ℝ)^512 := by
      have hnat : (26383 : ℕ)^2185*3125000000000000000^512 ≤ 10599996941599653^512*100000^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26383 100000 10599996941599653 3125000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26383/100000 : ℝ)) (X := (10599996941599653/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000004719042366961/50000000000000000000 : ℝ) ≤ (10000000221157859/10000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (50000004719042366961/50000000000000000000 : ℝ)^512 ≤ (10000000221157859/10000000000000000 : ℝ)^2185 := by
      have hnat : (50000004719042366961 : ℕ)^512*10000000000000000^2185 ≤ 10000000221157859^2185*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000004719042366961 50000000000000000000 10000000221157859 10000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000221157859/10000000000000000 : ℝ)) (X := (50000004719042366961/50000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100339204621173555857/100000000000000000000 : ℝ) ≤ (2001587621815467/2000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (100339204621173555857/100000000000000000000 : ℝ)^512 ≤ (2001587621815467/2000000000000000 : ℝ)^2185 := by
      have hnat : (100339204621173555857 : ℕ)^512*2000000000000000^2185 ≤ 2001587621815467^2185*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100339204621173555857 100000000000000000000 2001587621815467 2000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001587621815467/2000000000000000 : ℝ)) (X := (100339204621173555857/100000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1573099996941599653/1562500000000000000 : ℝ) ≤ (10015875996996811/10000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (1573099996941599653/1562500000000000000 : ℝ)^512 ≤ (10015875996996811/10000000000000000 : ℝ)^2185 := by
      have hnat : (1573099996941599653 : ℕ)^512*10000000000000000^2185 ≤ 10015875996996811^2185*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1573099996941599653 1562500000000000000 10015875996996811 10000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015875996996811/10000000000000000 : ℝ)) (X := (1573099996941599653/1562500000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4719042366961/100000000000000000000 : ℝ) ≤ ((244599523920573916877/244630000000000000000 : ℝ)+2*(1984471979869/611575000000000 : ℝ)*(12/625 : ℝ))^(2185/512 : ℝ) := by
    rw [show (244599523920573916877/244630000000000000000 : ℝ)+2*(1984471979869/611575000000000 : ℝ)*(12/625 : ℝ)=(10000000221157859/10000000000000000 : ℝ) by norm_num, show 1+2*(4719042366961/100000000000000000000 : ℝ)=(50000004719042366961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10599996941599653/3125000000000000000 : ℝ)+(4719042366961/100000000000000000000 : ℝ) ≤ ((244599523920573916877/244630000000000000000 : ℝ)+(1984471979869/611575000000000 : ℝ)*((26383/100000 : ℝ)+(12/625 : ℝ)))^(2185/512 : ℝ) := by
    rw [show (244599523920573916877/244630000000000000000 : ℝ)+(1984471979869/611575000000000 : ℝ)*((26383/100000 : ℝ)+(12/625 : ℝ))=(2001587621815467/2000000000000000 : ℝ) by norm_num, show 1+(10599996941599653/3125000000000000000 : ℝ)+(4719042366961/100000000000000000000 : ℝ)=(100339204621173555857/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10599996941599653/3125000000000000000 : ℝ) ≤ ((244599523920573916877/244630000000000000000 : ℝ)+2*(1984471979869/611575000000000 : ℝ)*(26383/100000 : ℝ))^(2185/512 : ℝ) := by
    rw [show (244599523920573916877/244630000000000000000 : ℝ)+2*(1984471979869/611575000000000 : ℝ)*(26383/100000 : ℝ)=(10015875996996811/10000000000000000 : ℝ) by norm_num, show 1+2*(10599996941599653/3125000000000000000 : ℝ)=(1573099996941599653/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (244599523920573916877/244630000000000000000 : ℝ)*(X 1 0+X 2 0)+(1984471979869/611575000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (12/625 : ℝ)) (hi := (26383/100000 : ℝ)) (c := (244599523920573916877/244630000000000000000 : ℝ)) (alpha := (1984471979869/611575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (244599523920573916877/244630000000000000000 : ℝ)*(X 0 1+X 2 1)+(1984471979869/611575000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (12/625 : ℝ)) (hi := (26383/100000 : ℝ)) (c := (244599523920573916877/244630000000000000000 : ℝ)) (alpha := (1984471979869/611575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (244599523920573916877/244630000000000000000 : ℝ)*(X 0 2+X 1 2)+(1984471979869/611575000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (12/625 : ℝ)) (hi := (26383/100000 : ℝ)) (c := (244599523920573916877/244630000000000000000 : ℝ)) (alpha := (1984471979869/611575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1943963109/10000000000 : ℝ)*X 0 0+(5612522379/10000000000 : ℝ)*X 0 1+(316882587/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((674828131/1250000000 : ℝ)*X 1 0+(-2231777129/10000000000 : ℝ)*X 1 1+(5070118437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1349655827/2500000000 : ℝ)*X 2 0+(2535060817/5000000000 : ℝ)*X 2 1+(-1115887651/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4279907317/10000000000 : ℝ)*X 0 0+(1866383489/5000000000 : ℝ)*X 0 1+(979687323/2000000000 : ℝ)*X 0 2+(4279907317/10000000000 : ℝ)*X 1 0+(1866383489/5000000000 : ℝ)*X 1 1+(979687323/2000000000 : ℝ)*X 1 2+(4279907317/10000000000 : ℝ)*X 2 0+(1866383489/5000000000 : ℝ)*X 2 1+(979687323/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-194438581/1000000000 : ℝ)*X 0 0+(5076569997/10000000000 : ℝ)*X 0 1+(5605963209/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5257100083/10000000000 : ℝ)*X 1 0+(-1695932523/10000000000 : ℝ)*X 1 1+(2802981513/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2628550367/5000000000 : ℝ)*X 2 0+(5605963537/10000000000 : ℝ)*X 2 1+(-847965433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((535102053/1250000000 : ℝ)*X 0 0+(4884573367/10000000000 : ℝ)*X 0 1+(468358689/1250000000 : ℝ)*X 0 2+(535102053/1250000000 : ℝ)*X 1 0+(4884573367/10000000000 : ℝ)*X 1 1+(468358689/1250000000 : ℝ)*X 1 2+(535102053/1250000000 : ℝ)*X 2 0+(4884573367/10000000000 : ℝ)*X 2 1+(468358689/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (881575888255935897405250653/95558593750000000000000000000000 : ℝ) := by norm_num
    linear_combination (193327409/100000000000000 : ℝ)*(base1) + (2237789231/100000000000000 : ℝ)*(base19) + (821784677/50000000000000 : ℝ)*(base23) + (38687541/100000000000000 : ℝ)*(upper3) + (718823029/100000000000000 : ℝ)*(upper5) + (84423425143523/6250000000000 : ℝ)*(major0) + (84423425143523/6250000000000 : ℝ)*(major1) + (84423425143523/6250000000000 : ℝ)*(major2) + (460913767470119/25000000000000 : ℝ)*(sp0) + (921830254259231/50000000000000 : ℝ)*(sp1) + (92183055136917/5000000000000 : ℝ)*(sp2) + (107235397452253/12500000000000 : ℝ)*(sp3) + (3934877313/50000000000000 : ℝ)*(sp4) + (635564581/20000000000000 : ℝ)*(sp7) + (428943275384169/50000000000000 : ℝ)*(f.failure) + (921831373153847/50000000000000 : ℝ)*(f.sum) + (112207807243/477792968750000000000000000 : ℝ)*base65 + (1624073072730550171/1528937500000000000000000000000000 : ℝ)*base67 + (8849667469966862671/1528937500000000000000000000000000 : ℝ)*base69 + (4286108644619737671/1528937500000000000000000000000000 : ℝ)*base71 + (114391989842667/122315000000000000000000000000 : ℝ)*base74 + (14542228259549112671/1528937500000000000000000000000000 : ℝ)*base75 + (6387491744377737671/1528937500000000000000000000000000 : ℝ)*base77 + (7192574122815824829/1528937500000000000000000000000000 : ℝ)*base80 + (9625272723179/15289375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1939559/250000000000000000000 : ℝ)*base90 + (1939559/250000000000000000000 : ℝ)*base92 + (1939559/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6708051320790425530399955469/764468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (288583889/100000000000000 : ℝ)*(base1) + (509166201/25000000000000 : ℝ)*(base19) + (2395538877/100000000000000 : ℝ)*(base23) + (170457983/100000000000000 : ℝ)*(upper3) + (86966637/25000000000000 : ℝ)*(upper5) + (86497547603099/6250000000000 : ℝ)*(major0) + (86497547603099/6250000000000 : ℝ)*(major1) + (86497547603099/6250000000000 : ℝ)*(major2) + (1971142657/20000000000000 : ℝ)*(sp1) + (14497731513/100000000000000 : ℝ)*(sp2) + (1844685872151/97656250000 : ℝ)*(sp4) + (1888946152120647/100000000000000 : ℝ)*(sp5) + (944470575614173/50000000000000 : ℝ)*(sp6) + (2197407244309/250000000000 : ℝ)*(sp7) + (878963186307489/100000000000000 : ℝ)*(f.failure) + (377791608899747/20000000000000 : ℝ)*(f.sum) + (2996876361319/1911171875000000000000000000 : ℝ)*base66 + (1572944397347001823/1528937500000000000000000000000000 : ℝ)*base67 + (3565501175138001823/1528937500000000000000000000000000 : ℝ)*base69 + (2877164964449185677/1528937500000000000000000000000000 : ℝ)*base72 + (92631731353513/61157500000000000000000000000 : ℝ)*base74 + (7039748964881560677/1528937500000000000000000000000000 : ℝ)*base76 + (20748968283310498177/1528937500000000000000000000000000 : ℝ)*base78 + (8978620106722248177/1528937500000000000000000000000000 : ℝ)*base80 + (21667747508007/61157500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (732079/500000000000000000000 : ℝ)*base90 + (732079/500000000000000000000 : ℝ)*base92 + (732079/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1411_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (12/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7501/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2371/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1411_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1411_s2_0 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-494614619/2500000000 : ℝ)*x 0 + (2731149133/5000000000 : ℝ)*x 1 + (2599081717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (494614619/2500000000 : ℝ)^4371 ≤ (241030078707/2000000000000 : ℝ)^3347 := by
    have hnat : (494614619 : ℕ)^4371*2000000000000^3347 ≤ 241030078707^3347*2500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494614619 2500000000 241030078707 2000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731149133/5000000000 : ℝ)^4371 ≤ (9079387734903/20000000000000 : ℝ)^3347 := by
    have hnat : (2731149133 : ℕ)^4371*20000000000000^3347 ≤ 9079387734903^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731149133 5000000000 9079387734903 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2599081717/5000000000 : ℝ)^4371 ≤ (8510311473827/20000000000000 : ℝ)^3347 := by
    have hnat : (2599081717 : ℕ)^4371*20000000000000^3347 ≤ 8510311473827^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599081717 5000000000 8510311473827 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-494614619/2500000000 : ℝ), (2731149133/5000000000 : ℝ), (2599081717/5000000000 : ℝ)] ![(241030078707/2000000000000 : ℝ), (9079387734903/20000000000000 : ℝ), (8510311473827/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-494614619/2500000000 : ℝ)|^4371 ≤ (241030078707/2000000000000 : ℝ)^3347
        have hw : |(-494614619/2500000000 : ℝ)|=(494614619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731149133/5000000000 : ℝ)|^4371 ≤ (9079387734903/20000000000000 : ℝ)^3347
        have hw : |(2731149133/5000000000 : ℝ)|=(2731149133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2599081717/5000000000 : ℝ)|^4371 ≤ (8510311473827/20000000000000 : ℝ)^3347
        have hw : |(2599081717/5000000000 : ℝ)|=(2599081717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s2_1 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072259147/2000000000 : ℝ)*x 0 + (-33038519/156250000 : ℝ)*x 1 + (5198163407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072259147/2000000000 : ℝ)^4371 ≤ (8860761132043/20000000000000 : ℝ)^3347 := by
    have hnat : (1072259147 : ℕ)^4371*20000000000000^3347 ≤ 8860761132043^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072259147 2000000000 8860761132043 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33038519/156250000 : ℝ)^4371 ≤ (13144637254459/100000000000000 : ℝ)^3347 := by
    have hnat : (33038519 : ℕ)^4371*100000000000000^3347 ≤ 13144637254459^3347*156250000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33038519 156250000 13144637254459 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5198163407/10000000000 : ℝ)^4371 ≤ (42551557080497/100000000000000 : ℝ)^3347 := by
    have hnat : (5198163407 : ℕ)^4371*100000000000000^3347 ≤ 42551557080497^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198163407 10000000000 42551557080497 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072259147/2000000000 : ℝ), (-33038519/156250000 : ℝ), (5198163407/10000000000 : ℝ)] ![(8860761132043/20000000000000 : ℝ), (13144637254459/100000000000000 : ℝ), (42551557080497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072259147/2000000000 : ℝ)|^4371 ≤ (8860761132043/20000000000000 : ℝ)^3347
        have hw : |(1072259147/2000000000 : ℝ)|=(1072259147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33038519/156250000 : ℝ)|^4371 ≤ (13144637254459/100000000000000 : ℝ)^3347
        have hw : |(-33038519/156250000 : ℝ)|=(33038519/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5198163407/10000000000 : ℝ)|^4371 ≤ (42551557080497/100000000000000 : ℝ)^3347
        have hw : |(5198163407/10000000000 : ℝ)|=(5198163407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s2_2 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214451819/400000000 : ℝ)*x 0 + (5198163701/10000000000 : ℝ)*x 1 + (-1057232587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214451819/400000000 : ℝ)^4371 ≤ (44303802854331/100000000000000 : ℝ)^3347 := by
    have hnat : (214451819 : ℕ)^4371*100000000000000^3347 ≤ 44303802854331^3347*400000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214451819 400000000 44303802854331 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5198163701/10000000000 : ℝ)^4371 ≤ (851031204469/2000000000000 : ℝ)^3347 := by
    have hnat : (5198163701 : ℕ)^4371*2000000000000^3347 ≤ 851031204469^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198163701 10000000000 851031204469 2000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057232587/5000000000 : ℝ)^4371 ≤ (3286159228371/25000000000000 : ℝ)^3347 := by
    have hnat : (1057232587 : ℕ)^4371*25000000000000^3347 ≤ 3286159228371^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057232587 5000000000 3286159228371 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214451819/400000000 : ℝ), (5198163701/10000000000 : ℝ), (-1057232587/5000000000 : ℝ)] ![(44303802854331/100000000000000 : ℝ), (851031204469/2000000000000 : ℝ), (3286159228371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214451819/400000000 : ℝ)|^4371 ≤ (44303802854331/100000000000000 : ℝ)^3347
        have hw : |(214451819/400000000 : ℝ)|=(214451819/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5198163701/10000000000 : ℝ)|^4371 ≤ (851031204469/2000000000000 : ℝ)^3347
        have hw : |(5198163701/10000000000 : ℝ)|=(5198163701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1057232587/5000000000 : ℝ)|^4371 ≤ (3286159228371/25000000000000 : ℝ)^3347
        have hw : |(-1057232587/5000000000 : ℝ)|=(1057232587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s2_3 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215210497/500000000 : ℝ)*x 0 + (2014426199/5000000000 : ℝ)*x 1 + (4596498057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215210497/500000000 : ℝ)^4371 ≤ (33257128494831/100000000000000 : ℝ)^3347 := by
    have hnat : (215210497 : ℕ)^4371*100000000000000^3347 ≤ 33257128494831^3347*500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215210497 500000000 33257128494831 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2014426199/5000000000 : ℝ)^4371 ≤ (30506214597923/100000000000000 : ℝ)^3347 := by
    have hnat : (2014426199 : ℕ)^4371*100000000000000^3347 ≤ 30506214597923^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014426199 5000000000 30506214597923 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4596498057/10000000000 : ℝ)^4371 ≤ (4529582111123/12500000000000 : ℝ)^3347 := by
    have hnat : (4596498057 : ℕ)^4371*12500000000000^3347 ≤ 4529582111123^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4596498057 10000000000 4529582111123 12500000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215210497/500000000 : ℝ), (2014426199/5000000000 : ℝ), (4596498057/10000000000 : ℝ)] ![(33257128494831/100000000000000 : ℝ), (30506214597923/100000000000000 : ℝ), (4529582111123/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215210497/500000000 : ℝ)|^4371 ≤ (33257128494831/100000000000000 : ℝ)^3347
        have hw : |(215210497/500000000 : ℝ)|=(215210497/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2014426199/5000000000 : ℝ)|^4371 ≤ (30506214597923/100000000000000 : ℝ)^3347
        have hw : |(2014426199/5000000000 : ℝ)|=(2014426199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4596498057/10000000000 : ℝ)|^4371 ≤ (4529582111123/12500000000000 : ℝ)^3347
        have hw : |(4596498057/10000000000 : ℝ)|=(4596498057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s2_4 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-989253609/5000000000 : ℝ)*x 0 + (2599851291/5000000000 : ℝ)*x 1 + (2730373211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989253609/5000000000 : ℝ)^4371 ≤ (12051891678723/100000000000000 : ℝ)^3347 := by
    have hnat : (989253609 : ℕ)^4371*100000000000000^3347 ≤ 12051891678723^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989253609 5000000000 12051891678723 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2599851291/5000000000 : ℝ)^4371 ≤ (21284006047959/50000000000000 : ℝ)^3347 := by
    have hnat : (2599851291 : ℕ)^4371*50000000000000^3347 ≤ 21284006047959^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599851291 5000000000 21284006047959 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730373211/5000000000 : ℝ)^4371 ≤ (11345024054487/25000000000000 : ℝ)^3347 := by
    have hnat : (2730373211 : ℕ)^4371*25000000000000^3347 ≤ 11345024054487^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730373211 5000000000 11345024054487 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-989253609/5000000000 : ℝ), (2599851291/5000000000 : ℝ), (2730373211/5000000000 : ℝ)] ![(12051891678723/100000000000000 : ℝ), (21284006047959/50000000000000 : ℝ), (11345024054487/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-989253609/5000000000 : ℝ)|^4371 ≤ (12051891678723/100000000000000 : ℝ)^3347
        have hw : |(-989253609/5000000000 : ℝ)|=(989253609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2599851291/5000000000 : ℝ)|^4371 ≤ (21284006047959/50000000000000 : ℝ)^3347
        have hw : |(2599851291/5000000000 : ℝ)|=(2599851291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730373211/5000000000 : ℝ)|^4371 ≤ (11345024054487/25000000000000 : ℝ)^3347
        have hw : |(2730373211/5000000000 : ℝ)|=(2730373211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s2_5 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323182507/2500000000 : ℝ)*x 0 + (-185188283/1000000000 : ℝ)*x 1 + (5460746149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323182507/2500000000 : ℝ)^4371 ≤ (43565305973147/100000000000000 : ℝ)^3347 := by
    have hnat : (1323182507 : ℕ)^4371*100000000000000^3347 ≤ 43565305973147^3347*2500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323182507 2500000000 43565305973147 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (185188283/1000000000 : ℝ)^4371 ≤ (552730038159/5000000000000 : ℝ)^3347 := by
    have hnat : (185188283 : ℕ)^4371*5000000000000^3347 ≤ 552730038159^3347*1000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185188283 1000000000 552730038159 5000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460746149/10000000000 : ℝ)^4371 ≤ (45380093255157/100000000000000 : ℝ)^3347 := by
    have hnat : (5460746149 : ℕ)^4371*100000000000000^3347 ≤ 45380093255157^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460746149 10000000000 45380093255157 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323182507/2500000000 : ℝ), (-185188283/1000000000 : ℝ), (5460746149/10000000000 : ℝ)] ![(43565305973147/100000000000000 : ℝ), (552730038159/5000000000000 : ℝ), (45380093255157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323182507/2500000000 : ℝ)|^4371 ≤ (43565305973147/100000000000000 : ℝ)^3347
        have hw : |(1323182507/2500000000 : ℝ)|=(1323182507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-185188283/1000000000 : ℝ)|^4371 ≤ (552730038159/5000000000000 : ℝ)^3347
        have hw : |(-185188283/1000000000 : ℝ)|=(185188283/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460746149/10000000000 : ℝ)|^4371 ≤ (45380093255157/100000000000000 : ℝ)^3347
        have hw : |(5460746149/10000000000 : ℝ)|=(5460746149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s2_6 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529273147/1000000000 : ℝ)*x 0 + (5460746129/10000000000 : ℝ)*x 1 + (-1851880869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529273147/1000000000 : ℝ)^4371 ≤ (871306429477/2000000000000 : ℝ)^3347 := by
    have hnat : (529273147 : ℕ)^4371*2000000000000^3347 ≤ 871306429477^3347*1000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529273147 1000000000 871306429477 2000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460746129/10000000000 : ℝ)^4371 ≤ (22690046519051/50000000000000 : ℝ)^3347 := by
    have hnat : (5460746129 : ℕ)^4371*50000000000000^3347 ≤ 22690046519051^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460746129 10000000000 22690046519051 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1851880869/10000000000 : ℝ)^4371 ≤ (11054585475831/100000000000000 : ℝ)^3347 := by
    have hnat : (1851880869 : ℕ)^4371*100000000000000^3347 ≤ 11054585475831^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851880869 10000000000 11054585475831 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529273147/1000000000 : ℝ), (5460746129/10000000000 : ℝ), (-1851880869/10000000000 : ℝ)] ![(871306429477/2000000000000 : ℝ), (22690046519051/50000000000000 : ℝ), (11054585475831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529273147/1000000000 : ℝ)|^4371 ≤ (871306429477/2000000000000 : ℝ)^3347
        have hw : |(529273147/1000000000 : ℝ)|=(529273147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460746129/10000000000 : ℝ)|^4371 ≤ (22690046519051/50000000000000 : ℝ)^3347
        have hw : |(5460746129/10000000000 : ℝ)|=(5460746129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1851880869/10000000000 : ℝ)|^4371 ≤ (11054585475831/100000000000000 : ℝ)^3347
        have hw : |(-1851880869/10000000000 : ℝ)|=(1851880869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s2_7 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4304315837/10000000000 : ℝ)*x 0 + (2296595361/5000000000 : ℝ)*x 1 + (4032186973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304315837/10000000000 : ℝ)^4371 ≤ (16629098530829/50000000000000 : ℝ)^3347 := by
    have hnat : (4304315837 : ℕ)^4371*50000000000000^3347 ≤ 16629098530829^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304315837 10000000000 16629098530829 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2296595361/5000000000 : ℝ)^4371 ≤ (18101305036207/50000000000000 : ℝ)^3347 := by
    have hnat : (2296595361 : ℕ)^4371*50000000000000^3347 ≤ 18101305036207^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296595361 5000000000 18101305036207 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4032186973/10000000000 : ℝ)^4371 ≤ (15269596420733/50000000000000 : ℝ)^3347 := by
    have hnat : (4032186973 : ℕ)^4371*50000000000000^3347 ≤ 15269596420733^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032186973 10000000000 15269596420733 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304315837/10000000000 : ℝ), (2296595361/5000000000 : ℝ), (4032186973/10000000000 : ℝ)] ![(16629098530829/50000000000000 : ℝ), (18101305036207/50000000000000 : ℝ), (15269596420733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304315837/10000000000 : ℝ)|^4371 ≤ (16629098530829/50000000000000 : ℝ)^3347
        have hw : |(4304315837/10000000000 : ℝ)|=(4304315837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2296595361/5000000000 : ℝ)|^4371 ≤ (18101305036207/50000000000000 : ℝ)^3347
        have hw : |(2296595361/5000000000 : ℝ)|=(2296595361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4032186973/10000000000 : ℝ)|^4371 ≤ (15269596420733/50000000000000 : ℝ)^3347
        have hw : |(4032186973/10000000000 : ℝ)|=(4032186973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1411_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2371/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7501/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10269/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (991/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2371/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7501/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2371/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7501/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2371/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7501/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2371/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7501/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2371/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7501/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2371/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7501/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7501/100000 : ℝ) ^ (2185/512 : ℝ) ≤ (316601634735077/20000000000000000000 : ℝ) := by
    have hpowers : (7501/100000 : ℝ)^2185 ≤ (316601634735077/20000000000000000000 : ℝ)^512 := by
      have hnat : (7501 : ℕ)^2185*20000000000000000000^512 ≤ 316601634735077^512*100000^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7501 100000 316601634735077 20000000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7501/100000 : ℝ)) (X := (316601634735077/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2371/12500 : ℝ) ^ (2185/512 : ℝ) ≤ (8296607056092047/10000000000000000000 : ℝ) := by
    have hpowers : (2371/12500 : ℝ)^2185 ≤ (8296607056092047/10000000000000000000 : ℝ)^512 := by
      have hnat : (2371 : ℕ)^2185*10000000000000000000^512 ≤ 8296607056092047^512*12500^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2371 12500 8296607056092047 10000000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2371/12500 : ℝ)) (X := (8296607056092047/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000316601634735077/10000000000000000000 : ℝ) ≤ (5000037093380379/5000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (10000316601634735077/10000000000000000000 : ℝ)^512 ≤ (5000037093380379/5000000000000000 : ℝ)^2185 := by
      have hnat : (10000316601634735077 : ℕ)^512*5000000000000000^2185 ≤ 5000037093380379^2185*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000316601634735077 10000000000000000000 5000037093380379 5000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000037093380379/5000000000000000 : ℝ)) (X := (10000316601634735077/10000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20016909815746919171/20000000000000000000 : ℝ) ≤ (10001980554838129/10000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (20016909815746919171/20000000000000000000 : ℝ)^512 ≤ (10001980554838129/10000000000000000 : ℝ)^2185 := by
      have hnat : (20016909815746919171 : ℕ)^512*10000000000000000^2185 ≤ 10001980554838129^2185*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20016909815746919171 20000000000000000000 10001980554838129 10000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001980554838129/10000000000000000 : ℝ)) (X := (20016909815746919171/20000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5008296607056092047/5000000000000000000 : ℝ) ≤ (20007773845831/20000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (5008296607056092047/5000000000000000000 : ℝ)^512 ≤ (20007773845831/20000000000000 : ℝ)^2185 := by
      have hnat : (5008296607056092047 : ℕ)^512*20000000000000^2185 ≤ 20007773845831^2185*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5008296607056092047 5000000000000000000 20007773845831 20000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20007773845831/20000000000000 : ℝ)) (X := (5008296607056092047/5000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(316601634735077/20000000000000000000 : ℝ) ≤ ((28660562841422223061/28667500000000000000 : ℝ)+2*(1906368077371/1146700000000000 : ℝ)*(7501/100000 : ℝ))^(2185/512 : ℝ) := by
    rw [show (28660562841422223061/28667500000000000000 : ℝ)+2*(1906368077371/1146700000000000 : ℝ)*(7501/100000 : ℝ)=(5000037093380379/5000000000000000 : ℝ) by norm_num, show 1+2*(316601634735077/20000000000000000000 : ℝ)=(10000316601634735077/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8296607056092047/10000000000000000000 : ℝ)+(316601634735077/20000000000000000000 : ℝ) ≤ ((28660562841422223061/28667500000000000000 : ℝ)+(1906368077371/1146700000000000 : ℝ)*((2371/12500 : ℝ)+(7501/100000 : ℝ)))^(2185/512 : ℝ) := by
    rw [show (28660562841422223061/28667500000000000000 : ℝ)+(1906368077371/1146700000000000 : ℝ)*((2371/12500 : ℝ)+(7501/100000 : ℝ))=(10001980554838129/10000000000000000 : ℝ) by norm_num, show 1+(8296607056092047/10000000000000000000 : ℝ)+(316601634735077/20000000000000000000 : ℝ)=(20016909815746919171/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8296607056092047/10000000000000000000 : ℝ) ≤ ((28660562841422223061/28667500000000000000 : ℝ)+2*(1906368077371/1146700000000000 : ℝ)*(2371/12500 : ℝ))^(2185/512 : ℝ) := by
    rw [show (28660562841422223061/28667500000000000000 : ℝ)+2*(1906368077371/1146700000000000 : ℝ)*(2371/12500 : ℝ)=(20007773845831/20000000000000 : ℝ) by norm_num, show 1+2*(8296607056092047/10000000000000000000 : ℝ)=(5008296607056092047/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28660562841422223061/28667500000000000000 : ℝ)*(X 1 0+X 2 0)+(1906368077371/1146700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (7501/100000 : ℝ)) (hi := (2371/12500 : ℝ)) (c := (28660562841422223061/28667500000000000000 : ℝ)) (alpha := (1906368077371/1146700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28660562841422223061/28667500000000000000 : ℝ)*(X 0 1+X 2 1)+(1906368077371/1146700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (7501/100000 : ℝ)) (hi := (2371/12500 : ℝ)) (c := (28660562841422223061/28667500000000000000 : ℝ)) (alpha := (1906368077371/1146700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28660562841422223061/28667500000000000000 : ℝ)*(X 0 2+X 1 2)+(1906368077371/1146700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (7501/100000 : ℝ)) (hi := (2371/12500 : ℝ)) (c := (28660562841422223061/28667500000000000000 : ℝ)) (alpha := (1906368077371/1146700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-494614619/2500000000 : ℝ)*X 0 0+(2731149133/5000000000 : ℝ)*X 0 1+(2599081717/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1072259147/2000000000 : ℝ)*X 1 0+(-33038519/156250000 : ℝ)*X 1 1+(5198163407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214451819/400000000 : ℝ)*X 2 0+(5198163701/10000000000 : ℝ)*X 2 1+(-1057232587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((215210497/500000000 : ℝ)*X 0 0+(2014426199/5000000000 : ℝ)*X 0 1+(4596498057/10000000000 : ℝ)*X 0 2+(215210497/500000000 : ℝ)*X 1 0+(2014426199/5000000000 : ℝ)*X 1 1+(4596498057/10000000000 : ℝ)*X 1 2+(215210497/500000000 : ℝ)*X 2 0+(2014426199/5000000000 : ℝ)*X 2 1+(4596498057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-989253609/5000000000 : ℝ)*X 0 0+(2599851291/5000000000 : ℝ)*X 0 1+(2730373211/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323182507/2500000000 : ℝ)*X 1 0+(-185188283/1000000000 : ℝ)*X 1 1+(5460746149/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529273147/1000000000 : ℝ)*X 2 0+(5460746129/10000000000 : ℝ)*X 2 1+(-1851880869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4304315837/10000000000 : ℝ)*X 0 0+(2296595361/5000000000 : ℝ)*X 0 1+(4032186973/10000000000 : ℝ)*X 0 2+(4304315837/10000000000 : ℝ)*X 1 0+(2296595361/5000000000 : ℝ)*X 1 1+(4032186973/10000000000 : ℝ)*X 1 2+(4304315837/10000000000 : ℝ)*X 2 0+(2296595361/5000000000 : ℝ)*X 2 1+(4032186973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (142550889496176249632860389/17917187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (299840801/25000000000000 : ℝ)*(base19) + (411370601/50000000000000 : ℝ)*(base23) + (103482903/100000000000000 : ℝ)*(lower2) + (117326769/50000000000000 : ℝ)*(upper3) + (9970173/12500000000000 : ℝ)*(upper5) + (17336403857777/625000000000 : ℝ)*(major0) + (17336403857777/625000000000 : ℝ)*(major1) + (17336403857777/625000000000 : ℝ)*(major2) + (1892980446640939/50000000000000 : ℝ)*(sp0) + (1892986150470271/50000000000000 : ℝ)*(sp1) + (236623292347659/6250000000000 : ℝ)*(sp2) + (880834037987539/50000000000000 : ℝ)*(sp3) + (3151755467/25000000000000 : ℝ)*(sp4) + (3696503281/50000000000000 : ℝ)*(sp7) + (44041886724541/2500000000000 : ℝ)*(f.failure) + (1892986750151873/50000000000000 : ℝ)*(f.sum) + (5982771893991/1146700000000000000000000000 : ℝ)*base66 + (6061891778860853/17917187500000000000000000000000 : ℝ)*base68 + (191230722680573353/17917187500000000000000000000000 : ℝ)*base70 + (84215670181648353/17917187500000000000000000000000 : ℝ)*base72 + (7090915965979/1433375000000000000000000000 : ℝ)*base73 + (39874936887930511/8958593750000000000000000000000 : ℝ)*base75 + (103595143562706989/8958593750000000000000000000000 : ℝ)*base78 + (37584112537517103/17917187500000000000000000000000 : ℝ)*base80 + (1617293506633/716687500000000000000000000 : ℝ)*base82 + (39251/12500000000000000000 : ℝ)*base90 + (39251/12500000000000000000 : ℝ)*base92 + (39251/12500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1370985964748272028579180817/1433375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23545649/10000000000000 : ℝ)*(base19) + (124966943/10000000000000 : ℝ)*(base23) + (230904439/100000000000000 : ℝ)*(lower2) + (1149641/50000000000000 : ℝ)*(upper3) + (31401649/100000000000000 : ℝ)*(lower4) + (2806655020638453/100000000000000 : ℝ)*(major0) + (2806655020638453/100000000000000 : ℝ)*(major1) + (1403327510319227/50000000000000 : ℝ)*(major2) + (6705394687/25000000000000 : ℝ)*(sp2) + (691122191/50000000000000 : ℝ)*(sp3) + (3830783720956989/100000000000000 : ℝ)*(sp4) + (3830783485500499/100000000000000 : ℝ)*(sp5) + (957688912427203/25000000000000 : ℝ)*(sp6) + (891262453096529/50000000000000 : ℝ)*(sp7) + (5570394651367/312500000000 : ℝ)*(f.failure) + (3830783720956989/100000000000000 : ℝ)*(f.sum) + (560108479080583/114670000000000000000000000000 : ℝ)*base66 + (690004764381685367/2866750000000000000000000000000000 : ℝ)*base68 + (13293982521409131347/1433375000000000000000000000000000 : ℝ)*base69 + (2437564765094314633/2866750000000000000000000000000000 : ℝ)*base71 + (300348400476357/114670000000000000000000000000 : ℝ)*base73 + (8772852607067756347/1433375000000000000000000000000000 : ℝ)*base75 + (14670109261353960367/2866750000000000000000000000000000 : ℝ)*base78 + (10079168074707460367/2866750000000000000000000000000000 : ℝ)*base80 + (57767260057317/57335000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6131/781250000000000000 : ℝ)*base90 + (6131/781250000000000000 : ℝ)*base92 + (27887/1562500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1411_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2371/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7501/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (991/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1411_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1411_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (991/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1411_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1411_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1411_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (991/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1411_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

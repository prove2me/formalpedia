-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1048_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:53:10.190223+00:00
-- url     : https://prove2.me/submissions/dd1ea740-5e61-4bdf-b31f-f863ea37eff5

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
theorem support_rectangle_w1048_s6_0 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2212606841/10000000000 : ℝ)*x 0 + (2697645813/5000000000 : ℝ)*x 1 + (131588299/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2212606841/10000000000 : ℝ)^8241 ≤ (1679487418051/12500000000000 : ℝ)^6193 := by
    have hnat : (2212606841 : ℕ)^8241*12500000000000^6193 ≤ 1679487418051^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212606841 10000000000 1679487418051 12500000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697645813/5000000000 : ℝ)^8241 ≤ (549924867271/1250000000000 : ℝ)^6193 := by
    have hnat : (2697645813 : ℕ)^8241*1250000000000^6193 ≤ 549924867271^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697645813 5000000000 549924867271 1250000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131588299/250000000 : ℝ)^8241 ≤ (10642527815513/25000000000000 : ℝ)^6193 := by
    have hnat : (131588299 : ℕ)^8241*25000000000000^6193 ≤ 10642527815513^6193*250000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131588299 250000000 10642527815513 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2212606841/10000000000 : ℝ), (2697645813/5000000000 : ℝ), (131588299/250000000 : ℝ)] ![(1679487418051/12500000000000 : ℝ), (549924867271/1250000000000 : ℝ), (10642527815513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2212606841/10000000000 : ℝ)|^8241 ≤ (1679487418051/12500000000000 : ℝ)^6193
        have hw : |(-2212606841/10000000000 : ℝ)|=(2212606841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697645813/5000000000 : ℝ)|^8241 ≤ (549924867271/1250000000000 : ℝ)^6193
        have hw : |(2697645813/5000000000 : ℝ)|=(2697645813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131588299/250000000 : ℝ)|^8241 ≤ (10642527815513/25000000000000 : ℝ)^6193
        have hw : |(131588299/250000000 : ℝ)|=(131588299/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s6_1 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334073311/625000000 : ℝ)*x 0 + (-2279471419/10000000000 : ℝ)*x 1 + (5263531951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334073311/625000000 : ℝ)^8241 ≤ (10862751151489/25000000000000 : ℝ)^6193 := by
    have hnat : (334073311 : ℕ)^8241*25000000000000^6193 ≤ 10862751151489^6193*625000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334073311 625000000 10862751151489 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279471419/10000000000 : ℝ)^8241 ≤ (1747360526763/12500000000000 : ℝ)^6193 := by
    have hnat : (2279471419 : ℕ)^8241*12500000000000^6193 ≤ 1747360526763^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279471419 10000000000 1747360526763 12500000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263531951/10000000000 : ℝ)^8241 ≤ (42570111165191/100000000000000 : ℝ)^6193 := by
    have hnat : (5263531951 : ℕ)^8241*100000000000000^6193 ≤ 42570111165191^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263531951 10000000000 42570111165191 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334073311/625000000 : ℝ), (-2279471419/10000000000 : ℝ), (5263531951/10000000000 : ℝ)] ![(10862751151489/25000000000000 : ℝ), (1747360526763/12500000000000 : ℝ), (42570111165191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334073311/625000000 : ℝ)|^8241 ≤ (10862751151489/25000000000000 : ℝ)^6193
        have hw : |(334073311/625000000 : ℝ)|=(334073311/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2279471419/10000000000 : ℝ)|^8241 ≤ (1747360526763/12500000000000 : ℝ)^6193
        have hw : |(-2279471419/10000000000 : ℝ)|=(2279471419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263531951/10000000000 : ℝ)|^8241 ≤ (42570111165191/100000000000000 : ℝ)^6193
        have hw : |(5263531951/10000000000 : ℝ)|=(5263531951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s6_2 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534517279/1000000000 : ℝ)*x 0 + (2631766037/5000000000 : ℝ)*x 1 + (-1139735751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534517279/1000000000 : ℝ)^8241 ≤ (43451002593947/100000000000000 : ℝ)^6193 := by
    have hnat : (534517279 : ℕ)^8241*100000000000000^6193 ≤ 43451002593947^6193*1000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534517279 1000000000 43451002593947 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631766037/5000000000 : ℝ)^8241 ≤ (21285056244479/50000000000000 : ℝ)^6193 := by
    have hnat : (2631766037 : ℕ)^8241*50000000000000^6193 ≤ 21285056244479^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631766037 5000000000 21285056244479 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139735751/5000000000 : ℝ)^8241 ≤ (13978884891427/100000000000000 : ℝ)^6193 := by
    have hnat : (1139735751 : ℕ)^8241*100000000000000^6193 ≤ 13978884891427^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139735751 5000000000 13978884891427 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534517279/1000000000 : ℝ), (2631766037/5000000000 : ℝ), (-1139735751/5000000000 : ℝ)] ![(43451002593947/100000000000000 : ℝ), (21285056244479/50000000000000 : ℝ), (13978884891427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534517279/1000000000 : ℝ)|^8241 ≤ (43451002593947/100000000000000 : ℝ)^6193
        have hw : |(534517279/1000000000 : ℝ)|=(534517279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631766037/5000000000 : ℝ)|^8241 ≤ (21285056244479/50000000000000 : ℝ)^6193
        have hw : |(2631766037/5000000000 : ℝ)|=(2631766037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1139735751/5000000000 : ℝ)|^8241 ≤ (13978884891427/100000000000000 : ℝ)^6193
        have hw : |(-1139735751/5000000000 : ℝ)|=(1139735751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s6_3 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136814261/312500000 : ℝ)*x 0 + (2125662701/5000000000 : ℝ)*x 1 + (4508633779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136814261/312500000 : ℝ)^8241 ≤ (33316129589743/100000000000000 : ℝ)^6193 := by
    have hnat : (136814261 : ℕ)^8241*100000000000000^6193 ≤ 33316129589743^6193*312500000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136814261 312500000 33316129589743 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125662701/5000000000 : ℝ)^8241 ≤ (640779856333/2000000000000 : ℝ)^6193 := by
    have hnat : (2125662701 : ℕ)^8241*2000000000000^6193 ≤ 640779856333^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125662701 5000000000 640779856333 2000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508633779/10000000000 : ℝ)^8241 ≤ (34644877578619/100000000000000 : ℝ)^6193 := by
    have hnat : (4508633779 : ℕ)^8241*100000000000000^6193 ≤ 34644877578619^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508633779 10000000000 34644877578619 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136814261/312500000 : ℝ), (2125662701/5000000000 : ℝ), (4508633779/10000000000 : ℝ)] ![(33316129589743/100000000000000 : ℝ), (640779856333/2000000000000 : ℝ), (34644877578619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136814261/312500000 : ℝ)|^8241 ≤ (33316129589743/100000000000000 : ℝ)^6193
        have hw : |(136814261/312500000 : ℝ)|=(136814261/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2125662701/5000000000 : ℝ)|^8241 ≤ (640779856333/2000000000000 : ℝ)^6193
        have hw : |(2125662701/5000000000 : ℝ)|=(2125662701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508633779/10000000000 : ℝ)|^8241 ≤ (34644877578619/100000000000000 : ℝ)^6193
        have hw : |(4508633779/10000000000 : ℝ)|=(4508633779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s6_4 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2212612119/10000000000 : ℝ)*x 0 + (526386477/1000000000 : ℝ)*x 1 + (1348739397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2212612119/10000000000 : ℝ)^8241 ≤ (13435941993607/100000000000000 : ℝ)^6193 := by
    have hnat : (2212612119 : ℕ)^8241*100000000000000^6193 ≤ 13435941993607^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212612119 10000000000 13435941993607 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526386477/1000000000 : ℝ)^8241 ≤ (10643423277741/25000000000000 : ℝ)^6193 := by
    have hnat : (526386477 : ℕ)^8241*25000000000000^6193 ≤ 10643423277741^6193*1000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526386477 1000000000 10643423277741 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348739397/2500000000 : ℝ)^8241 ≤ (43990364876837/100000000000000 : ℝ)^6193 := by
    have hnat : (1348739397 : ℕ)^8241*100000000000000^6193 ≤ 43990364876837^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348739397 2500000000 43990364876837 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2212612119/10000000000 : ℝ), (526386477/1000000000 : ℝ), (1348739397/2500000000 : ℝ)] ![(13435941993607/100000000000000 : ℝ), (10643423277741/25000000000000 : ℝ), (43990364876837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2212612119/10000000000 : ℝ)|^8241 ≤ (13435941993607/100000000000000 : ℝ)^6193
        have hw : |(-2212612119/10000000000 : ℝ)|=(2212612119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526386477/1000000000 : ℝ)|^8241 ≤ (10643423277741/25000000000000 : ℝ)^6193
        have hw : |(526386477/1000000000 : ℝ)|=(526386477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348739397/2500000000 : ℝ)|^8241 ≤ (43990364876837/100000000000000 : ℝ)^6193
        have hw : |(1348739397/2500000000 : ℝ)|=(1348739397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s6_5 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265601657/500000000 : ℝ)*x 0 + (-2148045781/10000000000 : ℝ)*x 1 + (1348739417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265601657/500000000 : ℝ)^8241 ≤ (8618578140329/20000000000000 : ℝ)^6193 := by
    have hnat : (265601657 : ℕ)^8241*20000000000000^6193 ≤ 8618578140329^6193*500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265601657 500000000 8618578140329 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2148045781/10000000000 : ℝ)^8241 ≤ (3229185884993/25000000000000 : ℝ)^6193 := by
    have hnat : (2148045781 : ℕ)^8241*25000000000000^6193 ≤ 3229185884993^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148045781 10000000000 3229185884993 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348739417/2500000000 : ℝ)^8241 ≤ (21995182872437/50000000000000 : ℝ)^6193 := by
    have hnat : (1348739417 : ℕ)^8241*50000000000000^6193 ≤ 21995182872437^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348739417 2500000000 21995182872437 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265601657/500000000 : ℝ), (-2148045781/10000000000 : ℝ), (1348739417/2500000000 : ℝ)] ![(8618578140329/20000000000000 : ℝ), (3229185884993/25000000000000 : ℝ), (21995182872437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265601657/500000000 : ℝ)|^8241 ≤ (8618578140329/20000000000000 : ℝ)^6193
        have hw : |(265601657/500000000 : ℝ)|=(265601657/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2148045781/10000000000 : ℝ)|^8241 ≤ (3229185884993/25000000000000 : ℝ)^6193
        have hw : |(-2148045781/10000000000 : ℝ)|=(2148045781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348739417/2500000000 : ℝ)|^8241 ≤ (21995182872437/50000000000000 : ℝ)^6193
        have hw : |(1348739417/2500000000 : ℝ)|=(1348739417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s6_6 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328008283/2500000000 : ℝ)*x 0 + (5394957627/10000000000 : ℝ)*x 1 + (-2148045847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328008283/2500000000 : ℝ)^8241 ≤ (8618578123057/20000000000000 : ℝ)^6193 := by
    have hnat : (1328008283 : ℕ)^8241*20000000000000^6193 ≤ 8618578123057^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328008283 2500000000 8618578123057 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394957627/10000000000 : ℝ)^8241 ≤ (8798073060001/20000000000000 : ℝ)^6193 := by
    have hnat : (5394957627 : ℕ)^8241*20000000000000^6193 ≤ 8798073060001^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394957627 10000000000 8798073060001 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2148045847/10000000000 : ℝ)^8241 ≤ (12916744068091/100000000000000 : ℝ)^6193 := by
    have hnat : (2148045847 : ℕ)^8241*100000000000000^6193 ≤ 12916744068091^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148045847 10000000000 12916744068091 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328008283/2500000000 : ℝ), (5394957627/10000000000 : ℝ), (-2148045847/10000000000 : ℝ)] ![(8618578123057/20000000000000 : ℝ), (8798073060001/20000000000000 : ℝ), (12916744068091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328008283/2500000000 : ℝ)|^8241 ≤ (8618578123057/20000000000000 : ℝ)^6193
        have hw : |(1328008283/2500000000 : ℝ)|=(1328008283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394957627/10000000000 : ℝ)|^8241 ≤ (8798073060001/20000000000000 : ℝ)^6193
        have hw : |(5394957627/10000000000 : ℝ)|=(5394957627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2148045847/10000000000 : ℝ)|^8241 ≤ (12916744068091/100000000000000 : ℝ)^6193
        have hw : |(-2148045847/10000000000 : ℝ)|=(2148045847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s6_7 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218903339/500000000 : ℝ)*x 0 + (4507983537/10000000000 : ℝ)*x 1 + (2125988921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218903339/500000000 : ℝ)^8241 ≤ (33316235187143/100000000000000 : ℝ)^6193 := by
    have hnat : (218903339 : ℕ)^8241*100000000000000^6193 ≤ 33316235187143^6193*500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218903339 500000000 33316235187143 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507983537/10000000000 : ℝ)^8241 ≤ (34638228865941/100000000000000 : ℝ)^6193 := by
    have hnat : (4507983537 : ℕ)^8241*100000000000000^6193 ≤ 34638228865941^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507983537 10000000000 34638228865941 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125988921/5000000000 : ℝ)^8241 ≤ (16022767968741/50000000000000 : ℝ)^6193 := by
    have hnat : (2125988921 : ℕ)^8241*50000000000000^6193 ≤ 16022767968741^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125988921 5000000000 16022767968741 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218903339/500000000 : ℝ), (4507983537/10000000000 : ℝ), (2125988921/5000000000 : ℝ)] ![(33316235187143/100000000000000 : ℝ), (34638228865941/100000000000000 : ℝ), (16022767968741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218903339/500000000 : ℝ)|^8241 ≤ (33316235187143/100000000000000 : ℝ)^6193
        have hw : |(218903339/500000000 : ℝ)|=(218903339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507983537/10000000000 : ℝ)|^8241 ≤ (34638228865941/100000000000000 : ℝ)^6193
        have hw : |(4507983537/10000000000 : ℝ)|=(4507983537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2125988921/5000000000 : ℝ)|^8241 ≤ (16022767968741/50000000000000 : ℝ)^6193
        have hw : |(2125988921/5000000000 : ℝ)|=(2125988921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1048_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5607/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2801/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3513/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3513/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3513/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3513/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3513/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3513/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11169/100000 : ℝ) ^ (515/128 : ℝ) ≤ (14782401665497453/100000000000000000000 : ℝ) := by
    have hpowers : (11169/100000 : ℝ)^515 ≤ (14782401665497453/100000000000000000000 : ℝ)^128 := by
      have hnat : (11169 : ℕ)^515*100000000000000000000^128 ≤ 14782401665497453^128*100000^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11169 100000 14782401665497453 100000000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11169/100000 : ℝ)) (X := (14782401665497453/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hpowhi : (3513/25000 : ℝ) ^ (515/128 : ℝ) ≤ (4654657071575351/12500000000000000000 : ℝ) := by
    have hpowers : (3513/25000 : ℝ)^515 ≤ (4654657071575351/12500000000000000000 : ℝ)^128 := by
      have hnat : (3513 : ℕ)^515*12500000000000000000^128 ≤ 4654657071575351^128*25000^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3513 25000 4654657071575351 12500000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3513/25000 : ℝ)) (X := (4654657071575351/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014782401665497453/50000000000000000000 : ℝ) ≤ (10000734732917863/10000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (50014782401665497453/50000000000000000000 : ℝ)^128 ≤ (10000734732917863/10000000000000000 : ℝ)^515 := by
      have hnat : (50014782401665497453 : ℕ)^128*10000000000000000^515 ≤ 10000734732917863^515*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014782401665497453 50000000000000000000 10000734732917863 10000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000734732917863/10000000000000000 : ℝ)) (X := (50014782401665497453/50000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052019658238100261/100000000000000000000 : ℝ) ≤ (1250161582893833/1250000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (100052019658238100261/100000000000000000000 : ℝ)^128 ≤ (1250161582893833/1250000000000000 : ℝ)^515 := by
      have hnat : (100052019658238100261 : ℕ)^128*1250000000000000^515 ≤ 1250161582893833^515*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052019658238100261 100000000000000000000 1250161582893833 1250000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250161582893833/1250000000000000 : ℝ)) (X := (100052019658238100261/100000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254654657071575351/6250000000000000000 : ℝ) ≤ (2000370118676693/2000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (6254654657071575351/6250000000000000000 : ℝ)^128 ≤ (2000370118676693/2000000000000000 : ℝ)^515 := by
      have hnat : (6254654657071575351 : ℕ)^128*2000000000000000^515 ≤ 2000370118676693^515*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254654657071575351 6250000000000000000 2000370118676693 2000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000370118676693/2000000000000000 : ℝ)) (X := (6254654657071575351/6250000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14782401665497453/100000000000000000000 : ℝ) ≤ ((9606551729820630097/9610000000000000000 : ℝ)+2*(185976744267/96100000000000 : ℝ)*(11169/100000 : ℝ))^(515/128 : ℝ) := by
    rw [show (9606551729820630097/9610000000000000000 : ℝ)+2*(185976744267/96100000000000 : ℝ)*(11169/100000 : ℝ)=(10000734732917863/10000000000000000 : ℝ) by norm_num, show 1+2*(14782401665497453/100000000000000000000 : ℝ)=(50014782401665497453/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4654657071575351/12500000000000000000 : ℝ)+(14782401665497453/100000000000000000000 : ℝ) ≤ ((9606551729820630097/9610000000000000000 : ℝ)+(185976744267/96100000000000 : ℝ)*((3513/25000 : ℝ)+(11169/100000 : ℝ)))^(515/128 : ℝ) := by
    rw [show (9606551729820630097/9610000000000000000 : ℝ)+(185976744267/96100000000000 : ℝ)*((3513/25000 : ℝ)+(11169/100000 : ℝ))=(1250161582893833/1250000000000000 : ℝ) by norm_num, show 1+(4654657071575351/12500000000000000000 : ℝ)+(14782401665497453/100000000000000000000 : ℝ)=(100052019658238100261/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4654657071575351/12500000000000000000 : ℝ) ≤ ((9606551729820630097/9610000000000000000 : ℝ)+2*(185976744267/96100000000000 : ℝ)*(3513/25000 : ℝ))^(515/128 : ℝ) := by
    rw [show (9606551729820630097/9610000000000000000 : ℝ)+2*(185976744267/96100000000000 : ℝ)*(3513/25000 : ℝ)=(2000370118676693/2000000000000000 : ℝ) by norm_num, show 1+2*(4654657071575351/12500000000000000000 : ℝ)=(6254654657071575351/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9606551729820630097/9610000000000000000 : ℝ)*(X 1 0+X 2 0)+(185976744267/96100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (11169/100000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (9606551729820630097/9610000000000000000 : ℝ)) (alpha := (185976744267/96100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9606551729820630097/9610000000000000000 : ℝ)*(X 0 1+X 2 1)+(185976744267/96100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (11169/100000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (9606551729820630097/9610000000000000000 : ℝ)) (alpha := (185976744267/96100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9606551729820630097/9610000000000000000 : ℝ)*(X 0 2+X 1 2)+(185976744267/96100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (11169/100000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (9606551729820630097/9610000000000000000 : ℝ)) (alpha := (185976744267/96100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2212606841/10000000000 : ℝ)*X 0 0+(2697645813/5000000000 : ℝ)*X 0 1+(131588299/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334073311/625000000 : ℝ)*X 1 0+(-2279471419/10000000000 : ℝ)*X 1 1+(5263531951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534517279/1000000000 : ℝ)*X 2 0+(2631766037/5000000000 : ℝ)*X 2 1+(-1139735751/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((136814261/312500000 : ℝ)*X 0 0+(2125662701/5000000000 : ℝ)*X 0 1+(4508633779/10000000000 : ℝ)*X 0 2+(136814261/312500000 : ℝ)*X 1 0+(2125662701/5000000000 : ℝ)*X 1 1+(4508633779/10000000000 : ℝ)*X 1 2+(136814261/312500000 : ℝ)*X 2 0+(2125662701/5000000000 : ℝ)*X 2 1+(4508633779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2212612119/10000000000 : ℝ)*X 0 0+(526386477/1000000000 : ℝ)*X 0 1+(1348739397/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265601657/500000000 : ℝ)*X 1 0+(-2148045781/10000000000 : ℝ)*X 1 1+(1348739417/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328008283/2500000000 : ℝ)*X 2 0+(5394957627/10000000000 : ℝ)*X 2 1+(-2148045847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((218903339/500000000 : ℝ)*X 0 0+(4507983537/10000000000 : ℝ)*X 0 1+(2125988921/5000000000 : ℝ)*X 0 2+(218903339/500000000 : ℝ)*X 1 0+(4507983537/10000000000 : ℝ)*X 1 1+(2125988921/5000000000 : ℝ)*X 1 2+(218903339/500000000 : ℝ)*X 2 0+(4507983537/10000000000 : ℝ)*X 2 1+(2125988921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (150317475308281042918619973/30031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (284236431/25000000000000 : ℝ)*(base19) + (855687829/100000000000000 : ℝ)*(base23) + (9170007/100000000000000 : ℝ)*(lower2) + (21710677/10000000000000 : ℝ)*(upper3) + (4805889/20000000000000 : ℝ)*(upper5) + (358626757088853/6250000000000 : ℝ)*(major0) + (358626757088853/6250000000000 : ℝ)*(major1) + (358626757088853/6250000000000 : ℝ)*(major2) + (948701431415279/12500000000000 : ℝ)*(sp0) + (758963424983517/10000000000000 : ℝ)*(sp1) + (3794817265546533/50000000000000 : ℝ)*(sp2) + (155456105695461/4000000000000 : ℝ)*(sp3) + (23935458663/100000000000000 : ℝ)*(sp4) + (18030830249/100000000000000 : ℝ)*(sp7) + (1943210336608387/50000000000000 : ℝ)*(f.failure) + (3794817693390447/50000000000000 : ℝ)*(f.sum) + (24346826644161/4805000000000000000000000000 : ℝ)*base65 + (65335158756453759/60062500000000000000000000000000 : ℝ)*base68 + (1195251311507203759/60062500000000000000000000000000 : ℝ)*base70 + (340525146366358741/60062500000000000000000000000000 : ℝ)*base71 + (12300434470951/4805000000000000000000000000 : ℝ)*base73 + (304872625186328759/60062500000000000000000000000000 : ℝ)*base76 + (392388003597391259/60062500000000000000000000000000 : ℝ)*base78 + (638851577277171241/60062500000000000000000000000000 : ℝ)*base79 + (23503316540289/4805000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (18449387/5000000000000000000000 : ℝ)*base89 + (18449387/5000000000000000000000 : ℝ)*base91 + (18449387/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4198527922445760649839168951/480500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (939846379/50000000000000 : ℝ)*(base19) + (1003931709/50000000000000 : ℝ)*(base23) + (98466209/50000000000000 : ℝ)*(upper3) + (20934893/25000000000000 : ℝ)*(lower4) + (34991857/12500000000000 : ℝ)*(upper5) + (5767172511311087/100000000000000 : ℝ)*(major0) + (5767172511311087/100000000000000 : ℝ)*(major1) + (5767172511311087/100000000000000 : ℝ)*(major2) + (13880455567/25000000000000 : ℝ)*(sp1) + (52639668179/100000000000000 : ℝ)*(sp2) + (762818428200051/10000000000000 : ℝ)*(sp4) + (1525625376097097/20000000000000 : ℝ)*(sp5) + (476758102154307/6250000000000 : ℝ)*(sp6) + (122067514042519/3125000000000 : ℝ)*(sp7) + (122067514042519/3125000000000 : ℝ)*(f.failure) + (762818428200051/10000000000000 : ℝ)*(f.sum) + (29797858759521/4805000000000000000000000000 : ℝ)*base66 + (18884330758611114561/961000000000000000000000000000000 : ℝ)*base68 + (19716436268431114561/961000000000000000000000000000000 : ℝ)*base70 + (30363727071643114561/961000000000000000000000000000000 : ℝ)*base72 + (16536961779967/2402500000000000000000000000 : ℝ)*base73 + (9126566041679114561/961000000000000000000000000000000 : ℝ)*base76 + (5368154863929114561/961000000000000000000000000000000 : ℝ)*base78 + (13177367266181114561/961000000000000000000000000000000 : ℝ)*base80 + (14947924882041/4805000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (115481/312500000000000000000 : ℝ)*base90 + (115481/312500000000000000000 : ℝ)*base92 + (115481/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1048_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1048_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1048_s7_0 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2212650779/10000000000 : ℝ)*x 0 + (2697392211/5000000000 : ℝ)*x 1 + (1316002581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2212650779/10000000000 : ℝ)^8241 ≤ (13436254389109/100000000000000 : ℝ)^6193 := by
    have hnat : (2212650779 : ℕ)^8241*100000000000000^6193 ≤ 13436254389109^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212650779 10000000000 13436254389109 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697392211/5000000000 : ℝ)^8241 ≤ (4398848595513/10000000000000 : ℝ)^6193 := by
    have hnat : (2697392211 : ℕ)^8241*10000000000000^6193 ≤ 4398848595513^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697392211 5000000000 4398848595513 10000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316002581/2500000000 : ℝ)^8241 ≤ (10643814912811/25000000000000 : ℝ)^6193 := by
    have hnat : (1316002581 : ℕ)^8241*25000000000000^6193 ≤ 10643814912811^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316002581 2500000000 10643814912811 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2212650779/10000000000 : ℝ), (2697392211/5000000000 : ℝ), (1316002581/2500000000 : ℝ)] ![(13436254389109/100000000000000 : ℝ), (4398848595513/10000000000000 : ℝ), (10643814912811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2212650779/10000000000 : ℝ)|^8241 ≤ (13436254389109/100000000000000 : ℝ)^6193
        have hw : |(-2212650779/10000000000 : ℝ)|=(2212650779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697392211/5000000000 : ℝ)|^8241 ≤ (4398848595513/10000000000000 : ℝ)^6193
        have hw : |(2697392211/5000000000 : ℝ)|=(2697392211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316002581/2500000000 : ℝ)|^8241 ≤ (10643814912811/25000000000000 : ℝ)^6193
        have hw : |(1316002581/2500000000 : ℝ)|=(1316002581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s7_1 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345046581/10000000000 : ℝ)*x 0 + (-2279008329/10000000000 : ℝ)*x 1 + (1316002527/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345046581/10000000000 : ℝ)^8241 ≤ (43449637364909/100000000000000 : ℝ)^6193 := by
    have hnat : (5345046581 : ℕ)^8241*100000000000000^6193 ≤ 43449637364909^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345046581 10000000000 43449637364909 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279008329/10000000000 : ℝ)^8241 ≤ (6987552645721/50000000000000 : ℝ)^6193 := by
    have hnat : (2279008329 : ℕ)^8241*50000000000000^6193 ≤ 6987552645721^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279008329 10000000000 6987552645721 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316002527/2500000000 : ℝ)^8241 ≤ (4257525732651/10000000000000 : ℝ)^6193 := by
    have hnat : (1316002527 : ℕ)^8241*10000000000000^6193 ≤ 4257525732651^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316002527 2500000000 4257525732651 10000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345046581/10000000000 : ℝ), (-2279008329/10000000000 : ℝ), (1316002527/2500000000 : ℝ)] ![(43449637364909/100000000000000 : ℝ), (6987552645721/50000000000000 : ℝ), (4257525732651/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345046581/10000000000 : ℝ)|^8241 ≤ (43449637364909/100000000000000 : ℝ)^6193
        have hw : |(5345046581/10000000000 : ℝ)|=(5345046581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2279008329/10000000000 : ℝ)|^8241 ≤ (6987552645721/50000000000000 : ℝ)^6193
        have hw : |(-2279008329/10000000000 : ℝ)|=(2279008329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316002527/2500000000 : ℝ)|^8241 ≤ (4257525732651/10000000000000 : ℝ)^6193
        have hw : |(1316002527/2500000000 : ℝ)|=(1316002527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s7_2 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345046517/10000000000 : ℝ)*x 0 + (5264010281/10000000000 : ℝ)*x 1 + (-2279008187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345046517/10000000000 : ℝ)^8241 ≤ (4344963667261/10000000000000 : ℝ)^6193 := by
    have hnat : (5345046517 : ℕ)^8241*10000000000000^6193 ≤ 4344963667261^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345046517 10000000000 4344963667261 10000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264010281/10000000000 : ℝ)^8241 ≤ (851505183769/2000000000000 : ℝ)^6193 := by
    have hnat : (5264010281 : ℕ)^8241*2000000000000^6193 ≤ 851505183769^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264010281 10000000000 851505183769 2000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2279008187/10000000000 : ℝ)^8241 ≤ (13975104132727/100000000000000 : ℝ)^6193 := by
    have hnat : (2279008187 : ℕ)^8241*100000000000000^6193 ≤ 13975104132727^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279008187 10000000000 13975104132727 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345046517/10000000000 : ℝ), (5264010281/10000000000 : ℝ), (-2279008187/10000000000 : ℝ)] ![(4344963667261/10000000000000 : ℝ), (851505183769/2000000000000 : ℝ), (13975104132727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345046517/10000000000 : ℝ)|^8241 ≤ (4344963667261/10000000000000 : ℝ)^6193
        have hw : |(5345046517/10000000000 : ℝ)|=(5345046517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264010281/10000000000 : ℝ)|^8241 ≤ (851505183769/2000000000000 : ℝ)^6193
        have hw : |(5264010281/10000000000 : ℝ)|=(5264010281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2279008187/10000000000 : ℝ)|^8241 ≤ (13975104132727/100000000000000 : ℝ)^6193
        have hw : |(-2279008187/10000000000 : ℝ)|=(2279008187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s7_3 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (875616339/2000000000 : ℝ)*x 0 + (4252284167/10000000000 : ℝ)*x 1 + (2253834149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875616339/2000000000 : ℝ)^8241 ≤ (16658193110771/50000000000000 : ℝ)^6193 := by
    have hnat : (875616339 : ℕ)^8241*50000000000000^6193 ≤ 16658193110771^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875616339 2000000000 16658193110771 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4252284167/10000000000 : ℝ)^8241 ≤ (32048608091581/100000000000000 : ℝ)^6193 := by
    have hnat : (4252284167 : ℕ)^8241*100000000000000^6193 ≤ 32048608091581^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252284167 10000000000 32048608091581 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253834149/5000000000 : ℝ)^8241 ≤ (6927001133403/20000000000000 : ℝ)^6193 := by
    have hnat : (2253834149 : ℕ)^8241*20000000000000^6193 ≤ 6927001133403^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253834149 5000000000 6927001133403 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875616339/2000000000 : ℝ), (4252284167/10000000000 : ℝ), (2253834149/5000000000 : ℝ)] ![(16658193110771/50000000000000 : ℝ), (32048608091581/100000000000000 : ℝ), (6927001133403/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875616339/2000000000 : ℝ)|^8241 ≤ (16658193110771/50000000000000 : ℝ)^6193
        have hw : |(875616339/2000000000 : ℝ)|=(875616339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4252284167/10000000000 : ℝ)|^8241 ≤ (32048608091581/100000000000000 : ℝ)^6193
        have hw : |(4252284167/10000000000 : ℝ)|=(4252284167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253834149/5000000000 : ℝ)|^8241 ≤ (6927001133403/20000000000000 : ℝ)^6193
        have hw : |(2253834149/5000000000 : ℝ)|=(2253834149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s7_4 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-553164031/2500000000 : ℝ)*x 0 + (1316084539/2500000000 : ℝ)*x 1 + (5394455251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (553164031/2500000000 : ℝ)^8241 ≤ (1343629757999/10000000000000 : ℝ)^6193 := by
    have hnat : (553164031 : ℕ)^8241*10000000000000^6193 ≤ 1343629757999^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553164031 2500000000 1343629757999 10000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316084539/2500000000 : ℝ)^8241 ≤ (42578788030193/100000000000000 : ℝ)^6193 := by
    have hnat : (1316084539 : ℕ)^8241*100000000000000^6193 ≤ 42578788030193^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316084539 2500000000 42578788030193 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394455251/10000000000 : ℝ)^8241 ≤ (8796982874111/20000000000000 : ℝ)^6193 := by
    have hnat : (5394455251 : ℕ)^8241*20000000000000^6193 ≤ 8796982874111^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394455251 10000000000 8796982874111 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-553164031/2500000000 : ℝ), (1316084539/2500000000 : ℝ), (5394455251/10000000000 : ℝ)] ![(1343629757999/10000000000000 : ℝ), (42578788030193/100000000000000 : ℝ), (8796982874111/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-553164031/2500000000 : ℝ)|^8241 ≤ (1343629757999/10000000000000 : ℝ)^6193
        have hw : |(-553164031/2500000000 : ℝ)|=(553164031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316084539/2500000000 : ℝ)|^8241 ≤ (42578788030193/100000000000000 : ℝ)^6193
        have hw : |(1316084539/2500000000 : ℝ)|=(1316084539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394455251/10000000000 : ℝ)|^8241 ≤ (8796982874111/20000000000000 : ℝ)^6193
        have hw : |(5394455251/10000000000 : ℝ)|=(5394455251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s7_5 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664019361/1250000000 : ℝ)*x 0 + (-53714079/250000000 : ℝ)*x 1 + (5394454971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664019361/1250000000 : ℝ)^8241 ≤ (43094204979431/100000000000000 : ℝ)^6193 := by
    have hnat : (664019361 : ℕ)^8241*100000000000000^6193 ≤ 43094204979431^6193*1250000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664019361 1250000000 43094204979431 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53714079/250000000 : ℝ)^8241 ≤ (3230220918569/25000000000000 : ℝ)^6193 := by
    have hnat : (53714079 : ℕ)^8241*25000000000000^6193 ≤ 3230220918569^6193*250000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53714079 250000000 3230220918569 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394454971/10000000000 : ℝ)^8241 ≤ (21992455666259/50000000000000 : ℝ)^6193 := by
    have hnat : (5394454971 : ℕ)^8241*50000000000000^6193 ≤ 21992455666259^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394454971 10000000000 21992455666259 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664019361/1250000000 : ℝ), (-53714079/250000000 : ℝ), (5394454971/10000000000 : ℝ)] ![(43094204979431/100000000000000 : ℝ), (3230220918569/25000000000000 : ℝ), (21992455666259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664019361/1250000000 : ℝ)|^8241 ≤ (43094204979431/100000000000000 : ℝ)^6193
        have hw : |(664019361/1250000000 : ℝ)|=(664019361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-53714079/250000000 : ℝ)|^8241 ≤ (3230220918569/25000000000000 : ℝ)^6193
        have hw : |(-53714079/250000000 : ℝ)|=(53714079/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394454971/10000000000 : ℝ)|^8241 ≤ (21992455666259/50000000000000 : ℝ)^6193
        have hw : |(5394454971/10000000000 : ℝ)|=(5394454971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s7_6 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332009667/625000000 : ℝ)*x 0 + (269722769/500000000 : ℝ)*x 1 + (-2148562897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332009667/625000000 : ℝ)^8241 ≤ (5386775330961/12500000000000 : ℝ)^6193 := by
    have hnat : (332009667 : ℕ)^8241*12500000000000^6193 ≤ 5386775330961^6193*625000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332009667 625000000 5386775330961 12500000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269722769/500000000 : ℝ)^8241 ≤ (21992457885111/50000000000000 : ℝ)^6193 := by
    have hnat : (269722769 : ℕ)^8241*50000000000000^6193 ≤ 21992457885111^6193*500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269722769 500000000 21992457885111 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2148562897/10000000000 : ℝ)^8241 ≤ (403777549051/3125000000000 : ℝ)^6193 := by
    have hnat : (2148562897 : ℕ)^8241*3125000000000^6193 ≤ 403777549051^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148562897 10000000000 403777549051 3125000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332009667/625000000 : ℝ), (269722769/500000000 : ℝ), (-2148562897/10000000000 : ℝ)] ![(5386775330961/12500000000000 : ℝ), (21992457885111/50000000000000 : ℝ), (403777549051/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332009667/625000000 : ℝ)|^8241 ≤ (5386775330961/12500000000000 : ℝ)^6193
        have hw : |(332009667/625000000 : ℝ)|=(332009667/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269722769/500000000 : ℝ)|^8241 ≤ (21992457885111/50000000000000 : ℝ)^6193
        have hw : |(269722769/500000000 : ℝ)|=(269722769/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2148562897/10000000000 : ℝ)|^8241 ≤ (403777549051/3125000000000 : ℝ)^6193
        have hw : |(-2148562897/10000000000 : ℝ)|=(2148562897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s7_7 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378091023/10000000000 : ℝ)*x 0 + (1126757137/2500000000 : ℝ)*x 1 + (2126463463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378091023/10000000000 : ℝ)^8241 ≤ (4164560085019/12500000000000 : ℝ)^6193 := by
    have hnat : (4378091023 : ℕ)^8241*12500000000000^6193 ≤ 4164560085019^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378091023 10000000000 4164560085019 12500000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126757137/2500000000 : ℝ)^8241 ≤ (3462846469563/10000000000000 : ℝ)^6193 := by
    have hnat : (1126757137 : ℕ)^8241*10000000000000^6193 ≤ 3462846469563^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126757137 2500000000 3462846469563 10000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126463463/5000000000 : ℝ)^8241 ≤ (32055054602869/100000000000000 : ℝ)^6193 := by
    have hnat : (2126463463 : ℕ)^8241*100000000000000^6193 ≤ 32055054602869^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126463463 5000000000 32055054602869 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378091023/10000000000 : ℝ), (1126757137/2500000000 : ℝ), (2126463463/5000000000 : ℝ)] ![(4164560085019/12500000000000 : ℝ), (3462846469563/10000000000000 : ℝ), (32055054602869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378091023/10000000000 : ℝ)|^8241 ≤ (4164560085019/12500000000000 : ℝ)^6193
        have hw : |(4378091023/10000000000 : ℝ)|=(4378091023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126757137/2500000000 : ℝ)|^8241 ≤ (3462846469563/10000000000000 : ℝ)^6193
        have hw : |(1126757137/2500000000 : ℝ)|=(1126757137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2126463463/5000000000 : ℝ)|^8241 ≤ (32055054602869/100000000000000 : ℝ)^6193
        have hw : |(2126463463/5000000000 : ℝ)|=(2126463463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1048_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1403/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6997/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2801/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2801/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2801/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2801/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2801/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2801/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5607/50000 : ℝ) ^ (515/128 : ℝ) ≤ (15023494764632709/100000000000000000000 : ℝ) := by
    have hpowers : (5607/50000 : ℝ)^515 ≤ (15023494764632709/100000000000000000000 : ℝ)^128 := by
      have hnat : (5607 : ℕ)^515*100000000000000000000^128 ≤ 15023494764632709^128*50000^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5607 50000 15023494764632709 100000000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5607/50000 : ℝ)) (X := (15023494764632709/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2801/20000 : ℝ) ^ (515/128 : ℝ) ≤ (4592334099160343/12500000000000000000 : ℝ) := by
    have hpowers : (2801/20000 : ℝ)^515 ≤ (4592334099160343/12500000000000000000 : ℝ)^128 := by
      have hnat : (2801 : ℕ)^515*12500000000000000000^128 ≤ 4592334099160343^128*20000^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2801 20000 4592334099160343 12500000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2801/20000 : ℝ)) (X := (4592334099160343/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015023494764632709/50000000000000000000 : ℝ) ≤ (1250093339333497/1250000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (50015023494764632709/50000000000000000000 : ℝ)^128 ≤ (1250093339333497/1250000000000000 : ℝ)^515 := by
      have hnat : (50015023494764632709 : ℕ)^128*1250000000000000^515 ≤ 1250093339333497^515*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015023494764632709 50000000000000000000 1250093339333497 1250000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250093339333497/1250000000000000 : ℝ)) (X := (50015023494764632709/50000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051762167557915453/100000000000000000000 : ℝ) ≤ (5000643132938339/5000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (100051762167557915453/100000000000000000000 : ℝ)^128 ≤ (5000643132938339/5000000000000000 : ℝ)^515 := by
      have hnat : (100051762167557915453 : ℕ)^128*5000000000000000^515 ≤ 5000643132938339^515*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051762167557915453 100000000000000000000 5000643132938339 5000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000643132938339/5000000000000000 : ℝ)) (X := (100051762167557915453/100000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254592334099160343/6250000000000000000 : ℝ) ≤ (500091290854269/500000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (6254592334099160343/6250000000000000000 : ℝ)^128 ≤ (500091290854269/500000000000000 : ℝ)^515 := by
      have hnat : (6254592334099160343 : ℕ)^128*500000000000000^515 ≤ 500091290854269^515*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254592334099160343 6250000000000000000 500091290854269 500000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500091290854269/500000000000000 : ℝ)) (X := (6254592334099160343/6250000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15023494764632709/100000000000000000000 : ℝ) ≤ ((348749787826619407/348875000000000000 : ℝ)+2*(269775604351/139550000000000 : ℝ)*(5607/50000 : ℝ))^(515/128 : ℝ) := by
    rw [show (348749787826619407/348875000000000000 : ℝ)+2*(269775604351/139550000000000 : ℝ)*(5607/50000 : ℝ)=(1250093339333497/1250000000000000 : ℝ) by norm_num, show 1+2*(15023494764632709/100000000000000000000 : ℝ)=(50015023494764632709/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4592334099160343/12500000000000000000 : ℝ)+(15023494764632709/100000000000000000000 : ℝ) ≤ ((348749787826619407/348875000000000000 : ℝ)+(269775604351/139550000000000 : ℝ)*((2801/20000 : ℝ)+(5607/50000 : ℝ)))^(515/128 : ℝ) := by
    rw [show (348749787826619407/348875000000000000 : ℝ)+(269775604351/139550000000000 : ℝ)*((2801/20000 : ℝ)+(5607/50000 : ℝ))=(5000643132938339/5000000000000000 : ℝ) by norm_num, show 1+(4592334099160343/12500000000000000000 : ℝ)+(15023494764632709/100000000000000000000 : ℝ)=(100051762167557915453/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4592334099160343/12500000000000000000 : ℝ) ≤ ((348749787826619407/348875000000000000 : ℝ)+2*(269775604351/139550000000000 : ℝ)*(2801/20000 : ℝ))^(515/128 : ℝ) := by
    rw [show (348749787826619407/348875000000000000 : ℝ)+2*(269775604351/139550000000000 : ℝ)*(2801/20000 : ℝ)=(500091290854269/500000000000000 : ℝ) by norm_num, show 1+2*(4592334099160343/12500000000000000000 : ℝ)=(6254592334099160343/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (348749787826619407/348875000000000000 : ℝ)*(X 1 0+X 2 0)+(269775604351/139550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (348749787826619407/348875000000000000 : ℝ)) (alpha := (269775604351/139550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (348749787826619407/348875000000000000 : ℝ)*(X 0 1+X 2 1)+(269775604351/139550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (348749787826619407/348875000000000000 : ℝ)) (alpha := (269775604351/139550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (348749787826619407/348875000000000000 : ℝ)*(X 0 2+X 1 2)+(269775604351/139550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (348749787826619407/348875000000000000 : ℝ)) (alpha := (269775604351/139550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2212650779/10000000000 : ℝ)*X 0 0+(2697392211/5000000000 : ℝ)*X 0 1+(1316002581/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345046581/10000000000 : ℝ)*X 1 0+(-2279008329/10000000000 : ℝ)*X 1 1+(1316002527/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345046517/10000000000 : ℝ)*X 2 0+(5264010281/10000000000 : ℝ)*X 2 1+(-2279008187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875616339/2000000000 : ℝ)*X 0 0+(4252284167/10000000000 : ℝ)*X 0 1+(2253834149/5000000000 : ℝ)*X 0 2+(875616339/2000000000 : ℝ)*X 1 0+(4252284167/10000000000 : ℝ)*X 1 1+(2253834149/5000000000 : ℝ)*X 1 2+(875616339/2000000000 : ℝ)*X 2 0+(4252284167/10000000000 : ℝ)*X 2 1+(2253834149/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-553164031/2500000000 : ℝ)*X 0 0+(1316084539/2500000000 : ℝ)*X 0 1+(5394455251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664019361/1250000000 : ℝ)*X 1 0+(-53714079/250000000 : ℝ)*X 1 1+(5394454971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332009667/625000000 : ℝ)*X 2 0+(269722769/500000000 : ℝ)*X 2 1+(-2148562897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378091023/10000000000 : ℝ)*X 0 0+(1126757137/2500000000 : ℝ)*X 0 1+(2126463463/5000000000 : ℝ)*X 0 2+(4378091023/10000000000 : ℝ)*X 1 0+(1126757137/2500000000 : ℝ)*X 1 1+(2126463463/5000000000 : ℝ)*X 1 2+(4378091023/10000000000 : ℝ)*X 2 0+(1126757137/2500000000 : ℝ)*X 2 1+(2126463463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8231244854057568219813021/1090234375000000000000000000000 : ℝ) := by norm_num
    linear_combination (668590363/50000000000000 : ℝ)*(base19) + (936181621/100000000000000 : ℝ)*(base23) + (165396229/100000000000000 : ℝ)*(lower2) + (132998817/100000000000000 : ℝ)*(upper3) + (107557371/100000000000000 : ℝ)*(upper5) + (5781264000636467/100000000000000 : ℝ)*(major0) + (5781264000636467/100000000000000 : ℝ)*(major1) + (5781264000636467/100000000000000 : ℝ)*(major2) + (7646797311018891/100000000000000 : ℝ)*(sp0) + (7646821664162287/100000000000000 : ℝ)*(sp1) + (477926379072587/6250000000000 : ℝ)*(sp2) + (3915686532306407/100000000000000 : ℝ)*(sp3) + (12845162061/50000000000000 : ℝ)*(sp4) + (9107978797/50000000000000 : ℝ)*(sp7) + (1957852374132001/50000000000000 : ℝ)*(f.failure) + (7646823001343013/100000000000000 : ℝ)*(f.sum) + (2160174672337/436093750000000000000000000 : ℝ)*base65 + (185645364851845069/34887500000000000000000000000000 : ℝ)*base67 + (129379149505457569/34887500000000000000000000000000 : ℝ)*base69 + (281100259597232569/34887500000000000000000000000000 : ℝ)*base71 + (7832557009639/3488750000000000000000000000 : ℝ)*base74 + (188882128204417431/34887500000000000000000000000000 : ℝ)*base76 + (525522750355395069/34887500000000000000000000000000 : ℝ)*base77 + (121244570785120069/34887500000000000000000000000000 : ℝ)*base79 + (1603876899501/3488750000000000000000000000 : ℝ)*base81 + (47775001/5000000000000000000000 : ℝ)*base89 + (47775001/5000000000000000000000 : ℝ)*base91 + (47775001/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45525183421466676086446989/8721875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1103028661/100000000000000 : ℝ)*(base19) + (379781153/25000000000000 : ℝ)*(base23) + (288096997/100000000000000 : ℝ)*(upper2) + (32154717/100000000000000 : ℝ)*(upper3) + (5674228377593/97656250000 : ℝ)*(major0) + (5674228377593/97656250000 : ℝ)*(major1) + (5674228377593/97656250000 : ℝ)*(major2) + (19982360581/100000000000000 : ℝ)*(sp1) + (50063786377/100000000000000 : ℝ)*(sp2) + (3705121663/50000000000000 : ℝ)*(sp3) + (1921343507488677/25000000000000 : ℝ)*(sp4) + (3842676472282733/50000000000000 : ℝ)*(sp5) + (192133061176093/2500000000000 : ℝ)*(sp6) + (1967719051561951/50000000000000 : ℝ)*(sp7) + (983861378341807/25000000000000 : ℝ)*(f.failure) + (1921343507488677/25000000000000 : ℝ)*(f.sum) + (21092880329639/3488750000000000000000000000 : ℝ)*base66 + (53085218855036553/4360937500000000000000000000000 : ℝ)*base67 + (3457062422594839/2180468750000000000000000000000 : ℝ)*base69 + (38061677801607481/8721875000000000000000000000000 : ℝ)*base71 + (15188409614169/13955000000000000000000000000 : ℝ)*base73 + (95351266157586553/4360937500000000000000000000000 : ℝ)*base75 + (5295088847080019/8721875000000000000000000000000 : ℝ)*base78 + (55085841650548769/8721875000000000000000000000000 : ℝ)*base80 + (63644460367391/13955000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (10757193/2500000000000000000000 : ℝ)*base90 + (10757193/2500000000000000000000 : ℝ)*base92 + (10757193/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1048_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1048_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1048_s8_0 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106331341/5000000000 : ℝ)*x 0 + (2697334819/5000000000 : ℝ)*x 1 + (1052823421/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106331341/5000000000 : ℝ)^8241 ≤ (6718175286351/50000000000000 : ℝ)^6193 := by
    have hnat : (1106331341 : ℕ)^8241*50000000000000^6193 ≤ 6718175286351^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106331341 5000000000 6718175286351 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697334819/5000000000 : ℝ)^8241 ≤ (1099681012823/2500000000000 : ℝ)^6193 := by
    have hnat : (2697334819 : ℕ)^8241*2500000000000^6193 ≤ 1099681012823^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697334819 5000000000 1099681012823 2500000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052823421/2000000000 : ℝ)^8241 ≤ (4257640890213/10000000000000 : ℝ)^6193 := by
    have hnat : (1052823421 : ℕ)^8241*10000000000000^6193 ≤ 4257640890213^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052823421 2000000000 4257640890213 10000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106331341/5000000000 : ℝ), (2697334819/5000000000 : ℝ), (1052823421/2000000000 : ℝ)] ![(6718175286351/50000000000000 : ℝ), (1099681012823/2500000000000 : ℝ), (4257640890213/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106331341/5000000000 : ℝ)|^8241 ≤ (6718175286351/50000000000000 : ℝ)^6193
        have hw : |(-1106331341/5000000000 : ℝ)|=(1106331341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697334819/5000000000 : ℝ)|^8241 ≤ (1099681012823/2500000000000 : ℝ)^6193
        have hw : |(2697334819/5000000000 : ℝ)|=(2697334819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052823421/2000000000 : ℝ)|^8241 ≤ (4257640890213/10000000000000 : ℝ)^6193
        have hw : |(1052823421/2000000000 : ℝ)|=(1052823421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s8_1 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672508717/5000000000 : ℝ)*x 0 + (-1139452921/5000000000 : ℝ)*x 1 + (1052823421/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672508717/5000000000 : ℝ)^8241 ≤ (8689864415451/20000000000000 : ℝ)^6193 := by
    have hnat : (2672508717 : ℕ)^8241*20000000000000^6193 ≤ 8689864415451^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672508717 5000000000 8689864415451 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1139452921/5000000000 : ℝ)^8241 ≤ (13974269007877/100000000000000 : ℝ)^6193 := by
    have hnat : (1139452921 : ℕ)^8241*100000000000000^6193 ≤ 13974269007877^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139452921 5000000000 13974269007877 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052823421/2000000000 : ℝ)^8241 ≤ (4257640890213/10000000000000 : ℝ)^6193 := by
    have hnat : (1052823421 : ℕ)^8241*10000000000000^6193 ≤ 4257640890213^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052823421 2000000000 4257640890213 10000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672508717/5000000000 : ℝ), (-1139452921/5000000000 : ℝ), (1052823421/2000000000 : ℝ)] ![(8689864415451/20000000000000 : ℝ), (13974269007877/100000000000000 : ℝ), (4257640890213/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672508717/5000000000 : ℝ)|^8241 ≤ (8689864415451/20000000000000 : ℝ)^6193
        have hw : |(2672508717/5000000000 : ℝ)|=(2672508717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1139452921/5000000000 : ℝ)|^8241 ≤ (13974269007877/100000000000000 : ℝ)^6193
        have hw : |(-1139452921/5000000000 : ℝ)|=(1139452921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052823421/2000000000 : ℝ)|^8241 ≤ (4257640890213/10000000000000 : ℝ)^6193
        have hw : |(1052823421/2000000000 : ℝ)|=(1052823421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s8_2 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672508717/5000000000 : ℝ)*x 0 + (1052823421/2000000000 : ℝ)*x 1 + (-1139452921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672508717/5000000000 : ℝ)^8241 ≤ (8689864415451/20000000000000 : ℝ)^6193 := by
    have hnat : (2672508717 : ℕ)^8241*20000000000000^6193 ≤ 8689864415451^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672508717 5000000000 8689864415451 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052823421/2000000000 : ℝ)^8241 ≤ (4257640890213/10000000000000 : ℝ)^6193 := by
    have hnat : (1052823421 : ℕ)^8241*10000000000000^6193 ≤ 4257640890213^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052823421 2000000000 4257640890213 10000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139452921/5000000000 : ℝ)^8241 ≤ (13974269007877/100000000000000 : ℝ)^6193 := by
    have hnat : (1139452921 : ℕ)^8241*100000000000000^6193 ≤ 13974269007877^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139452921 5000000000 13974269007877 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672508717/5000000000 : ℝ), (1052823421/2000000000 : ℝ), (-1139452921/5000000000 : ℝ)] ![(8689864415451/20000000000000 : ℝ), (4257640890213/10000000000000 : ℝ), (13974269007877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672508717/5000000000 : ℝ)|^8241 ≤ (8689864415451/20000000000000 : ℝ)^6193
        have hw : |(2672508717/5000000000 : ℝ)|=(2672508717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052823421/2000000000 : ℝ)|^8241 ≤ (4257640890213/10000000000000 : ℝ)^6193
        have hw : |(1052823421/2000000000 : ℝ)|=(1052823421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1139452921/5000000000 : ℝ)|^8241 ≤ (13974269007877/100000000000000 : ℝ)^6193
        have hw : |(-1139452921/5000000000 : ℝ)|=(1139452921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s8_3 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378087307/10000000000 : ℝ)*x 0 + (4252500103/10000000000 : ℝ)*x 1 + (2253725463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378087307/10000000000 : ℝ)^8241 ≤ (33316443050621/100000000000000 : ℝ)^6193 := by
    have hnat : (4378087307 : ℕ)^8241*100000000000000^6193 ≤ 33316443050621^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378087307 10000000000 33316443050621 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4252500103/10000000000 : ℝ)^8241 ≤ (32050773772279/100000000000000 : ℝ)^6193 := by
    have hnat : (4252500103 : ℕ)^8241*100000000000000^6193 ≤ 32050773772279^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252500103 10000000000 32050773772279 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253725463/5000000000 : ℝ)^8241 ≤ (17316391582189/50000000000000 : ℝ)^6193 := by
    have hnat : (2253725463 : ℕ)^8241*50000000000000^6193 ≤ 17316391582189^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253725463 5000000000 17316391582189 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378087307/10000000000 : ℝ), (4252500103/10000000000 : ℝ), (2253725463/5000000000 : ℝ)] ![(33316443050621/100000000000000 : ℝ), (32050773772279/100000000000000 : ℝ), (17316391582189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378087307/10000000000 : ℝ)|^8241 ≤ (33316443050621/100000000000000 : ℝ)^6193
        have hw : |(4378087307/10000000000 : ℝ)|=(4378087307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4252500103/10000000000 : ℝ)|^8241 ≤ (32050773772279/100000000000000 : ℝ)^6193
        have hw : |(4252500103/10000000000 : ℝ)|=(4252500103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253725463/5000000000 : ℝ)|^8241 ≤ (17316391582189/50000000000000 : ℝ)^6193
        have hw : |(2253725463/5000000000 : ℝ)|=(2253725463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s8_4 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106333889/5000000000 : ℝ)*x 0 + (2632221897/5000000000 : ℝ)*x 1 + (674292723/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106333889/5000000000 : ℝ)^8241 ≤ (6718195875791/50000000000000 : ℝ)^6193 := by
    have hnat : (1106333889 : ℕ)^8241*50000000000000^6193 ≤ 6718195875791^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106333889 5000000000 6718195875791 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632221897/5000000000 : ℝ)^8241 ≤ (42579925002697/100000000000000 : ℝ)^6193 := by
    have hnat : (2632221897 : ℕ)^8241*100000000000000^6193 ≤ 42579925002697^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632221897 5000000000 42579925002697 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674292723/1250000000 : ℝ)^8241 ≤ (21991841621499/50000000000000 : ℝ)^6193 := by
    have hnat : (674292723 : ℕ)^8241*50000000000000^6193 ≤ 21991841621499^6193*1250000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674292723 1250000000 21991841621499 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106333889/5000000000 : ℝ), (2632221897/5000000000 : ℝ), (674292723/1250000000 : ℝ)] ![(6718195875791/50000000000000 : ℝ), (42579925002697/100000000000000 : ℝ), (21991841621499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106333889/5000000000 : ℝ)|^8241 ≤ (6718195875791/50000000000000 : ℝ)^6193
        have hw : |(-1106333889/5000000000 : ℝ)|=(1106333889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632221897/5000000000 : ℝ)|^8241 ≤ (42579925002697/100000000000000 : ℝ)^6193
        have hw : |(2632221897/5000000000 : ℝ)|=(2632221897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674292723/1250000000 : ℝ)|^8241 ≤ (21991841621499/50000000000000 : ℝ)^6193
        have hw : |(674292723/1250000000 : ℝ)|=(674292723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s8_5 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656090663/5000000000 : ℝ)*x 0 + (-537170241/2500000000 : ℝ)*x 1 + (269717089/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656090663/5000000000 : ℝ)^8241 ≤ (21547245190361/50000000000000 : ℝ)^6193 := by
    have hnat : (2656090663 : ℕ)^8241*50000000000000^6193 ≤ 21547245190361^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656090663 5000000000 21547245190361 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537170241/2500000000 : ℝ)^8241 ≤ (3230456600837/25000000000000 : ℝ)^6193 := by
    have hnat : (537170241 : ℕ)^8241*25000000000000^6193 ≤ 3230456600837^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537170241 2500000000 3230456600837 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269717089/500000000 : ℝ)^8241 ≤ (21991841599799/50000000000000 : ℝ)^6193 := by
    have hnat : (269717089 : ℕ)^8241*50000000000000^6193 ≤ 21991841599799^6193*500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269717089 500000000 21991841599799 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656090663/5000000000 : ℝ), (-537170241/2500000000 : ℝ), (269717089/500000000 : ℝ)] ![(21547245190361/50000000000000 : ℝ), (3230456600837/25000000000000 : ℝ), (21991841599799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656090663/5000000000 : ℝ)|^8241 ≤ (21547245190361/50000000000000 : ℝ)^6193
        have hw : |(2656090663/5000000000 : ℝ)|=(2656090663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-537170241/2500000000 : ℝ)|^8241 ≤ (3230456600837/25000000000000 : ℝ)^6193
        have hw : |(-537170241/2500000000 : ℝ)|=(537170241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269717089/500000000 : ℝ)|^8241 ≤ (21991841599799/50000000000000 : ℝ)^6193
        have hw : |(269717089/500000000 : ℝ)|=(269717089/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s8_6 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328045227/2500000000 : ℝ)*x 0 + (5394341703/10000000000 : ℝ)*x 1 + (-67146301/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328045227/2500000000 : ℝ)^8241 ≤ (1077362146709/2500000000000 : ℝ)^6193 := by
    have hnat : (1328045227 : ℕ)^8241*2500000000000^6193 ≤ 1077362146709^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328045227 2500000000 1077362146709 2500000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394341703/10000000000 : ℝ)^8241 ≤ (2748980147759/6250000000000 : ℝ)^6193 := by
    have hnat : (5394341703 : ℕ)^8241*6250000000000^6193 ≤ 2748980147759^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394341703 10000000000 2748980147759 6250000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67146301/312500000 : ℝ)^8241 ≤ (12921831749081/100000000000000 : ℝ)^6193 := by
    have hnat : (67146301 : ℕ)^8241*100000000000000^6193 ≤ 12921831749081^6193*312500000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67146301 312500000 12921831749081 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328045227/2500000000 : ℝ), (5394341703/10000000000 : ℝ), (-67146301/312500000 : ℝ)] ![(1077362146709/2500000000000 : ℝ), (2748980147759/6250000000000 : ℝ), (12921831749081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328045227/2500000000 : ℝ)|^8241 ≤ (1077362146709/2500000000000 : ℝ)^6193
        have hw : |(1328045227/2500000000 : ℝ)|=(1328045227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394341703/10000000000 : ℝ)|^8241 ≤ (2748980147759/6250000000000 : ℝ)^6193
        have hw : |(5394341703/10000000000 : ℝ)|=(5394341703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67146301/312500000 : ℝ)|^8241 ≤ (12921831749081/100000000000000 : ℝ)^6193
        have hw : |(-67146301/312500000 : ℝ)|=(67146301/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s8_7 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2189048409/5000000000 : ℝ)*x 0 + (901362577/2000000000 : ℝ)*x 1 + (850628183/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189048409/5000000000 : ℝ)^8241 ≤ (6663307872479/20000000000000 : ℝ)^6193 := by
    have hnat : (2189048409 : ℕ)^8241*20000000000000^6193 ≤ 6663307872479^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189048409 5000000000 6663307872479 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901362577/2000000000 : ℝ)^8241 ≤ (17313129884943/50000000000000 : ℝ)^6193 := by
    have hnat : (901362577 : ℕ)^8241*50000000000000^6193 ≤ 17313129884943^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901362577 2000000000 17313129884943 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850628183/2000000000 : ℝ)^8241 ≤ (6411440172737/20000000000000 : ℝ)^6193 := by
    have hnat : (850628183 : ℕ)^8241*20000000000000^6193 ≤ 6411440172737^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850628183 2000000000 6411440172737 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189048409/5000000000 : ℝ), (901362577/2000000000 : ℝ), (850628183/2000000000 : ℝ)] ![(6663307872479/20000000000000 : ℝ), (17313129884943/50000000000000 : ℝ), (6411440172737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189048409/5000000000 : ℝ)|^8241 ≤ (6663307872479/20000000000000 : ℝ)^6193
        have hw : |(2189048409/5000000000 : ℝ)|=(2189048409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901362577/2000000000 : ℝ)|^8241 ≤ (17313129884943/50000000000000 : ℝ)^6193
        have hw : |(901362577/2000000000 : ℝ)|=(901362577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850628183/2000000000 : ℝ)|^8241 ≤ (6411440172737/20000000000000 : ℝ)^6193
        have hw : |(850628183/2000000000 : ℝ)|=(850628183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1048_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5613/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1749/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6997/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1403/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6997/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1403/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6997/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1403/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6997/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1403/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6997/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1403/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6997/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1403/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1403/12500 : ℝ) ^ (515/128 : ℝ) ≤ (15077469819410221/100000000000000000000 : ℝ) := by
    have hpowers : (1403/12500 : ℝ)^515 ≤ (15077469819410221/100000000000000000000 : ℝ)^128 := by
      have hnat : (1403 : ℕ)^515*100000000000000000000^128 ≤ 15077469819410221^128*12500^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1403 12500 15077469819410221 100000000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1403/12500 : ℝ)) (X := (15077469819410221/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hpowhi : (6997/50000 : ℝ) ^ (515/128 : ℝ) ≤ (7324542217248803/20000000000000000000 : ℝ) := by
    have hpowers : (6997/50000 : ℝ)^515 ≤ (7324542217248803/20000000000000000000 : ℝ)^128 := by
      have hnat : (6997 : ℕ)^515*20000000000000000000^128 ≤ 7324542217248803^128*50000^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6997 50000 7324542217248803 20000000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6997/50000 : ℝ)) (X := (7324542217248803/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015077469819410221/50000000000000000000 : ℝ) ≤ (2000149879418619/2000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (50015077469819410221/50000000000000000000 : ℝ)^128 ≤ (2000149879418619/2000000000000000 : ℝ)^515 := by
      have hnat : (50015077469819410221 : ℕ)^128*2000000000000000^515 ≤ 2000149879418619^515*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015077469819410221 50000000000000000000 2000149879418619 2000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000149879418619/2000000000000000 : ℝ)) (X := (50015077469819410221/50000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012925045226413559/25000000000000000000 : ℝ) ≤ (10001284725836187/10000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (25012925045226413559/25000000000000000000 : ℝ)^128 ≤ (10001284725836187/10000000000000000 : ℝ)^515 := by
      have hnat : (25012925045226413559 : ℕ)^128*10000000000000000^515 ≤ 10001284725836187^515*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012925045226413559 25000000000000000000 10001284725836187 10000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001284725836187/10000000000000000 : ℝ)) (X := (25012925045226413559/25000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007324542217248803/10000000000000000000 : ℝ) ≤ (10001820054579279/10000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (10007324542217248803/10000000000000000000 : ℝ)^128 ≤ (10001820054579279/10000000000000000 : ℝ)^515 := by
      have hnat : (10007324542217248803 : ℕ)^128*10000000000000000^515 ≤ 10001820054579279^515*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007324542217248803 10000000000000000000 10001820054579279 10000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001820054579279/10000000000000000 : ℝ)) (X := (10007324542217248803/10000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15077469819410221/100000000000000000000 : ℝ) ≤ ((13845029385161471967/13850000000000000000 : ℝ)+2*(133832185773/69250000000000 : ℝ)*(1403/12500 : ℝ))^(515/128 : ℝ) := by
    rw [show (13845029385161471967/13850000000000000000 : ℝ)+2*(133832185773/69250000000000 : ℝ)*(1403/12500 : ℝ)=(2000149879418619/2000000000000000 : ℝ) by norm_num, show 1+2*(15077469819410221/100000000000000000000 : ℝ)=(50015077469819410221/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7324542217248803/20000000000000000000 : ℝ)+(15077469819410221/100000000000000000000 : ℝ) ≤ ((13845029385161471967/13850000000000000000 : ℝ)+(133832185773/69250000000000 : ℝ)*((6997/50000 : ℝ)+(1403/12500 : ℝ)))^(515/128 : ℝ) := by
    rw [show (13845029385161471967/13850000000000000000 : ℝ)+(133832185773/69250000000000 : ℝ)*((6997/50000 : ℝ)+(1403/12500 : ℝ))=(10001284725836187/10000000000000000 : ℝ) by norm_num, show 1+(7324542217248803/20000000000000000000 : ℝ)+(15077469819410221/100000000000000000000 : ℝ)=(25012925045226413559/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7324542217248803/20000000000000000000 : ℝ) ≤ ((13845029385161471967/13850000000000000000 : ℝ)+2*(133832185773/69250000000000 : ℝ)*(6997/50000 : ℝ))^(515/128 : ℝ) := by
    rw [show (13845029385161471967/13850000000000000000 : ℝ)+2*(133832185773/69250000000000 : ℝ)*(6997/50000 : ℝ)=(10001820054579279/10000000000000000 : ℝ) by norm_num, show 1+2*(7324542217248803/20000000000000000000 : ℝ)=(10007324542217248803/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13845029385161471967/13850000000000000000 : ℝ)*(X 1 0+X 2 0)+(133832185773/69250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (6997/50000 : ℝ)) (c := (13845029385161471967/13850000000000000000 : ℝ)) (alpha := (133832185773/69250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13845029385161471967/13850000000000000000 : ℝ)*(X 0 1+X 2 1)+(133832185773/69250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (6997/50000 : ℝ)) (c := (13845029385161471967/13850000000000000000 : ℝ)) (alpha := (133832185773/69250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13845029385161471967/13850000000000000000 : ℝ)*(X 0 2+X 1 2)+(133832185773/69250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (6997/50000 : ℝ)) (c := (13845029385161471967/13850000000000000000 : ℝ)) (alpha := (133832185773/69250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1106331341/5000000000 : ℝ)*X 0 0+(2697334819/5000000000 : ℝ)*X 0 1+(1052823421/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672508717/5000000000 : ℝ)*X 1 0+(-1139452921/5000000000 : ℝ)*X 1 1+(1052823421/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672508717/5000000000 : ℝ)*X 2 0+(1052823421/2000000000 : ℝ)*X 2 1+(-1139452921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378087307/10000000000 : ℝ)*X 0 0+(4252500103/10000000000 : ℝ)*X 0 1+(2253725463/5000000000 : ℝ)*X 0 2+(4378087307/10000000000 : ℝ)*X 1 0+(4252500103/10000000000 : ℝ)*X 1 1+(2253725463/5000000000 : ℝ)*X 1 2+(4378087307/10000000000 : ℝ)*X 2 0+(4252500103/10000000000 : ℝ)*X 2 1+(2253725463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1106333889/5000000000 : ℝ)*X 0 0+(2632221897/5000000000 : ℝ)*X 0 1+(674292723/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656090663/5000000000 : ℝ)*X 1 0+(-537170241/2500000000 : ℝ)*X 1 1+(269717089/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328045227/2500000000 : ℝ)*X 2 0+(5394341703/10000000000 : ℝ)*X 2 1+(-67146301/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2189048409/5000000000 : ℝ)*X 0 0+(901362577/2000000000 : ℝ)*X 0 1+(850628183/2000000000 : ℝ)*X 0 2+(2189048409/5000000000 : ℝ)*X 1 0+(901362577/2000000000 : ℝ)*X 1 1+(850628183/2000000000 : ℝ)*X 1 2+(2189048409/5000000000 : ℝ)*X 2 0+(901362577/2000000000 : ℝ)*X 2 1+(850628183/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3253976934747515566720289091/346250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (236723441/12500000000000 : ℝ)*(base19) + (1764005539/100000000000000 : ℝ)*(base23) + (69368701/100000000000000 : ℝ)*(lower2) + (238409391/100000000000000 : ℝ)*(upper3) + (70804943/50000000000000 : ℝ)*(upper5) + (5791116980902191/100000000000000 : ℝ)*(major0) + (5791116980902191/100000000000000 : ℝ)*(major1) + (5791116980902191/100000000000000 : ℝ)*(major2) + (1914951204941637/25000000000000 : ℝ)*(sp0) + (1914963372459047/25000000000000 : ℝ)*(sp1) + (7659853619618177/100000000000000 : ℝ)*(sp2) + (245146891858049/6250000000000 : ℝ)*(sp3) + (3160241073/6250000000000 : ℝ)*(sp4) + (27995192959/100000000000000 : ℝ)*(sp7) + (1961189132460871/50000000000000 : ℝ)*(f.failure) + (1914963845905929/25000000000000 : ℝ)*(f.sum) + (754428511317/865625000000000000000000000 : ℝ)*base65 + (18921811820011020303/1385000000000000000000000000000000 : ℝ)*base68 + (26930929209641020303/1385000000000000000000000000000000 : ℝ)*base70 + (21879789918726020303/1385000000000000000000000000000000 : ℝ)*base72 + (35867583901889/6925000000000000000000000000 : ℝ)*base74 + (1883044225521020303/1385000000000000000000000000000000 : ℝ)*base76 + (523698308263979697/1385000000000000000000000000000000 : ℝ)*base77 + (34975253428076020303/1385000000000000000000000000000000 : ℝ)*base80 + (4924473019911/6925000000000000000000000000 : ℝ)*base81 + (40486129/5000000000000000000000 : ℝ)*base90 + (40486129/5000000000000000000000 : ℝ)*base92 + (40486129/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1948105995615858781813355313/173125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1845088339/100000000000000 : ℝ)*(base19) + (55372621/5000000000000 : ℝ)*(base23) + (90708599/100000000000000 : ℝ)*(upper2) + (15711669/100000000000000 : ℝ)*(upper3) + (118722589/50000000000000 : ℝ)*(upper5) + (2910109100783613/50000000000000 : ℝ)*(major0) + (2910109100783613/50000000000000 : ℝ)*(major1) + (2910109100783613/50000000000000 : ℝ)*(major2) + (31906150649/50000000000000 : ℝ)*(sp1) + (14852805269/100000000000000 : ℝ)*(sp2) + (7698347231324441/100000000000000 : ℝ)*(sp4) + (7698281573934803/100000000000000 : ℝ)*(sp5) + (60143213055209/781250000000 : ℝ)*(sp6) + (1971044398361703/50000000000000 : ℝ)*(sp7) + (1971044398361703/50000000000000 : ℝ)*(f.failure) + (7698347231324441/100000000000000 : ℝ)*(f.sum) + (27245601241073/3462500000000000000000000000 : ℝ)*base65 + (4525382245017723229/692500000000000000000000000000000 : ℝ)*base68 + (7935698055742723229/692500000000000000000000000000000 : ℝ)*base70 + (3291336687162723229/692500000000000000000000000000000 : ℝ)*base72 + (17162270467523/3462500000000000000000000000 : ℝ)*base73 + (3287450309297723229/692500000000000000000000000000000 : ℝ)*base76 + (11201917939827276771/692500000000000000000000000000000 : ℝ)*base77 + (29153740149815223229/692500000000000000000000000000000 : ℝ)*base80 + (4021607158749/1731250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (14390703/5000000000000000000000 : ℝ)*base89 + (14390703/5000000000000000000000 : ℝ)*base91 + (14390703/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1048_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1749/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1048_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1048_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1749/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1048_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1048_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1048_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1749/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1048_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

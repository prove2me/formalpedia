-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1749_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:19:00.28835+00:00
-- url     : https://prove2.me/submissions/f357b8bc-31fc-4391-af02-d4eb740e0b68

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
theorem support_rectangle_w1749_s0_0 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-73873291/625000000 : ℝ)*x 0 + (2816717097/5000000000 : ℝ)*x 1 + (19438983/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73873291/625000000 : ℝ)^5759 ≤ (7448138934247/100000000000000 : ℝ)^4735 := by
    have hnat : (73873291 : ℕ)^5759*100000000000000^4735 ≤ 7448138934247^4735*625000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73873291 625000000 7448138934247 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2816717097/5000000000 : ℝ)^5759 ≤ (9951876330601/20000000000000 : ℝ)^4735 := by
    have hnat : (2816717097 : ℕ)^5759*20000000000000^4735 ≤ 9951876330601^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2816717097 5000000000 9951876330601 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19438983/39062500 : ℝ)^5759 ≤ (1337264981133/3125000000000 : ℝ)^4735 := by
    have hnat : (19438983 : ℕ)^5759*3125000000000^4735 ≤ 1337264981133^4735*39062500^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19438983 39062500 1337264981133 3125000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-73873291/625000000 : ℝ), (2816717097/5000000000 : ℝ), (19438983/39062500 : ℝ)] ![(7448138934247/100000000000000 : ℝ), (9951876330601/20000000000000 : ℝ), (1337264981133/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-73873291/625000000 : ℝ)|^5759 ≤ (7448138934247/100000000000000 : ℝ)^4735
        have hw : |(-73873291/625000000 : ℝ)|=(73873291/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2816717097/5000000000 : ℝ)|^5759 ≤ (9951876330601/20000000000000 : ℝ)^4735
        have hw : |(2816717097/5000000000 : ℝ)|=(2816717097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19438983/39062500 : ℝ)|^5759 ≤ (1337264981133/3125000000000 : ℝ)^4735
        have hw : |(19438983/39062500 : ℝ)|=(19438983/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s0_1 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343241677/2500000000 : ℝ)*x 0 + (-1534634433/10000000000 : ℝ)*x 1 + (1244095011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343241677/2500000000 : ℝ)^5759 ≤ (9395064157109/20000000000000 : ℝ)^4735 := by
    have hnat : (1343241677 : ℕ)^5759*20000000000000^4735 ≤ 9395064157109^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343241677 2500000000 9395064157109 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1534634433/10000000000 : ℝ)^5759 ≤ (2558048916147/25000000000000 : ℝ)^4735 := by
    have hnat : (1534634433 : ℕ)^5759*25000000000000^4735 ≤ 2558048916147^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1534634433 10000000000 2558048916147 25000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1244095011/2500000000 : ℝ)^5759 ≤ (42792483537933/100000000000000 : ℝ)^4735 := by
    have hnat : (1244095011 : ℕ)^5759*100000000000000^4735 ≤ 42792483537933^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244095011 2500000000 42792483537933 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343241677/2500000000 : ℝ), (-1534634433/10000000000 : ℝ), (1244095011/2500000000 : ℝ)] ![(9395064157109/20000000000000 : ℝ), (2558048916147/25000000000000 : ℝ), (42792483537933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343241677/2500000000 : ℝ)|^5759 ≤ (9395064157109/20000000000000 : ℝ)^4735
        have hw : |(1343241677/2500000000 : ℝ)|=(1343241677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1534634433/10000000000 : ℝ)|^5759 ≤ (2558048916147/25000000000000 : ℝ)^4735
        have hw : |(-1534634433/10000000000 : ℝ)|=(1534634433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1244095011/2500000000 : ℝ)|^5759 ≤ (42792483537933/100000000000000 : ℝ)^4735
        have hw : |(1244095011/2500000000 : ℝ)|=(1244095011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s0_2 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372968191/10000000000 : ℝ)*x 0 + (2488189597/5000000000 : ℝ)*x 1 + (-95914599/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372968191/10000000000 : ℝ)^5759 ≤ (46975336555261/100000000000000 : ℝ)^4735 := by
    have hnat : (5372968191 : ℕ)^5759*100000000000000^4735 ≤ 46975336555261^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372968191 10000000000 46975336555261 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2488189597/5000000000 : ℝ)^5759 ≤ (4279247464797/10000000000000 : ℝ)^4735 := by
    have hnat : (2488189597 : ℕ)^5759*10000000000000^4735 ≤ 4279247464797^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2488189597 5000000000 4279247464797 10000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95914599/625000000 : ℝ)^5759 ≤ (10232188779671/100000000000000 : ℝ)^4735 := by
    have hnat : (95914599 : ℕ)^5759*100000000000000^4735 ≤ 10232188779671^4735*625000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95914599 625000000 10232188779671 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372968191/10000000000 : ℝ), (2488189597/5000000000 : ℝ), (-95914599/625000000 : ℝ)] ![(46975336555261/100000000000000 : ℝ), (4279247464797/10000000000000 : ℝ), (10232188779671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372968191/10000000000 : ℝ)|^5759 ≤ (46975336555261/100000000000000 : ℝ)^4735
        have hw : |(5372968191/10000000000 : ℝ)|=(5372968191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2488189597/5000000000 : ℝ)|^5759 ≤ (4279247464797/10000000000000 : ℝ)^4735
        have hw : |(2488189597/5000000000 : ℝ)|=(2488189597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-95914599/625000000 : ℝ)|^5759 ≤ (10232188779671/100000000000000 : ℝ)^4735
        have hw : |(-95914599/625000000 : ℝ)|=(95914599/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s0_3 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1989510473/5000000000 : ℝ)*x 0 + (2982995221/10000000000 : ℝ)*x 1 + (5132992801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989510473/5000000000 : ℝ)^5759 ≤ (16300205657831/50000000000000 : ℝ)^4735 := by
    have hnat : (1989510473 : ℕ)^5759*50000000000000^4735 ≤ 16300205657831^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989510473 5000000000 16300205657831 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2982995221/10000000000 : ℝ)^5759 ≤ (358806216041/1562500000000 : ℝ)^4735 := by
    have hnat : (2982995221 : ℕ)^5759*1562500000000^4735 ≤ 358806216041^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2982995221 10000000000 358806216041 1562500000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5132992801/10000000000 : ℝ)^5759 ≤ (8887198169761/20000000000000 : ℝ)^4735 := by
    have hnat : (5132992801 : ℕ)^5759*20000000000000^4735 ≤ 8887198169761^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132992801 10000000000 8887198169761 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1989510473/5000000000 : ℝ), (2982995221/10000000000 : ℝ), (5132992801/10000000000 : ℝ)] ![(16300205657831/50000000000000 : ℝ), (358806216041/1562500000000 : ℝ), (8887198169761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1989510473/5000000000 : ℝ)|^5759 ≤ (16300205657831/50000000000000 : ℝ)^4735
        have hw : |(1989510473/5000000000 : ℝ)|=(1989510473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2982995221/10000000000 : ℝ)|^5759 ≤ (358806216041/1562500000000 : ℝ)^4735
        have hw : |(2982995221/10000000000 : ℝ)|=(2982995221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5132992801/10000000000 : ℝ)|^5759 ≤ (8887198169761/20000000000000 : ℝ)^4735
        have hw : |(5132992801/10000000000 : ℝ)|=(5132992801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s0_4 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-118335803/1000000000 : ℝ)*x 0 + (156035783/312500000 : ℝ)*x 1 + (1404028073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (118335803/1000000000 : ℝ)^5759 ≤ (932344759717/12500000000000 : ℝ)^4735 := by
    have hnat : (118335803 : ℕ)^5759*12500000000000^4735 ≤ 932344759717^4735*1000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118335803 1000000000 932344759717 12500000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156035783/312500000 : ℝ)^5759 ≤ (42967888936203/100000000000000 : ℝ)^4735 := by
    have hnat : (156035783 : ℕ)^5759*100000000000000^4735 ≤ 42967888936203^4735*312500000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156035783 312500000 42967888936203 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1404028073/2500000000 : ℝ)^5759 ≤ (49573352981333/100000000000000 : ℝ)^4735 := by
    have hnat : (1404028073 : ℕ)^5759*100000000000000^4735 ≤ 49573352981333^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404028073 2500000000 49573352981333 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-118335803/1000000000 : ℝ), (156035783/312500000 : ℝ), (1404028073/2500000000 : ℝ)] ![(932344759717/12500000000000 : ℝ), (42967888936203/100000000000000 : ℝ), (49573352981333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-118335803/1000000000 : ℝ)|^5759 ≤ (932344759717/12500000000000 : ℝ)^4735
        have hw : |(-118335803/1000000000 : ℝ)|=(118335803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156035783/312500000 : ℝ)|^5759 ≤ (42967888936203/100000000000000 : ℝ)^4735
        have hw : |(156035783/312500000 : ℝ)|=(156035783/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1404028073/2500000000 : ℝ)|^5759 ≤ (49573352981333/100000000000000 : ℝ)^4735
        have hw : |(1404028073/2500000000 : ℝ)|=(1404028073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s0_5 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197562719/10000000000 : ℝ)*x 0 + (-44745051/500000000 : ℝ)*x 1 + (5616112397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197562719/10000000000 : ℝ)^5759 ≤ (45116775805897/100000000000000 : ℝ)^4735 := by
    have hnat : (5197562719 : ℕ)^5759*100000000000000^4735 ≤ 45116775805897^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197562719 10000000000 45116775805897 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44745051/500000000 : ℝ)^5759 ≤ (5309870079271/100000000000000 : ℝ)^4735 := by
    have hnat : (44745051 : ℕ)^5759*100000000000000^4735 ≤ 5309870079271^4735*500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44745051 500000000 5309870079271 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5616112397/10000000000 : ℝ)^5759 ≤ (9914670821721/20000000000000 : ℝ)^4735 := by
    have hnat : (5616112397 : ℕ)^5759*20000000000000^4735 ≤ 9914670821721^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5616112397 10000000000 9914670821721 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197562719/10000000000 : ℝ), (-44745051/500000000 : ℝ), (5616112397/10000000000 : ℝ)] ![(45116775805897/100000000000000 : ℝ), (5309870079271/100000000000000 : ℝ), (9914670821721/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197562719/10000000000 : ℝ)|^5759 ≤ (45116775805897/100000000000000 : ℝ)^4735
        have hw : |(5197562719/10000000000 : ℝ)|=(5197562719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44745051/500000000 : ℝ)|^5759 ≤ (5309870079271/100000000000000 : ℝ)^4735
        have hw : |(-44745051/500000000 : ℝ)|=(44745051/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5616112397/10000000000 : ℝ)|^5759 ≤ (9914670821721/20000000000000 : ℝ)^4735
        have hw : |(5616112397/10000000000 : ℝ)|=(5616112397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s0_6 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598781179/5000000000 : ℝ)*x 0 + (2808056191/5000000000 : ℝ)*x 1 + (-894901571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598781179/5000000000 : ℝ)^5759 ≤ (45116771994601/100000000000000 : ℝ)^4735 := by
    have hnat : (2598781179 : ℕ)^5759*100000000000000^4735 ≤ 45116771994601^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598781179 5000000000 45116771994601 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2808056191/5000000000 : ℝ)^5759 ≤ (24786676973783/50000000000000 : ℝ)^4735 := by
    have hnat : (2808056191 : ℕ)^5759*50000000000000^4735 ≤ 24786676973783^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2808056191 5000000000 24786676973783 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (894901571/10000000000 : ℝ)^5759 ≤ (5309874055649/100000000000000 : ℝ)^4735 := by
    have hnat : (894901571 : ℕ)^5759*100000000000000^4735 ≤ 5309874055649^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894901571 10000000000 5309874055649 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598781179/5000000000 : ℝ), (2808056191/5000000000 : ℝ), (-894901571/10000000000 : ℝ)] ![(45116771994601/100000000000000 : ℝ), (24786676973783/50000000000000 : ℝ), (5309874055649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598781179/5000000000 : ℝ)|^5759 ≤ (45116771994601/100000000000000 : ℝ)^4735
        have hw : |(2598781179/5000000000 : ℝ)|=(2598781179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2808056191/5000000000 : ℝ)|^5759 ≤ (24786676973783/50000000000000 : ℝ)^4735
        have hw : |(2808056191/5000000000 : ℝ)|=(2808056191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-894901571/10000000000 : ℝ)|^5759 ≤ (5309874055649/100000000000000 : ℝ)^4735
        have hw : |(-894901571/10000000000 : ℝ)|=(894901571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s0_7 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (796710929/2000000000 : ℝ)*x 0 + (2539066157/5000000000 : ℝ)*x 1 + (94989849/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (796710929/2000000000 : ℝ)^5759 ≤ (16322797420901/50000000000000 : ℝ)^4735 := by
    have hnat : (796710929 : ℕ)^5759*50000000000000^4735 ≤ 16322797420901^4735*2000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796710929 2000000000 16322797420901 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2539066157/5000000000 : ℝ)^5759 ≤ (43859028649943/100000000000000 : ℝ)^4735 := by
    have hnat : (2539066157 : ℕ)^5759*100000000000000^4735 ≤ 43859028649943^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539066157 5000000000 43859028649943 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94989849/312500000 : ℝ)^5759 ≤ (4699075297799/20000000000000 : ℝ)^4735 := by
    have hnat : (94989849 : ℕ)^5759*20000000000000^4735 ≤ 4699075297799^4735*312500000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94989849 312500000 4699075297799 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(796710929/2000000000 : ℝ), (2539066157/5000000000 : ℝ), (94989849/312500000 : ℝ)] ![(16322797420901/50000000000000 : ℝ), (43859028649943/100000000000000 : ℝ), (4699075297799/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(796710929/2000000000 : ℝ)|^5759 ≤ (16322797420901/50000000000000 : ℝ)^4735
        have hw : |(796710929/2000000000 : ℝ)|=(796710929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2539066157/5000000000 : ℝ)|^5759 ≤ (43859028649943/100000000000000 : ℝ)^4735
        have hw : |(2539066157/5000000000 : ℝ)|=(2539066157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(94989849/312500000 : ℝ)|^5759 ≤ (4699075297799/20000000000000 : ℝ)^4735
        have hw : |(94989849/312500000 : ℝ)|=(94989849/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1749_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1337/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5221/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5743/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5743 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5743*1^1024 ≤ 0^1024*1^5743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5743/1024 : ℝ) ≤ (586399885921194481/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5743 ≤ (586399885921194481/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5743*100000000000000000000^1024 ≤ 586399885921194481^1024*5^5743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 586399885921194481 100000000000000000000 5743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (586399885921194481/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5743 := by
      have hnat : (1 : ℕ)^1024*1^5743 ≤ 1^5743*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100586399885921194481/100000000000000000000 : ℝ) ≤ (10010430645050877/10000000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (100586399885921194481/100000000000000000000 : ℝ)^1024 ≤ (10010430645050877/10000000000000000 : ℝ)^5743 := by
      have hnat : (100586399885921194481 : ℕ)^1024*10000000000000000^5743 ≤ 10010430645050877^5743*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100586399885921194481 100000000000000000000 10010430645050877 10000000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010430645050877/10000000000000000 : ℝ)) (X := (100586399885921194481/100000000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50586399885921194481/50000000000000000000 : ℝ) ≤ (5010430645050877/5000000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (50586399885921194481/50000000000000000000 : ℝ)^1024 ≤ (5010430645050877/5000000000000000 : ℝ)^5743 := by
      have hnat : (50586399885921194481 : ℕ)^1024*5000000000000000^5743 ≤ 5010430645050877^5743*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50586399885921194481 50000000000000000000 5010430645050877 5000000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010430645050877/5000000000000000 : ℝ)) (X := (50586399885921194481/50000000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(10430645050877/4000000000000000 : ℝ)*(0 : ℝ))^(5743/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10430645050877/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(586399885921194481/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(10430645050877/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5743/1024 : ℝ) := by
    rw [show (1 : ℝ)+(10430645050877/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10010430645050877/10000000000000000 : ℝ) by norm_num, show 1+(586399885921194481/100000000000000000000 : ℝ)+(0 : ℝ)=(100586399885921194481/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(586399885921194481/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(10430645050877/4000000000000000 : ℝ)*(2/5 : ℝ))^(5743/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10430645050877/4000000000000000 : ℝ)*(2/5 : ℝ)=(5010430645050877/5000000000000000 : ℝ) by norm_num, show 1+2*(586399885921194481/100000000000000000000 : ℝ)=(50586399885921194481/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(10430645050877/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10430645050877/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(10430645050877/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10430645050877/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(10430645050877/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10430645050877/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-73873291/625000000 : ℝ)*X 0 0+(2816717097/5000000000 : ℝ)*X 0 1+(19438983/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1343241677/2500000000 : ℝ)*X 1 0+(-1534634433/10000000000 : ℝ)*X 1 1+(1244095011/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5372968191/10000000000 : ℝ)*X 2 0+(2488189597/5000000000 : ℝ)*X 2 1+(-95914599/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1989510473/5000000000 : ℝ)*X 0 0+(2982995221/10000000000 : ℝ)*X 0 1+(5132992801/10000000000 : ℝ)*X 0 2+(1989510473/5000000000 : ℝ)*X 1 0+(2982995221/10000000000 : ℝ)*X 1 1+(5132992801/10000000000 : ℝ)*X 1 2+(1989510473/5000000000 : ℝ)*X 2 0+(2982995221/10000000000 : ℝ)*X 2 1+(5132992801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-118335803/1000000000 : ℝ)*X 0 0+(156035783/312500000 : ℝ)*X 0 1+(1404028073/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5197562719/10000000000 : ℝ)*X 1 0+(-44745051/500000000 : ℝ)*X 1 1+(5616112397/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2598781179/5000000000 : ℝ)*X 2 0+(2808056191/5000000000 : ℝ)*X 2 1+(-894901571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((796710929/2000000000 : ℝ)*X 0 0+(2539066157/5000000000 : ℝ)*X 0 1+(94989849/312500000 : ℝ)*X 0 2+(796710929/2000000000 : ℝ)*X 1 0+(2539066157/5000000000 : ℝ)*X 1 1+(94989849/312500000 : ℝ)*X 1 2+(796710929/2000000000 : ℝ)*X 2 0+(2539066157/5000000000 : ℝ)*X 2 1+(94989849/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2211357487232251419/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73643817/20000000000000 : ℝ)*(base19) + (150295709/25000000000000 : ℝ)*(base23) + (70790063/100000000000000 : ℝ)*(base24) + (31249461/50000000000000 : ℝ)*(upper4) + (34365303/25000000000000 : ℝ)*(upper5) + (496766745609089/50000000000000 : ℝ)*(major0) + (496766745609089/50000000000000 : ℝ)*(major1) + (496766745609089/50000000000000 : ℝ)*(major2) + (1521944477936463/100000000000000 : ℝ)*(sp0) + (1521947943325517/100000000000000 : ℝ)*(sp1) + (1521947639571703/100000000000000 : ℝ)*(sp2) + (465117753402897/100000000000000 : ℝ)*(sp3) + (1916804069/50000000000000 : ℝ)*(sp4) + (843776937/100000000000000 : ℝ)*(sp7) + (232559298589917/50000000000000 : ℝ)*(f.failure) + (1521948311544601/100000000000000 : ℝ)*(f.sum) + (94481147278947/100000000000000000000000000000 : ℝ)*base66 + (128672957621053/200000000000000000000000000000 : ℝ)*base67 + (452472312021053/200000000000000000000000000000 : ℝ)*base69 + (345789433978947/200000000000000000000000000000 : ℝ)*base72 + (26801699221053/100000000000000000000000000000 : ℝ)*base73 + (1497816773578947/200000000000000000000000000000 : ℝ)*base76 + (232751681378947/200000000000000000000000000000 : ℝ)*base78 + (623460208778947/200000000000000000000000000000 : ℝ)*base80 + (369481622521053/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1569197/1250000000000000000000 : ℝ)*base90 + (1569197/1250000000000000000000 : ℝ)*base92 + (1569197/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1042406014934139955461591/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1090995141/50000000000000 : ℝ)*(base19) + (1024930239/50000000000000 : ℝ)*(base23) + (8520289/100000000000000 : ℝ)*(upper2) + (186061271/50000000000000 : ℝ)*(upper3) + (166391601/50000000000000 : ℝ)*(upper5) + (1047893777048161/100000000000000 : ℝ)*(major0) + (1047893777048161/100000000000000 : ℝ)*(major1) + (1047893777048161/100000000000000 : ℝ)*(major2) + (4699561319/50000000000000 : ℝ)*(sp1) + (4150863899/50000000000000 : ℝ)*(sp2) + (321044013266547/20000000000000 : ℝ)*(sp4) + (200651060652477/12500000000000 : ℝ)*(sp5) + (1605209714744459/100000000000000 : ℝ)*(sp6) + (490567140294909/100000000000000 : ℝ)*(sp7) + (490567140294909/100000000000000 : ℝ)*(f.failure) + (321044013266547/20000000000000 : ℝ)*(f.sum) + (1153549326712803/200000000000000000000000000000 : ℝ)*base66 + (3127469689887197/400000000000000000000000000000 : ℝ)*base67 + (2784850608512803/400000000000000000000000000000 : ℝ)*base70 + (2977642360912803/400000000000000000000000000000 : ℝ)*base72 + (135912153887197/200000000000000000000000000000 : ℝ)*base73 + (2130457170112803/400000000000000000000000000000 : ℝ)*base76 + (3032511293712803/400000000000000000000000000000 : ℝ)*base78 + (1304182493887197/400000000000000000000000000000 : ℝ)*base79 + (757872593912803/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (12308531/2500000000000000000000 : ℝ)*base89 + (12308531/2500000000000000000000 : ℝ)*base91 + (12308531/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1749_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1337/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5221/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1749_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1749_s1_0 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-613333381/5000000000 : ℝ)*x 0 + (5501855899/10000000000 : ℝ)*x 1 + (507808309/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (613333381/5000000000 : ℝ)^5759 ≤ (7792070960059/100000000000000 : ℝ)^4735 := by
    have hnat : (613333381 : ℕ)^5759*100000000000000^4735 ≤ 7792070960059^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613333381 5000000000 7792070960059 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5501855899/10000000000 : ℝ)^5759 ≤ (755459647699/1562500000000 : ℝ)^4735 := by
    have hnat : (5501855899 : ℕ)^5759*1562500000000^4735 ≤ 755459647699^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501855899 10000000000 755459647699 1562500000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (507808309/1000000000 : ℝ)^5759 ≤ (43858511568993/100000000000000 : ℝ)^4735 := by
    have hnat : (507808309 : ℕ)^5759*100000000000000^4735 ≤ 43858511568993^4735*1000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507808309 1000000000 43858511568993 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-613333381/5000000000 : ℝ), (5501855899/10000000000 : ℝ), (507808309/1000000000 : ℝ)] ![(7792070960059/100000000000000 : ℝ), (755459647699/1562500000000 : ℝ), (43858511568993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-613333381/5000000000 : ℝ)|^5759 ≤ (7792070960059/100000000000000 : ℝ)^4735
        have hw : |(-613333381/5000000000 : ℝ)|=(613333381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5501855899/10000000000 : ℝ)|^5759 ≤ (755459647699/1562500000000 : ℝ)^4735
        have hw : |(5501855899/10000000000 : ℝ)|=(5501855899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(507808309/1000000000 : ℝ)|^5759 ≤ (43858511568993/100000000000000 : ℝ)^4735
        have hw : |(507808309/1000000000 : ℝ)|=(507808309/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s1_1 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (667243769/1250000000 : ℝ)*x 0 + (-724266381/5000000000 : ℝ)*x 1 + (1269520773/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667243769/1250000000 : ℝ)^5759 ≤ (9320645908739/20000000000000 : ℝ)^4735 := by
    have hnat : (667243769 : ℕ)^5759*20000000000000^4735 ≤ 9320645908739^4735*1250000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667243769 1250000000 9320645908739 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (724266381/5000000000 : ℝ)^5759 ≤ (1192282355999/12500000000000 : ℝ)^4735 := by
    have hnat : (724266381 : ℕ)^5759*12500000000000^4735 ≤ 1192282355999^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      724266381 5000000000 1192282355999 12500000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1269520773/2500000000 : ℝ)^5759 ≤ (21929255795001/50000000000000 : ℝ)^4735 := by
    have hnat : (1269520773 : ℕ)^5759*50000000000000^4735 ≤ 21929255795001^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269520773 2500000000 21929255795001 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(667243769/1250000000 : ℝ), (-724266381/5000000000 : ℝ), (1269520773/2500000000 : ℝ)] ![(9320645908739/20000000000000 : ℝ), (1192282355999/12500000000000 : ℝ), (21929255795001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(667243769/1250000000 : ℝ)|^5759 ≤ (9320645908739/20000000000000 : ℝ)^4735
        have hw : |(667243769/1250000000 : ℝ)|=(667243769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-724266381/5000000000 : ℝ)|^5759 ≤ (1192282355999/12500000000000 : ℝ)^4735
        have hw : |(-724266381/5000000000 : ℝ)|=(724266381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1269520773/2500000000 : ℝ)|^5759 ≤ (21929255795001/50000000000000 : ℝ)^4735
        have hw : |(1269520773/2500000000 : ℝ)|=(1269520773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s1_2 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067589981/2000000000 : ℝ)*x 0 + (634760411/1250000000 : ℝ)*x 1 + (-724266417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067589981/2000000000 : ℝ)^5759 ≤ (46603226920893/100000000000000 : ℝ)^4735 := by
    have hnat : (1067589981 : ℕ)^5759*100000000000000^4735 ≤ 46603226920893^4735*2000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067589981 2000000000 46603226920893 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (634760411/1250000000 : ℝ)^5759 ≤ (43858513648911/100000000000000 : ℝ)^4735 := by
    have hnat : (634760411 : ℕ)^5759*100000000000000^4735 ≤ 43858513648911^4735*1250000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634760411 1250000000 43858513648911 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (724266417/5000000000 : ℝ)^5759 ≤ (9538259424627/100000000000000 : ℝ)^4735 := by
    have hnat : (724266417 : ℕ)^5759*100000000000000^4735 ≤ 9538259424627^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      724266417 5000000000 9538259424627 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067589981/2000000000 : ℝ), (634760411/1250000000 : ℝ), (-724266417/5000000000 : ℝ)] ![(46603226920893/100000000000000 : ℝ), (43858513648911/100000000000000 : ℝ), (9538259424627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067589981/2000000000 : ℝ)|^5759 ≤ (46603226920893/100000000000000 : ℝ)^4735
        have hw : |(1067589981/2000000000 : ℝ)|=(1067589981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(634760411/1250000000 : ℝ)|^5759 ≤ (43858513648911/100000000000000 : ℝ)^4735
        have hw : |(634760411/1250000000 : ℝ)|=(634760411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-724266417/5000000000 : ℝ)|^5759 ≤ (9538259424627/100000000000000 : ℝ)^4735
        have hw : |(-724266417/5000000000 : ℝ)|=(724266417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s1_3 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (502758753/1250000000 : ℝ)*x 0 + (210087343/625000000 : ℝ)*x 1 + (2374026851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502758753/1250000000 : ℝ)^5759 ≤ (8257473126349/25000000000000 : ℝ)^4735 := by
    have hnat : (502758753 : ℕ)^5759*25000000000000^4735 ≤ 8257473126349^4735*1250000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502758753 1250000000 8257473126349 25000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210087343/625000000 : ℝ)^5759 ≤ (26553646452629/100000000000000 : ℝ)^4735 := by
    have hnat : (210087343 : ℕ)^5759*100000000000000^4735 ≤ 26553646452629^4735*625000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210087343 625000000 26553646452629 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2374026851/5000000000 : ℝ)^5759 ≤ (20208230509411/50000000000000 : ℝ)^4735 := by
    have hnat : (2374026851 : ℕ)^5759*50000000000000^4735 ≤ 20208230509411^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2374026851 5000000000 20208230509411 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(502758753/1250000000 : ℝ), (210087343/625000000 : ℝ), (2374026851/5000000000 : ℝ)] ![(8257473126349/25000000000000 : ℝ), (26553646452629/100000000000000 : ℝ), (20208230509411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(502758753/1250000000 : ℝ)|^5759 ≤ (8257473126349/25000000000000 : ℝ)^4735
        have hw : |(502758753/1250000000 : ℝ)|=(502758753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210087343/625000000 : ℝ)|^5759 ≤ (26553646452629/100000000000000 : ℝ)^4735
        have hw : |(210087343/625000000 : ℝ)|=(210087343/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2374026851/5000000000 : ℝ)|^5759 ≤ (20208230509411/50000000000000 : ℝ)^4735
        have hw : |(2374026851/5000000000 : ℝ)|=(2374026851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s1_4 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-613517743/5000000000 : ℝ)*x 0 + (5085067911/10000000000 : ℝ)*x 1 + (5494722549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (613517743/5000000000 : ℝ)^5759 ≤ (1948729951423/25000000000000 : ℝ)^4735 := by
    have hnat : (613517743 : ℕ)^5759*25000000000000^4735 ≤ 1948729951423^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613517743 5000000000 1948729951423 25000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5085067911/10000000000 : ℝ)^5759 ≤ (21965947754709/50000000000000 : ℝ)^4735 := by
    have hnat : (5085067911 : ℕ)^5759*50000000000000^4735 ≤ 21965947754709^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085067911 10000000000 21965947754709 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5494722549/10000000000 : ℝ)^5759 ≤ (9654636934751/20000000000000 : ℝ)^4735 := by
    have hnat : (5494722549 : ℕ)^5759*20000000000000^4735 ≤ 9654636934751^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494722549 10000000000 9654636934751 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-613517743/5000000000 : ℝ), (5085067911/10000000000 : ℝ), (5494722549/10000000000 : ℝ)] ![(1948729951423/25000000000000 : ℝ), (21965947754709/50000000000000 : ℝ), (9654636934751/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-613517743/5000000000 : ℝ)|^5759 ≤ (1948729951423/25000000000000 : ℝ)^4735
        have hw : |(-613517743/5000000000 : ℝ)|=(613517743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5085067911/10000000000 : ℝ)|^5759 ≤ (21965947754709/50000000000000 : ℝ)^4735
        have hw : |(5085067911/10000000000 : ℝ)|=(5085067911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5494722549/10000000000 : ℝ)|^5759 ≤ (9654636934751/20000000000000 : ℝ)^4735
        have hw : |(5494722549/10000000000 : ℝ)|=(5494722549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s1_5 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225563609/10000000000 : ℝ)*x 0 + (-515946527/5000000000 : ℝ)*x 1 + (1373680627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225563609/10000000000 : ℝ)^5759 ≤ (45412570112877/100000000000000 : ℝ)^4735 := by
    have hnat : (5225563609 : ℕ)^5759*100000000000000^4735 ≤ 45412570112877^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225563609 10000000000 45412570112877 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515946527/5000000000 : ℝ)^5759 ≤ (6314245638981/100000000000000 : ℝ)^4735 := by
    have hnat : (515946527 : ℕ)^5759*100000000000000^4735 ≤ 6314245638981^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515946527 5000000000 6314245638981 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1373680627/2500000000 : ℝ)^5759 ≤ (48273184235657/100000000000000 : ℝ)^4735 := by
    have hnat : (1373680627 : ℕ)^5759*100000000000000^4735 ≤ 48273184235657^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373680627 2500000000 48273184235657 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225563609/10000000000 : ℝ), (-515946527/5000000000 : ℝ), (1373680627/2500000000 : ℝ)] ![(45412570112877/100000000000000 : ℝ), (6314245638981/100000000000000 : ℝ), (48273184235657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225563609/10000000000 : ℝ)|^5759 ≤ (45412570112877/100000000000000 : ℝ)^4735
        have hw : |(5225563609/10000000000 : ℝ)|=(5225563609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-515946527/5000000000 : ℝ)|^5759 ≤ (6314245638981/100000000000000 : ℝ)^4735
        have hw : |(-515946527/5000000000 : ℝ)|=(515946527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1373680627/2500000000 : ℝ)|^5759 ≤ (48273184235657/100000000000000 : ℝ)^4735
        have hw : |(1373680627/2500000000 : ℝ)|=(1373680627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s1_6 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612781533/5000000000 : ℝ)*x 0 + (219788923/400000000 : ℝ)*x 1 + (-103189301/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612781533/5000000000 : ℝ)^5759 ≤ (5676570546679/12500000000000 : ℝ)^4735 := by
    have hnat : (2612781533 : ℕ)^5759*12500000000000^4735 ≤ 5676570546679^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612781533 5000000000 5676570546679 12500000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219788923/400000000 : ℝ)^5759 ≤ (4827319029423/10000000000000 : ℝ)^4735 := by
    have hnat : (219788923 : ℕ)^5759*10000000000000^4735 ≤ 4827319029423^4735*400000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219788923 400000000 4827319029423 10000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103189301/1000000000 : ℝ)^5759 ≤ (1262849062303/20000000000000 : ℝ)^4735 := by
    have hnat : (103189301 : ℕ)^5759*20000000000000^4735 ≤ 1262849062303^4735*1000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103189301 1000000000 1262849062303 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612781533/5000000000 : ℝ), (219788923/400000000 : ℝ), (-103189301/1000000000 : ℝ)] ![(5676570546679/12500000000000 : ℝ), (4827319029423/10000000000000 : ℝ), (1262849062303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612781533/5000000000 : ℝ)|^5759 ≤ (5676570546679/12500000000000 : ℝ)^4735
        have hw : |(2612781533/5000000000 : ℝ)|=(2612781533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219788923/400000000 : ℝ)|^5759 ≤ (4827319029423/10000000000000 : ℝ)^4735
        have hw : |(219788923/400000000 : ℝ)|=(219788923/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103189301/1000000000 : ℝ)|^5759 ≤ (1262849062303/20000000000000 : ℝ)^4735
        have hw : |(-103189301/1000000000 : ℝ)|=(103189301/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s1_7 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4023277079/10000000000 : ℝ)*x 0 + (2362600887/5000000000 : ℝ)*x 1 + (3384736457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4023277079/10000000000 : ℝ)^5759 ≤ (264335593049/800000000000 : ℝ)^4735 := by
    have hnat : (4023277079 : ℕ)^5759*800000000000^4735 ≤ 264335593049^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023277079 10000000000 264335593049 800000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2362600887/5000000000 : ℝ)^5759 ≤ (40179996360047/100000000000000 : ℝ)^4735 := by
    have hnat : (2362600887 : ℕ)^5759*100000000000000^4735 ≤ 40179996360047^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2362600887 5000000000 40179996360047 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3384736457/10000000000 : ℝ)^5759 ≤ (6694513622453/25000000000000 : ℝ)^4735 := by
    have hnat : (3384736457 : ℕ)^5759*25000000000000^4735 ≤ 6694513622453^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3384736457 10000000000 6694513622453 25000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4023277079/10000000000 : ℝ), (2362600887/5000000000 : ℝ), (3384736457/10000000000 : ℝ)] ![(264335593049/800000000000 : ℝ), (40179996360047/100000000000000 : ℝ), (6694513622453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4023277079/10000000000 : ℝ)|^5759 ≤ (264335593049/800000000000 : ℝ)^4735
        have hw : |(4023277079/10000000000 : ℝ)|=(4023277079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2362600887/5000000000 : ℝ)|^5759 ≤ (40179996360047/100000000000000 : ℝ)^4735
        have hw : |(2362600887/5000000000 : ℝ)|=(2362600887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3384736457/10000000000 : ℝ)|^5759 ≤ (6694513622453/25000000000000 : ℝ)^4735
        have hw : |(3384736457/10000000000 : ℝ)|=(3384736457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1749_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5221/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1337/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (8967/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18069/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5221/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1337/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5221/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1337/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5221/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1337/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5221/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1337/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5221/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1337/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5221/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1337/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1337/20000 : ℝ) ^ (5743/1024 : ℝ) ≤ (25745456248351/100000000000000000000 : ℝ) := by
    have hpowers : (1337/20000 : ℝ)^5743 ≤ (25745456248351/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1337 : ℕ)^5743*100000000000000000000^1024 ≤ 25745456248351^1024*20000^5743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1337 20000 25745456248351 100000000000000000000 5743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1337/20000 : ℝ)) (X := (25745456248351/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5221/25000 : ℝ) ^ (5743/1024 : ℝ) ≤ (7659741890309813/50000000000000000000 : ℝ) := by
    have hpowers : (5221/25000 : ℝ)^5743 ≤ (7659741890309813/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5221 : ℕ)^5743*50000000000000000000^1024 ≤ 7659741890309813^1024*25000^5743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5221 25000 7659741890309813 50000000000000000000 5743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5221/25000 : ℝ)) (X := (7659741890309813/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000025745456248351/50000000000000000000 : ℝ) ≤ (10000000918103487/10000000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (50000025745456248351/50000000000000000000 : ℝ)^1024 ≤ (10000000918103487/10000000000000000 : ℝ)^5743 := by
      have hnat : (50000025745456248351 : ℕ)^1024*10000000000000000^5743 ≤ 10000000918103487^5743*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000025745456248351 50000000000000000000 10000000918103487 10000000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000918103487/10000000000000000 : ℝ)) (X := (50000025745456248351/50000000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100015345229236867977/100000000000000000000 : ℝ) ≤ (2000054718872239/2000000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (100015345229236867977/100000000000000000000 : ℝ)^1024 ≤ (2000054718872239/2000000000000000 : ℝ)^5743 := by
      have hnat : (100015345229236867977 : ℕ)^1024*2000000000000000^5743 ≤ 2000054718872239^5743*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100015345229236867977 100000000000000000000 2000054718872239 2000000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000054718872239/2000000000000000 : ℝ)) (X := (100015345229236867977/100000000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25007659741890309813/25000000000000000000 : ℝ) ≤ (10000546270618903/10000000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (25007659741890309813/25000000000000000000 : ℝ)^1024 ≤ (10000546270618903/10000000000000000 : ℝ)^5743 := by
      have hnat : (25007659741890309813 : ℕ)^1024*10000000000000000^5743 ≤ 10000546270618903^5743*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007659741890309813 25000000000000000000 10000546270618903 10000000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000546270618903/10000000000000000 : ℝ)) (X := (25007659741890309813/25000000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(25745456248351/100000000000000000000 : ℝ) ≤ ((141986367354585855953/141990000000000000000 : ℝ)+2*(68169064427/354975000000000 : ℝ)*(1337/20000 : ℝ))^(5743/1024 : ℝ) := by
    rw [show (141986367354585855953/141990000000000000000 : ℝ)+2*(68169064427/354975000000000 : ℝ)*(1337/20000 : ℝ)=(10000000918103487/10000000000000000 : ℝ) by norm_num, show 1+2*(25745456248351/100000000000000000000 : ℝ)=(50000025745456248351/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7659741890309813/50000000000000000000 : ℝ)+(25745456248351/100000000000000000000 : ℝ) ≤ ((141986367354585855953/141990000000000000000 : ℝ)+(68169064427/354975000000000 : ℝ)*((5221/25000 : ℝ)+(1337/20000 : ℝ)))^(5743/1024 : ℝ) := by
    rw [show (141986367354585855953/141990000000000000000 : ℝ)+(68169064427/354975000000000 : ℝ)*((5221/25000 : ℝ)+(1337/20000 : ℝ))=(2000054718872239/2000000000000000 : ℝ) by norm_num, show 1+(7659741890309813/50000000000000000000 : ℝ)+(25745456248351/100000000000000000000 : ℝ)=(100015345229236867977/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7659741890309813/50000000000000000000 : ℝ) ≤ ((141986367354585855953/141990000000000000000 : ℝ)+2*(68169064427/354975000000000 : ℝ)*(5221/25000 : ℝ))^(5743/1024 : ℝ) := by
    rw [show (141986367354585855953/141990000000000000000 : ℝ)+2*(68169064427/354975000000000 : ℝ)*(5221/25000 : ℝ)=(10000546270618903/10000000000000000 : ℝ) by norm_num, show 1+2*(7659741890309813/50000000000000000000 : ℝ)=(25007659741890309813/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (141986367354585855953/141990000000000000000 : ℝ)*(X 1 0+X 2 0)+(68169064427/354975000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (1337/20000 : ℝ)) (hi := (5221/25000 : ℝ)) (c := (141986367354585855953/141990000000000000000 : ℝ)) (alpha := (68169064427/354975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (141986367354585855953/141990000000000000000 : ℝ)*(X 0 1+X 2 1)+(68169064427/354975000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (1337/20000 : ℝ)) (hi := (5221/25000 : ℝ)) (c := (141986367354585855953/141990000000000000000 : ℝ)) (alpha := (68169064427/354975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (141986367354585855953/141990000000000000000 : ℝ)*(X 0 2+X 1 2)+(68169064427/354975000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (1337/20000 : ℝ)) (hi := (5221/25000 : ℝ)) (c := (141986367354585855953/141990000000000000000 : ℝ)) (alpha := (68169064427/354975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-613333381/5000000000 : ℝ)*X 0 0+(5501855899/10000000000 : ℝ)*X 0 1+(507808309/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((667243769/1250000000 : ℝ)*X 1 0+(-724266381/5000000000 : ℝ)*X 1 1+(1269520773/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1067589981/2000000000 : ℝ)*X 2 0+(634760411/1250000000 : ℝ)*X 2 1+(-724266417/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((502758753/1250000000 : ℝ)*X 0 0+(210087343/625000000 : ℝ)*X 0 1+(2374026851/5000000000 : ℝ)*X 0 2+(502758753/1250000000 : ℝ)*X 1 0+(210087343/625000000 : ℝ)*X 1 1+(2374026851/5000000000 : ℝ)*X 1 2+(502758753/1250000000 : ℝ)*X 2 0+(210087343/625000000 : ℝ)*X 2 1+(2374026851/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-613517743/5000000000 : ℝ)*X 0 0+(5085067911/10000000000 : ℝ)*X 0 1+(5494722549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5225563609/10000000000 : ℝ)*X 1 0+(-515946527/5000000000 : ℝ)*X 1 1+(1373680627/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2612781533/5000000000 : ℝ)*X 2 0+(219788923/400000000 : ℝ)*X 2 1+(-103189301/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4023277079/10000000000 : ℝ)*X 0 0+(2362600887/5000000000 : ℝ)*X 0 1+(3384736457/10000000000 : ℝ)*X 0 2+(4023277079/10000000000 : ℝ)*X 1 0+(2362600887/5000000000 : ℝ)*X 1 1+(3384736457/10000000000 : ℝ)*X 1 2+(4023277079/10000000000 : ℝ)*X 2 0+(2362600887/5000000000 : ℝ)*X 2 1+(3384736457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7715750854987056326911300313/2366500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (250171711/50000000000000 : ℝ)*(base19) + (329881273/100000000000000 : ℝ)*(base23) + (16352849/50000000000000 : ℝ)*(lower2) + (24615097/25000000000000 : ℝ)*(upper3) + (119019/12500000000000 : ℝ)*(upper5) + (1540462278536707/100000000000000 : ℝ)*(major0) + (1540462278536707/100000000000000 : ℝ)*(major1) + (1540462278536707/100000000000000 : ℝ)*(major2) + (294969980159149/12500000000000 : ℝ)*(sp0) + (23597628997967/1000000000000 : ℝ)*(sp1) + (73742595945589/3125000000000 : ℝ)*(sp2) + (721159945583373/100000000000000 : ℝ)*(sp3) + (3558866929/100000000000000 : ℝ)*(sp4) + (275667427/25000000000000 : ℝ)*(sp7) + (18029026206327/2500000000000 : ℝ)*(f.failure) + (1179881700070061/50000000000000 : ℝ)*(f.sum) + (76051193591507/35497500000000000000000000000 : ℝ)*base66 + (62063892065976433229/14199000000000000000000000000000000 : ℝ)*base68 + (6316385415216433229/14199000000000000000000000000000000 : ℝ)*base70 + (147729701279835433229/14199000000000000000000000000000000 : ℝ)*base72 + (12604000582591/17748750000000000000000000000 : ℝ)*base74 + (126655623829917433229/14199000000000000000000000000000000 : ℝ)*base76 + (12454565136795433229/14199000000000000000000000000000000 : ℝ)*base78 + (70727515526079433229/14199000000000000000000000000000000 : ℝ)*base80 + (2214436874203/35497500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (615007/62500000000000000000 : ℝ)*base90 + (615007/62500000000000000000 : ℝ)*base92 + (615007/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5323901562355578378304332021/473300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (718770783/50000000000000 : ℝ)*(base19) + (1488596641/100000000000000 : ℝ)*(base23) + (10012079/3125000000000 : ℝ)*(upper3) + (105316427/100000000000000 : ℝ)*(lower4) + (15247043/50000000000000 : ℝ)*(upper5) + (318708525754043/20000000000000 : ℝ)*(major0) + (318708525754043/20000000000000 : ℝ)*(major1) + (318708525754043/20000000000000 : ℝ)*(major2) + (1903669099/25000000000000 : ℝ)*(sp1) + (3102936881/25000000000000 : ℝ)*(sp2) + (1220537243891073/50000000000000 : ℝ)*(sp4) + (305133179445523/12500000000000 : ℝ)*(sp5) + (2441060587437981/100000000000000 : ℝ)*(sp6) + (46625649675577/6250000000000 : ℝ)*(sp7) + (46625649675577/6250000000000 : ℝ)*(f.failure) + (1220537243891073/50000000000000 : ℝ)*(f.sum) + (2349369698927/1774875000000000000000000000 : ℝ)*base65 + (15685406802004567979/2839800000000000000000000000000000 : ℝ)*base67 + (244316323965367979/2839800000000000000000000000000000 : ℝ)*base69 + (7477558414524967979/2839800000000000000000000000000000 : ℝ)*base71 + (9458409232831/3549750000000000000000000000 : ℝ)*base73 + (1052733218084632021/2839800000000000000000000000000000 : ℝ)*base76 + (3727732144051432021/2839800000000000000000000000000000 : ℝ)*base78 + (5324187830660767979/2839800000000000000000000000000000 : ℝ)*base79 + (3182798471479/7099500000000000000000000000 : ℝ)*base82 + (433243/156250000000000000000 : ℝ)*base89 + (433243/156250000000000000000 : ℝ)*base91 + (433243/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1749_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5221/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1337/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8967/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18069/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1749_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1749_s2_0 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-613868597/5000000000 : ℝ)*x 0 + (1099684929/2000000000 : ℝ)*x 1 + (508078659/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (613868597/5000000000 : ℝ)^5759 ≤ (312013674919/4000000000000 : ℝ)^4735 := by
    have hnat : (613868597 : ℕ)^5759*4000000000000^4735 ≤ 312013674919^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613868597 5000000000 312013674919 4000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099684929/2000000000 : ℝ)^5759 ≤ (1207818640311/2500000000000 : ℝ)^4735 := by
    have hnat : (1099684929 : ℕ)^5759*2500000000000^4735 ≤ 1207818640311^4735*2000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099684929 2000000000 1207818640311 2500000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508078659/1000000000 : ℝ)^5759 ≤ (21943456249197/50000000000000 : ℝ)^4735 := by
    have hnat : (508078659 : ℕ)^5759*50000000000000^4735 ≤ 21943456249197^4735*1000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508078659 1000000000 21943456249197 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-613868597/5000000000 : ℝ), (1099684929/2000000000 : ℝ), (508078659/1000000000 : ℝ)] ![(312013674919/4000000000000 : ℝ), (1207818640311/2500000000000 : ℝ), (21943456249197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-613868597/5000000000 : ℝ)|^5759 ≤ (312013674919/4000000000000 : ℝ)^4735
        have hw : |(-613868597/5000000000 : ℝ)|=(613868597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099684929/2000000000 : ℝ)|^5759 ≤ (1207818640311/2500000000000 : ℝ)^4735
        have hw : |(1099684929/2000000000 : ℝ)|=(1099684929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(508078659/1000000000 : ℝ)|^5759 ≤ (21943456249197/50000000000000 : ℝ)^4735
        have hw : |(508078659/1000000000 : ℝ)|=(508078659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s2_1 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20847653/39062500 : ℝ)*x 0 + (-36156171/250000000 : ℝ)*x 1 + (5080786727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20847653/39062500 : ℝ)^5759 ≤ (46593131588521/100000000000000 : ℝ)^4735 := by
    have hnat : (20847653 : ℕ)^5759*100000000000000^4735 ≤ 46593131588521^4735*39062500^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20847653 39062500 46593131588521 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36156171/250000000 : ℝ)^5759 ≤ (9519954463107/100000000000000 : ℝ)^4735 := by
    have hnat : (36156171 : ℕ)^5759*100000000000000^4735 ≤ 9519954463107^4735*250000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36156171 250000000 9519954463107 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5080786727/10000000000 : ℝ)^5759 ≤ (8777382787539/20000000000000 : ℝ)^4735 := by
    have hnat : (5080786727 : ℕ)^5759*20000000000000^4735 ≤ 8777382787539^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080786727 10000000000 8777382787539 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20847653/39062500 : ℝ), (-36156171/250000000 : ℝ), (5080786727/10000000000 : ℝ)] ![(46593131588521/100000000000000 : ℝ), (9519954463107/100000000000000 : ℝ), (8777382787539/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20847653/39062500 : ℝ)|^5759 ≤ (46593131588521/100000000000000 : ℝ)^4735
        have hw : |(20847653/39062500 : ℝ)|=(20847653/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36156171/250000000 : ℝ)|^5759 ≤ (9519954463107/100000000000000 : ℝ)^4735
        have hw : |(-36156171/250000000 : ℝ)|=(36156171/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5080786727/10000000000 : ℝ)|^5759 ≤ (8777382787539/20000000000000 : ℝ)^4735
        have hw : |(5080786727/10000000000 : ℝ)|=(5080786727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s2_2 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (667124903/1250000000 : ℝ)*x 0 + (5080787401/10000000000 : ℝ)*x 1 + (-1446245881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667124903/1250000000 : ℝ)^5759 ≤ (23296566091571/50000000000000 : ℝ)^4735 := by
    have hnat : (667124903 : ℕ)^5759*50000000000000^4735 ≤ 23296566091571^4735*1250000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667124903 1250000000 23296566091571 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5080787401/10000000000 : ℝ)^5759 ≤ (21943460509319/50000000000000 : ℝ)^4735 := by
    have hnat : (5080787401 : ℕ)^5759*50000000000000^4735 ≤ 21943460509319^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080787401 10000000000 21943460509319 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1446245881/10000000000 : ℝ)^5759 ≤ (2379986696321/25000000000000 : ℝ)^4735 := by
    have hnat : (1446245881 : ℕ)^5759*25000000000000^4735 ≤ 2379986696321^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1446245881 10000000000 2379986696321 25000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(667124903/1250000000 : ℝ), (5080787401/10000000000 : ℝ), (-1446245881/10000000000 : ℝ)] ![(23296566091571/50000000000000 : ℝ), (21943460509319/50000000000000 : ℝ), (2379986696321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(667124903/1250000000 : ℝ)|^5759 ≤ (23296566091571/50000000000000 : ℝ)^4735
        have hw : |(667124903/1250000000 : ℝ)|=(667124903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5080787401/10000000000 : ℝ)|^5759 ≤ (21943460509319/50000000000000 : ℝ)^4735
        have hw : |(5080787401/10000000000 : ℝ)|=(5080787401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1446245881/10000000000 : ℝ)|^5759 ≤ (2379986696321/25000000000000 : ℝ)^4735
        have hw : |(-1446245881/10000000000 : ℝ)|=(1446245881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s2_3 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4022945013/10000000000 : ℝ)*x 0 + (3371370749/10000000000 : ℝ)*x 1 + (2368974383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4022945013/10000000000 : ℝ)^5759 ≤ (33038632223741/100000000000000 : ℝ)^4735 := by
    have hnat : (4022945013 : ℕ)^5759*100000000000000^4735 ≤ 33038632223741^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022945013 10000000000 33038632223741 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3371370749/10000000000 : ℝ)^5759 ≤ (13324749954679/50000000000000 : ℝ)^4735 := by
    have hnat : (3371370749 : ℕ)^5759*50000000000000^4735 ≤ 13324749954679^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3371370749 10000000000 13324749954679 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2368974383/5000000000 : ℝ)^5759 ≤ (8062373570389/20000000000000 : ℝ)^4735 := by
    have hnat : (2368974383 : ℕ)^5759*20000000000000^4735 ≤ 8062373570389^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2368974383 5000000000 8062373570389 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4022945013/10000000000 : ℝ), (3371370749/10000000000 : ℝ), (2368974383/5000000000 : ℝ)] ![(33038632223741/100000000000000 : ℝ), (13324749954679/50000000000000 : ℝ), (8062373570389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4022945013/10000000000 : ℝ)|^5759 ≤ (33038632223741/100000000000000 : ℝ)^4735
        have hw : |(4022945013/10000000000 : ℝ)|=(4022945013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3371370749/10000000000 : ℝ)|^5759 ≤ (13324749954679/50000000000000 : ℝ)^4735
        have hw : |(3371370749/10000000000 : ℝ)|=(3371370749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2368974383/5000000000 : ℝ)|^5759 ≤ (8062373570389/20000000000000 : ℝ)^4735
        have hw : |(2368974383/5000000000 : ℝ)|=(2368974383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s2_4 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-614044823/5000000000 : ℝ)*x 0 + (1271892739/2500000000 : ℝ)*x 1 + (85804663/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (614044823/5000000000 : ℝ)^5759 ≤ (975383188397/12500000000000 : ℝ)^4735 := by
    have hnat : (614044823 : ℕ)^5759*12500000000000^4735 ≤ 975383188397^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614044823 5000000000 975383188397 12500000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271892739/2500000000 : ℝ)^5759 ≤ (21979099156729/50000000000000 : ℝ)^4735 := by
    have hnat : (1271892739 : ℕ)^5759*50000000000000^4735 ≤ 21979099156729^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271892739 2500000000 21979099156729 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85804663/156250000 : ℝ)^5759 ≤ (24119368079119/50000000000000 : ℝ)^4735 := by
    have hnat : (85804663 : ℕ)^5759*50000000000000^4735 ≤ 24119368079119^4735*156250000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85804663 156250000 24119368079119 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-614044823/5000000000 : ℝ), (1271892739/2500000000 : ℝ), (85804663/156250000 : ℝ)] ![(975383188397/12500000000000 : ℝ), (21979099156729/50000000000000 : ℝ), (24119368079119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-614044823/5000000000 : ℝ)|^5759 ≤ (975383188397/12500000000000 : ℝ)^4735
        have hw : |(-614044823/5000000000 : ℝ)|=(614044823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1271892739/2500000000 : ℝ)|^5759 ≤ (21979099156729/50000000000000 : ℝ)^4735
        have hw : |(1271892739/2500000000 : ℝ)|=(1271892739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85804663/156250000 : ℝ)|^5759 ≤ (24119368079119/50000000000000 : ℝ)^4735
        have hw : |(85804663/156250000 : ℝ)|=(85804663/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s2_5 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1306564191/2500000000 : ℝ)*x 0 + (-517767913/5000000000 : ℝ)*x 1 + (1372874609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306564191/2500000000 : ℝ)^5759 ≤ (45419896782813/100000000000000 : ℝ)^4735 := by
    have hnat : (1306564191 : ℕ)^5759*100000000000000^4735 ≤ 45419896782813^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306564191 2500000000 45419896782813 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517767913/5000000000 : ℝ)^5759 ≤ (6341366999039/100000000000000 : ℝ)^4735 := by
    have hnat : (517767913 : ℕ)^5759*100000000000000^4735 ≤ 6341366999039^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517767913 5000000000 6341366999039 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372874609/2500000000 : ℝ)^5759 ≤ (24119368100487/50000000000000 : ℝ)^4735 := by
    have hnat : (1372874609 : ℕ)^5759*50000000000000^4735 ≤ 24119368100487^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372874609 2500000000 24119368100487 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306564191/2500000000 : ℝ), (-517767913/5000000000 : ℝ), (1372874609/2500000000 : ℝ)] ![(45419896782813/100000000000000 : ℝ), (6341366999039/100000000000000 : ℝ), (24119368100487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306564191/2500000000 : ℝ)|^5759 ≤ (45419896782813/100000000000000 : ℝ)^4735
        have hw : |(1306564191/2500000000 : ℝ)|=(1306564191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-517767913/5000000000 : ℝ)|^5759 ≤ (6341366999039/100000000000000 : ℝ)^4735
        have hw : |(-517767913/5000000000 : ℝ)|=(517767913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372874609/2500000000 : ℝ)|^5759 ≤ (24119368100487/50000000000000 : ℝ)^4735
        have hw : |(1372874609/2500000000 : ℝ)|=(1372874609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s2_6 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1306564191/2500000000 : ℝ)*x 0 + (5491498437/10000000000 : ℝ)*x 1 + (-41421433/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306564191/2500000000 : ℝ)^5759 ≤ (45419896782813/100000000000000 : ℝ)^4735 := by
    have hnat : (1306564191 : ℕ)^5759*100000000000000^4735 ≤ 45419896782813^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306564191 2500000000 45419896782813 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5491498437/10000000000 : ℝ)^5759 ≤ (24119368105829/50000000000000 : ℝ)^4735 := by
    have hnat : (5491498437 : ℕ)^5759*50000000000000^4735 ≤ 24119368105829^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491498437 10000000000 24119368105829 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41421433/400000000 : ℝ)^5759 ≤ (6341366991591/100000000000000 : ℝ)^4735 := by
    have hnat : (41421433 : ℕ)^5759*100000000000000^4735 ≤ 6341366991591^4735*400000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41421433 400000000 6341366991591 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306564191/2500000000 : ℝ), (5491498437/10000000000 : ℝ), (-41421433/400000000 : ℝ)] ![(45419896782813/100000000000000 : ℝ), (24119368105829/50000000000000 : ℝ), (6341366991591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306564191/2500000000 : ℝ)|^5759 ≤ (45419896782813/100000000000000 : ℝ)^4735
        have hw : |(1306564191/2500000000 : ℝ)|=(1306564191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5491498437/10000000000 : ℝ)|^5759 ≤ (24119368105829/50000000000000 : ℝ)^4735
        have hw : |(5491498437/10000000000 : ℝ)|=(5491498437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41421433/400000000 : ℝ)|^5759 ≤ (6341366991591/100000000000000 : ℝ)^4735
        have hw : |(-41421433/400000000 : ℝ)|=(41421433/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s2_7 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4024101391/10000000000 : ℝ)*x 0 + (4715752511/10000000000 : ℝ)*x 1 + (848508007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4024101391/10000000000 : ℝ)^5759 ≤ (33050183191623/100000000000000 : ℝ)^4735 := by
    have hnat : (4024101391 : ℕ)^5759*100000000000000^4735 ≤ 33050183191623^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024101391 10000000000 33050183191623 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4715752511/10000000000 : ℝ)^5759 ≤ (20041145251627/50000000000000 : ℝ)^4735 := by
    have hnat : (4715752511 : ℕ)^5759*50000000000000^4735 ≤ 20041145251627^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4715752511 10000000000 20041145251627 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848508007/2500000000 : ℝ)^5759 ≤ (26867526292331/100000000000000 : ℝ)^4735 := by
    have hnat : (848508007 : ℕ)^5759*100000000000000^4735 ≤ 26867526292331^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848508007 2500000000 26867526292331 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4024101391/10000000000 : ℝ), (4715752511/10000000000 : ℝ), (848508007/2500000000 : ℝ)] ![(33050183191623/100000000000000 : ℝ), (20041145251627/50000000000000 : ℝ), (26867526292331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4024101391/10000000000 : ℝ)|^5759 ≤ (33050183191623/100000000000000 : ℝ)^4735
        have hw : |(4024101391/10000000000 : ℝ)|=(4024101391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4715752511/10000000000 : ℝ)|^5759 ≤ (20041145251627/50000000000000 : ℝ)^4735
        have hw : |(4715752511/10000000000 : ℝ)|=(4715752511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848508007/2500000000 : ℝ)|^5759 ≤ (26867526292331/100000000000000 : ℝ)^4735
        have hw : |(848508007/2500000000 : ℝ)|=(848508007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1749_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8967/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4513/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4499/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8967/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8967/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8967/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8967/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8967/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8967/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8967/100000 : ℝ) ^ (5743/1024 : ℝ) ≤ (33417044118371/25000000000000000000 : ℝ) := by
    have hpowers : (8967/100000 : ℝ)^5743 ≤ (33417044118371/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8967 : ℕ)^5743*25000000000000000000^1024 ≤ 33417044118371^1024*100000^5743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8967 100000 33417044118371 25000000000000000000 5743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8967/100000 : ℝ)) (X := (33417044118371/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18069/100000 : ℝ) ^ (5743/1024 : ℝ) ≤ (1360255415090187/20000000000000000000 : ℝ) := by
    have hpowers : (18069/100000 : ℝ)^5743 ≤ (1360255415090187/20000000000000000000 : ℝ)^1024 := by
      have hnat : (18069 : ℕ)^5743*20000000000000000000^1024 ≤ 1360255415090187^1024*100000^5743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18069 100000 1360255415090187 20000000000000000000 5743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18069/100000 : ℝ)) (X := (1360255415090187/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500033417044118371/12500000000000000000 : ℝ) ≤ (2500001191677367/2500000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (12500033417044118371/12500000000000000000 : ℝ)^1024 ≤ (2500001191677367/2500000000000000 : ℝ)^5743 := by
      have hnat : (12500033417044118371 : ℕ)^1024*2500000000000000^5743 ≤ 2500001191677367^5743*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500033417044118371 12500000000000000000 2500001191677367 2500000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500001191677367/2500000000000000 : ℝ)) (X := (12500033417044118371/12500000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100006934945251924419/100000000000000000000 : ℝ) ≤ (5000061824670149/5000000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (100006934945251924419/100000000000000000000 : ℝ)^1024 ≤ (5000061824670149/5000000000000000 : ℝ)^5743 := by
      have hnat : (100006934945251924419 : ℕ)^1024*5000000000000000^5743 ≤ 5000061824670149^5743*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100006934945251924419 100000000000000000000 5000061824670149 5000000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000061824670149/5000000000000000 : ℝ)) (X := (100006934945251924419/100000000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10001360255415090187/10000000000000000000 : ℝ) ≤ (1250030316496391/1250000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (10001360255415090187/10000000000000000000 : ℝ)^1024 ≤ (1250030316496391/1250000000000000 : ℝ)^5743 := by
      have hnat : (10001360255415090187 : ℕ)^1024*1250000000000000^5743 ≤ 1250030316496391^5743*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001360255415090187 10000000000000000000 1250030316496391 1250000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250030316496391/1250000000000000 : ℝ)) (X := (10001360255415090187/10000000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(33417044118371/25000000000000000000 : ℝ) ≤ ((7584825945457356043/7585000000000000000 : ℝ)+2*(3962754361/30340000000000 : ℝ)*(8967/100000 : ℝ))^(5743/1024 : ℝ) := by
    rw [show (7584825945457356043/7585000000000000000 : ℝ)+2*(3962754361/30340000000000 : ℝ)*(8967/100000 : ℝ)=(2500001191677367/2500000000000000 : ℝ) by norm_num, show 1+2*(33417044118371/25000000000000000000 : ℝ)=(12500033417044118371/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1360255415090187/20000000000000000000 : ℝ)+(33417044118371/25000000000000000000 : ℝ) ≤ ((7584825945457356043/7585000000000000000 : ℝ)+(3962754361/30340000000000 : ℝ)*((18069/100000 : ℝ)+(8967/100000 : ℝ)))^(5743/1024 : ℝ) := by
    rw [show (7584825945457356043/7585000000000000000 : ℝ)+(3962754361/30340000000000 : ℝ)*((18069/100000 : ℝ)+(8967/100000 : ℝ))=(5000061824670149/5000000000000000 : ℝ) by norm_num, show 1+(1360255415090187/20000000000000000000 : ℝ)+(33417044118371/25000000000000000000 : ℝ)=(100006934945251924419/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1360255415090187/20000000000000000000 : ℝ) ≤ ((7584825945457356043/7585000000000000000 : ℝ)+2*(3962754361/30340000000000 : ℝ)*(18069/100000 : ℝ))^(5743/1024 : ℝ) := by
    rw [show (7584825945457356043/7585000000000000000 : ℝ)+2*(3962754361/30340000000000 : ℝ)*(18069/100000 : ℝ)=(1250030316496391/1250000000000000 : ℝ) by norm_num, show 1+2*(1360255415090187/20000000000000000000 : ℝ)=(10001360255415090187/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7584825945457356043/7585000000000000000 : ℝ)*(X 1 0+X 2 0)+(3962754361/30340000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (8967/100000 : ℝ)) (hi := (18069/100000 : ℝ)) (c := (7584825945457356043/7585000000000000000 : ℝ)) (alpha := (3962754361/30340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7584825945457356043/7585000000000000000 : ℝ)*(X 0 1+X 2 1)+(3962754361/30340000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (8967/100000 : ℝ)) (hi := (18069/100000 : ℝ)) (c := (7584825945457356043/7585000000000000000 : ℝ)) (alpha := (3962754361/30340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7584825945457356043/7585000000000000000 : ℝ)*(X 0 2+X 1 2)+(3962754361/30340000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (8967/100000 : ℝ)) (hi := (18069/100000 : ℝ)) (c := (7584825945457356043/7585000000000000000 : ℝ)) (alpha := (3962754361/30340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-613868597/5000000000 : ℝ)*X 0 0+(1099684929/2000000000 : ℝ)*X 0 1+(508078659/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((20847653/39062500 : ℝ)*X 1 0+(-36156171/250000000 : ℝ)*X 1 1+(5080786727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((667124903/1250000000 : ℝ)*X 2 0+(5080787401/10000000000 : ℝ)*X 2 1+(-1446245881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4022945013/10000000000 : ℝ)*X 0 0+(3371370749/10000000000 : ℝ)*X 0 1+(2368974383/5000000000 : ℝ)*X 0 2+(4022945013/10000000000 : ℝ)*X 1 0+(3371370749/10000000000 : ℝ)*X 1 1+(2368974383/5000000000 : ℝ)*X 1 2+(4022945013/10000000000 : ℝ)*X 2 0+(3371370749/10000000000 : ℝ)*X 2 1+(2368974383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-614044823/5000000000 : ℝ)*X 0 0+(1271892739/2500000000 : ℝ)*X 0 1+(85804663/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1306564191/2500000000 : ℝ)*X 1 0+(-517767913/5000000000 : ℝ)*X 1 1+(1372874609/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1306564191/2500000000 : ℝ)*X 2 0+(5491498437/10000000000 : ℝ)*X 2 1+(-41421433/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4024101391/10000000000 : ℝ)*X 0 0+(4715752511/10000000000 : ℝ)*X 0 1+(848508007/2500000000 : ℝ)*X 0 2+(4024101391/10000000000 : ℝ)*X 1 0+(4715752511/10000000000 : ℝ)*X 1 1+(848508007/2500000000 : ℝ)*X 1 2+(4024101391/10000000000 : ℝ)*X 2 0+(4715752511/10000000000 : ℝ)*X 2 1+(848508007/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (561530536358801067068717199/47406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2588285361/100000000000000 : ℝ)*(base19) + (2279748841/100000000000000 : ℝ)*(base23) + (87972057/50000000000000 : ℝ)*(upper3) + (17807491/10000000000000 : ℝ)*(upper4) + (226377859/50000000000000 : ℝ)*(upper5) + (195389519258777/12500000000000 : ℝ)*(major0) + (195389519258777/12500000000000 : ℝ)*(major1) + (195389519258777/12500000000000 : ℝ)*(major2) + (1197219015696003/50000000000000 : ℝ)*(sp0) + (239446295857413/10000000000000 : ℝ)*(sp1) + (2394463267110651/100000000000000 : ℝ)*(sp2) + (365880409736261/50000000000000 : ℝ)*(sp3) + (13757733743/50000000000000 : ℝ)*(sp4) + (2773486307/50000000000000 : ℝ)*(sp7) + (45735397902821/6250000000000 : ℝ)*(f.failure) + (598616386714873/25000000000000 : ℝ)*(f.sum) + (423813174901/379250000000000000000000000 : ℝ)*base66 + (13131161163936097/2562500000000000000000000000000 : ℝ)*base68 + (1963666541311097/2562500000000000000000000000000 : ℝ)*base70 + (18739308961561097/2562500000000000000000000000000 : ℝ)*base72 + (59932581517/379250000000000000000000000 : ℝ)*base74 + (7897368524936097/2562500000000000000000000000000 : ℝ)*base76 + (15748387108061097/2562500000000000000000000000000 : ℝ)*base78 + (42065331549248597/2562500000000000000000000000000 : ℝ)*base80 + (1112508272751/303400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1090539/156250000000000000000 : ℝ)*base89 + (1090539/156250000000000000000 : ℝ)*base91 + (1090539/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1738019667175531686196057383/189625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (297936681/25000000000000 : ℝ)*(base19) + (155911/12207031250 : ℝ)*(base23) + (50018943/25000000000000 : ℝ)*(upper3) + (37726913/100000000000000 : ℝ)*(lower4) + (191516503/100000000000000 : ℝ)*(upper5) + (808070319893291/50000000000000 : ℝ)*(major0) + (808070319893291/50000000000000 : ℝ)*(major1) + (808070319893291/50000000000000 : ℝ)*(major2) + (8234820043/100000000000000 : ℝ)*(sp1) + (1107744883/12500000000000 : ℝ)*(sp2) + (247569141379593/10000000000000 : ℝ)*(sp4) + (618920496807291/25000000000000 : ℝ)*(sp5) + (1237840637306977/50000000000000 : ℝ)*(sp6) + (756589560258501/100000000000000 : ℝ)*(sp7) + (756589560258501/100000000000000 : ℝ)*(f.failure) + (247569141379593/10000000000000 : ℝ)*(f.sum) + (596146972457/303400000000000000000000000 : ℝ)*base66 + (15294769310946149/10250000000000000000000000000000 : ℝ)*base67 + (75968653166696149/10250000000000000000000000000000 : ℝ)*base69 + (19031823780946149/10250000000000000000000000000000 : ℝ)*base71 + (8964796697657/1517000000000000000000000000 : ℝ)*base74 + (3966759365446149/10250000000000000000000000000000 : ℝ)*base75 + (37735391642946149/10250000000000000000000000000000 : ℝ)*base77 + (61016601120446149/10250000000000000000000000000000 : ℝ)*base79 + (1896972975249/379250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1503659/2500000000000000000000 : ℝ)*base89 + (1503659/2500000000000000000000 : ℝ)*base91 + (1503659/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1749_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8967/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4513/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4499/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1749_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1749_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4513/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4499/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1749_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1749_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1749_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4513/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4499/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1749_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

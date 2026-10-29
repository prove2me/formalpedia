-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1407_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:00.957267+00:00
-- url     : https://prove2.me/submissions/dff0937b-4cfc-44f4-a695-4b834dcb60b1

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
theorem support_rectangle_w1407_s6_0 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1989118911/10000000000 : ℝ)*x 0 + (1352339391/2500000000 : ℝ)*x 1 + (5246390747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989118911/10000000000 : ℝ)^4367 ≤ (12129204825449/100000000000000 : ℝ)^3343 := by
    have hnat : (1989118911 : ℕ)^4367*100000000000000^3343 ≤ 12129204825449^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989118911 10000000000 12129204825449 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352339391/2500000000 : ℝ)^4367 ≤ (11203277721641/25000000000000 : ℝ)^3343 := by
    have hnat : (1352339391 : ℕ)^4367*25000000000000^3343 ≤ 11203277721641^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352339391 2500000000 11203277721641 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246390747/10000000000 : ℝ)^4367 ≤ (43057684265981/100000000000000 : ℝ)^3343 := by
    have hnat : (5246390747 : ℕ)^4367*100000000000000^3343 ≤ 43057684265981^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246390747 10000000000 43057684265981 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1989118911/10000000000 : ℝ), (1352339391/2500000000 : ℝ), (5246390747/10000000000 : ℝ)] ![(12129204825449/100000000000000 : ℝ), (11203277721641/25000000000000 : ℝ), (43057684265981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1989118911/10000000000 : ℝ)|^4367 ≤ (12129204825449/100000000000000 : ℝ)^3343
        have hw : |(-1989118911/10000000000 : ℝ)|=(1989118911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352339391/2500000000 : ℝ)|^4367 ≤ (11203277721641/25000000000000 : ℝ)^3343
        have hw : |(1352339391/2500000000 : ℝ)|=(1352339391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246390747/10000000000 : ℝ)|^4367 ≤ (43057684265981/100000000000000 : ℝ)^3343
        have hw : |(5246390747/10000000000 : ℝ)|=(5246390747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s6_1 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347781549/10000000000 : ℝ)*x 0 + (-1036052121/5000000000 : ℝ)*x 1 + (5246390497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347781549/10000000000 : ℝ)^4367 ≤ (44147902098329/100000000000000 : ℝ)^3343 := by
    have hnat : (5347781549 : ℕ)^4367*100000000000000^3343 ≤ 44147902098329^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347781549 10000000000 44147902098329 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036052121/5000000000 : ℝ)^4367 ≤ (6397208150053/50000000000000 : ℝ)^3343 := by
    have hnat : (1036052121 : ℕ)^4367*50000000000000^3343 ≤ 6397208150053^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036052121 5000000000 6397208150053 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246390497/10000000000 : ℝ)^4367 ≤ (43057681585721/100000000000000 : ℝ)^3343 := by
    have hnat : (5246390497 : ℕ)^4367*100000000000000^3343 ≤ 43057681585721^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246390497 10000000000 43057681585721 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347781549/10000000000 : ℝ), (-1036052121/5000000000 : ℝ), (5246390497/10000000000 : ℝ)] ![(44147902098329/100000000000000 : ℝ), (6397208150053/50000000000000 : ℝ), (43057681585721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347781549/10000000000 : ℝ)|^4367 ≤ (44147902098329/100000000000000 : ℝ)^3343
        have hw : |(5347781549/10000000000 : ℝ)|=(5347781549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036052121/5000000000 : ℝ)|^4367 ≤ (6397208150053/50000000000000 : ℝ)^3343
        have hw : |(-1036052121/5000000000 : ℝ)|=(1036052121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246390497/10000000000 : ℝ)|^4367 ≤ (43057681585721/100000000000000 : ℝ)^3343
        have hw : |(5246390497/10000000000 : ℝ)|=(5246390497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s6_2 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347782661/10000000000 : ℝ)*x 0 + (5246389683/10000000000 : ℝ)*x 1 + (-1036051919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347782661/10000000000 : ℝ)^4367 ≤ (44147914090229/100000000000000 : ℝ)^3343 := by
    have hnat : (5347782661 : ℕ)^4367*100000000000000^3343 ≤ 44147914090229^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347782661 10000000000 44147914090229 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246389683/10000000000 : ℝ)^4367 ≤ (10764418214699/25000000000000 : ℝ)^3343 := by
    have hnat : (5246389683 : ℕ)^4367*25000000000000^3343 ≤ 10764418214699^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246389683 10000000000 10764418214699 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036051919/5000000000 : ℝ)^4367 ≤ (12794413041461/100000000000000 : ℝ)^3343 := by
    have hnat : (1036051919 : ℕ)^4367*100000000000000^3343 ≤ 12794413041461^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036051919 5000000000 12794413041461 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347782661/10000000000 : ℝ), (5246389683/10000000000 : ℝ), (-1036051919/5000000000 : ℝ)] ![(44147914090229/100000000000000 : ℝ), (10764418214699/25000000000000 : ℝ), (12794413041461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347782661/10000000000 : ℝ)|^4367 ≤ (44147914090229/100000000000000 : ℝ)^3343
        have hw : |(5347782661/10000000000 : ℝ)|=(5347782661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246389683/10000000000 : ℝ)|^4367 ≤ (10764418214699/25000000000000 : ℝ)^3343
        have hw : |(5246389683/10000000000 : ℝ)|=(5246389683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1036051919/5000000000 : ℝ)|^4367 ≤ (12794413041461/100000000000000 : ℝ)^3343
        have hw : |(-1036051919/5000000000 : ℝ)|=(1036051919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s6_3 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (861981147/2000000000 : ℝ)*x 0 + (827653777/2000000000 : ℝ)*x 1 + (2243991509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861981147/2000000000 : ℝ)^4367 ≤ (8326087742631/25000000000000 : ℝ)^3343 := by
    have hnat : (861981147 : ℕ)^4367*25000000000000^3343 ≤ 8326087742631^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861981147 2000000000 8326087742631 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (827653777/2000000000 : ℝ)^4367 ≤ (31582448268743/100000000000000 : ℝ)^3343 := by
    have hnat : (827653777 : ℕ)^4367*100000000000000^3343 ≤ 31582448268743^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827653777 2000000000 31582448268743 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243991509/5000000000 : ℝ)^4367 ≤ (2194575046397/6250000000000 : ℝ)^3343 := by
    have hnat : (2243991509 : ℕ)^4367*6250000000000^3343 ≤ 2194575046397^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243991509 5000000000 2194575046397 6250000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861981147/2000000000 : ℝ), (827653777/2000000000 : ℝ), (2243991509/5000000000 : ℝ)] ![(8326087742631/25000000000000 : ℝ), (31582448268743/100000000000000 : ℝ), (2194575046397/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861981147/2000000000 : ℝ)|^4367 ≤ (8326087742631/25000000000000 : ℝ)^3343
        have hw : |(861981147/2000000000 : ℝ)|=(861981147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(827653777/2000000000 : ℝ)|^4367 ≤ (31582448268743/100000000000000 : ℝ)^3343
        have hw : |(827653777/2000000000 : ℝ)|=(827653777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2243991509/5000000000 : ℝ)|^4367 ≤ (2194575046397/6250000000000 : ℝ)^3343
        have hw : |(2243991509/5000000000 : ℝ)|=(2243991509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s6_4 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1989130707/10000000000 : ℝ)*x 0 + (1311744223/2500000000 : ℝ)*x 1 + (676096023/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989130707/10000000000 : ℝ)^4367 ≤ (3032324696933/25000000000000 : ℝ)^3343 := by
    have hnat : (1989130707 : ℕ)^4367*25000000000000^3343 ≤ 3032324696933^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989130707 10000000000 3032324696933 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311744223/2500000000 : ℝ)^4367 ≤ (10765992114137/25000000000000 : ℝ)^3343 := by
    have hnat : (1311744223 : ℕ)^4367*25000000000000^3343 ≤ 10765992114137^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311744223 2500000000 10765992114137 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676096023/1250000000 : ℝ)^4367 ≤ (44806732741891/100000000000000 : ℝ)^3343 := by
    have hnat : (676096023 : ℕ)^4367*100000000000000^3343 ≤ 44806732741891^3343*1250000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676096023 1250000000 44806732741891 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1989130707/10000000000 : ℝ), (1311744223/2500000000 : ℝ), (676096023/1250000000 : ℝ)] ![(3032324696933/25000000000000 : ℝ), (10765992114137/25000000000000 : ℝ), (44806732741891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1989130707/10000000000 : ℝ)|^4367 ≤ (3032324696933/25000000000000 : ℝ)^3343
        have hw : |(-1989130707/10000000000 : ℝ)|=(1989130707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311744223/2500000000 : ℝ)|^4367 ≤ (10765992114137/25000000000000 : ℝ)^3343
        have hw : |(1311744223/2500000000 : ℝ)|=(1311744223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676096023/1250000000 : ℝ)|^4367 ≤ (44806732741891/100000000000000 : ℝ)^3343
        have hw : |(676096023/1250000000 : ℝ)|=(676096023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s6_5 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305507763/10000000000 : ℝ)*x 0 + (-1909726151/10000000000 : ℝ)*x 1 + (1081753637/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305507763/10000000000 : ℝ)^4367 ≤ (43692571019301/100000000000000 : ℝ)^3343 := by
    have hnat : (5305507763 : ℕ)^4367*100000000000000^3343 ≤ 43692571019301^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305507763 10000000000 43692571019301 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1909726151/10000000000 : ℝ)^4367 ≤ (575034810601/5000000000000 : ℝ)^3343 := by
    have hnat : (1909726151 : ℕ)^4367*5000000000000^3343 ≤ 575034810601^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909726151 10000000000 575034810601 5000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081753637/2000000000 : ℝ)^4367 ≤ (5600841594089/12500000000000 : ℝ)^3343 := by
    have hnat : (1081753637 : ℕ)^4367*12500000000000^3343 ≤ 5600841594089^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081753637 2000000000 5600841594089 12500000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305507763/10000000000 : ℝ), (-1909726151/10000000000 : ℝ), (1081753637/2000000000 : ℝ)] ![(43692571019301/100000000000000 : ℝ), (575034810601/5000000000000 : ℝ), (5600841594089/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305507763/10000000000 : ℝ)|^4367 ≤ (43692571019301/100000000000000 : ℝ)^3343
        have hw : |(5305507763/10000000000 : ℝ)|=(5305507763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1909726151/10000000000 : ℝ)|^4367 ≤ (575034810601/5000000000000 : ℝ)^3343
        have hw : |(-1909726151/10000000000 : ℝ)|=(1909726151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081753637/2000000000 : ℝ)|^4367 ≤ (5600841594089/12500000000000 : ℝ)^3343
        have hw : |(1081753637/2000000000 : ℝ)|=(1081753637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s6_6 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061101553/2000000000 : ℝ)*x 0 + (1081753637/2000000000 : ℝ)*x 1 + (-1909726149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061101553/2000000000 : ℝ)^4367 ≤ (43692571040817/100000000000000 : ℝ)^3343 := by
    have hnat : (1061101553 : ℕ)^4367*100000000000000^3343 ≤ 43692571040817^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061101553 2000000000 43692571040817 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081753637/2000000000 : ℝ)^4367 ≤ (5600841594089/12500000000000 : ℝ)^3343 := by
    have hnat : (1081753637 : ℕ)^4367*12500000000000^3343 ≤ 5600841594089^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081753637 2000000000 5600841594089 12500000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1909726149/10000000000 : ℝ)^4367 ≤ (5750348098143/50000000000000 : ℝ)^3343 := by
    have hnat : (1909726149 : ℕ)^4367*50000000000000^3343 ≤ 5750348098143^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909726149 10000000000 5750348098143 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061101553/2000000000 : ℝ), (1081753637/2000000000 : ℝ), (-1909726149/10000000000 : ℝ)] ![(43692571040817/100000000000000 : ℝ), (5600841594089/12500000000000 : ℝ), (5750348098143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061101553/2000000000 : ℝ)|^4367 ≤ (43692571040817/100000000000000 : ℝ)^3343
        have hw : |(1061101553/2000000000 : ℝ)|=(1061101553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081753637/2000000000 : ℝ)|^4367 ≤ (5600841594089/12500000000000 : ℝ)^3343
        have hw : |(1081753637/2000000000 : ℝ)|=(1081753637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1909726149/10000000000 : ℝ)|^4367 ≤ (5750348098143/50000000000000 : ℝ)^3343
        have hw : |(-1909726149/10000000000 : ℝ)|=(1909726149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s6_7 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4309929803/10000000000 : ℝ)*x 0 + (4486724261/10000000000 : ℝ)*x 1 + (413953483/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309929803/10000000000 : ℝ)^4367 ≤ (8326148480619/25000000000000 : ℝ)^3343 := by
    have hnat : (4309929803 : ℕ)^4367*25000000000000^3343 ≤ 8326148480619^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309929803 10000000000 8326148480619 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4486724261/10000000000 : ℝ)^4367 ≤ (1404013454007/4000000000000 : ℝ)^3343 := by
    have hnat : (4486724261 : ℕ)^4367*4000000000000^3343 ≤ 1404013454007^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486724261 10000000000 1404013454007 4000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413953483/1000000000 : ℝ)^4367 ≤ (31595069713963/100000000000000 : ℝ)^3343 := by
    have hnat : (413953483 : ℕ)^4367*100000000000000^3343 ≤ 31595069713963^3343*1000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413953483 1000000000 31595069713963 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309929803/10000000000 : ℝ), (4486724261/10000000000 : ℝ), (413953483/1000000000 : ℝ)] ![(8326148480619/25000000000000 : ℝ), (1404013454007/4000000000000 : ℝ), (31595069713963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309929803/10000000000 : ℝ)|^4367 ≤ (8326148480619/25000000000000 : ℝ)^3343
        have hw : |(4309929803/10000000000 : ℝ)|=(4309929803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4486724261/10000000000 : ℝ)|^4367 ≤ (1404013454007/4000000000000 : ℝ)^3343
        have hw : |(4486724261/10000000000 : ℝ)|=(4486724261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(413953483/1000000000 : ℝ)|^4367 ≤ (31595069713963/100000000000000 : ℝ)^3343
        have hw : |(413953483/1000000000 : ℝ)|=(413953483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1407_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5647/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7373/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1129/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1129/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1129/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1129/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1129/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1129/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1129/10000 : ℝ) ^ (2183/512 : ℝ) ≤ (1828217235078103/20000000000000000000 : ℝ) := by
    have hpowers : (1129/10000 : ℝ)^2183 ≤ (1828217235078103/20000000000000000000 : ℝ)^512 := by
      have hnat : (1129 : ℕ)^2183*20000000000000000000^512 ≤ 1828217235078103^512*10000^2183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1129 10000 1828217235078103 20000000000000000000 2183 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1129/10000 : ℝ)) (X := (1828217235078103/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hpowhi : (59/400 : ℝ) ^ (2183/512 : ℝ) ≤ (14288015710413767/50000000000000000000 : ℝ) := by
    have hpowers : (59/400 : ℝ)^2183 ≤ (14288015710413767/50000000000000000000 : ℝ)^512 := by
      have hnat : (59 : ℕ)^2183*50000000000000000000^512 ≤ 14288015710413767^512*400^2183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59 400 14288015710413767 50000000000000000000 2183 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59/400 : ℝ)) (X := (14288015710413767/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001828217235078103/10000000000000000000 : ℝ) ≤ (500021437969191/500000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (10001828217235078103/10000000000000000000 : ℝ)^512 ≤ (500021437969191/500000000000000 : ℝ)^2183 := by
      have hnat : (10001828217235078103 : ℕ)^512*500000000000000^2183 ≤ 500021437969191^2183*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001828217235078103 10000000000000000000 500021437969191 500000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500021437969191/500000000000000 : ℝ)) (X := (10001828217235078103/10000000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037717117596218049/100000000000000000000 : ℝ) ≤ (1000088448818913/1000000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (100037717117596218049/100000000000000000000 : ℝ)^512 ≤ (1000088448818913/1000000000000000 : ℝ)^2183 := by
      have hnat : (100037717117596218049 : ℕ)^512*1000000000000000^2183 ≤ 1000088448818913^2183*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037717117596218049 100000000000000000000 1000088448818913 1000000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000088448818913/1000000000000000 : ℝ)) (X := (100037717117596218049/100000000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014288015710413767/25000000000000000000 : ℝ) ≤ (250033505424861/250000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (25014288015710413767/25000000000000000000 : ℝ)^512 ≤ (250033505424861/250000000000000 : ℝ)^2183 := by
      have hnat : (25014288015710413767 : ℕ)^512*250000000000000^2183 ≤ 250033505424861^2183*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014288015710413767 25000000000000000000 250033505424861 250000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250033505424861/250000000000000 : ℝ)) (X := (25014288015710413767/25000000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1828217235078103/20000000000000000000 : ℝ) ≤ ((172955965755220587/173000000000000000 : ℝ)+2*(45572880531/34600000000000 : ℝ)*(1129/10000 : ℝ))^(2183/512 : ℝ) := by
    rw [show (172955965755220587/173000000000000000 : ℝ)+2*(45572880531/34600000000000 : ℝ)*(1129/10000 : ℝ)=(500021437969191/500000000000000 : ℝ) by norm_num, show 1+2*(1828217235078103/20000000000000000000 : ℝ)=(10001828217235078103/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14288015710413767/50000000000000000000 : ℝ)+(1828217235078103/20000000000000000000 : ℝ) ≤ ((172955965755220587/173000000000000000 : ℝ)+(45572880531/34600000000000 : ℝ)*((59/400 : ℝ)+(1129/10000 : ℝ)))^(2183/512 : ℝ) := by
    rw [show (172955965755220587/173000000000000000 : ℝ)+(45572880531/34600000000000 : ℝ)*((59/400 : ℝ)+(1129/10000 : ℝ))=(1000088448818913/1000000000000000 : ℝ) by norm_num, show 1+(14288015710413767/50000000000000000000 : ℝ)+(1828217235078103/20000000000000000000 : ℝ)=(100037717117596218049/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14288015710413767/50000000000000000000 : ℝ) ≤ ((172955965755220587/173000000000000000 : ℝ)+2*(45572880531/34600000000000 : ℝ)*(59/400 : ℝ))^(2183/512 : ℝ) := by
    rw [show (172955965755220587/173000000000000000 : ℝ)+2*(45572880531/34600000000000 : ℝ)*(59/400 : ℝ)=(250033505424861/250000000000000 : ℝ) by norm_num, show 1+2*(14288015710413767/50000000000000000000 : ℝ)=(25014288015710413767/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (172955965755220587/173000000000000000 : ℝ)*(X 1 0+X 2 0)+(45572880531/34600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (59/400 : ℝ)) (c := (172955965755220587/173000000000000000 : ℝ)) (alpha := (45572880531/34600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (172955965755220587/173000000000000000 : ℝ)*(X 0 1+X 2 1)+(45572880531/34600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (59/400 : ℝ)) (c := (172955965755220587/173000000000000000 : ℝ)) (alpha := (45572880531/34600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (172955965755220587/173000000000000000 : ℝ)*(X 0 2+X 1 2)+(45572880531/34600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (59/400 : ℝ)) (c := (172955965755220587/173000000000000000 : ℝ)) (alpha := (45572880531/34600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1989118911/10000000000 : ℝ)*X 0 0+(1352339391/2500000000 : ℝ)*X 0 1+(5246390747/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347781549/10000000000 : ℝ)*X 1 0+(-1036052121/5000000000 : ℝ)*X 1 1+(5246390497/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347782661/10000000000 : ℝ)*X 2 0+(5246389683/10000000000 : ℝ)*X 2 1+(-1036051919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((861981147/2000000000 : ℝ)*X 0 0+(827653777/2000000000 : ℝ)*X 0 1+(2243991509/5000000000 : ℝ)*X 0 2+(861981147/2000000000 : ℝ)*X 1 0+(827653777/2000000000 : ℝ)*X 1 1+(2243991509/5000000000 : ℝ)*X 1 2+(861981147/2000000000 : ℝ)*X 2 0+(827653777/2000000000 : ℝ)*X 2 1+(2243991509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1989130707/10000000000 : ℝ)*X 0 0+(1311744223/2500000000 : ℝ)*X 0 1+(676096023/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305507763/10000000000 : ℝ)*X 1 0+(-1909726151/10000000000 : ℝ)*X 1 1+(1081753637/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061101553/2000000000 : ℝ)*X 2 0+(1081753637/2000000000 : ℝ)*X 2 1+(-1909726149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4309929803/10000000000 : ℝ)*X 0 0+(4486724261/10000000000 : ℝ)*X 0 1+(413953483/1000000000 : ℝ)*X 0 2+(4309929803/10000000000 : ℝ)*X 1 0+(4486724261/10000000000 : ℝ)*X 1 1+(413953483/1000000000 : ℝ)*X 1 2+(4309929803/10000000000 : ℝ)*X 2 0+(4486724261/10000000000 : ℝ)*X 2 1+(413953483/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26680755636190200333683529/4325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (258497669/20000000000000 : ℝ)*(base19) + (913340203/50000000000000 : ℝ)*(base23) + (198337853/50000000000000 : ℝ)*(lower2) + (510843/1000000000000 : ℝ)*(upper3) + (236213957/100000000000000 : ℝ)*(upper5) + (2248937419196111/50000000000000 : ℝ)*(major0) + (2248937419196111/50000000000000 : ℝ)*(major1) + (2248937419196111/50000000000000 : ℝ)*(major2) + (613621715044353/10000000000000 : ℝ)*(sp0) + (1534060275527677/25000000000000 : ℝ)*(sp1) + (6136240567918647/100000000000000 : ℝ)*(sp2) + (285949018364151/10000000000000 : ℝ)*(sp3) + (25244155523/100000000000000 : ℝ)*(sp4) + (4223227961/25000000000000 : ℝ)*(sp7) + (1429753538276677/50000000000000 : ℝ)*(f.failure) + (6136242394599053/100000000000000 : ℝ)*(f.sum) + (1229712816363/432500000000000000000000000 : ℝ)*base65 + (97015089136742157/8650000000000000000000000000000 : ℝ)*base67 + (14453418808942157/8650000000000000000000000000000 : ℝ)*base69 + (60407647272142157/8650000000000000000000000000000 : ℝ)*base71 + (1906487957171/865000000000000000000000000 : ℝ)*base73 + (51328488140157843/8650000000000000000000000000000 : ℝ)*base76 + (25051179038392157/8650000000000000000000000000000 : ℝ)*base77 + (60489157835507843/8650000000000000000000000000000 : ℝ)*base80 + (2834487269669/865000000000000000000000000 : ℝ)*base82 + (45736903/5000000000000000000000 : ℝ)*base90 + (45736903/5000000000000000000000 : ℝ)*base92 + (45736903/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25392703131313230011224329/2162500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1988238697/100000000000000 : ℝ)*(base19) + (216259561/10000000000000 : ℝ)*(base23) + (674161601/100000000000000 : ℝ)*(lower1) + (119651483/50000000000000 : ℝ)*(upper3) + (4847903/6250000000000 : ℝ)*(lower4) + (239964727/100000000000000 : ℝ)*(upper5) + (2265252870933311/50000000000000 : ℝ)*(major0) + (2265252870933311/50000000000000 : ℝ)*(major1) + (2265252870933311/50000000000000 : ℝ)*(major2) + (324130639/10000000000000 : ℝ)*(sp2) + (6180759041142841/100000000000000 : ℝ)*(sp4) + (6180757052904143/100000000000000 : ℝ)*(sp5) + (6180753637240841/100000000000000 : ℝ)*(sp6) + (288025205118069/10000000000000 : ℝ)*(sp7) + (288025205118069/10000000000000 : ℝ)*(f.failure) + (6180759041142841/100000000000000 : ℝ)*(f.sum) + (1595069087327/432500000000000000000000000 : ℝ)*base66 + (9402691945678557/8650000000000000000000000000000 : ℝ)*base67 + (121163691921378557/8650000000000000000000000000000 : ℝ)*base69 + (530474220736371443/8650000000000000000000000000000 : ℝ)*base72 + (229141100441/216250000000000000000000000 : ℝ)*base74 + (1460936936421228557/8650000000000000000000000000000 : ℝ)*base75 + (39130251065728557/8650000000000000000000000000000 : ℝ)*base77 + (338767117622728557/8650000000000000000000000000000 : ℝ)*base79 + (727591332887/432500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2784809/1000000000000000000000 : ℝ)*base89 + (2784809/1000000000000000000000 : ℝ)*base91 + (2784809/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1407_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1407_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1407_s7_0 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1989121997/10000000000 : ℝ)*x 0 + (5409328061/10000000000 : ℝ)*x 1 + (1311604559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989121997/10000000000 : ℝ)^4367 ≤ (3032307351823/25000000000000 : ℝ)^3343 := by
    have hnat : (1989121997 : ℕ)^4367*25000000000000^3343 ≤ 3032307351823^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989121997 10000000000 3032307351823 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409328061/10000000000 : ℝ)^4367 ≤ (5601598950791/12500000000000 : ℝ)^3343 := by
    have hnat : (5409328061 : ℕ)^4367*12500000000000^3343 ≤ 5601598950791^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409328061 10000000000 5601598950791 12500000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311604559/2500000000 : ℝ)^4367 ≤ (43057978976841/100000000000000 : ℝ)^3343 := by
    have hnat : (1311604559 : ℕ)^4367*100000000000000^3343 ≤ 43057978976841^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311604559 2500000000 43057978976841 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1989121997/10000000000 : ℝ), (5409328061/10000000000 : ℝ), (1311604559/2500000000 : ℝ)] ![(3032307351823/25000000000000 : ℝ), (5601598950791/12500000000000 : ℝ), (43057978976841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1989121997/10000000000 : ℝ)|^4367 ≤ (3032307351823/25000000000000 : ℝ)^3343
        have hw : |(-1989121997/10000000000 : ℝ)|=(1989121997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409328061/10000000000 : ℝ)|^4367 ≤ (5601598950791/12500000000000 : ℝ)^3343
        have hw : |(5409328061/10000000000 : ℝ)|=(5409328061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311604559/2500000000 : ℝ)|^4367 ≤ (43057978976841/100000000000000 : ℝ)^3343
        have hw : |(1311604559/2500000000 : ℝ)|=(1311604559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s7_1 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267388717/500000000 : ℝ)*x 0 + (-1036038519/5000000000 : ℝ)*x 1 + (1049283643/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267388717/500000000 : ℝ)^4367 ≤ (44147824355889/100000000000000 : ℝ)^3343 := by
    have hnat : (267388717 : ℕ)^4367*100000000000000^3343 ≤ 44147824355889^3343*500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267388717 500000000 44147824355889 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036038519/5000000000 : ℝ)^4367 ≤ (12794196874359/100000000000000 : ℝ)^3343 := by
    have hnat : (1036038519 : ℕ)^4367*100000000000000^3343 ≤ 12794196874359^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036038519 5000000000 12794196874359 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049283643/2000000000 : ℝ)^4367 ≤ (43057978751699/100000000000000 : ℝ)^3343 := by
    have hnat : (1049283643 : ℕ)^4367*100000000000000^3343 ≤ 43057978751699^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049283643 2000000000 43057978751699 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267388717/500000000 : ℝ), (-1036038519/5000000000 : ℝ), (1049283643/2000000000 : ℝ)] ![(44147824355889/100000000000000 : ℝ), (12794196874359/100000000000000 : ℝ), (43057978751699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267388717/500000000 : ℝ)|^4367 ≤ (44147824355889/100000000000000 : ℝ)^3343
        have hw : |(267388717/500000000 : ℝ)|=(267388717/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036038519/5000000000 : ℝ)|^4367 ≤ (12794196874359/100000000000000 : ℝ)^3343
        have hw : |(-1036038519/5000000000 : ℝ)|=(1036038519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049283643/2000000000 : ℝ)|^4367 ≤ (43057978751699/100000000000000 : ℝ)^3343
        have hw : |(1049283643/2000000000 : ℝ)|=(1049283643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s7_2 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347774403/10000000000 : ℝ)*x 0 + (5246418187/10000000000 : ℝ)*x 1 + (-2072076991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347774403/10000000000 : ℝ)^4367 ≤ (22073912517643/50000000000000 : ℝ)^3343 := by
    have hnat : (5347774403 : ℕ)^4367*50000000000000^3343 ≤ 22073912517643^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347774403 10000000000 22073912517643 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246418187/10000000000 : ℝ)^4367 ≤ (4305797845151/10000000000000 : ℝ)^3343 := by
    have hnat : (5246418187 : ℕ)^4367*10000000000000^3343 ≤ 4305797845151^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246418187 10000000000 4305797845151 10000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072076991/10000000000 : ℝ)^4367 ≤ (12794196495261/100000000000000 : ℝ)^3343 := by
    have hnat : (2072076991 : ℕ)^4367*100000000000000^3343 ≤ 12794196495261^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072076991 10000000000 12794196495261 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347774403/10000000000 : ℝ), (5246418187/10000000000 : ℝ), (-2072076991/10000000000 : ℝ)] ![(22073912517643/50000000000000 : ℝ), (4305797845151/10000000000000 : ℝ), (12794196495261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347774403/10000000000 : ℝ)|^4367 ≤ (22073912517643/50000000000000 : ℝ)^3343
        have hw : |(5347774403/10000000000 : ℝ)|=(5347774403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246418187/10000000000 : ℝ)|^4367 ≤ (4305797845151/10000000000000 : ℝ)^3343
        have hw : |(5246418187/10000000000 : ℝ)|=(5246418187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2072076991/10000000000 : ℝ)|^4367 ≤ (12794196495261/100000000000000 : ℝ)^3343
        have hw : |(-2072076991/10000000000 : ℝ)|=(2072076991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s7_3 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2154953541/5000000000 : ℝ)*x 0 + (4138331197/10000000000 : ℝ)*x 1 + (897584181/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154953541/5000000000 : ℝ)^4367 ≤ (16652182283833/50000000000000 : ℝ)^3343 := by
    have hnat : (2154953541 : ℕ)^4367*50000000000000^3343 ≤ 16652182283833^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154953541 5000000000 16652182283833 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4138331197/10000000000 : ℝ)^4367 ≤ (31583069490411/100000000000000 : ℝ)^3343 := by
    have hnat : (4138331197 : ℕ)^4367*100000000000000^3343 ≤ 31583069490411^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138331197 10000000000 31583069490411 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897584181/2000000000 : ℝ)^4367 ≤ (35112565926717/100000000000000 : ℝ)^3343 := by
    have hnat : (897584181 : ℕ)^4367*100000000000000^3343 ≤ 35112565926717^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897584181 2000000000 35112565926717 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154953541/5000000000 : ℝ), (4138331197/10000000000 : ℝ), (897584181/2000000000 : ℝ)] ![(16652182283833/50000000000000 : ℝ), (31583069490411/100000000000000 : ℝ), (35112565926717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154953541/5000000000 : ℝ)|^4367 ≤ (16652182283833/50000000000000 : ℝ)^3343
        have hw : |(2154953541/5000000000 : ℝ)|=(2154953541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4138331197/10000000000 : ℝ)|^4367 ≤ (31583069490411/100000000000000 : ℝ)^3343
        have hw : |(4138331197/10000000000 : ℝ)|=(4138331197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897584181/2000000000 : ℝ)|^4367 ≤ (35112565926717/100000000000000 : ℝ)^3343
        have hw : |(897584181/2000000000 : ℝ)|=(897584181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s7_4 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-497283389/2500000000 : ℝ)*x 0 + (655875557/1250000000 : ℝ)*x 1 + (5408738779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (497283389/2500000000 : ℝ)^4367 ≤ (12129321481767/100000000000000 : ℝ)^3343 := by
    have hnat : (497283389 : ℕ)^4367*100000000000000^3343 ≤ 12129321481767^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497283389 2500000000 12129321481767 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655875557/1250000000 : ℝ)^4367 ≤ (53830329977/125000000000 : ℝ)^3343 := by
    have hnat : (655875557 : ℕ)^4367*125000000000^3343 ≤ 53830329977^3343*1250000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655875557 1250000000 53830329977 125000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408738779/10000000000 : ℝ)^4367 ≤ (44806414532827/100000000000000 : ℝ)^3343 := by
    have hnat : (5408738779 : ℕ)^4367*100000000000000^3343 ≤ 44806414532827^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408738779 10000000000 44806414532827 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-497283389/2500000000 : ℝ), (655875557/1250000000 : ℝ), (5408738779/10000000000 : ℝ)] ![(12129321481767/100000000000000 : ℝ), (53830329977/125000000000 : ℝ), (44806414532827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-497283389/2500000000 : ℝ)|^4367 ≤ (12129321481767/100000000000000 : ℝ)^3343
        have hw : |(-497283389/2500000000 : ℝ)|=(497283389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655875557/1250000000 : ℝ)|^4367 ≤ (53830329977/125000000000 : ℝ)^3343
        have hw : |(655875557/1250000000 : ℝ)|=(655875557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408738779/10000000000 : ℝ)|^4367 ≤ (44806414532827/100000000000000 : ℝ)^3343
        have hw : |(5408738779/10000000000 : ℝ)|=(5408738779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s7_5 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305515123/10000000000 : ℝ)*x 0 + (-477439113/2500000000 : ℝ)*x 1 + (5408738841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305515123/10000000000 : ℝ)^4367 ≤ (21846325098727/50000000000000 : ℝ)^3343 := by
    have hnat : (5305515123 : ℕ)^4367*50000000000000^3343 ≤ 21846325098727^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305515123 10000000000 21846325098727 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (477439113/2500000000 : ℝ)^4367 ≤ (5750467292731/50000000000000 : ℝ)^3343 := by
    have hnat : (477439113 : ℕ)^4367*50000000000000^3343 ≤ 5750467292731^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477439113 2500000000 5750467292731 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408738841/10000000000 : ℝ)^4367 ≤ (8961283040753/20000000000000 : ℝ)^3343 := by
    have hnat : (5408738841 : ℕ)^4367*20000000000000^3343 ≤ 8961283040753^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408738841 10000000000 8961283040753 20000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305515123/10000000000 : ℝ), (-477439113/2500000000 : ℝ), (5408738841/10000000000 : ℝ)] ![(21846325098727/50000000000000 : ℝ), (5750467292731/50000000000000 : ℝ), (8961283040753/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305515123/10000000000 : ℝ)|^4367 ≤ (21846325098727/50000000000000 : ℝ)^3343
        have hw : |(5305515123/10000000000 : ℝ)|=(5305515123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-477439113/2500000000 : ℝ)|^4367 ≤ (5750467292731/50000000000000 : ℝ)^3343
        have hw : |(-477439113/2500000000 : ℝ)|=(477439113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408738841/10000000000 : ℝ)|^4367 ≤ (8961283040753/20000000000000 : ℝ)^3343
        have hw : |(5408738841/10000000000 : ℝ)|=(5408738841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s7_6 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305515121/10000000000 : ℝ)*x 0 + (5408738809/10000000000 : ℝ)*x 1 + (-1909756499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305515121/10000000000 : ℝ)^4367 ≤ (43692650175939/100000000000000 : ℝ)^3343 := by
    have hnat : (5305515121 : ℕ)^4367*100000000000000^3343 ≤ 43692650175939^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305515121 10000000000 43692650175939 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408738809/10000000000 : ℝ)^4367 ≤ (22403207428737/50000000000000 : ℝ)^3343 := by
    have hnat : (5408738809 : ℕ)^4367*50000000000000^3343 ≤ 22403207428737^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408738809 10000000000 22403207428737 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1909756499/10000000000 : ℝ)^4367 ≤ (2300186991041/20000000000000 : ℝ)^3343 := by
    have hnat : (1909756499 : ℕ)^4367*20000000000000^3343 ≤ 2300186991041^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909756499 10000000000 2300186991041 20000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305515121/10000000000 : ℝ), (5408738809/10000000000 : ℝ), (-1909756499/10000000000 : ℝ)] ![(43692650175939/100000000000000 : ℝ), (22403207428737/50000000000000 : ℝ), (2300186991041/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305515121/10000000000 : ℝ)|^4367 ≤ (43692650175939/100000000000000 : ℝ)^3343
        have hw : |(5305515121/10000000000 : ℝ)|=(5305515121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408738809/10000000000 : ℝ)|^4367 ≤ (22403207428737/50000000000000 : ℝ)^3343
        have hw : |(5408738809/10000000000 : ℝ)|=(5408738809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1909756499/10000000000 : ℝ)|^4367 ≤ (2300186991041/20000000000000 : ℝ)^3343
        have hw : |(-1909756499/10000000000 : ℝ)|=(1909756499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s7_7 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4309931803/10000000000 : ℝ)*x 0 + (4486662987/10000000000 : ℝ)*x 1 + (4139595609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309931803/10000000000 : ℝ)^4367 ≤ (33304614111289/100000000000000 : ℝ)^3343 := by
    have hnat : (4309931803 : ℕ)^4367*100000000000000^3343 ≤ 33304614111289^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309931803 10000000000 33304614111289 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4486662987/10000000000 : ℝ)^4367 ≤ (3509971016319/10000000000000 : ℝ)^3343 := by
    have hnat : (4486662987 : ℕ)^4367*10000000000000^3343 ≤ 3509971016319^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486662987 10000000000 3509971016319 10000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4139595609/10000000000 : ℝ)^4367 ≤ (1974729731817/6250000000000 : ℝ)^3343 := by
    have hnat : (4139595609 : ℕ)^4367*6250000000000^3343 ≤ 1974729731817^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139595609 10000000000 1974729731817 6250000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309931803/10000000000 : ℝ), (4486662987/10000000000 : ℝ), (4139595609/10000000000 : ℝ)] ![(33304614111289/100000000000000 : ℝ), (3509971016319/10000000000000 : ℝ), (1974729731817/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309931803/10000000000 : ℝ)|^4367 ≤ (33304614111289/100000000000000 : ℝ)^3343
        have hw : |(4309931803/10000000000 : ℝ)|=(4309931803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4486662987/10000000000 : ℝ)|^4367 ≤ (3509971016319/10000000000000 : ℝ)^3343
        have hw : |(4486662987/10000000000 : ℝ)|=(4486662987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4139595609/10000000000 : ℝ)|^4367 ≤ (1974729731817/6250000000000 : ℝ)^3343
        have hw : |(4139595609/10000000000 : ℝ)|=(4139595609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1407_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2259/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2949/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7373/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5647/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7373/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5647/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7373/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5647/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7373/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5647/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7373/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5647/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7373/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5647/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5647/50000 : ℝ) ^ (2183/512 : ℝ) ≤ (9154902696673921/100000000000000000000 : ℝ) := by
    have hpowers : (5647/50000 : ℝ)^2183 ≤ (9154902696673921/100000000000000000000 : ℝ)^512 := by
      have hnat : (5647 : ℕ)^2183*100000000000000000000^512 ≤ 9154902696673921^512*50000^2183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5647 50000 9154902696673921 100000000000000000000 2183 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5647/50000 : ℝ)) (X := (9154902696673921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7373/50000 : ℝ) ^ (2183/512 : ℝ) ≤ (2854300500321409/10000000000000000000 : ℝ) := by
    have hpowers : (7373/50000 : ℝ)^2183 ≤ (2854300500321409/10000000000000000000 : ℝ)^512 := by
      have hnat : (7373 : ℕ)^2183*10000000000000000000^512 ≤ 2854300500321409^512*50000^2183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7373 50000 2854300500321409 10000000000000000000 2183 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7373/50000 : ℝ)) (X := (2854300500321409/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009154902696673921/50000000000000000000 : ℝ) ≤ (10000429407397411/10000000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (50009154902696673921/50000000000000000000 : ℝ)^512 ≤ (10000429407397411/10000000000000000 : ℝ)^2183 := by
      have hnat : (50009154902696673921 : ℕ)^512*10000000000000000^2183 ≤ 10000429407397411^2183*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009154902696673921 50000000000000000000 10000429407397411 10000000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000429407397411/10000000000000000 : ℝ)) (X := (50009154902696673921/50000000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037697907699888011/100000000000000000000 : ℝ) ≤ (156263813090171/156250000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (100037697907699888011/100000000000000000000 : ℝ)^512 ≤ (156263813090171/156250000000000 : ℝ)^2183 := by
      have hnat : (100037697907699888011 : ℕ)^512*156250000000000^2183 ≤ 156263813090171^2183*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037697907699888011 100000000000000000000 156263813090171 156250000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156263813090171/156250000000000 : ℝ)) (X := (100037697907699888011/100000000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002854300500321409/5000000000000000000 : ℝ) ≤ (10001338668144477/10000000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (5002854300500321409/5000000000000000000 : ℝ)^512 ≤ (10001338668144477/10000000000000000 : ℝ)^2183 := by
      have hnat : (5002854300500321409 : ℕ)^512*10000000000000000^2183 ≤ 10001338668144477^2183*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002854300500321409 5000000000000000000 10001338668144477 10000000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001338668144477/10000000000000000 : ℝ)) (X := (5002854300500321409/5000000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9154902696673921/100000000000000000000 : ℝ) ≤ ((4313901640432312421/4315000000000000000 : ℝ)+2*(454630373533/345200000000000 : ℝ)*(5647/50000 : ℝ))^(2183/512 : ℝ) := by
    rw [show (4313901640432312421/4315000000000000000 : ℝ)+2*(454630373533/345200000000000 : ℝ)*(5647/50000 : ℝ)=(10000429407397411/10000000000000000 : ℝ) by norm_num, show 1+2*(9154902696673921/100000000000000000000 : ℝ)=(50009154902696673921/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2854300500321409/10000000000000000000 : ℝ)+(9154902696673921/100000000000000000000 : ℝ) ≤ ((4313901640432312421/4315000000000000000 : ℝ)+(454630373533/345200000000000 : ℝ)*((7373/50000 : ℝ)+(5647/50000 : ℝ)))^(2183/512 : ℝ) := by
    rw [show (4313901640432312421/4315000000000000000 : ℝ)+(454630373533/345200000000000 : ℝ)*((7373/50000 : ℝ)+(5647/50000 : ℝ))=(156263813090171/156250000000000 : ℝ) by norm_num, show 1+(2854300500321409/10000000000000000000 : ℝ)+(9154902696673921/100000000000000000000 : ℝ)=(100037697907699888011/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2854300500321409/10000000000000000000 : ℝ) ≤ ((4313901640432312421/4315000000000000000 : ℝ)+2*(454630373533/345200000000000 : ℝ)*(7373/50000 : ℝ))^(2183/512 : ℝ) := by
    rw [show (4313901640432312421/4315000000000000000 : ℝ)+2*(454630373533/345200000000000 : ℝ)*(7373/50000 : ℝ)=(10001338668144477/10000000000000000 : ℝ) by norm_num, show 1+2*(2854300500321409/10000000000000000000 : ℝ)=(5002854300500321409/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4313901640432312421/4315000000000000000 : ℝ)*(X 1 0+X 2 0)+(454630373533/345200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (5647/50000 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (4313901640432312421/4315000000000000000 : ℝ)) (alpha := (454630373533/345200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4313901640432312421/4315000000000000000 : ℝ)*(X 0 1+X 2 1)+(454630373533/345200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (5647/50000 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (4313901640432312421/4315000000000000000 : ℝ)) (alpha := (454630373533/345200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4313901640432312421/4315000000000000000 : ℝ)*(X 0 2+X 1 2)+(454630373533/345200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (5647/50000 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (4313901640432312421/4315000000000000000 : ℝ)) (alpha := (454630373533/345200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1989121997/10000000000 : ℝ)*X 0 0+(5409328061/10000000000 : ℝ)*X 0 1+(1311604559/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267388717/500000000 : ℝ)*X 1 0+(-1036038519/5000000000 : ℝ)*X 1 1+(1049283643/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347774403/10000000000 : ℝ)*X 2 0+(5246418187/10000000000 : ℝ)*X 2 1+(-2072076991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2154953541/5000000000 : ℝ)*X 0 0+(4138331197/10000000000 : ℝ)*X 0 1+(897584181/2000000000 : ℝ)*X 0 2+(2154953541/5000000000 : ℝ)*X 1 0+(4138331197/10000000000 : ℝ)*X 1 1+(897584181/2000000000 : ℝ)*X 1 2+(2154953541/5000000000 : ℝ)*X 2 0+(4138331197/10000000000 : ℝ)*X 2 1+(897584181/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-497283389/2500000000 : ℝ)*X 0 0+(655875557/1250000000 : ℝ)*X 0 1+(5408738779/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305515123/10000000000 : ℝ)*X 1 0+(-477439113/2500000000 : ℝ)*X 1 1+(5408738841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305515121/10000000000 : ℝ)*X 2 0+(5408738809/10000000000 : ℝ)*X 2 1+(-1909756499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4309931803/10000000000 : ℝ)*X 0 0+(4486662987/10000000000 : ℝ)*X 0 1+(4139595609/10000000000 : ℝ)*X 0 2+(4309931803/10000000000 : ℝ)*X 1 0+(4486662987/10000000000 : ℝ)*X 1 1+(4139595609/10000000000 : ℝ)*X 1 2+(4309931803/10000000000 : ℝ)*X 2 0+(4486662987/10000000000 : ℝ)*X 2 1+(4139595609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46417804874682733476168729/13484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10438953/2000000000000 : ℝ)*(base19) + (263849807/50000000000000 : ℝ)*(base23) + (35595807/100000000000000 : ℝ)*(lower2) + (2375043/5000000000000 : ℝ)*(upper3) + (70501797/100000000000000 : ℝ)*(upper5) + (281215374785621/6250000000000 : ℝ)*(major0) + (281215374785621/6250000000000 : ℝ)*(major1) + (281215374785621/6250000000000 : ℝ)*(major2) + (767296797388443/12500000000000 : ℝ)*(sp0) + (6138385421969283/100000000000000 : ℝ)*(sp1) + (6138385416217319/100000000000000 : ℝ)*(sp2) + (174591119606/6103515625 : ℝ)*(sp3) + (11564809389/100000000000000 : ℝ)*(sp4) + (1257713389/25000000000000 : ℝ)*(sp7) + (2860505934478259/100000000000000 : ℝ)*(f.failure) + (6138385943916933/100000000000000 : ℝ)*(f.sum) + (896778337847/1078750000000000000000000000 : ℝ)*base66 + (373050404402785941/26968750000000000000000000000000 : ℝ)*base67 + (76157123065504691/26968750000000000000000000000000 : ℝ)*base69 + (4378385095160941/26968750000000000000000000000000 : ℝ)*base71 + (7280092470209/2157500000000000000000000000 : ℝ)*base74 + (150932798250192191/26968750000000000000000000000000 : ℝ)*base75 + (150365264024557809/26968750000000000000000000000000 : ℝ)*base78 + (632588186079192191/26968750000000000000000000000000 : ℝ)*base79 + (17667273566453/4315000000000000000000000000 : ℝ)*base82 + (56117601/10000000000000000000000 : ℝ)*base90 + (56117601/10000000000000000000000 : ℝ)*base92 + (56117601/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (362884893935582757259908621/43150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1227094729/100000000000000 : ℝ)*(base19) + (660539837/50000000000000 : ℝ)*(base23) + (80331761/20000000000000 : ℝ)*(lower1) + (12504171/6250000000000 : ℝ)*(upper3) + (11137279/25000000000000 : ℝ)*(lower4) + (149505931/100000000000000 : ℝ)*(upper5) + (906422566050933/20000000000000 : ℝ)*(major0) + (906422566050933/20000000000000 : ℝ)*(major1) + (906422566050933/20000000000000 : ℝ)*(major2) + (387567981/25000000000000 : ℝ)*(sp2) + (3091475814289441/50000000000000 : ℝ)*(sp4) + (6182950401484153/100000000000000 : ℝ)*(sp5) + (6182948757227283/100000000000000 : ℝ)*(sp6) + (1440636875801097/50000000000000 : ℝ)*(sp7) + (1440636875801097/50000000000000 : ℝ)*(f.failure) + (3091475814289441/50000000000000 : ℝ)*(f.sum) + (24219938161991/3452000000000000000000000000 : ℝ)*base66 + (5106736795412848707/86300000000000000000000000000000 : ℝ)*base68 + (53661076951293/86300000000000000000000000000000 : ℝ)*base69 + (6956723381541851293/86300000000000000000000000000000 : ℝ)*base71 + (4052980426251/690400000000000000000000000 : ℝ)*base74 + (3569143637428451293/86300000000000000000000000000000 : ℝ)*base75 + (418531731452948707/86300000000000000000000000000000 : ℝ)*base78 + (1722759591026251293/86300000000000000000000000000000 : ℝ)*base79 + (774271245451/3452000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (46920717/5000000000000000000000 : ℝ)*base89 + (46920717/5000000000000000000000 : ℝ)*base91 + (46920717/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1407_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1407_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1407_box_0 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-365370679/2000000000 : ℝ)*x 0 + (1077439333/2000000000 : ℝ)*x 1 + (1346799133/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (365370679/2000000000 : ℝ)^4367 ≤ (2170625493427/20000000000000 : ℝ)^3343 := by
    have hnat : (365370679 : ℕ)^4367*20000000000000^3343 ≤ 2170625493427^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365370679 2000000000 2170625493427 20000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077439333/2000000000 : ℝ)^4367 ≤ (44573436980713/100000000000000 : ℝ)^3343 := by
    have hnat : (1077439333 : ℕ)^4367*100000000000000^3343 ≤ 44573436980713^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077439333 2000000000 44573436980713 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346799133/2500000000 : ℝ)^4367 ≤ (55716794429/125000000000 : ℝ)^3343 := by
    have hnat : (1346799133 : ℕ)^4367*125000000000^3343 ≤ 55716794429^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346799133 2500000000 55716794429 125000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-365370679/2000000000 : ℝ), (1077439333/2000000000 : ℝ), (1346799133/2500000000 : ℝ)] ![(2170625493427/20000000000000 : ℝ), (44573436980713/100000000000000 : ℝ), (55716794429/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-365370679/2000000000 : ℝ)|^4367 ≤ (2170625493427/20000000000000 : ℝ)^3343
        have hw : |(-365370679/2000000000 : ℝ)|=(365370679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077439333/2000000000 : ℝ)|^4367 ≤ (44573436980713/100000000000000 : ℝ)^3343
        have hw : |(1077439333/2000000000 : ℝ)|=(1077439333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346799133/2500000000 : ℝ)|^4367 ≤ (55716794429/125000000000 : ℝ)^3343
        have hw : |(1346799133/2500000000 : ℝ)|=(1346799133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_box_1 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285891487/10000000000 : ℝ)*x 0 + (-1965940361/10000000000 : ℝ)*x 1 + (673399561/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285891487/10000000000 : ℝ)^4367 ≤ (679400948529/1562500000000 : ℝ)^3343 := by
    have hnat : (5285891487 : ℕ)^4367*1562500000000^3343 ≤ 679400948529^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285891487 10000000000 679400948529 1562500000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1965940361/10000000000 : ℝ)^4367 ≤ (5972452103289/50000000000000 : ℝ)^3343 := by
    have hnat : (1965940361 : ℕ)^4367*50000000000000^3343 ≤ 5972452103289^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965940361 10000000000 5972452103289 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673399561/1250000000 : ℝ)^4367 ≤ (2785839691727/6250000000000 : ℝ)^3343 := by
    have hnat : (673399561 : ℕ)^4367*6250000000000^3343 ≤ 2785839691727^3343*1250000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673399561 1250000000 2785839691727 6250000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285891487/10000000000 : ℝ), (-1965940361/10000000000 : ℝ), (673399561/1250000000 : ℝ)] ![(679400948529/1562500000000 : ℝ), (5972452103289/50000000000000 : ℝ), (2785839691727/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285891487/10000000000 : ℝ)|^4367 ≤ (679400948529/1562500000000 : ℝ)^3343
        have hw : |(5285891487/10000000000 : ℝ)|=(5285891487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1965940361/10000000000 : ℝ)|^4367 ≤ (5972452103289/50000000000000 : ℝ)^3343
        have hw : |(-1965940361/10000000000 : ℝ)|=(1965940361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673399561/1250000000 : ℝ)|^4367 ≤ (2785839691727/6250000000000 : ℝ)^3343
        have hw : |(673399561/1250000000 : ℝ)|=(673399561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_box_2 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642945387/5000000000 : ℝ)*x 0 + (5387196817/10000000000 : ℝ)*x 1 + (-982970439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642945387/5000000000 : ℝ)^4367 ≤ (10870413261043/25000000000000 : ℝ)^3343 := by
    have hnat : (2642945387 : ℕ)^4367*25000000000000^3343 ≤ 10870413261043^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642945387 5000000000 10870413261043 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387196817/10000000000 : ℝ)^4367 ≤ (8914687724717/20000000000000 : ℝ)^3343 := by
    have hnat : (5387196817 : ℕ)^4367*20000000000000^3343 ≤ 8914687724717^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387196817 10000000000 8914687724717 20000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (982970439/5000000000 : ℝ)^4367 ≤ (11944908310033/100000000000000 : ℝ)^3343 := by
    have hnat : (982970439 : ℕ)^4367*100000000000000^3343 ≤ 11944908310033^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982970439 5000000000 11944908310033 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642945387/5000000000 : ℝ), (5387196817/10000000000 : ℝ), (-982970439/5000000000 : ℝ)] ![(10870413261043/25000000000000 : ℝ), (8914687724717/20000000000000 : ℝ), (11944908310033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642945387/5000000000 : ℝ)|^4367 ≤ (10870413261043/25000000000000 : ℝ)^3343
        have hw : |(2642945387/5000000000 : ℝ)|=(2642945387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387196817/10000000000 : ℝ)|^4367 ≤ (8914687724717/20000000000000 : ℝ)^3343
        have hw : |(5387196817/10000000000 : ℝ)|=(5387196817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-982970439/5000000000 : ℝ)|^4367 ≤ (11944908310033/100000000000000 : ℝ)^3343
        have hw : |(-982970439/5000000000 : ℝ)|=(982970439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_box_3 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2228327051/5000000000 : ℝ)*x 0 + (1060071411/2500000000 : ℝ)*x 1 + (1060071441/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2228327051/5000000000 : ℝ)^4367 ≤ (34793350942809/100000000000000 : ℝ)^3343 := by
    have hnat : (2228327051 : ℕ)^4367*100000000000000^3343 ≤ 34793350942809^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228327051 5000000000 34793350942809 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060071411/2500000000 : ℝ)^4367 ≤ (4075415489979/12500000000000 : ℝ)^3343 := by
    have hnat : (1060071411 : ℕ)^4367*12500000000000^3343 ≤ 4075415489979^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060071411 2500000000 4075415489979 12500000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060071441/2500000000 : ℝ)^4367 ≤ (32603325125131/100000000000000 : ℝ)^3343 := by
    have hnat : (1060071441 : ℕ)^4367*100000000000000^3343 ≤ 32603325125131^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060071441 2500000000 32603325125131 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2228327051/5000000000 : ℝ), (1060071411/2500000000 : ℝ), (1060071441/2500000000 : ℝ)] ![(34793350942809/100000000000000 : ℝ), (4075415489979/12500000000000 : ℝ), (32603325125131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2228327051/5000000000 : ℝ)|^4367 ≤ (34793350942809/100000000000000 : ℝ)^3343
        have hw : |(2228327051/5000000000 : ℝ)|=(2228327051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060071411/2500000000 : ℝ)|^4367 ≤ (4075415489979/12500000000000 : ℝ)^3343
        have hw : |(1060071411/2500000000 : ℝ)|=(1060071411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060071441/2500000000 : ℝ)|^4367 ≤ (32603325125131/100000000000000 : ℝ)^3343
        have hw : |(1060071441/2500000000 : ℝ)|=(1060071441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_box_4 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1077065061/5000000000 : ℝ)*x 0 + (2633091299/5000000000 : ℝ)*x 1 + (2633091287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077065061/5000000000 : ℝ)^4367 ≤ (6730004167891/50000000000000 : ℝ)^3343 := by
    have hnat : (1077065061 : ℕ)^4367*50000000000000^3343 ≤ 6730004167891^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077065061 5000000000 6730004167891 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633091299/5000000000 : ℝ)^4367 ≤ (21634997975603/50000000000000 : ℝ)^3343 := by
    have hnat : (2633091299 : ℕ)^4367*50000000000000^3343 ≤ 21634997975603^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633091299 5000000000 21634997975603 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633091287/5000000000 : ℝ)^4367 ≤ (10817498923401/25000000000000 : ℝ)^3343 := by
    have hnat : (2633091287 : ℕ)^4367*25000000000000^3343 ≤ 10817498923401^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633091287 5000000000 10817498923401 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1077065061/5000000000 : ℝ), (2633091299/5000000000 : ℝ), (2633091287/5000000000 : ℝ)] ![(6730004167891/50000000000000 : ℝ), (21634997975603/50000000000000 : ℝ), (10817498923401/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1077065061/5000000000 : ℝ)|^4367 ≤ (6730004167891/50000000000000 : ℝ)^3343
        have hw : |(-1077065061/5000000000 : ℝ)|=(1077065061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633091299/5000000000 : ℝ)|^4367 ≤ (21634997975603/50000000000000 : ℝ)^3343
        have hw : |(2633091299/5000000000 : ℝ)|=(2633091299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633091287/5000000000 : ℝ)|^4367 ≤ (10817498923401/25000000000000 : ℝ)^3343
        have hw : |(2633091287/5000000000 : ℝ)|=(2633091287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_box_5 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370658871/10000000000 : ℝ)*x 0 + (-1007465879/5000000000 : ℝ)*x 1 + (5266182829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370658871/10000000000 : ℝ)^4367 ≤ (22197387261531/50000000000000 : ℝ)^3343 := by
    have hnat : (5370658871 : ℕ)^4367*50000000000000^3343 ≤ 22197387261531^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370658871 10000000000 22197387261531 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007465879/5000000000 : ℝ)^4367 ≤ (6167613517893/50000000000000 : ℝ)^3343 := by
    have hnat : (1007465879 : ℕ)^4367*50000000000000^3343 ≤ 6167613517893^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007465879 5000000000 6167613517893 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266182829/10000000000 : ℝ)^4367 ≤ (1352187450957/3125000000000 : ℝ)^3343 := by
    have hnat : (5266182829 : ℕ)^4367*3125000000000^3343 ≤ 1352187450957^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266182829 10000000000 1352187450957 3125000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370658871/10000000000 : ℝ), (-1007465879/5000000000 : ℝ), (5266182829/10000000000 : ℝ)] ![(22197387261531/50000000000000 : ℝ), (6167613517893/50000000000000 : ℝ), (1352187450957/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370658871/10000000000 : ℝ)|^4367 ≤ (22197387261531/50000000000000 : ℝ)^3343
        have hw : |(5370658871/10000000000 : ℝ)|=(5370658871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1007465879/5000000000 : ℝ)|^4367 ≤ (6167613517893/50000000000000 : ℝ)^3343
        have hw : |(-1007465879/5000000000 : ℝ)|=(1007465879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266182829/10000000000 : ℝ)|^4367 ≤ (1352187450957/3125000000000 : ℝ)^3343
        have hw : |(5266182829/10000000000 : ℝ)|=(5266182829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_box_6 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370658919/10000000000 : ℝ)*x 0 + (2633091239/5000000000 : ℝ)*x 1 + (-503733041/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370658919/10000000000 : ℝ)^4367 ≤ (1387336720043/3125000000000 : ℝ)^3343 := by
    have hnat : (5370658919 : ℕ)^4367*3125000000000^3343 ≤ 1387336720043^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370658919 10000000000 1387336720043 3125000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633091239/5000000000 : ℝ)^4367 ≤ (43269994663197/100000000000000 : ℝ)^3343 := by
    have hnat : (2633091239 : ℕ)^4367*100000000000000^3343 ≤ 43269994663197^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633091239 5000000000 43269994663197 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503733041/2500000000 : ℝ)^4367 ≤ (12335230282617/100000000000000 : ℝ)^3343 := by
    have hnat : (503733041 : ℕ)^4367*100000000000000^3343 ≤ 12335230282617^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503733041 2500000000 12335230282617 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370658919/10000000000 : ℝ), (2633091239/5000000000 : ℝ), (-503733041/2500000000 : ℝ)] ![(1387336720043/3125000000000 : ℝ), (43269994663197/100000000000000 : ℝ), (12335230282617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370658919/10000000000 : ℝ)|^4367 ≤ (1387336720043/3125000000000 : ℝ)^3343
        have hw : |(5370658919/10000000000 : ℝ)|=(5370658919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633091239/5000000000 : ℝ)|^4367 ≤ (43269994663197/100000000000000 : ℝ)^3343
        have hw : |(2633091239/5000000000 : ℝ)|=(2633091239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-503733041/2500000000 : ℝ)|^4367 ≤ (12335230282617/100000000000000 : ℝ)^3343
        have hw : |(-503733041/2500000000 : ℝ)|=(503733041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_box_7 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2081071009/5000000000 : ℝ)*x 0 + (2193745083/5000000000 : ℝ)*x 1 + (4387490257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2081071009/5000000000 : ℝ)^4367 ≤ (31820661760991/100000000000000 : ℝ)^3343 := by
    have hnat : (2081071009 : ℕ)^4367*100000000000000^3343 ≤ 31820661760991^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081071009 5000000000 31820661760991 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2193745083/5000000000 : ℝ)^4367 ≤ (3408966865503/10000000000000 : ℝ)^3343 := by
    have hnat : (2193745083 : ℕ)^4367*10000000000000^3343 ≤ 3408966865503^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193745083 5000000000 3408966865503 10000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4387490257/10000000000 : ℝ)^4367 ≤ (34089669578653/100000000000000 : ℝ)^3343 := by
    have hnat : (4387490257 : ℕ)^4367*100000000000000^3343 ≤ 34089669578653^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387490257 10000000000 34089669578653 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2081071009/5000000000 : ℝ), (2193745083/5000000000 : ℝ), (4387490257/10000000000 : ℝ)] ![(31820661760991/100000000000000 : ℝ), (3408966865503/10000000000000 : ℝ), (34089669578653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2081071009/5000000000 : ℝ)|^4367 ≤ (31820661760991/100000000000000 : ℝ)^3343
        have hw : |(2081071009/5000000000 : ℝ)|=(2081071009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2193745083/5000000000 : ℝ)|^4367 ≤ (3408966865503/10000000000000 : ℝ)^3343
        have hw : |(2193745083/5000000000 : ℝ)|=(2193745083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4387490257/10000000000 : ℝ)|^4367 ≤ (34089669578653/100000000000000 : ℝ)^3343
        have hw : |(4387490257/10000000000 : ℝ)|=(4387490257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_box_8 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-417049023/2000000000 : ℝ)*x 0 + (5182576797/10000000000 : ℝ)*x 1 + (2700591969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417049023/2000000000 : ℝ)^4367 ≤ (806282047809/6250000000000 : ℝ)^3343 := by
    have hnat : (417049023 : ℕ)^4367*6250000000000^3343 ≤ 806282047809^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417049023 2000000000 806282047809 6250000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182576797/10000000000 : ℝ)^4367 ≤ (42374810565501/100000000000000 : ℝ)^3343 := by
    have hnat : (5182576797 : ℕ)^4367*100000000000000^3343 ≤ 42374810565501^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182576797 10000000000 42374810565501 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700591969/5000000000 : ℝ)^4367 ≤ (44724676650371/100000000000000 : ℝ)^3343 := by
    have hnat : (2700591969 : ℕ)^4367*100000000000000^3343 ≤ 44724676650371^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700591969 5000000000 44724676650371 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417049023/2000000000 : ℝ), (5182576797/10000000000 : ℝ), (2700591969/5000000000 : ℝ)] ![(806282047809/6250000000000 : ℝ), (42374810565501/100000000000000 : ℝ), (44724676650371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417049023/2000000000 : ℝ)|^4367 ≤ (806282047809/6250000000000 : ℝ)^3343
        have hw : |(-417049023/2000000000 : ℝ)|=(417049023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182576797/10000000000 : ℝ)|^4367 ≤ (42374810565501/100000000000000 : ℝ)^3343
        have hw : |(5182576797/10000000000 : ℝ)|=(5182576797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700591969/5000000000 : ℝ)|^4367 ≤ (44724676650371/100000000000000 : ℝ)^3343
        have hw : |(2700591969/5000000000 : ℝ)|=(2700591969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_box_9 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276089373/10000000000 : ℝ)*x 0 + (-392029961/2000000000 : ℝ)*x 1 + (5401183777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276089373/10000000000 : ℝ)^4367 ≤ (10844090015353/25000000000000 : ℝ)^3343 := by
    have hnat : (5276089373 : ℕ)^4367*25000000000000^3343 ≤ 10844090015353^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276089373 10000000000 10844090015353 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (392029961/2000000000 : ℝ)^4367 ≤ (11898965017921/100000000000000 : ℝ)^3343 := by
    have hnat : (392029961 : ℕ)^4367*100000000000000^3343 ≤ 11898965017921^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392029961 2000000000 11898965017921 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401183777/10000000000 : ℝ)^4367 ≤ (44724674908841/100000000000000 : ℝ)^3343 := by
    have hnat : (5401183777 : ℕ)^4367*100000000000000^3343 ≤ 44724674908841^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401183777 10000000000 44724674908841 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276089373/10000000000 : ℝ), (-392029961/2000000000 : ℝ), (5401183777/10000000000 : ℝ)] ![(10844090015353/25000000000000 : ℝ), (11898965017921/100000000000000 : ℝ), (44724674908841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276089373/10000000000 : ℝ)|^4367 ≤ (10844090015353/25000000000000 : ℝ)^3343
        have hw : |(5276089373/10000000000 : ℝ)|=(5276089373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-392029961/2000000000 : ℝ)|^4367 ≤ (11898965017921/100000000000000 : ℝ)^3343
        have hw : |(-392029961/2000000000 : ℝ)|=(392029961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401183777/10000000000 : ℝ)|^4367 ≤ (44724674908841/100000000000000 : ℝ)^3343
        have hw : |(5401183777/10000000000 : ℝ)|=(5401183777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_box_10 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276088819/10000000000 : ℝ)*x 0 + (1080236843/2000000000 : ℝ)*x 1 + (-980074979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276088819/10000000000 : ℝ)^4367 ≤ (21688177055839/50000000000000 : ℝ)^3343 := by
    have hnat : (5276088819 : ℕ)^4367*50000000000000^3343 ≤ 21688177055839^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276088819 10000000000 21688177055839 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080236843/2000000000 : ℝ)^4367 ≤ (11181169911667/25000000000000 : ℝ)^3343 := by
    have hnat : (1080236843 : ℕ)^4367*25000000000000^3343 ≤ 11181169911667^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080236843 2000000000 11181169911667 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (980074979/5000000000 : ℝ)^4367 ≤ (11898966231193/100000000000000 : ℝ)^3343 := by
    have hnat : (980074979 : ℕ)^4367*100000000000000^3343 ≤ 11898966231193^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980074979 5000000000 11898966231193 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276088819/10000000000 : ℝ), (1080236843/2000000000 : ℝ), (-980074979/5000000000 : ℝ)] ![(21688177055839/50000000000000 : ℝ), (11181169911667/25000000000000 : ℝ), (11898966231193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276088819/10000000000 : ℝ)|^4367 ≤ (21688177055839/50000000000000 : ℝ)^3343
        have hw : |(5276088819/10000000000 : ℝ)|=(5276088819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080236843/2000000000 : ℝ)|^4367 ≤ (11181169911667/25000000000000 : ℝ)^3343
        have hw : |(1080236843/2000000000 : ℝ)|=(1080236843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-980074979/5000000000 : ℝ)|^4367 ≤ (11898966231193/100000000000000 : ℝ)^3343
        have hw : |(-980074979/5000000000 : ℝ)|=(980074979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_box_11 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1122533997/2500000000 : ℝ)*x 0 + (1055814483/2500000000 : ℝ)*x 1 + (2111628627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1122533997/2500000000 : ℝ)^4367 ≤ (2195950404939/6250000000000 : ℝ)^3343 := by
    have hnat : (1122533997 : ℕ)^4367*6250000000000^3343 ≤ 2195950404939^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122533997 2500000000 2195950404939 6250000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055814483/2500000000 : ℝ)^4367 ≤ (32432400157941/100000000000000 : ℝ)^3343 := by
    have hnat : (1055814483 : ℕ)^4367*100000000000000^3343 ≤ 32432400157941^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055814483 2500000000 32432400157941 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111628627/5000000000 : ℝ)^4367 ≤ (3243239335639/10000000000000 : ℝ)^3343 := by
    have hnat : (2111628627 : ℕ)^4367*10000000000000^3343 ≤ 3243239335639^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111628627 5000000000 3243239335639 10000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1122533997/2500000000 : ℝ), (1055814483/2500000000 : ℝ), (2111628627/5000000000 : ℝ)] ![(2195950404939/6250000000000 : ℝ), (32432400157941/100000000000000 : ℝ), (3243239335639/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1122533997/2500000000 : ℝ)|^4367 ≤ (2195950404939/6250000000000 : ℝ)^3343
        have hw : |(1122533997/2500000000 : ℝ)|=(1122533997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055814483/2500000000 : ℝ)|^4367 ≤ (32432400157941/100000000000000 : ℝ)^3343
        have hw : |(1055814483/2500000000 : ℝ)|=(1055814483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111628627/5000000000 : ℝ)|^4367 ≤ (3243239335639/10000000000000 : ℝ)^3343
        have hw : |(2111628627/5000000000 : ℝ)|=(2111628627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_box_12 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1895956533/10000000000 : ℝ)*x 0 + (2734367467/5000000000 : ℝ)*x 1 + (1313767043/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1895956533/10000000000 : ℝ)^4367 ≤ (2848123191779/25000000000000 : ℝ)^3343 := by
    have hnat : (1895956533 : ℕ)^4367*25000000000000^3343 ≤ 2848123191779^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895956533 10000000000 2848123191779 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734367467/5000000000 : ℝ)^4367 ≤ (11364192098859/25000000000000 : ℝ)^3343 := by
    have hnat : (2734367467 : ℕ)^4367*25000000000000^3343 ≤ 11364192098859^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734367467 5000000000 11364192098859 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313767043/2500000000 : ℝ)^4367 ≤ (43150738829759/100000000000000 : ℝ)^3343 := by
    have hnat : (1313767043 : ℕ)^4367*100000000000000^3343 ≤ 43150738829759^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313767043 2500000000 43150738829759 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1895956533/10000000000 : ℝ), (2734367467/5000000000 : ℝ), (1313767043/2500000000 : ℝ)] ![(2848123191779/25000000000000 : ℝ), (11364192098859/25000000000000 : ℝ), (43150738829759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1895956533/10000000000 : ℝ)|^4367 ≤ (2848123191779/25000000000000 : ℝ)^3343
        have hw : |(-1895956533/10000000000 : ℝ)|=(1895956533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734367467/5000000000 : ℝ)|^4367 ≤ (11364192098859/25000000000000 : ℝ)^3343
        have hw : |(2734367467/5000000000 : ℝ)|=(2734367467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313767043/2500000000 : ℝ)|^4367 ≤ (43150738829759/100000000000000 : ℝ)^3343
        have hw : |(1313767043/2500000000 : ℝ)|=(1313767043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_box_13 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075688423/2000000000 : ℝ)*x 0 + (-1009665207/5000000000 : ℝ)*x 1 + (1313767221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075688423/2000000000 : ℝ)^4367 ≤ (22239419072563/50000000000000 : ℝ)^3343 := by
    have hnat : (1075688423 : ℕ)^4367*50000000000000^3343 ≤ 22239419072563^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075688423 2000000000 22239419072563 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1009665207/5000000000 : ℝ)^4367 ≤ (1237041537143/10000000000000 : ℝ)^3343 := by
    have hnat : (1009665207 : ℕ)^4367*10000000000000^3343 ≤ 1237041537143^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009665207 5000000000 1237041537143 10000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313767221/2500000000 : ℝ)^4367 ≤ (10787686616751/25000000000000 : ℝ)^3343 := by
    have hnat : (1313767221 : ℕ)^4367*25000000000000^3343 ≤ 10787686616751^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313767221 2500000000 10787686616751 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075688423/2000000000 : ℝ), (-1009665207/5000000000 : ℝ), (1313767221/2500000000 : ℝ)] ![(22239419072563/50000000000000 : ℝ), (1237041537143/10000000000000 : ℝ), (10787686616751/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075688423/2000000000 : ℝ)|^4367 ≤ (22239419072563/50000000000000 : ℝ)^3343
        have hw : |(1075688423/2000000000 : ℝ)|=(1075688423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1009665207/5000000000 : ℝ)|^4367 ≤ (1237041537143/10000000000000 : ℝ)^3343
        have hw : |(-1009665207/5000000000 : ℝ)|=(1009665207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313767221/2500000000 : ℝ)|^4367 ≤ (10787686616751/25000000000000 : ℝ)^3343
        have hw : |(1313767221/2500000000 : ℝ)|=(1313767221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_box_14 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215137739/400000000 : ℝ)*x 0 + (1313766959/2500000000 : ℝ)*x 1 + (-2019329983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215137739/400000000 : ℝ)^4367 ≤ (22239426418593/50000000000000 : ℝ)^3343 := by
    have hnat : (215137739 : ℕ)^4367*50000000000000^3343 ≤ 22239426418593^3343*400000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215137739 400000000 22239426418593 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313766959/2500000000 : ℝ)^4367 ≤ (21575367612833/50000000000000 : ℝ)^3343 := by
    have hnat : (1313766959 : ℕ)^4367*50000000000000^3343 ≤ 21575367612833^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313766959 2500000000 21575367612833 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2019329983/10000000000 : ℝ)^4367 ≤ (193287686287/1562500000000 : ℝ)^3343 := by
    have hnat : (2019329983 : ℕ)^4367*1562500000000^3343 ≤ 193287686287^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019329983 10000000000 193287686287 1562500000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215137739/400000000 : ℝ), (1313766959/2500000000 : ℝ), (-2019329983/10000000000 : ℝ)] ![(22239426418593/50000000000000 : ℝ), (21575367612833/50000000000000 : ℝ), (193287686287/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215137739/400000000 : ℝ)|^4367 ≤ (22239426418593/50000000000000 : ℝ)^3343
        have hw : |(215137739/400000000 : ℝ)|=(215137739/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313766959/2500000000 : ℝ)|^4367 ≤ (21575367612833/50000000000000 : ℝ)^3343
        have hw : |(1313766959/2500000000 : ℝ)|=(1313766959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2019329983/10000000000 : ℝ)|^4367 ≤ (193287686287/1562500000000 : ℝ)^3343
        have hw : |(-2019329983/10000000000 : ℝ)|=(2019329983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_box_15 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2067321617/5000000000 : ℝ)*x 0 + (137531211/312500000 : ℝ)*x 1 + (4400999733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067321617/5000000000 : ℝ)^4367 ≤ (15773153574281/50000000000000 : ℝ)^3343 := by
    have hnat : (2067321617 : ℕ)^4367*50000000000000^3343 ≤ 15773153574281^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067321617 5000000000 15773153574281 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137531211/312500000 : ℝ)^4367 ≤ (34226841431393/100000000000000 : ℝ)^3343 := by
    have hnat : (137531211 : ℕ)^4367*100000000000000^3343 ≤ 34226841431393^3343*312500000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137531211 312500000 34226841431393 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4400999733/10000000000 : ℝ)^4367 ≤ (6845370279527/20000000000000 : ℝ)^3343 := by
    have hnat : (4400999733 : ℕ)^4367*20000000000000^3343 ≤ 6845370279527^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4400999733 10000000000 6845370279527 20000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2067321617/5000000000 : ℝ), (137531211/312500000 : ℝ), (4400999733/10000000000 : ℝ)] ![(15773153574281/50000000000000 : ℝ), (34226841431393/100000000000000 : ℝ), (6845370279527/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2067321617/5000000000 : ℝ)|^4367 ≤ (15773153574281/50000000000000 : ℝ)^3343
        have hw : |(2067321617/5000000000 : ℝ)|=(2067321617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137531211/312500000 : ℝ)|^4367 ≤ (34226841431393/100000000000000 : ℝ)^3343
        have hw : |(137531211/312500000 : ℝ)|=(137531211/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4400999733/10000000000 : ℝ)|^4367 ≤ (6845370279527/20000000000000 : ℝ)^3343
        have hw : |(4400999733/10000000000 : ℝ)|=(4400999733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1407_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31443/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59069/100000 : ℝ) ∧ (40163/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42301/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2949/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2259/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2949/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2259/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2949/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2259/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2949/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2259/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2949/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2259/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2949/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2259/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2259/20000 : ℝ) ^ (2183/512 : ℝ) ≤ (286198728853791/3125000000000000000 : ℝ) := by
    have hpowers : (2259/20000 : ℝ)^2183 ≤ (286198728853791/3125000000000000000 : ℝ)^512 := by
      have hnat : (2259 : ℕ)^2183*3125000000000000000^512 ≤ 286198728853791^512*20000^2183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2259 20000 286198728853791 3125000000000000000 2183 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2259/20000 : ℝ)) (X := (286198728853791/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2949/20000 : ℝ) ^ (2183/512 : ℝ) ≤ (713368824149781/2500000000000000000 : ℝ) := by
    have hpowers : (2949/20000 : ℝ)^2183 ≤ (713368824149781/2500000000000000000 : ℝ)^512 := by
      have hnat : (2949 : ℕ)^2183*2500000000000000000^512 ≤ 713368824149781^512*20000^2183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2949 20000 713368824149781 2500000000000000000 2183 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2949/20000 : ℝ)) (X := (713368824149781/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562786198728853791/1562500000000000000 : ℝ) ≤ (2500107392379467/2500000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (1562786198728853791/1562500000000000000 : ℝ)^512 ≤ (2500107392379467/2500000000000000 : ℝ)^2183 := by
      have hnat : (1562786198728853791 : ℕ)^512*2500000000000000^2183 ≤ 2500107392379467^2183*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562786198728853791 1562500000000000000 2500107392379467 2500000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500107392379467/2500000000000000 : ℝ)) (X := (1562786198728853791/1562500000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504711639036164069/12500000000000000000 : ℝ) ≤ (10000883925332007/10000000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (12504711639036164069/12500000000000000000 : ℝ)^512 ≤ (10000883925332007/10000000000000000 : ℝ)^2183 := by
      have hnat : (12504711639036164069 : ℕ)^512*10000000000000000^2183 ≤ 10000883925332007^2183*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504711639036164069 12500000000000000000 10000883925332007 10000000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000883925332007/10000000000000000 : ℝ)) (X := (12504711639036164069/12500000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250713368824149781/1250000000000000000 : ℝ) ≤ (5000669140573073/5000000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (1250713368824149781/1250000000000000000 : ℝ)^512 ≤ (5000669140573073/5000000000000000 : ℝ)^2183 := by
      have hnat : (1250713368824149781 : ℕ)^512*5000000000000000^2183 ≤ 5000669140573073^2183*1250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250713368824149781 1250000000000000000 5000669140573073 5000000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000669140573073/5000000000000000 : ℝ)) (X := (1250713368824149781/1250000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(286198728853791/3125000000000000000 : ℝ) ≤ ((1149707270566508153/1150000000000000000 : ℝ)+2*(454355814139/345000000000000 : ℝ)*(2259/20000 : ℝ))^(2183/512 : ℝ) := by
    rw [show (1149707270566508153/1150000000000000000 : ℝ)+2*(454355814139/345000000000000 : ℝ)*(2259/20000 : ℝ)=(2500107392379467/2500000000000000 : ℝ) by norm_num, show 1+2*(286198728853791/3125000000000000000 : ℝ)=(1562786198728853791/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(713368824149781/2500000000000000000 : ℝ)+(286198728853791/3125000000000000000 : ℝ) ≤ ((1149707270566508153/1150000000000000000 : ℝ)+(454355814139/345000000000000 : ℝ)*((2949/20000 : ℝ)+(2259/20000 : ℝ)))^(2183/512 : ℝ) := by
    rw [show (1149707270566508153/1150000000000000000 : ℝ)+(454355814139/345000000000000 : ℝ)*((2949/20000 : ℝ)+(2259/20000 : ℝ))=(10000883925332007/10000000000000000 : ℝ) by norm_num, show 1+(713368824149781/2500000000000000000 : ℝ)+(286198728853791/3125000000000000000 : ℝ)=(12504711639036164069/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(713368824149781/2500000000000000000 : ℝ) ≤ ((1149707270566508153/1150000000000000000 : ℝ)+2*(454355814139/345000000000000 : ℝ)*(2949/20000 : ℝ))^(2183/512 : ℝ) := by
    rw [show (1149707270566508153/1150000000000000000 : ℝ)+2*(454355814139/345000000000000 : ℝ)*(2949/20000 : ℝ)=(5000669140573073/5000000000000000 : ℝ) by norm_num, show 1+2*(713368824149781/2500000000000000000 : ℝ)=(1250713368824149781/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1149707270566508153/1150000000000000000 : ℝ)*(X 1 0+X 2 0)+(454355814139/345000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (2259/20000 : ℝ)) (hi := (2949/20000 : ℝ)) (c := (1149707270566508153/1150000000000000000 : ℝ)) (alpha := (454355814139/345000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1149707270566508153/1150000000000000000 : ℝ)*(X 0 1+X 2 1)+(454355814139/345000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (2259/20000 : ℝ)) (hi := (2949/20000 : ℝ)) (c := (1149707270566508153/1150000000000000000 : ℝ)) (alpha := (454355814139/345000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1149707270566508153/1150000000000000000 : ℝ)*(X 0 2+X 1 2)+(454355814139/345000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (2259/20000 : ℝ)) (hi := (2949/20000 : ℝ)) (c := (1149707270566508153/1150000000000000000 : ℝ)) (alpha := (454355814139/345000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-365370679/2000000000 : ℝ)*X 0 0+(1077439333/2000000000 : ℝ)*X 0 1+(1346799133/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285891487/10000000000 : ℝ)*X 1 0+(-1965940361/10000000000 : ℝ)*X 1 1+(673399561/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642945387/5000000000 : ℝ)*X 2 0+(5387196817/10000000000 : ℝ)*X 2 1+(-982970439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2228327051/5000000000 : ℝ)*X 0 0+(1060071411/2500000000 : ℝ)*X 0 1+(1060071441/2500000000 : ℝ)*X 0 2+(2228327051/5000000000 : ℝ)*X 1 0+(1060071411/2500000000 : ℝ)*X 1 1+(1060071441/2500000000 : ℝ)*X 1 2+(2228327051/5000000000 : ℝ)*X 2 0+(1060071411/2500000000 : ℝ)*X 2 1+(1060071441/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1077065061/5000000000 : ℝ)*X 0 0+(2633091299/5000000000 : ℝ)*X 0 1+(2633091287/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5370658871/10000000000 : ℝ)*X 1 0+(-1007465879/5000000000 : ℝ)*X 1 1+(5266182829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5370658919/10000000000 : ℝ)*X 2 0+(2633091239/5000000000 : ℝ)*X 2 1+(-503733041/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2081071009/5000000000 : ℝ)*X 0 0+(2193745083/5000000000 : ℝ)*X 0 1+(4387490257/10000000000 : ℝ)*X 0 2+(2081071009/5000000000 : ℝ)*X 1 0+(2193745083/5000000000 : ℝ)*X 1 1+(4387490257/10000000000 : ℝ)*X 1 2+(2081071009/5000000000 : ℝ)*X 2 0+(2193745083/5000000000 : ℝ)*X 2 1+(4387490257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-417049023/2000000000 : ℝ)*X 0 0+(5182576797/10000000000 : ℝ)*X 0 1+(2700591969/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276089373/10000000000 : ℝ)*X 1 0+(-392029961/2000000000 : ℝ)*X 1 1+(5401183777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276088819/10000000000 : ℝ)*X 2 0+(1080236843/2000000000 : ℝ)*X 2 1+(-980074979/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1122533997/2500000000 : ℝ)*X 0 0+(1055814483/2500000000 : ℝ)*X 0 1+(2111628627/5000000000 : ℝ)*X 0 2+(1122533997/2500000000 : ℝ)*X 1 0+(1055814483/2500000000 : ℝ)*X 1 1+(2111628627/5000000000 : ℝ)*X 1 2+(1122533997/2500000000 : ℝ)*X 2 0+(1055814483/2500000000 : ℝ)*X 2 1+(2111628627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1895956533/10000000000 : ℝ)*X 0 0+(2734367467/5000000000 : ℝ)*X 0 1+(1313767043/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1075688423/2000000000 : ℝ)*X 1 0+(-1009665207/5000000000 : ℝ)*X 1 1+(1313767221/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((215137739/400000000 : ℝ)*X 2 0+(1313766959/2500000000 : ℝ)*X 2 1+(-2019329983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2067321617/5000000000 : ℝ)*X 0 0+(137531211/312500000 : ℝ)*X 0 1+(4400999733/10000000000 : ℝ)*X 0 2+(2067321617/5000000000 : ℝ)*X 1 0+(137531211/312500000 : ℝ)*X 1 1+(4400999733/10000000000 : ℝ)*X 1 2+(2067321617/5000000000 : ℝ)*X 2 0+(137531211/312500000 : ℝ)*X 2 1+(4400999733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31443/50000 : ℝ) ≤ (-36158269755186615029426473925877/57500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74409471/100000000000000 : ℝ)*(upper1) + (76735993/50000000000000 : ℝ)*(upper2) + (2040363/100000000000000 : ℝ)*(upper3) + (5470759/100000000000000 : ℝ)*(lower4) + (28805893/100000000000000 : ℝ)*(upper5) + (2992753526502497/100000000000000 : ℝ)*(major0) + (2992753526502497/100000000000000 : ℝ)*(major1) + (2992753526502497/100000000000000 : ℝ)*(major2) + (1289961719/20000000000000 : ℝ)*(sp2) + (4103836527125631/100000000000000 : ℝ)*(sp4) + (512959656562337/12500000000000 : ℝ)*(sp5) + (1025957519329259/25000000000000 : ℝ)*(sp6) + (95131592083973/5000000000000 : ℝ)*(sp7) + (31854925387/20000000000000 : ℝ)*(sp13) + (95131592083973/5000000000000 : ℝ)*(f.failure) + (4103836527125631/100000000000000 : ℝ)*(f.sum) + (64996182985417/17250000000000000000000000000 : ℝ)*base66 + (3011632986616904123/345000000000000000000000000000000 : ℝ)*base67 + (1336855935403095877/345000000000000000000000000000000 : ℝ)*base70 + (1081478174818095877/345000000000000000000000000000000 : ℝ)*base72 + (80543647045583/17250000000000000000000000000 : ℝ)*base73 + (15648899135746904123/345000000000000000000000000000000 : ℝ)*base75 + (4067365846003095877/345000000000000000000000000000000 : ℝ)*base78 + (626518968208095877/345000000000000000000000000000000 : ℝ)*base80 + (278605952776583/17250000000000000000000000000 : ℝ)*base81 + (1253447/500000000000000000000 : ℝ)*base90 + (1253447/500000000000000000000 : ℝ)*base92 + (1253447/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59069/100000 : ℝ) ≤ (8491544618819016099791211477239/14375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26424891/25000000000000 : ℝ)*(lower0) + (330529061/100000000000000 : ℝ)*(upper2) + (33142693/50000000000000 : ℝ)*(lower5) + (1531806266684579/50000000000000 : ℝ)*(major0) + (1531806266684579/50000000000000 : ℝ)*(major1) + (1531806266684579/50000000000000 : ℝ)*(major2) + (415985010054049/10000000000000 : ℝ)*(sp0) + (519981402973129/12500000000000 : ℝ)*(sp1) + (4159846659301711/100000000000000 : ℝ)*(sp2) + (973836740730081/50000000000000 : ℝ)*(sp3) + (311489557/10000000000000 : ℝ)*(sp5) + (670835101/10000000000000 : ℝ)*(sp7) + (7679378891/100000000000000 : ℝ)*(sp10) + (4238140111/100000000000000 : ℝ)*(sp12) + (486920047452793/25000000000000 : ℝ)*(f.failure) + (2079927169340301/50000000000000 : ℝ)*(f.sum) + (1732798520053/4312500000000000000000000000 : ℝ)*base65 + (758091522653427761/172500000000000000000000000000000 : ℝ)*base67 + (1728389256998427761/172500000000000000000000000000000 : ℝ)*base69 + (107152207718427761/172500000000000000000000000000000 : ℝ)*base71 + (97147868905519/8625000000000000000000000000 : ℝ)*base74 + (611743734983427761/172500000000000000000000000000000 : ℝ)*base75 + (1607710734615927761/172500000000000000000000000000000 : ℝ)*base77 + (169519624926572239/172500000000000000000000000000000 : ℝ)*base80 + (5965844867269/8625000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (672573/2500000000000000000000 : ℝ)*base89 + (672573/2500000000000000000000 : ℝ)*base91 + (672573/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40163/50000 : ℝ) ≤ (230945398717520316145658225751/287500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42441601/100000000000000 : ℝ)*(upper2) + (24488761/100000000000000 : ℝ)*(lower3) + (364500629/100000000000000 : ℝ)*(lower5) + (16863426219063/500000000000 : ℝ)*(major0) + (16863426219063/500000000000 : ℝ)*(major1) + (16863426219063/500000000000 : ℝ)*(major2) + (197482951/10000000000000 : ℝ)*(sp0) + (47074454173/100000000000000 : ℝ)*(sp1) + (52463882019/20000000000000 : ℝ)*(sp2) + (2287206272753699/50000000000000 : ℝ)*(sp8) + (4574375127569957/100000000000000 : ℝ)*(sp9) + (914831976522807/20000000000000 : ℝ)*(sp10) + (268021500936111/12500000000000 : ℝ)*(sp11) + (3840843611/50000000000000 : ℝ)*(sp12) + (268021500936111/12500000000000 : ℝ)*(f.failure) + (457442220202413/10000000000000 : ℝ)*(f.sum) + (147744101953/57500000000000000000000000 : ℝ)*base65 + (695247666289361/575000000000000000000000000000 : ℝ)*base68 + (7077933425789361/575000000000000000000000000000 : ℝ)*base70 + (2980925701989361/575000000000000000000000000000 : ℝ)*base72 + (100304188103/57500000000000000000000000 : ℝ)*base73 + (4312874107164361/575000000000000000000000000000 : ℝ)*base76 + (1350712142214361/575000000000000000000000000000 : ℝ)*base78 + (5977245641989361/575000000000000000000000000000 : ℝ)*base80 + (72152066213/14375000000000000000000000 : ℝ)*base82 + (11292171/1250000000000000000000 : ℝ)*base89 + (11292171/1250000000000000000000 : ℝ)*base91 + (11292171/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-42301/50000 : ℝ) ≤ (-1057492277046934985511393713319/1250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (102377461/25000000000000 : ℝ)*(lower1) + (478402569/100000000000000 : ℝ)*(lower2) + (23532441/25000000000000 : ℝ)*(upper5) + (1704963368770557/50000000000000 : ℝ)*(major0) + (1704963368770557/50000000000000 : ℝ)*(major1) + (1704963368770557/50000000000000 : ℝ)*(major2) + (8817003741/50000000000000 : ℝ)*(sp0) + (278276064739/100000000000000 : ℝ)*(sp5) + (481330443289/100000000000000 : ℝ)*(sp6) + (218921049569/100000000000000 : ℝ)*(sp7) + (4680187487533311/100000000000000 : ℝ)*(sp12) + (2339963422738027/50000000000000 : ℝ)*(sp13) + (146241368471797/3125000000000 : ℝ)*(sp14) + (2167629226546447/100000000000000 : ℝ)*(sp15) + (135490509224751/6250000000000 : ℝ)*(f.failure) + (4680205121540793/100000000000000 : ℝ)*(f.sum) + (5820332799/15625000000000000000000000 : ℝ)*base65 + (14388114559272227/2500000000000000000000000000000 : ℝ)*base67 + (13368313435727773/2500000000000000000000000000000 : ℝ)*base70 + (7733978233227773/2500000000000000000000000000000 : ℝ)*base72 + (1071715488267/125000000000000000000000000 : ℝ)*base73 + (3464164563227773/2500000000000000000000000000000 : ℝ)*base76 + (1688853986772227/2500000000000000000000000000000 : ℝ)*base77 + (5474229145727773/2500000000000000000000000000000 : ℝ)*base80 + (147233866267/125000000000000000000000000 : ℝ)*base81 + (1344789/625000000000000000000 : ℝ)*base90 + (1344789/625000000000000000000 : ℝ)*base92 + (1344789/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1407_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31443/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59069/100000 : ℝ) else (40163/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42301/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1407_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1407_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31443/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59069/100000 : ℝ) else (40163/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42301/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1407_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1407_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1407_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31443/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59069/100000 : ℝ) else (40163/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42301/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1407_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

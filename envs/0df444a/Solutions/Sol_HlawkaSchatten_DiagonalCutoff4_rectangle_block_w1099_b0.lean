-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1099_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:00:15.96133+00:00
-- url     : https://prove2.me/submissions/76e172e5-4938-4ac0-9913-eee7e4bbc93b

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
theorem support_rectangle_w1099_s0_0 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-95274753/500000000 : ℝ)*x 0 + (1212864427/2000000000 : ℝ)*x 1 + (2387504989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (95274753/500000000 : ℝ)^2073 ≤ (2212504079239/20000000000000 : ℝ)^1561 := by
    have hnat : (95274753 : ℕ)^2073*20000000000000^1561 ≤ 2212504079239^1561*500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95274753 500000000 2212504079239 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1212864427/2000000000 : ℝ)^2073 ≤ (25733920952943/50000000000000 : ℝ)^1561 := by
    have hnat : (1212864427 : ℕ)^2073*50000000000000^1561 ≤ 25733920952943^1561*2000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212864427 2000000000 25733920952943 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2387504989/5000000000 : ℝ)^2073 ≤ (37469637681241/100000000000000 : ℝ)^1561 := by
    have hnat : (2387504989 : ℕ)^2073*100000000000000^1561 ≤ 37469637681241^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2387504989 5000000000 37469637681241 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-95274753/500000000 : ℝ), (1212864427/2000000000 : ℝ), (2387504989/5000000000 : ℝ)] ![(2212504079239/20000000000000 : ℝ), (25733920952943/50000000000000 : ℝ), (37469637681241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-95274753/500000000 : ℝ)|^2073 ≤ (2212504079239/20000000000000 : ℝ)^1561
        have hw : |(-95274753/500000000 : ℝ)|=(95274753/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1212864427/2000000000 : ℝ)|^2073 ≤ (25733920952943/50000000000000 : ℝ)^1561
        have hw : |(1212864427/2000000000 : ℝ)|=(1212864427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2387504989/5000000000 : ℝ)|^2073 ≤ (37469637681241/100000000000000 : ℝ)^1561
        have hw : |(2387504989/5000000000 : ℝ)|=(2387504989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s0_1 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2759607749/5000000000 : ℝ)*x 0 + (-330832413/1250000000 : ℝ)*x 1 + (2387504989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2759607749/5000000000 : ℝ)^2073 ≤ (9083316378371/20000000000000 : ℝ)^1561 := by
    have hnat : (2759607749 : ℕ)^2073*20000000000000^1561 ≤ 9083316378371^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759607749 5000000000 9083316378371 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330832413/1250000000 : ℝ)^2073 ≤ (1069611275577/6250000000000 : ℝ)^1561 := by
    have hnat : (330832413 : ℕ)^2073*6250000000000^1561 ≤ 1069611275577^1561*1250000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330832413 1250000000 1069611275577 6250000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2387504989/5000000000 : ℝ)^2073 ≤ (37469637681241/100000000000000 : ℝ)^1561 := by
    have hnat : (2387504989 : ℕ)^2073*100000000000000^1561 ≤ 37469637681241^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2387504989 5000000000 37469637681241 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2759607749/5000000000 : ℝ), (-330832413/1250000000 : ℝ), (2387504989/5000000000 : ℝ)] ![(9083316378371/20000000000000 : ℝ), (1069611275577/6250000000000 : ℝ), (37469637681241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2759607749/5000000000 : ℝ)|^2073 ≤ (9083316378371/20000000000000 : ℝ)^1561
        have hw : |(2759607749/5000000000 : ℝ)|=(2759607749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-330832413/1250000000 : ℝ)|^2073 ≤ (1069611275577/6250000000000 : ℝ)^1561
        have hw : |(-330832413/1250000000 : ℝ)|=(330832413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2387504989/5000000000 : ℝ)|^2073 ≤ (37469637681241/100000000000000 : ℝ)^1561
        have hw : |(2387504989/5000000000 : ℝ)|=(2387504989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s0_2 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2759607749/5000000000 : ℝ)*x 0 + (2387504989/5000000000 : ℝ)*x 1 + (-330832413/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2759607749/5000000000 : ℝ)^2073 ≤ (9083316378371/20000000000000 : ℝ)^1561 := by
    have hnat : (2759607749 : ℕ)^2073*20000000000000^1561 ≤ 9083316378371^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759607749 5000000000 9083316378371 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2387504989/5000000000 : ℝ)^2073 ≤ (37469637681241/100000000000000 : ℝ)^1561 := by
    have hnat : (2387504989 : ℕ)^2073*100000000000000^1561 ≤ 37469637681241^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2387504989 5000000000 37469637681241 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (330832413/1250000000 : ℝ)^2073 ≤ (1069611275577/6250000000000 : ℝ)^1561 := by
    have hnat : (330832413 : ℕ)^2073*6250000000000^1561 ≤ 1069611275577^1561*1250000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330832413 1250000000 1069611275577 6250000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2759607749/5000000000 : ℝ), (2387504989/5000000000 : ℝ), (-330832413/1250000000 : ℝ)] ![(9083316378371/20000000000000 : ℝ), (37469637681241/100000000000000 : ℝ), (1069611275577/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2759607749/5000000000 : ℝ)|^2073 ≤ (9083316378371/20000000000000 : ℝ)^1561
        have hw : |(2759607749/5000000000 : ℝ)|=(2759607749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2387504989/5000000000 : ℝ)|^2073 ≤ (37469637681241/100000000000000 : ℝ)^1561
        have hw : |(2387504989/5000000000 : ℝ)|=(2387504989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-330832413/1250000000 : ℝ)|^2073 ≤ (1069611275577/6250000000000 : ℝ)^1561
        have hw : |(-330832413/1250000000 : ℝ)|=(330832413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s0_3 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4204491379/10000000000 : ℝ)*x 0 + (195197211/625000000 : ℝ)*x 1 + (5666592323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204491379/10000000000 : ℝ)^2073 ≤ (3955518542593/12500000000000 : ℝ)^1561 := by
    have hnat : (4204491379 : ℕ)^2073*12500000000000^1561 ≤ 3955518542593^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204491379 10000000000 3955518542593 12500000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195197211/625000000 : ℝ)^2073 ≤ (1066087578147/5000000000000 : ℝ)^1561 := by
    have hnat : (195197211 : ℕ)^2073*5000000000000^1561 ≤ 1066087578147^1561*625000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195197211 625000000 1066087578147 5000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5666592323/10000000000 : ℝ)^2073 ≤ (47034100078181/100000000000000 : ℝ)^1561 := by
    have hnat : (5666592323 : ℕ)^2073*100000000000000^1561 ≤ 47034100078181^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5666592323 10000000000 47034100078181 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204491379/10000000000 : ℝ), (195197211/625000000 : ℝ), (5666592323/10000000000 : ℝ)] ![(3955518542593/12500000000000 : ℝ), (1066087578147/5000000000000 : ℝ), (47034100078181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204491379/10000000000 : ℝ)|^2073 ≤ (3955518542593/12500000000000 : ℝ)^1561
        have hw : |(4204491379/10000000000 : ℝ)|=(4204491379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195197211/625000000 : ℝ)|^2073 ≤ (1066087578147/5000000000000 : ℝ)^1561
        have hw : |(195197211/625000000 : ℝ)|=(195197211/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5666592323/10000000000 : ℝ)|^2073 ≤ (47034100078181/100000000000000 : ℝ)^1561
        have hw : |(5666592323/10000000000 : ℝ)|=(5666592323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s0_4 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1910769309/10000000000 : ℝ)*x 0 + (4808289791/10000000000 : ℝ)*x 1 + (753734377/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1910769309/10000000000 : ℝ)^2073 ≤ (5551601102689/50000000000000 : ℝ)^1561 := by
    have hnat : (1910769309 : ℕ)^2073*50000000000000^1561 ≤ 5551601102689^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910769309 10000000000 5551601102689 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4808289791/10000000000 : ℝ)^2073 ≤ (37816836170571/100000000000000 : ℝ)^1561 := by
    have hnat : (4808289791 : ℕ)^2073*100000000000000^1561 ≤ 37816836170571^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4808289791 10000000000 37816836170571 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (753734377/1250000000 : ℝ)^2073 ≤ (3192497600173/6250000000000 : ℝ)^1561 := by
    have hnat : (753734377 : ℕ)^2073*6250000000000^1561 ≤ 3192497600173^1561*1250000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753734377 1250000000 3192497600173 6250000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1910769309/10000000000 : ℝ), (4808289791/10000000000 : ℝ), (753734377/1250000000 : ℝ)] ![(5551601102689/50000000000000 : ℝ), (37816836170571/100000000000000 : ℝ), (3192497600173/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1910769309/10000000000 : ℝ)|^2073 ≤ (5551601102689/50000000000000 : ℝ)^1561
        have hw : |(-1910769309/10000000000 : ℝ)|=(1910769309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4808289791/10000000000 : ℝ)|^2073 ≤ (37816836170571/100000000000000 : ℝ)^1561
        have hw : |(4808289791/10000000000 : ℝ)|=(4808289791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(753734377/1250000000 : ℝ)|^2073 ≤ (3192497600173/6250000000000 : ℝ)^1561
        have hw : |(753734377/1250000000 : ℝ)|=(753734377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s0_5 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1292274661/2500000000 : ℝ)*x 0 + (-695897921/5000000000 : ℝ)*x 1 + (3014937773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292274661/2500000000 : ℝ)^2073 ≤ (8326190543747/20000000000000 : ℝ)^1561 := by
    have hnat : (1292274661 : ℕ)^2073*20000000000000^1561 ≤ 8326190543747^1561*2500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292274661 2500000000 8326190543747 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (695897921/5000000000 : ℝ)^2073 ≤ (58312637639/800000000000 : ℝ)^1561 := by
    have hnat : (695897921 : ℕ)^2073*800000000000^1561 ≤ 58312637639^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695897921 5000000000 58312637639 800000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3014937773/5000000000 : ℝ)^2073 ≤ (25539983782539/50000000000000 : ℝ)^1561 := by
    have hnat : (3014937773 : ℕ)^2073*50000000000000^1561 ≤ 25539983782539^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3014937773 5000000000 25539983782539 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292274661/2500000000 : ℝ), (-695897921/5000000000 : ℝ), (3014937773/5000000000 : ℝ)] ![(8326190543747/20000000000000 : ℝ), (58312637639/800000000000 : ℝ), (25539983782539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292274661/2500000000 : ℝ)|^2073 ≤ (8326190543747/20000000000000 : ℝ)^1561
        have hw : |(1292274661/2500000000 : ℝ)|=(1292274661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-695897921/5000000000 : ℝ)|^2073 ≤ (58312637639/800000000000 : ℝ)^1561
        have hw : |(-695897921/5000000000 : ℝ)|=(695897921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3014937773/5000000000 : ℝ)|^2073 ≤ (25539983782539/50000000000000 : ℝ)^1561
        have hw : |(3014937773/5000000000 : ℝ)|=(3014937773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s0_6 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1033819991/2000000000 : ℝ)*x 0 + (1507468853/2500000000 : ℝ)*x 1 + (-695897021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033819991/2000000000 : ℝ)^2073 ≤ (20815483370217/50000000000000 : ℝ)^1561 := by
    have hnat : (1033819991 : ℕ)^2073*50000000000000^1561 ≤ 20815483370217^1561*2000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033819991 2000000000 20815483370217 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1507468853/2500000000 : ℝ)^2073 ≤ (25539983028813/50000000000000 : ℝ)^1561 := by
    have hnat : (1507468853 : ℕ)^2073*50000000000000^1561 ≤ 25539983028813^1561*2500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507468853 2500000000 25539983028813 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (695897021/5000000000 : ℝ)^2073 ≤ (364453359299/5000000000000 : ℝ)^1561 := by
    have hnat : (695897021 : ℕ)^2073*5000000000000^1561 ≤ 364453359299^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695897021 5000000000 364453359299 5000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033819991/2000000000 : ℝ), (1507468853/2500000000 : ℝ), (-695897021/5000000000 : ℝ)] ![(20815483370217/50000000000000 : ℝ), (25539983028813/50000000000000 : ℝ), (364453359299/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033819991/2000000000 : ℝ)|^2073 ≤ (20815483370217/50000000000000 : ℝ)^1561
        have hw : |(1033819991/2000000000 : ℝ)|=(1033819991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1507468853/2500000000 : ℝ)|^2073 ≤ (25539983028813/50000000000000 : ℝ)^1561
        have hw : |(1507468853/2500000000 : ℝ)|=(1507468853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-695897021/5000000000 : ℝ)|^2073 ≤ (364453359299/5000000000000 : ℝ)^1561
        have hw : |(-695897021/5000000000 : ℝ)|=(695897021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s0_7 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2107446473/5000000000 : ℝ)*x 0 + (1400235411/2500000000 : ℝ)*x 1 + (159555419/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107446473/5000000000 : ℝ)^2073 ≤ (31748152613689/100000000000000 : ℝ)^1561 := by
    have hnat : (2107446473 : ℕ)^2073*100000000000000^1561 ≤ 31748152613689^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107446473 5000000000 31748152613689 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1400235411/2500000000 : ℝ)^2073 ≤ (5788979006539/12500000000000 : ℝ)^1561 := by
    have hnat : (1400235411 : ℕ)^2073*12500000000000^1561 ≤ 5788979006539^1561*2500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400235411 2500000000 5788979006539 12500000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159555419/500000000 : ℝ)^2073 ≤ (1371250957701/6250000000000 : ℝ)^1561 := by
    have hnat : (159555419 : ℕ)^2073*6250000000000^1561 ≤ 1371250957701^1561*500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159555419 500000000 1371250957701 6250000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2107446473/5000000000 : ℝ), (1400235411/2500000000 : ℝ), (159555419/500000000 : ℝ)] ![(31748152613689/100000000000000 : ℝ), (5788979006539/12500000000000 : ℝ), (1371250957701/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2107446473/5000000000 : ℝ)|^2073 ≤ (31748152613689/100000000000000 : ℝ)^1561
        have hw : |(2107446473/5000000000 : ℝ)|=(2107446473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1400235411/2500000000 : ℝ)|^2073 ≤ (5788979006539/12500000000000 : ℝ)^1561
        have hw : |(1400235411/2500000000 : ℝ)|=(1400235411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(159555419/500000000 : ℝ)|^2073 ≤ (1371250957701/6250000000000 : ℝ)^1561
        have hw : |(159555419/500000000 : ℝ)|=(159555419/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1099_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (47/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27981/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8291/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8291 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8291*1^2048 ≤ 0^2048*1^8291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8291 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8291/2048 : ℝ) ≤ (306135448136708683/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8291 ≤ (306135448136708683/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8291*12500000000000000000^2048 ≤ 306135448136708683^2048*5^8291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 306135448136708683 12500000000000000000 8291 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (306135448136708683/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8291 := by
      have hnat : (1 : ℕ)^2048*1^8291 ≤ 1^8291*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12806135448136708683/12500000000000000000 : ℝ) ≤ (10059946037893971/10000000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (12806135448136708683/12500000000000000000 : ℝ)^2048 ≤ (10059946037893971/10000000000000000 : ℝ)^8291 := by
      have hnat : (12806135448136708683 : ℕ)^2048*10000000000000000^8291 ≤ 10059946037893971^8291*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12806135448136708683 12500000000000000000 10059946037893971 10000000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059946037893971/10000000000000000 : ℝ)) (X := (12806135448136708683/12500000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6556135448136708683/6250000000000000000 : ℝ) ≤ (5059946037893971/5000000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (6556135448136708683/6250000000000000000 : ℝ)^2048 ≤ (5059946037893971/5000000000000000 : ℝ)^8291 := by
      have hnat : (6556135448136708683 : ℕ)^2048*5000000000000000^8291 ≤ 5059946037893971^8291*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6556135448136708683 6250000000000000000 5059946037893971 5000000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059946037893971/5000000000000000 : ℝ)) (X := (6556135448136708683/6250000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(59946037893971/4000000000000000 : ℝ)*(0 : ℝ))^(8291/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(59946037893971/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(306135448136708683/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(59946037893971/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8291/2048 : ℝ) := by
    rw [show (1 : ℝ)+(59946037893971/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10059946037893971/10000000000000000 : ℝ) by norm_num, show 1+(306135448136708683/12500000000000000000 : ℝ)+(0 : ℝ)=(12806135448136708683/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(306135448136708683/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(59946037893971/4000000000000000 : ℝ)*(2/5 : ℝ))^(8291/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(59946037893971/4000000000000000 : ℝ)*(2/5 : ℝ)=(5059946037893971/5000000000000000 : ℝ) by norm_num, show 1+2*(306135448136708683/12500000000000000000 : ℝ)=(6556135448136708683/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(59946037893971/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59946037893971/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(59946037893971/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59946037893971/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(59946037893971/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59946037893971/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-95274753/500000000 : ℝ)*X 0 0+(1212864427/2000000000 : ℝ)*X 0 1+(2387504989/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2759607749/5000000000 : ℝ)*X 1 0+(-330832413/1250000000 : ℝ)*X 1 1+(2387504989/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2759607749/5000000000 : ℝ)*X 2 0+(2387504989/5000000000 : ℝ)*X 2 1+(-330832413/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4204491379/10000000000 : ℝ)*X 0 0+(195197211/625000000 : ℝ)*X 0 1+(5666592323/10000000000 : ℝ)*X 0 2+(4204491379/10000000000 : ℝ)*X 1 0+(195197211/625000000 : ℝ)*X 1 1+(5666592323/10000000000 : ℝ)*X 1 2+(4204491379/10000000000 : ℝ)*X 2 0+(195197211/625000000 : ℝ)*X 2 1+(5666592323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1910769309/10000000000 : ℝ)*X 0 0+(4808289791/10000000000 : ℝ)*X 0 1+(753734377/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1292274661/2500000000 : ℝ)*X 1 0+(-695897921/5000000000 : ℝ)*X 1 1+(3014937773/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1033819991/2000000000 : ℝ)*X 2 0+(1507468853/2500000000 : ℝ)*X 2 1+(-695897021/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2107446473/5000000000 : ℝ)*X 0 0+(1400235411/2500000000 : ℝ)*X 0 1+(159555419/500000000 : ℝ)*X 0 2+(2107446473/5000000000 : ℝ)*X 1 0+(1400235411/2500000000 : ℝ)*X 1 1+(159555419/500000000 : ℝ)*X 1 2+(2107446473/5000000000 : ℝ)*X 2 0+(1400235411/2500000000 : ℝ)*X 2 1+(159555419/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (110624122015150376002521/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59064901/100000000000000 : ℝ)*(base1) + (690151411/50000000000000 : ℝ)*(base19) + (1286464807/100000000000000 : ℝ)*(base23) + (18767603/20000000000000 : ℝ)*(base24) + (39099173/12500000000000 : ℝ)*(upper3) + (116878778023339/20000000000000 : ℝ)*(major0) + (116878778023339/20000000000000 : ℝ)*(major1) + (116878778023339/20000000000000 : ℝ)*(major2) + (775611930275749/100000000000000 : ℝ)*(sp0) + (387806760397463/50000000000000 : ℝ)*(sp1) + (387806760397463/50000000000000 : ℝ)*(sp2) + (393170213512501/100000000000000 : ℝ)*(sp3) + (30298869/1000000000000 : ℝ)*(sp4) + (24221847/1000000000000 : ℝ)*(sp7) + (196586347381051/50000000000000 : ℝ)*(f.failure) + (193903725274437/25000000000000 : ℝ)*(f.sum) + (26730276170831/40000000000000000000000000000 : ℝ)*base66 + (335377689890831/80000000000000000000000000000 : ℝ)*base68 + (254656534210831/80000000000000000000000000000 : ℝ)*base70 + (420279612770831/80000000000000000000000000000 : ℝ)*base72 + (1658581490831/40000000000000000000000000000 : ℝ)*base74 + (315429150690831/80000000000000000000000000000 : ℝ)*base76 + (420279612770831/80000000000000000000000000000 : ℝ)*base78 + (469196058930831/80000000000000000000000000000 : ℝ)*base80 + (84775127370831/40000000000000000000000000000 : ℝ)*base82 + (12807471/5000000000000000000000 : ℝ)*base89 + (12807471/5000000000000000000000 : ℝ)*base91 + (12807471/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1323355468820790022826139/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1055758243/100000000000000 : ℝ)*(base19) + (845366273/50000000000000 : ℝ)*(base23) + (79420187/20000000000000 : ℝ)*(base39) + (311584849/100000000000000 : ℝ)*(base45) + (18868791/12500000000000 : ℝ)*(upper3) + (20184419/6250000000000 : ℝ)*(upper5) + (616784774252673/100000000000000 : ℝ)*(major0) + (616784774252673/100000000000000 : ℝ)*(major1) + (308392188575869/50000000000000 : ℝ)*(major2) + (154173557/25000000000000 : ℝ)*(sp2) + (204651016434741/25000000000000 : ℝ)*(sp4) + (818603009980721/100000000000000 : ℝ)*(sp5) + (1309763448661/160000000000 : ℝ)*(sp6) + (207482432553097/50000000000000 : ℝ)*(sp7) + (207482432553097/50000000000000 : ℝ)*(f.failure) + (8186044628399/1000000000000 : ℝ)*(f.sum) + (654321299493919/400000000000000000000000000000 : ℝ)*base66 + (1492217380814201/200000000000000000000000000000 : ℝ)*base68 + (3138578679734483/400000000000000000000000000000 : ℝ)*base69 + (710155458414201/200000000000000000000000000000 : ℝ)*base72 + (2515972981893919/400000000000000000000000000000 : ℝ)*base74 + (1983368582934483/400000000000000000000000000000 : ℝ)*base75 + (372365360134483/400000000000000000000000000000 : ℝ)*base77 + (784182630665517/400000000000000000000000000000 : ℝ)*base80 + (368348905734483/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (27448837/5000000000000000000000 : ℝ)*base89 + (27448837/5000000000000000000000 : ℝ)*base91 + (27448837/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1099_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (47/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27981/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1099_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1099_s1_0 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-84530331/400000000 : ℝ)*x 0 + (142829157/250000000 : ℝ)*x 1 + (1248283739/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84530331/400000000 : ℝ)^2073 ≤ (12692304523183/100000000000000 : ℝ)^1561 := by
    have hnat : (84530331 : ℕ)^2073*100000000000000^1561 ≤ 12692304523183^1561*400000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84530331 400000000 12692304523183 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142829157/250000000 : ℝ)^2073 ≤ (4754816068721/10000000000000 : ℝ)^1561 := by
    have hnat : (142829157 : ℕ)^2073*10000000000000^1561 ≤ 4754816068721^1561*250000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142829157 250000000 4754816068721 10000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1248283739/2500000000 : ℝ)^2073 ≤ (39759534779163/100000000000000 : ℝ)^1561 := by
    have hnat : (1248283739 : ℕ)^2073*100000000000000^1561 ≤ 39759534779163^1561*2500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248283739 2500000000 39759534779163 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84530331/400000000 : ℝ), (142829157/250000000 : ℝ), (1248283739/2500000000 : ℝ)] ![(12692304523183/100000000000000 : ℝ), (4754816068721/10000000000000 : ℝ), (39759534779163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84530331/400000000 : ℝ)|^2073 ≤ (12692304523183/100000000000000 : ℝ)^1561
        have hw : |(-84530331/400000000 : ℝ)|=(84530331/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142829157/250000000 : ℝ)|^2073 ≤ (4754816068721/10000000000000 : ℝ)^1561
        have hw : |(142829157/250000000 : ℝ)|=(142829157/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1248283739/2500000000 : ℝ)|^2073 ≤ (39759534779163/100000000000000 : ℝ)^1561
        have hw : |(1248283739/2500000000 : ℝ)|=(1248283739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s1_1 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5421491187/10000000000 : ℝ)*x 0 + (-1251345479/5000000000 : ℝ)*x 1 + (2496567543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421491187/10000000000 : ℝ)^2073 ≤ (44351781676421/100000000000000 : ℝ)^1561 := by
    have hnat : (5421491187 : ℕ)^2073*100000000000000^1561 ≤ 44351781676421^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421491187 10000000000 44351781676421 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1251345479/5000000000 : ℝ)^2073 ≤ (7944341078057/50000000000000 : ℝ)^1561 := by
    have hnat : (1251345479 : ℕ)^2073*50000000000000^1561 ≤ 7944341078057^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251345479 5000000000 7944341078057 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2496567543/5000000000 : ℝ)^2073 ≤ (19879768076931/50000000000000 : ℝ)^1561 := by
    have hnat : (2496567543 : ℕ)^2073*50000000000000^1561 ≤ 19879768076931^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2496567543 5000000000 19879768076931 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421491187/10000000000 : ℝ), (-1251345479/5000000000 : ℝ), (2496567543/5000000000 : ℝ)] ![(44351781676421/100000000000000 : ℝ), (7944341078057/50000000000000 : ℝ), (19879768076931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421491187/10000000000 : ℝ)|^2073 ≤ (44351781676421/100000000000000 : ℝ)^1561
        have hw : |(5421491187/10000000000 : ℝ)|=(5421491187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1251345479/5000000000 : ℝ)|^2073 ≤ (7944341078057/50000000000000 : ℝ)^1561
        have hw : |(-1251345479/5000000000 : ℝ)|=(1251345479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2496567543/5000000000 : ℝ)|^2073 ≤ (19879768076931/50000000000000 : ℝ)^1561
        have hw : |(2496567543/5000000000 : ℝ)|=(2496567543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s1_2 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1084298449/2000000000 : ℝ)*x 0 + (124828351/250000000 : ℝ)*x 1 + (-1251345453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084298449/2000000000 : ℝ)^2073 ≤ (22175896585253/50000000000000 : ℝ)^1561 := by
    have hnat : (1084298449 : ℕ)^2073*50000000000000^1561 ≤ 22175896585253^1561*2000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084298449 2000000000 22175896585253 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124828351/250000000 : ℝ)^2073 ≤ (1987976254641/5000000000000 : ℝ)^1561 := by
    have hnat : (124828351 : ℕ)^2073*5000000000000^1561 ≤ 1987976254641^1561*250000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124828351 250000000 1987976254641 5000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1251345453/5000000000 : ℝ)^2073 ≤ (1986085214713/12500000000000 : ℝ)^1561 := by
    have hnat : (1251345453 : ℕ)^2073*12500000000000^1561 ≤ 1986085214713^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251345453 5000000000 1986085214713 12500000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084298449/2000000000 : ℝ), (124828351/250000000 : ℝ), (-1251345453/5000000000 : ℝ)] ![(22175896585253/50000000000000 : ℝ), (1987976254641/5000000000000 : ℝ), (1986085214713/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084298449/2000000000 : ℝ)|^2073 ≤ (22175896585253/50000000000000 : ℝ)^1561
        have hw : |(1084298449/2000000000 : ℝ)|=(1084298449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(124828351/250000000 : ℝ)|^2073 ≤ (1987976254641/5000000000000 : ℝ)^1561
        have hw : |(124828351/250000000 : ℝ)|=(124828351/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1251345453/5000000000 : ℝ)|^2073 ≤ (1986085214713/12500000000000 : ℝ)^1561
        have hw : |(-1251345453/5000000000 : ℝ)|=(1251345453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s1_3 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4321055601/10000000000 : ℝ)*x 0 + (3668880019/10000000000 : ℝ)*x 1 + (5089290351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321055601/10000000000 : ℝ)^2073 ≤ (32814454912419/100000000000000 : ℝ)^1561 := by
    have hnat : (4321055601 : ℕ)^2073*100000000000000^1561 ≤ 32814454912419^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321055601 10000000000 32814454912419 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3668880019/10000000000 : ℝ)^2073 ≤ (26406006898029/100000000000000 : ℝ)^1561 := by
    have hnat : (3668880019 : ℕ)^2073*100000000000000^1561 ≤ 26406006898029^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3668880019 10000000000 26406006898029 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5089290351/10000000000 : ℝ)^2073 ≤ (40779538167553/100000000000000 : ℝ)^1561 := by
    have hnat : (5089290351 : ℕ)^2073*100000000000000^1561 ≤ 40779538167553^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5089290351 10000000000 40779538167553 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321055601/10000000000 : ℝ), (3668880019/10000000000 : ℝ), (5089290351/10000000000 : ℝ)] ![(32814454912419/100000000000000 : ℝ), (26406006898029/100000000000000 : ℝ), (40779538167553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321055601/10000000000 : ℝ)|^2073 ≤ (32814454912419/100000000000000 : ℝ)^1561
        have hw : |(4321055601/10000000000 : ℝ)|=(4321055601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3668880019/10000000000 : ℝ)|^2073 ≤ (26406006898029/100000000000000 : ℝ)^1561
        have hw : |(3668880019/10000000000 : ℝ)|=(3668880019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5089290351/10000000000 : ℝ)|^2073 ≤ (40779538167553/100000000000000 : ℝ)^1561
        have hw : |(5089290351/10000000000 : ℝ)|=(5089290351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s1_4 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2114126423/10000000000 : ℝ)*x 0 + (1250782297/2500000000 : ℝ)*x 1 + (114059427/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114126423/10000000000 : ℝ)^2073 ≤ (12699229324683/100000000000000 : ℝ)^1561 := by
    have hnat : (2114126423 : ℕ)^2073*100000000000000^1561 ≤ 12699229324683^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114126423 10000000000 12699229324683 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1250782297/2500000000 : ℝ)^2073 ≤ (1993262728413/5000000000000 : ℝ)^1561 := by
    have hnat : (1250782297 : ℕ)^2073*5000000000000^1561 ≤ 1993262728413^1561*2500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250782297 2500000000 1993262728413 5000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114059427/200000000 : ℝ)^2073 ≤ (47435516096817/100000000000000 : ℝ)^1561 := by
    have hnat : (114059427 : ℕ)^2073*100000000000000^1561 ≤ 47435516096817^1561*200000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114059427 200000000 47435516096817 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2114126423/10000000000 : ℝ), (1250782297/2500000000 : ℝ), (114059427/200000000 : ℝ)] ![(12699229324683/100000000000000 : ℝ), (1993262728413/5000000000000 : ℝ), (47435516096817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2114126423/10000000000 : ℝ)|^2073 ≤ (12699229324683/100000000000000 : ℝ)^1561
        have hw : |(-2114126423/10000000000 : ℝ)|=(2114126423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1250782297/2500000000 : ℝ)|^2073 ≤ (1993262728413/5000000000000 : ℝ)^1561
        have hw : |(1250782297/2500000000 : ℝ)|=(1250782297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(114059427/200000000 : ℝ)|^2073 ≤ (47435516096817/100000000000000 : ℝ)^1561
        have hw : |(114059427/200000000 : ℝ)|=(114059427/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s1_5 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (654661329/1250000000 : ℝ)*x 0 + (-358570879/2000000000 : ℝ)*x 1 + (5702971179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (654661329/1250000000 : ℝ)^2073 ≤ (42361868103489/100000000000000 : ℝ)^1561 := by
    have hnat : (654661329 : ℕ)^2073*100000000000000^1561 ≤ 42361868103489^1561*1250000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654661329 1250000000 42361868103489 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (358570879/2000000000 : ℝ)^2073 ≤ (1275327208697/12500000000000 : ℝ)^1561 := by
    have hnat : (358570879 : ℕ)^2073*12500000000000^1561 ≤ 1275327208697^1561*2000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358570879 2000000000 1275327208697 12500000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5702971179/10000000000 : ℝ)^2073 ≤ (23717757103989/50000000000000 : ℝ)^1561 := by
    have hnat : (5702971179 : ℕ)^2073*50000000000000^1561 ≤ 23717757103989^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5702971179 10000000000 23717757103989 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(654661329/1250000000 : ℝ), (-358570879/2000000000 : ℝ), (5702971179/10000000000 : ℝ)] ![(42361868103489/100000000000000 : ℝ), (1275327208697/12500000000000 : ℝ), (23717757103989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(654661329/1250000000 : ℝ)|^2073 ≤ (42361868103489/100000000000000 : ℝ)^1561
        have hw : |(654661329/1250000000 : ℝ)|=(654661329/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-358570879/2000000000 : ℝ)|^2073 ≤ (1275327208697/12500000000000 : ℝ)^1561
        have hw : |(-358570879/2000000000 : ℝ)|=(358570879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5702971179/10000000000 : ℝ)|^2073 ≤ (23717757103989/50000000000000 : ℝ)^1561
        have hw : |(5702971179/10000000000 : ℝ)|=(5702971179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s1_6 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2618645327/5000000000 : ℝ)*x 0 + (1425742827/2500000000 : ℝ)*x 1 + (-56026693/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2618645327/5000000000 : ℝ)^2073 ≤ (21180934169901/50000000000000 : ℝ)^1561 := by
    have hnat : (2618645327 : ℕ)^2073*50000000000000^1561 ≤ 21180934169901^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618645327 5000000000 21180934169901 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1425742827/2500000000 : ℝ)^2073 ≤ (11858878908223/25000000000000 : ℝ)^1561 := by
    have hnat : (1425742827 : ℕ)^2073*25000000000000^1561 ≤ 11858878908223^1561*2500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1425742827 2500000000 11858878908223 25000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56026693/312500000 : ℝ)^2073 ≤ (10202616014541/100000000000000 : ℝ)^1561 := by
    have hnat : (56026693 : ℕ)^2073*100000000000000^1561 ≤ 10202616014541^1561*312500000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56026693 312500000 10202616014541 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2618645327/5000000000 : ℝ), (1425742827/2500000000 : ℝ), (-56026693/312500000 : ℝ)] ![(21180934169901/50000000000000 : ℝ), (11858878908223/25000000000000 : ℝ), (10202616014541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2618645327/5000000000 : ℝ)|^2073 ≤ (21180934169901/50000000000000 : ℝ)^1561
        have hw : |(2618645327/5000000000 : ℝ)|=(2618645327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1425742827/2500000000 : ℝ)|^2073 ≤ (11858878908223/25000000000000 : ℝ)^1561
        have hw : |(1425742827/2500000000 : ℝ)|=(1425742827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56026693/312500000 : ℝ)|^2073 ≤ (10202616014541/100000000000000 : ℝ)^1561
        have hw : |(-56026693/312500000 : ℝ)|=(56026693/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s1_7 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (864553421/2000000000 : ℝ)*x 0 + (5069575397/10000000000 : ℝ)*x 1 + (3688990873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864553421/2000000000 : ℝ)^2073 ≤ (32831716385861/100000000000000 : ℝ)^1561 := by
    have hnat : (864553421 : ℕ)^2073*100000000000000^1561 ≤ 32831716385861^1561*2000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864553421 2000000000 32831716385861 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5069575397/10000000000 : ℝ)^2073 ≤ (10142471300653/25000000000000 : ℝ)^1561 := by
    have hnat : (5069575397 : ℕ)^2073*25000000000000^1561 ≤ 10142471300653^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5069575397 10000000000 10142471300653 25000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3688990873/10000000000 : ℝ)^2073 ≤ (531967968039/2000000000000 : ℝ)^1561 := by
    have hnat : (3688990873 : ℕ)^2073*2000000000000^1561 ≤ 531967968039^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688990873 10000000000 531967968039 2000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864553421/2000000000 : ℝ), (5069575397/10000000000 : ℝ), (3688990873/10000000000 : ℝ)] ![(32831716385861/100000000000000 : ℝ), (10142471300653/25000000000000 : ℝ), (531967968039/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864553421/2000000000 : ℝ)|^2073 ≤ (32831716385861/100000000000000 : ℝ)^1561
        have hw : |(864553421/2000000000 : ℝ)|=(864553421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5069575397/10000000000 : ℝ)|^2073 ≤ (10142471300653/25000000000000 : ℝ)^1561
        have hw : |(5069575397/10000000000 : ℝ)|=(5069575397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3688990873/10000000000 : ℝ)|^2073 ≤ (531967968039/2000000000000 : ℝ)^1561
        have hw : |(3688990873/10000000000 : ℝ)|=(3688990873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1099_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27981/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (47/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1081/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4127/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27981/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (47/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27981/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (47/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27981/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (47/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27981/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (47/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27981/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (47/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27981/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (47/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (47/20000 : ℝ) ^ (8291/2048 : ℝ) ≤ (569022303/25000000000000000000 : ℝ) := by
    have hpowers : (47/20000 : ℝ)^8291 ≤ (569022303/25000000000000000000 : ℝ)^2048 := by
      have hnat : (47 : ℕ)^8291*25000000000000000000^2048 ≤ 569022303^2048*20000^8291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47 20000 569022303 25000000000000000000 8291 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47/20000 : ℝ)) (X := (569022303/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27981/100000 : ℝ) ^ (8291/2048 : ℝ) ≤ (576387270637529323/100000000000000000000 : ℝ) := by
    have hpowers : (27981/100000 : ℝ)^8291 ≤ (576387270637529323/100000000000000000000 : ℝ)^2048 := by
      have hnat : (27981 : ℕ)^8291*100000000000000000000^2048 ≤ 576387270637529323^2048*100000^8291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27981 100000 576387270637529323 100000000000000000000 8291 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27981/100000 : ℝ)) (X := (576387270637529323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000000569022303/12500000000000000000 : ℝ) ≤ (5000000000056223/5000000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (12500000000569022303/12500000000000000000 : ℝ)^2048 ≤ (5000000000056223/5000000000000000 : ℝ)^8291 := by
      have hnat : (12500000000569022303 : ℕ)^2048*5000000000000000^8291 ≤ 5000000000056223^8291*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000000569022303 12500000000000000000 5000000000056223 5000000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000056223/5000000000000000 : ℝ)) (X := (12500000000569022303/12500000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20115277454582723707/20000000000000000000 : ℝ) ≤ (5007103413977843/5000000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (20115277454582723707/20000000000000000000 : ℝ)^2048 ≤ (5007103413977843/5000000000000000 : ℝ)^8291 := by
      have hnat : (20115277454582723707 : ℕ)^2048*5000000000000000^8291 ≤ 5007103413977843^8291*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20115277454582723707 20000000000000000000 5007103413977843 5000000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007103413977843/5000000000000000 : ℝ)) (X := (20115277454582723707/20000000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50576387270637529323/50000000000000000000 : ℝ) ≤ (5014206827899463/5000000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (50576387270637529323/50000000000000000000 : ℝ)^2048 ≤ (5014206827899463/5000000000000000 : ℝ)^8291 := by
      have hnat : (50576387270637529323 : ℕ)^2048*5000000000000000^8291 ≤ 5014206827899463^8291*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50576387270637529323 50000000000000000000 5014206827899463 5000000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014206827899463/5000000000000000 : ℝ)) (X := (50576387270637529323/50000000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(569022303/25000000000000000000 : ℝ) ≤ ((69363330698508400979/69365000000000000000 : ℝ)+2*(355170696081/69365000000000 : ℝ)*(47/20000 : ℝ))^(8291/2048 : ℝ) := by
    rw [show (69363330698508400979/69365000000000000000 : ℝ)+2*(355170696081/69365000000000 : ℝ)*(47/20000 : ℝ)=(5000000000056223/5000000000000000 : ℝ) by norm_num, show 1+2*(569022303/25000000000000000000 : ℝ)=(12500000000569022303/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(576387270637529323/100000000000000000000 : ℝ)+(569022303/25000000000000000000 : ℝ) ≤ ((69363330698508400979/69365000000000000000 : ℝ)+(355170696081/69365000000000 : ℝ)*((27981/100000 : ℝ)+(47/20000 : ℝ)))^(8291/2048 : ℝ) := by
    rw [show (69363330698508400979/69365000000000000000 : ℝ)+(355170696081/69365000000000 : ℝ)*((27981/100000 : ℝ)+(47/20000 : ℝ))=(5007103413977843/5000000000000000 : ℝ) by norm_num, show 1+(576387270637529323/100000000000000000000 : ℝ)+(569022303/25000000000000000000 : ℝ)=(20115277454582723707/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(576387270637529323/100000000000000000000 : ℝ) ≤ ((69363330698508400979/69365000000000000000 : ℝ)+2*(355170696081/69365000000000 : ℝ)*(27981/100000 : ℝ))^(8291/2048 : ℝ) := by
    rw [show (69363330698508400979/69365000000000000000 : ℝ)+2*(355170696081/69365000000000 : ℝ)*(27981/100000 : ℝ)=(5014206827899463/5000000000000000 : ℝ) by norm_num, show 1+2*(576387270637529323/100000000000000000000 : ℝ)=(50576387270637529323/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69363330698508400979/69365000000000000000 : ℝ)*(X 1 0+X 2 0)+(355170696081/69365000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (47/20000 : ℝ)) (hi := (27981/100000 : ℝ)) (c := (69363330698508400979/69365000000000000000 : ℝ)) (alpha := (355170696081/69365000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69363330698508400979/69365000000000000000 : ℝ)*(X 0 1+X 2 1)+(355170696081/69365000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (47/20000 : ℝ)) (hi := (27981/100000 : ℝ)) (c := (69363330698508400979/69365000000000000000 : ℝ)) (alpha := (355170696081/69365000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69363330698508400979/69365000000000000000 : ℝ)*(X 0 2+X 1 2)+(355170696081/69365000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (47/20000 : ℝ)) (hi := (27981/100000 : ℝ)) (c := (69363330698508400979/69365000000000000000 : ℝ)) (alpha := (355170696081/69365000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-84530331/400000000 : ℝ)*X 0 0+(142829157/250000000 : ℝ)*X 0 1+(1248283739/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5421491187/10000000000 : ℝ)*X 1 0+(-1251345479/5000000000 : ℝ)*X 1 1+(2496567543/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1084298449/2000000000 : ℝ)*X 2 0+(124828351/250000000 : ℝ)*X 2 1+(-1251345453/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321055601/10000000000 : ℝ)*X 0 0+(3668880019/10000000000 : ℝ)*X 0 1+(5089290351/10000000000 : ℝ)*X 0 2+(4321055601/10000000000 : ℝ)*X 1 0+(3668880019/10000000000 : ℝ)*X 1 1+(5089290351/10000000000 : ℝ)*X 1 2+(4321055601/10000000000 : ℝ)*X 2 0+(3668880019/10000000000 : ℝ)*X 2 1+(5089290351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2114126423/10000000000 : ℝ)*X 0 0+(1250782297/2500000000 : ℝ)*X 0 1+(114059427/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((654661329/1250000000 : ℝ)*X 1 0+(-358570879/2000000000 : ℝ)*X 1 1+(5702971179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2618645327/5000000000 : ℝ)*X 2 0+(1425742827/2500000000 : ℝ)*X 2 1+(-56026693/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864553421/2000000000 : ℝ)*X 0 0+(5069575397/10000000000 : ℝ)*X 0 1+(3688990873/10000000000 : ℝ)*X 0 2+(864553421/2000000000 : ℝ)*X 1 0+(5069575397/10000000000 : ℝ)*X 1 1+(3688990873/10000000000 : ℝ)*X 1 2+(864553421/2000000000 : ℝ)*X 2 0+(5069575397/10000000000 : ℝ)*X 2 1+(3688990873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3116294684335166414168282271/433531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (204656773/100000000000000 : ℝ)*(base1) + (140981061/10000000000000 : ℝ)*(base19) + (1680841649/100000000000000 : ℝ)*(base23) + (99763869/100000000000000 : ℝ)*(upper3) + (190686553/100000000000000 : ℝ)*(upper5) + (261608678314417/25000000000000 : ℝ)*(major0) + (261608678314417/25000000000000 : ℝ)*(major1) + (261608678314417/25000000000000 : ℝ)*(major2) + (1388834218736587/100000000000000 : ℝ)*(sp0) + (1388839957742669/100000000000000 : ℝ)*(sp1) + (138883968671163/10000000000000 : ℝ)*(sp2) + (704024780266623/100000000000000 : ℝ)*(sp3) + (1470694693/20000000000000 : ℝ)*(sp4) + (1417216557/50000000000000 : ℝ)*(sp7) + (70402781935651/10000000000000 : ℝ)*(f.failure) + (1085032318401/78125000000 : ℝ)*(f.sum) + (11364109121897/13873000000000000000000000000 : ℝ)*base66 + (173001465090239243/1734125000000000000000000000000000 : ℝ)*base67 + (8553811338693010757/1734125000000000000000000000000000 : ℝ)*base70 + (890593452073614243/1734125000000000000000000000000000 : ℝ)*base71 + (33507746676057/13873000000000000000000000000 : ℝ)*base74 + (6434020145897489243/1734125000000000000000000000000000 : ℝ)*base75 + (2279712120869739243/1734125000000000000000000000000000 : ℝ)*base77 + (6344401318507739243/1734125000000000000000000000000000 : ℝ)*base79 + (87252736738863/13873000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1294071/1000000000000000000000 : ℝ)*base89 + (1294071/1000000000000000000000 : ℝ)*base91 + (1294071/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (763142172842775543962709633/173412500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54312831/100000000000000 : ℝ)*(base1) + (7769081/781250000000 : ℝ)*(base19) + (253957617/25000000000000 : ℝ)*(base23) + (19361663/20000000000000 : ℝ)*(upper3) + (97709013/100000000000000 : ℝ)*(upper5) + (107661236441391/10000000000000 : ℝ)*(major0) + (107661236441391/10000000000000 : ℝ)*(major1) + (107661236441391/10000000000000 : ℝ)*(major2) + (1937756521/50000000000000 : ℝ)*(sp1) + (33694899/781250000000 : ℝ)*(sp2) + (178611710179817/12500000000000 : ℝ)*(sp4) + (285777751434059/20000000000000 : ℝ)*(sp5) + (357222074587041/25000000000000 : ℝ)*(sp6) + (362165450349081/50000000000000 : ℝ)*(sp7) + (45270684688187/6250000000000 : ℝ)*(f.failure) + (178611703390713/12500000000000 : ℝ)*(f.sum) + (12793732408673/6936500000000000000000000000 : ℝ)*base66 + (301559699397778211/693650000000000000000000000000000 : ℝ)*base68 + (1100924337946621789/693650000000000000000000000000000 : ℝ)*base69 + (1030325141761921789/693650000000000000000000000000000 : ℝ)*base71 + (33913002701929/13873000000000000000000000000 : ℝ)*base74 + (652288292484571789/693650000000000000000000000000000 : ℝ)*base75 + (3971415984484621789/693650000000000000000000000000000 : ℝ)*base77 + (1281057834764621789/693650000000000000000000000000000 : ℝ)*base79 + (36488193221/11098400000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (9028273/625000000000000000000 : ℝ)*base90 + (9028273/625000000000000000000 : ℝ)*base92 + (9028273/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1099_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27981/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (47/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1081/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4127/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1099_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1099_s2_0 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2168837859/10000000000 : ℝ)*x 0 + (5519193691/10000000000 : ℝ)*x 1 + (643976299/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168837859/10000000000 : ℝ)^2073 ≤ (13137507334823/100000000000000 : ℝ)^1561 := by
    have hnat : (2168837859 : ℕ)^2073*100000000000000^1561 ≤ 13137507334823^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168837859 10000000000 13137507334823 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5519193691/10000000000 : ℝ)^2073 ≤ (2270817179453/5000000000000 : ℝ)^1561 := by
    have hnat : (5519193691 : ℕ)^2073*5000000000000^1561 ≤ 2270817179453^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519193691 10000000000 2270817179453 5000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (643976299/1250000000 : ℝ)^2073 ≤ (129519215819/312500000000 : ℝ)^1561 := by
    have hnat : (643976299 : ℕ)^2073*312500000000^1561 ≤ 129519215819^1561*1250000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643976299 1250000000 129519215819 312500000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2168837859/10000000000 : ℝ), (5519193691/10000000000 : ℝ), (643976299/1250000000 : ℝ)] ![(13137507334823/100000000000000 : ℝ), (2270817179453/5000000000000 : ℝ), (129519215819/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2168837859/10000000000 : ℝ)|^2073 ≤ (13137507334823/100000000000000 : ℝ)^1561
        have hw : |(-2168837859/10000000000 : ℝ)|=(2168837859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5519193691/10000000000 : ℝ)|^2073 ≤ (2270817179453/5000000000000 : ℝ)^1561
        have hw : |(5519193691/10000000000 : ℝ)|=(5519193691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(643976299/1250000000 : ℝ)|^2073 ≤ (129519215819/312500000000 : ℝ)^1561
        have hw : |(643976299/1250000000 : ℝ)|=(643976299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s2_1 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5375735229/10000000000 : ℝ)*x 0 + (-147510607/625000000 : ℝ)*x 1 + (515181149/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375735229/10000000000 : ℝ)^2073 ≤ (43855379470161/100000000000000 : ℝ)^1561 := by
    have hnat : (5375735229 : ℕ)^2073*100000000000000^1561 ≤ 43855379470161^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375735229 10000000000 43855379470161 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147510607/625000000 : ℝ)^2073 ≤ (3674614931387/25000000000000 : ℝ)^1561 := by
    have hnat : (147510607 : ℕ)^2073*25000000000000^1561 ≤ 3674614931387^1561*625000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147510607 625000000 3674614931387 25000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515181149/1000000000 : ℝ)^2073 ≤ (41446160792757/100000000000000 : ℝ)^1561 := by
    have hnat : (515181149 : ℕ)^2073*100000000000000^1561 ≤ 41446160792757^1561*1000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515181149 1000000000 41446160792757 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375735229/10000000000 : ℝ), (-147510607/625000000 : ℝ), (515181149/1000000000 : ℝ)] ![(43855379470161/100000000000000 : ℝ), (3674614931387/25000000000000 : ℝ), (41446160792757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375735229/10000000000 : ℝ)|^2073 ≤ (43855379470161/100000000000000 : ℝ)^1561
        have hw : |(5375735229/10000000000 : ℝ)|=(5375735229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-147510607/625000000 : ℝ)|^2073 ≤ (3674614931387/25000000000000 : ℝ)^1561
        have hw : |(-147510607/625000000 : ℝ)|=(147510607/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(515181149/1000000000 : ℝ)|^2073 ≤ (41446160792757/100000000000000 : ℝ)^1561
        have hw : |(515181149/1000000000 : ℝ)|=(515181149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s2_2 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (335983449/625000000 : ℝ)*x 0 + (5151811539/10000000000 : ℝ)*x 1 + (-2360169707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335983449/625000000 : ℝ)^2073 ≤ (548192237283/1250000000000 : ℝ)^1561 := by
    have hnat : (335983449 : ℕ)^2073*1250000000000^1561 ≤ 548192237283^1561*625000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335983449 625000000 548192237283 1250000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5151811539/10000000000 : ℝ)^2073 ≤ (41446161316257/100000000000000 : ℝ)^1561 := by
    have hnat : (5151811539 : ℕ)^2073*100000000000000^1561 ≤ 41446161316257^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151811539 10000000000 41446161316257 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2360169707/10000000000 : ℝ)^2073 ≤ (3674614921049/25000000000000 : ℝ)^1561 := by
    have hnat : (2360169707 : ℕ)^2073*25000000000000^1561 ≤ 3674614921049^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2360169707 10000000000 3674614921049 25000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335983449/625000000 : ℝ), (5151811539/10000000000 : ℝ), (-2360169707/10000000000 : ℝ)] ![(548192237283/1250000000000 : ℝ), (41446161316257/100000000000000 : ℝ), (3674614921049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335983449/625000000 : ℝ)|^2073 ≤ (548192237283/1250000000000 : ℝ)^1561
        have hw : |(335983449/625000000 : ℝ)|=(335983449/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5151811539/10000000000 : ℝ)|^2073 ≤ (41446161316257/100000000000000 : ℝ)^1561
        have hw : |(5151811539/10000000000 : ℝ)|=(5151811539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2360169707/10000000000 : ℝ)|^2073 ≤ (3674614921049/25000000000000 : ℝ)^1561
        have hw : |(-2360169707/10000000000 : ℝ)|=(2360169707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s2_3 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (544883747/1250000000 : ℝ)*x 0 + (4011775709/10000000000 : ℝ)*x 1 + (18502007/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544883747/1250000000 : ℝ)^2073 ≤ (33198378236853/100000000000000 : ℝ)^1561 := by
    have hnat : (544883747 : ℕ)^2073*100000000000000^1561 ≤ 33198378236853^1561*1250000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544883747 1250000000 33198378236853 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4011775709/10000000000 : ℝ)^2073 ≤ (5946522853959/20000000000000 : ℝ)^1561 := by
    have hnat : (4011775709 : ℕ)^2073*20000000000000^1561 ≤ 5946522853959^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4011775709 10000000000 5946522853959 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18502007/39062500 : ℝ)^2073 ≤ (18534503738077/50000000000000 : ℝ)^1561 := by
    have hnat : (18502007 : ℕ)^2073*50000000000000^1561 ≤ 18534503738077^1561*39062500^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18502007 39062500 18534503738077 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544883747/1250000000 : ℝ), (4011775709/10000000000 : ℝ), (18502007/39062500 : ℝ)] ![(33198378236853/100000000000000 : ℝ), (5946522853959/20000000000000 : ℝ), (18534503738077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544883747/1250000000 : ℝ)|^2073 ≤ (33198378236853/100000000000000 : ℝ)^1561
        have hw : |(544883747/1250000000 : ℝ)|=(544883747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4011775709/10000000000 : ℝ)|^2073 ≤ (5946522853959/20000000000000 : ℝ)^1561
        have hw : |(4011775709/10000000000 : ℝ)|=(4011775709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(18502007/39062500 : ℝ)|^2073 ≤ (18534503738077/50000000000000 : ℝ)^1561
        have hw : |(18502007/39062500 : ℝ)|=(18502007/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s2_4 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1084476423/5000000000 : ℝ)*x 0 + (6443027/12500000 : ℝ)*x 1 + (5516555753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084476423/5000000000 : ℝ)^2073 ≤ (13138432320067/100000000000000 : ℝ)^1561 := by
    have hnat : (1084476423 : ℕ)^2073*100000000000000^1561 ≤ 13138432320067^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084476423 5000000000 13138432320067 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6443027/12500000 : ℝ)^2073 ≤ (41474048681207/100000000000000 : ℝ)^1561 := by
    have hnat : (6443027 : ℕ)^2073*100000000000000^1561 ≤ 41474048681207^1561*12500000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6443027 12500000 41474048681207 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5516555753/10000000000 : ℝ)^2073 ≤ (9077503795443/20000000000000 : ℝ)^1561 := by
    have hnat : (5516555753 : ℕ)^2073*20000000000000^1561 ≤ 9077503795443^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516555753 10000000000 9077503795443 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1084476423/5000000000 : ℝ), (6443027/12500000 : ℝ), (5516555753/10000000000 : ℝ)] ![(13138432320067/100000000000000 : ℝ), (41474048681207/100000000000000 : ℝ), (9077503795443/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1084476423/5000000000 : ℝ)|^2073 ≤ (13138432320067/100000000000000 : ℝ)^1561
        have hw : |(-1084476423/5000000000 : ℝ)|=(1084476423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6443027/12500000 : ℝ)|^2073 ≤ (41474048681207/100000000000000 : ℝ)^1561
        have hw : |(6443027/12500000 : ℝ)|=(6443027/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5516555753/10000000000 : ℝ)|^2073 ≤ (9077503795443/20000000000000 : ℝ)^1561
        have hw : |(5516555753/10000000000 : ℝ)|=(5516555753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s2_5 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2641395653/5000000000 : ℝ)*x 0 + (-1995424913/10000000000 : ℝ)*x 1 + (5516555841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641395653/5000000000 : ℝ)^2073 ≤ (42851308480263/100000000000000 : ℝ)^1561 := by
    have hnat : (2641395653 : ℕ)^2073*100000000000000^1561 ≤ 42851308480263^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641395653 5000000000 42851308480263 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1995424913/10000000000 : ℝ)^2073 ≤ (11761171567099/100000000000000 : ℝ)^1561 := by
    have hnat : (1995424913 : ℕ)^2073*100000000000000^1561 ≤ 11761171567099^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995424913 10000000000 11761171567099 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5516555841/10000000000 : ℝ)^2073 ≤ (45387519938711/100000000000000 : ℝ)^1561 := by
    have hnat : (5516555841 : ℕ)^2073*100000000000000^1561 ≤ 45387519938711^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516555841 10000000000 45387519938711 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641395653/5000000000 : ℝ), (-1995424913/10000000000 : ℝ), (5516555841/10000000000 : ℝ)] ![(42851308480263/100000000000000 : ℝ), (11761171567099/100000000000000 : ℝ), (45387519938711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641395653/5000000000 : ℝ)|^2073 ≤ (42851308480263/100000000000000 : ℝ)^1561
        have hw : |(2641395653/5000000000 : ℝ)|=(2641395653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1995424913/10000000000 : ℝ)|^2073 ≤ (11761171567099/100000000000000 : ℝ)^1561
        have hw : |(-1995424913/10000000000 : ℝ)|=(1995424913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5516555841/10000000000 : ℝ)|^2073 ≤ (45387519938711/100000000000000 : ℝ)^1561
        have hw : |(5516555841/10000000000 : ℝ)|=(5516555841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s2_6 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (528279147/1000000000 : ℝ)*x 0 + (5516555771/10000000000 : ℝ)*x 1 + (-997712393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528279147/1000000000 : ℝ)^2073 ≤ (21425655123437/50000000000000 : ℝ)^1561 := by
    have hnat : (528279147 : ℕ)^2073*50000000000000^1561 ≤ 21425655123437^1561*1000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528279147 1000000000 21425655123437 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5516555771/10000000000 : ℝ)^2073 ≤ (9077503834777/20000000000000 : ℝ)^1561 := by
    have hnat : (5516555771 : ℕ)^2073*20000000000000^1561 ≤ 9077503834777^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516555771 10000000000 9077503834777 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (997712393/5000000000 : ℝ)^2073 ≤ (11761170573033/100000000000000 : ℝ)^1561 := by
    have hnat : (997712393 : ℕ)^2073*100000000000000^1561 ≤ 11761170573033^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997712393 5000000000 11761170573033 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528279147/1000000000 : ℝ), (5516555771/10000000000 : ℝ), (-997712393/5000000000 : ℝ)] ![(21425655123437/50000000000000 : ℝ), (9077503834777/20000000000000 : ℝ), (11761170573033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528279147/1000000000 : ℝ)|^2073 ≤ (21425655123437/50000000000000 : ℝ)^1561
        have hw : |(528279147/1000000000 : ℝ)|=(528279147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5516555771/10000000000 : ℝ)|^2073 ≤ (9077503834777/20000000000000 : ℝ)^1561
        have hw : |(5516555771/10000000000 : ℝ)|=(5516555771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-997712393/5000000000 : ℝ)|^2073 ≤ (11761170573033/100000000000000 : ℝ)^1561
        have hw : |(-997712393/5000000000 : ℝ)|=(997712393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s2_7 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4359298129/10000000000 : ℝ)*x 0 + (4731363411/10000000000 : ℝ)*x 1 + (4016977879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359298129/10000000000 : ℝ)^2073 ≤ (16600342888693/50000000000000 : ℝ)^1561 := by
    have hnat : (4359298129 : ℕ)^2073*50000000000000^1561 ≤ 16600342888693^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359298129 10000000000 16600342888693 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4731363411/10000000000 : ℝ)^2073 ≤ (37015488174781/100000000000000 : ℝ)^1561 := by
    have hnat : (4731363411 : ℕ)^2073*100000000000000^1561 ≤ 37015488174781^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4731363411 10000000000 37015488174781 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4016977879/10000000000 : ℝ)^2073 ≤ (7445956507751/25000000000000 : ℝ)^1561 := by
    have hnat : (4016977879 : ℕ)^2073*25000000000000^1561 ≤ 7445956507751^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016977879 10000000000 7445956507751 25000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359298129/10000000000 : ℝ), (4731363411/10000000000 : ℝ), (4016977879/10000000000 : ℝ)] ![(16600342888693/50000000000000 : ℝ), (37015488174781/100000000000000 : ℝ), (7445956507751/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359298129/10000000000 : ℝ)|^2073 ≤ (16600342888693/50000000000000 : ℝ)^1561
        have hw : |(4359298129/10000000000 : ℝ)|=(4359298129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4731363411/10000000000 : ℝ)|^2073 ≤ (37015488174781/100000000000000 : ℝ)^1561
        have hw : |(4731363411/10000000000 : ℝ)|=(4731363411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4016977879/10000000000 : ℝ)|^2073 ≤ (7445956507751/25000000000000 : ℝ)^1561
        have hw : |(4016977879/10000000000 : ℝ)|=(4016977879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1099_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4127/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1081/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (8871/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8317/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4127/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1081/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4127/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1081/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4127/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1081/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4127/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1081/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4127/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1081/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4127/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1081/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1081/20000 : ℝ) ^ (8291/2048 : ℝ) ≤ (148236902267307/20000000000000000000 : ℝ) := by
    have hpowers : (1081/20000 : ℝ)^8291 ≤ (148236902267307/20000000000000000000 : ℝ)^2048 := by
      have hnat : (1081 : ℕ)^8291*20000000000000000000^2048 ≤ 148236902267307^2048*20000^8291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1081 20000 148236902267307 20000000000000000000 8291 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1081/20000 : ℝ)) (X := (148236902267307/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4127/20000 : ℝ) ^ (8291/2048 : ℝ) ≤ (10499436650342111/6250000000000000000 : ℝ) := by
    have hpowers : (4127/20000 : ℝ)^8291 ≤ (10499436650342111/6250000000000000000 : ℝ)^2048 := by
      have hnat : (4127 : ℕ)^8291*6250000000000000000^2048 ≤ 10499436650342111^2048*20000^8291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4127 20000 10499436650342111 6250000000000000000 8291 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4127/20000 : ℝ)) (X := (10499436650342111/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000148236902267307/10000000000000000000 : ℝ) ≤ (2500009154127413/2500000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (10000148236902267307/10000000000000000000 : ℝ)^2048 ≤ (2500009154127413/2500000000000000 : ℝ)^8291 := by
      have hnat : (10000148236902267307 : ℕ)^2048*2500000000000000^8291 ≤ 2500009154127413^8291*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000148236902267307 10000000000000000000 2500009154127413 2500000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500009154127413/2500000000000000 : ℝ)) (X := (10000148236902267307/10000000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100168732170916810311/100000000000000000000 : ℝ) ≤ (10004165289809997/10000000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (100168732170916810311/100000000000000000000 : ℝ)^2048 ≤ (10004165289809997/10000000000000000 : ℝ)^8291 := by
      have hnat : (100168732170916810311 : ℕ)^2048*10000000000000000^8291 ≤ 10004165289809997^8291*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100168732170916810311 100000000000000000000 10004165289809997 10000000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004165289809997/10000000000000000 : ℝ)) (X := (100168732170916810311/100000000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3135499436650342111/3125000000000000000 : ℝ) ≤ (5004146981555171/5000000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (3135499436650342111/3125000000000000000 : ℝ)^2048 ≤ (5004146981555171/5000000000000000 : ℝ)^8291 := by
      have hnat : (3135499436650342111 : ℕ)^2048*5000000000000000^8291 ≤ 5004146981555171^8291*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3135499436650342111 3125000000000000000 5004146981555171 5000000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004146981555171/5000000000000000 : ℝ)) (X := (3135499436650342111/3125000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(148236902267307/20000000000000000000 : ℝ) ≤ ((15225592671106527051/15230000000000000000 : ℝ)+2*(825734660069/304600000000000 : ℝ)*(1081/20000 : ℝ))^(8291/2048 : ℝ) := by
    rw [show (15225592671106527051/15230000000000000000 : ℝ)+2*(825734660069/304600000000000 : ℝ)*(1081/20000 : ℝ)=(2500009154127413/2500000000000000 : ℝ) by norm_num, show 1+2*(148236902267307/20000000000000000000 : ℝ)=(10000148236902267307/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10499436650342111/6250000000000000000 : ℝ)+(148236902267307/20000000000000000000 : ℝ) ≤ ((15225592671106527051/15230000000000000000 : ℝ)+(825734660069/304600000000000 : ℝ)*((4127/20000 : ℝ)+(1081/20000 : ℝ)))^(8291/2048 : ℝ) := by
    rw [show (15225592671106527051/15230000000000000000 : ℝ)+(825734660069/304600000000000 : ℝ)*((4127/20000 : ℝ)+(1081/20000 : ℝ))=(10004165289809997/10000000000000000 : ℝ) by norm_num, show 1+(10499436650342111/6250000000000000000 : ℝ)+(148236902267307/20000000000000000000 : ℝ)=(100168732170916810311/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10499436650342111/6250000000000000000 : ℝ) ≤ ((15225592671106527051/15230000000000000000 : ℝ)+2*(825734660069/304600000000000 : ℝ)*(4127/20000 : ℝ))^(8291/2048 : ℝ) := by
    rw [show (15225592671106527051/15230000000000000000 : ℝ)+2*(825734660069/304600000000000 : ℝ)*(4127/20000 : ℝ)=(5004146981555171/5000000000000000 : ℝ) by norm_num, show 1+2*(10499436650342111/6250000000000000000 : ℝ)=(3135499436650342111/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15225592671106527051/15230000000000000000 : ℝ)*(X 1 0+X 2 0)+(825734660069/304600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (1081/20000 : ℝ)) (hi := (4127/20000 : ℝ)) (c := (15225592671106527051/15230000000000000000 : ℝ)) (alpha := (825734660069/304600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15225592671106527051/15230000000000000000 : ℝ)*(X 0 1+X 2 1)+(825734660069/304600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (1081/20000 : ℝ)) (hi := (4127/20000 : ℝ)) (c := (15225592671106527051/15230000000000000000 : ℝ)) (alpha := (825734660069/304600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15225592671106527051/15230000000000000000 : ℝ)*(X 0 2+X 1 2)+(825734660069/304600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (1081/20000 : ℝ)) (hi := (4127/20000 : ℝ)) (c := (15225592671106527051/15230000000000000000 : ℝ)) (alpha := (825734660069/304600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2168837859/10000000000 : ℝ)*X 0 0+(5519193691/10000000000 : ℝ)*X 0 1+(643976299/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5375735229/10000000000 : ℝ)*X 1 0+(-147510607/625000000 : ℝ)*X 1 1+(515181149/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335983449/625000000 : ℝ)*X 2 0+(5151811539/10000000000 : ℝ)*X 2 1+(-2360169707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544883747/1250000000 : ℝ)*X 0 0+(4011775709/10000000000 : ℝ)*X 0 1+(18502007/39062500 : ℝ)*X 0 2+(544883747/1250000000 : ℝ)*X 1 0+(4011775709/10000000000 : ℝ)*X 1 1+(18502007/39062500 : ℝ)*X 1 2+(544883747/1250000000 : ℝ)*X 2 0+(4011775709/10000000000 : ℝ)*X 2 1+(18502007/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1084476423/5000000000 : ℝ)*X 0 0+(6443027/12500000 : ℝ)*X 0 1+(5516555753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2641395653/5000000000 : ℝ)*X 1 0+(-1995424913/10000000000 : ℝ)*X 1 1+(5516555841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((528279147/1000000000 : ℝ)*X 2 0+(5516555771/10000000000 : ℝ)*X 2 1+(-997712393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359298129/10000000000 : ℝ)*X 0 0+(4731363411/10000000000 : ℝ)*X 0 1+(4016977879/10000000000 : ℝ)*X 0 2+(4359298129/10000000000 : ℝ)*X 1 0+(4731363411/10000000000 : ℝ)*X 1 1+(4016977879/10000000000 : ℝ)*X 1 2+(4359298129/10000000000 : ℝ)*X 2 0+(4731363411/10000000000 : ℝ)*X 2 1+(4016977879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133831148107534205919822849/19037500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (194991577/25000000000000 : ℝ)*(base19) + (505752091/100000000000000 : ℝ)*(base23) + (99421607/50000000000000 : ℝ)*(upper3) + (135161391/100000000000000 : ℝ)*(upper4) + (1724773/50000000000000 : ℝ)*(upper5) + (102545010523367/5000000000000 : ℝ)*(major0) + (102545010523367/5000000000000 : ℝ)*(major1) + (102545010523367/5000000000000 : ℝ)*(major2) + (680491946754049/25000000000000 : ℝ)*(sp0) + (1360990058408279/50000000000000 : ℝ)*(sp1) + (340247548878847/12500000000000 : ℝ)*(sp2) + (1379813100398221/100000000000000 : ℝ)*(sp3) + (13109766669/100000000000000 : ℝ)*(sp4) + (3094712293/50000000000000 : ℝ)*(sp7) + (1379819289822807/100000000000000 : ℝ)*(f.failure) + (1360990448391433/50000000000000 : ℝ)*(f.sum) + (3505254403/1218400000000000000000000 : ℝ)*base65 + (1381327681717600717/76150000000000000000000000000000 : ℝ)*base67 + (587601280122000717/76150000000000000000000000000000 : ℝ)*base69 + (506293537286450717/76150000000000000000000000000000 : ℝ)*base71 + (10412210465649/1523000000000000000000000000 : ℝ)*base73 + (119892105091350717/76150000000000000000000000000000 : ℝ)*base75 + (171317225984150717/76150000000000000000000000000000 : ℝ)*base77 + (413471042974599283/76150000000000000000000000000000 : ℝ)*base80 + (295387437429/380750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (66153253/10000000000000000000000 : ℝ)*base90 + (66153253/10000000000000000000000 : ℝ)*base92 + (66153253/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (413746278950935767443808687/190375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (214885647/50000000000000 : ℝ)*(base19) + (143316051/25000000000000 : ℝ)*(base23) + (10327993/12500000000000 : ℝ)*(upper3) + (571207/5000000000000 : ℝ)*(lower4) + (14998533/50000000000000 : ℝ)*(upper5) + (520151500410721/25000000000000 : ℝ)*(major0) + (520151500410721/25000000000000 : ℝ)*(major1) + (520151500410721/25000000000000 : ℝ)*(major2) + (3683730747/100000000000000 : ℝ)*(sp1) + (1147600893/20000000000000 : ℝ)*(sp2) + (1380703483345963/50000000000000 : ℝ)*(sp4) + (552280570637977/20000000000000 : ℝ)*(sp5) + (345175081927907/12500000000000 : ℝ)*(sp6) + (1399804964149753/100000000000000 : ℝ)*(sp7) + (1399804964149753/100000000000000 : ℝ)*(f.failure) + (1380703483345963/50000000000000 : ℝ)*(f.sum) + (29568239906783/7615000000000000000000000000 : ℝ)*base65 + (4062162032113771/380750000000000000000000000000000 : ℝ)*base67 + (3054264650439386229/380750000000000000000000000000000 : ℝ)*base70 + (1364349058076863771/380750000000000000000000000000000 : ℝ)*base71 + (305492289861/951875000000000000000000000 : ℝ)*base73 + (644416604722863771/380750000000000000000000000000000 : ℝ)*base75 + (479431677338386229/380750000000000000000000000000000 : ℝ)*base78 + (1894512408043863771/380750000000000000000000000000000 : ℝ)*base79 + (17014437797921/3807500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (44201013/10000000000000000000000 : ℝ)*base89 + (44201013/10000000000000000000000 : ℝ)*base91 + (44201013/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1099_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4127/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1081/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8871/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8317/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1099_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1099_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8871/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8317/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1099_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1099_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1099_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8871/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8317/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1099_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

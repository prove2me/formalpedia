-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1163_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:41:04.520468+00:00
-- url     : https://prove2.me/submissions/3fbe9c4d-5e6b-4ebe-a35d-393916fcd87b

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
theorem support_rectangle_w1163_s0_0 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1885182049/10000000000 : ℝ)*x 0 + (1512372301/2500000000 : ℝ)*x 1 + (2391561257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885182049/10000000000 : ℝ)^2089 ≤ (2741728004427/25000000000000 : ℝ)^1577 := by
    have hnat : (1885182049 : ℕ)^2089*25000000000000^1577 ≤ 2741728004427^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885182049 10000000000 2741728004427 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1512372301/2500000000 : ℝ)^2089 ≤ (51386608298141/100000000000000 : ℝ)^1577 := by
    have hnat : (1512372301 : ℕ)^2089*100000000000000^1577 ≤ 51386608298141^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512372301 2500000000 51386608298141 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2391561257/5000000000 : ℝ)^2089 ≤ (7529295934397/20000000000000 : ℝ)^1577 := by
    have hnat : (2391561257 : ℕ)^2089*20000000000000^1577 ≤ 7529295934397^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2391561257 5000000000 7529295934397 20000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1885182049/10000000000 : ℝ), (1512372301/2500000000 : ℝ), (2391561257/5000000000 : ℝ)] ![(2741728004427/25000000000000 : ℝ), (51386608298141/100000000000000 : ℝ), (7529295934397/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1885182049/10000000000 : ℝ)|^2089 ≤ (2741728004427/25000000000000 : ℝ)^1577
        have hw : |(-1885182049/10000000000 : ℝ)|=(1885182049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1512372301/2500000000 : ℝ)|^2089 ≤ (51386608298141/100000000000000 : ℝ)^1577
        have hw : |(1512372301/2500000000 : ℝ)|=(1512372301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2391561257/5000000000 : ℝ)|^2089 ≤ (7529295934397/20000000000000 : ℝ)^1577
        have hw : |(2391561257/5000000000 : ℝ)|=(2391561257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s0_1 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1103122113/2000000000 : ℝ)*x 0 + (-2611333969/10000000000 : ℝ)*x 1 + (1195780621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103122113/2000000000 : ℝ)^2089 ≤ (45467129794801/100000000000000 : ℝ)^1577 := by
    have hnat : (1103122113 : ℕ)^2089*100000000000000^1577 ≤ 45467129794801^1577*2000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103122113 2000000000 45467129794801 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2611333969/10000000000 : ℝ)^2089 ≤ (8443195417879/50000000000000 : ℝ)^1577 := by
    have hnat : (2611333969 : ℕ)^2089*50000000000000^1577 ≤ 8443195417879^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611333969 10000000000 8443195417879 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1195780621/2500000000 : ℝ)^2089 ≤ (9411619839801/25000000000000 : ℝ)^1577 := by
    have hnat : (1195780621 : ℕ)^2089*25000000000000^1577 ≤ 9411619839801^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195780621 2500000000 9411619839801 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103122113/2000000000 : ℝ), (-2611333969/10000000000 : ℝ), (1195780621/2500000000 : ℝ)] ![(45467129794801/100000000000000 : ℝ), (8443195417879/50000000000000 : ℝ), (9411619839801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103122113/2000000000 : ℝ)|^2089 ≤ (45467129794801/100000000000000 : ℝ)^1577
        have hw : |(1103122113/2000000000 : ℝ)|=(1103122113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2611333969/10000000000 : ℝ)|^2089 ≤ (8443195417879/50000000000000 : ℝ)^1577
        have hw : |(-2611333969/10000000000 : ℝ)|=(2611333969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1195780621/2500000000 : ℝ)|^2089 ≤ (9411619839801/25000000000000 : ℝ)^1577
        have hw : |(1195780621/2500000000 : ℝ)|=(1195780621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s0_2 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5515610589/10000000000 : ℝ)*x 0 + (956624497/2000000000 : ℝ)*x 1 + (-2611333937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5515610589/10000000000 : ℝ)^2089 ≤ (45467130056873/100000000000000 : ℝ)^1577 := by
    have hnat : (5515610589 : ℕ)^2089*100000000000000^1577 ≤ 45467130056873^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515610589 10000000000 45467130056873 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (956624497/2000000000 : ℝ)^2089 ≤ (3764647936963/10000000000000 : ℝ)^1577 := by
    have hnat : (956624497 : ℕ)^2089*10000000000000^1577 ≤ 3764647936963^1577*2000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956624497 2000000000 3764647936963 10000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2611333937/10000000000 : ℝ)^2089 ≤ (4221597640411/25000000000000 : ℝ)^1577 := by
    have hnat : (2611333937 : ℕ)^2089*25000000000000^1577 ≤ 4221597640411^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611333937 10000000000 4221597640411 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5515610589/10000000000 : ℝ), (956624497/2000000000 : ℝ), (-2611333937/10000000000 : ℝ)] ![(45467130056873/100000000000000 : ℝ), (3764647936963/10000000000000 : ℝ), (4221597640411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5515610589/10000000000 : ℝ)|^2089 ≤ (45467130056873/100000000000000 : ℝ)^1577
        have hw : |(5515610589/10000000000 : ℝ)|=(5515610589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(956624497/2000000000 : ℝ)|^2089 ≤ (3764647936963/10000000000000 : ℝ)^1577
        have hw : |(956624497/2000000000 : ℝ)|=(956624497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2611333937/10000000000 : ℝ)|^2089 ≤ (4221597640411/25000000000000 : ℝ)^1577
        have hw : |(-2611333937/10000000000 : ℝ)|=(2611333937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s0_3 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4199297707/10000000000 : ℝ)*x 0 + (3120125633/10000000000 : ℝ)*x 1 + (706238891/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199297707/10000000000 : ℝ)^2089 ≤ (3168360055373/10000000000000 : ℝ)^1577 := by
    have hnat : (4199297707 : ℕ)^2089*10000000000000^1577 ≤ 3168360055373^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199297707 10000000000 3168360055373 10000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3120125633/10000000000 : ℝ)^2089 ≤ (10688491289641/50000000000000 : ℝ)^1577 := by
    have hnat : (3120125633 : ℕ)^2089*50000000000000^1577 ≤ 10688491289641^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3120125633 10000000000 10688491289641 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (706238891/1250000000 : ℝ)^2089 ≤ (46939416848491/100000000000000 : ℝ)^1577 := by
    have hnat : (706238891 : ℕ)^2089*100000000000000^1577 ≤ 46939416848491^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706238891 1250000000 46939416848491 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199297707/10000000000 : ℝ), (3120125633/10000000000 : ℝ), (706238891/1250000000 : ℝ)] ![(3168360055373/10000000000000 : ℝ), (10688491289641/50000000000000 : ℝ), (46939416848491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199297707/10000000000 : ℝ)|^2089 ≤ (3168360055373/10000000000000 : ℝ)^1577
        have hw : |(4199297707/10000000000 : ℝ)|=(4199297707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3120125633/10000000000 : ℝ)|^2089 ≤ (10688491289641/50000000000000 : ℝ)^1577
        have hw : |(3120125633/10000000000 : ℝ)|=(3120125633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(706238891/1250000000 : ℝ)|^2089 ≤ (46939416848491/100000000000000 : ℝ)^1577
        have hw : |(706238891/1250000000 : ℝ)|=(706238891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s0_4 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-236283267/1250000000 : ℝ)*x 0 + (4815780407/10000000000 : ℝ)*x 1 + (6015681551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (236283267/1250000000 : ℝ)^2089 ≤ (2201221585651/20000000000000 : ℝ)^1577 := by
    have hnat : (236283267 : ℕ)^2089*20000000000000^1577 ≤ 2201221585651^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236283267 1250000000 2201221585651 20000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4815780407/10000000000 : ℝ)^2089 ≤ (37987349161839/100000000000000 : ℝ)^1577 := by
    have hnat : (4815780407 : ℕ)^2089*100000000000000^1577 ≤ 37987349161839^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4815780407 10000000000 37987349161839 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6015681551/10000000000 : ℝ)^2089 ≤ (637581786091/1250000000000 : ℝ)^1577 := by
    have hnat : (6015681551 : ℕ)^2089*1250000000000^1577 ≤ 637581786091^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6015681551 10000000000 637581786091 1250000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-236283267/1250000000 : ℝ), (4815780407/10000000000 : ℝ), (6015681551/10000000000 : ℝ)] ![(2201221585651/20000000000000 : ℝ), (37987349161839/100000000000000 : ℝ), (637581786091/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-236283267/1250000000 : ℝ)|^2089 ≤ (2201221585651/20000000000000 : ℝ)^1577
        have hw : |(-236283267/1250000000 : ℝ)|=(236283267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4815780407/10000000000 : ℝ)|^2089 ≤ (37987349161839/100000000000000 : ℝ)^1577
        have hw : |(4815780407/10000000000 : ℝ)|=(4815780407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6015681551/10000000000 : ℝ)|^2089 ≤ (637581786091/1250000000000 : ℝ)^1577
        have hw : |(6015681551/10000000000 : ℝ)|=(6015681551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s0_5 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5171408973/10000000000 : ℝ)*x 0 + (-1378775051/10000000000 : ℝ)*x 1 + (6015681343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171408973/10000000000 : ℝ)^2089 ≤ (41747177149483/100000000000000 : ℝ)^1577 := by
    have hnat : (5171408973 : ℕ)^2089*100000000000000^1577 ≤ 41747177149483^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171408973 10000000000 41747177149483 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1378775051/10000000000 : ℝ)^2089 ≤ (3623141141853/50000000000000 : ℝ)^1577 := by
    have hnat : (1378775051 : ℕ)^2089*50000000000000^1577 ≤ 3623141141853^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378775051 10000000000 3623141141853 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6015681343/10000000000 : ℝ)^2089 ≤ (25503270275537/50000000000000 : ℝ)^1577 := by
    have hnat : (6015681343 : ℕ)^2089*50000000000000^1577 ≤ 25503270275537^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6015681343 10000000000 25503270275537 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171408973/10000000000 : ℝ), (-1378775051/10000000000 : ℝ), (6015681343/10000000000 : ℝ)] ![(41747177149483/100000000000000 : ℝ), (3623141141853/50000000000000 : ℝ), (25503270275537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171408973/10000000000 : ℝ)|^2089 ≤ (41747177149483/100000000000000 : ℝ)^1577
        have hw : |(5171408973/10000000000 : ℝ)|=(5171408973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1378775051/10000000000 : ℝ)|^2089 ≤ (3623141141853/50000000000000 : ℝ)^1577
        have hw : |(-1378775051/10000000000 : ℝ)|=(1378775051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6015681343/10000000000 : ℝ)|^2089 ≤ (25503270275537/50000000000000 : ℝ)^1577
        have hw : |(6015681343/10000000000 : ℝ)|=(6015681343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s0_6 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (323213059/625000000 : ℝ)*x 0 + (240627257/400000000 : ℝ)*x 1 + (-1378774963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323213059/625000000 : ℝ)^2089 ≤ (5218397104921/12500000000000 : ℝ)^1577 := by
    have hnat : (323213059 : ℕ)^2089*12500000000000^1577 ≤ 5218397104921^1577*625000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323213059 625000000 5218397104921 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240627257/400000000 : ℝ)^2089 ≤ (25503270736039/50000000000000 : ℝ)^1577 := by
    have hnat : (240627257 : ℕ)^2089*50000000000000^1577 ≤ 25503270736039^1577*400000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240627257 400000000 25503270736039 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1378774963/10000000000 : ℝ)^2089 ≤ (3623140835529/50000000000000 : ℝ)^1577 := by
    have hnat : (1378774963 : ℕ)^2089*50000000000000^1577 ≤ 3623140835529^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378774963 10000000000 3623140835529 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(323213059/625000000 : ℝ), (240627257/400000000 : ℝ), (-1378774963/10000000000 : ℝ)] ![(5218397104921/12500000000000 : ℝ), (25503270736039/50000000000000 : ℝ), (3623140835529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(323213059/625000000 : ℝ)|^2089 ≤ (5218397104921/12500000000000 : ℝ)^1577
        have hw : |(323213059/625000000 : ℝ)|=(323213059/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(240627257/400000000 : ℝ)|^2089 ≤ (25503270736039/50000000000000 : ℝ)^1577
        have hw : |(240627257/400000000 : ℝ)|=(240627257/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1378774963/10000000000 : ℝ)|^2089 ≤ (3623140835529/50000000000000 : ℝ)^1577
        have hw : |(-1378774963/10000000000 : ℝ)|=(1378774963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s0_7 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4209454223/10000000000 : ℝ)*x 0 + (1116934213/2000000000 : ℝ)*x 1 + (3187662461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4209454223/10000000000 : ℝ)^2089 ≤ (31785150513639/100000000000000 : ℝ)^1577 := by
    have hnat : (4209454223 : ℕ)^2089*100000000000000^1577 ≤ 31785150513639^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209454223 10000000000 31785150513639 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1116934213/2000000000 : ℝ)^2089 ≤ (46222778208881/100000000000000 : ℝ)^1577 := by
    have hnat : (1116934213 : ℕ)^2089*100000000000000^1577 ≤ 46222778208881^1577*2000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116934213 2000000000 46222778208881 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3187662461/10000000000 : ℝ)^2089 ≤ (10996035628607/50000000000000 : ℝ)^1577 := by
    have hnat : (3187662461 : ℕ)^2089*50000000000000^1577 ≤ 10996035628607^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3187662461 10000000000 10996035628607 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4209454223/10000000000 : ℝ), (1116934213/2000000000 : ℝ), (3187662461/10000000000 : ℝ)] ![(31785150513639/100000000000000 : ℝ), (46222778208881/100000000000000 : ℝ), (10996035628607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4209454223/10000000000 : ℝ)|^2089 ≤ (31785150513639/100000000000000 : ℝ)^1577
        have hw : |(4209454223/10000000000 : ℝ)|=(4209454223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1116934213/2000000000 : ℝ)|^2089 ≤ (46222778208881/100000000000000 : ℝ)^1577
        have hw : |(1116934213/2000000000 : ℝ)|=(1116934213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3187662461/10000000000 : ℝ)|^2089 ≤ (10996035628607/50000000000000 : ℝ)^1577
        have hw : |(3187662461/10000000000 : ℝ)|=(3187662461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1163_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1/200 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5547/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8355/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8355 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8355*1^2048 ≤ 0^2048*1^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8355/2048 : ℝ) ≤ (2379950816924383521/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8355 ≤ (2379950816924383521/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8355*100000000000000000000^2048 ≤ 2379950816924383521^2048*5^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2379950816924383521 100000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2379950816924383521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8355 := by
      have hnat : (1 : ℕ)^2048*1^8355 ≤ 1^8355*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102379950816924383521/100000000000000000000 : ℝ) ≤ (10057821128886619/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (102379950816924383521/100000000000000000000 : ℝ)^2048 ≤ (10057821128886619/10000000000000000 : ℝ)^8355 := by
      have hnat : (102379950816924383521 : ℕ)^2048*10000000000000000^8355 ≤ 10057821128886619^8355*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102379950816924383521 100000000000000000000 10057821128886619 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10057821128886619/10000000000000000 : ℝ)) (X := (102379950816924383521/100000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52379950816924383521/50000000000000000000 : ℝ) ≤ (5057821128886619/5000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (52379950816924383521/50000000000000000000 : ℝ)^2048 ≤ (5057821128886619/5000000000000000 : ℝ)^8355 := by
      have hnat : (52379950816924383521 : ℕ)^2048*5000000000000000^8355 ≤ 5057821128886619^8355*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52379950816924383521 50000000000000000000 5057821128886619 5000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5057821128886619/5000000000000000 : ℝ)) (X := (52379950816924383521/50000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(57821128886619/4000000000000000 : ℝ)*(0 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(57821128886619/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2379950816924383521/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(57821128886619/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8355/2048 : ℝ) := by
    rw [show (1 : ℝ)+(57821128886619/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10057821128886619/10000000000000000 : ℝ) by norm_num, show 1+(2379950816924383521/100000000000000000000 : ℝ)+(0 : ℝ)=(102379950816924383521/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2379950816924383521/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(57821128886619/4000000000000000 : ℝ)*(2/5 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(57821128886619/4000000000000000 : ℝ)*(2/5 : ℝ)=(5057821128886619/5000000000000000 : ℝ) by norm_num, show 1+2*(2379950816924383521/100000000000000000000 : ℝ)=(52379950816924383521/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(57821128886619/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57821128886619/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(57821128886619/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57821128886619/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(57821128886619/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57821128886619/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1885182049/10000000000 : ℝ)*X 0 0+(1512372301/2500000000 : ℝ)*X 0 1+(2391561257/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1103122113/2000000000 : ℝ)*X 1 0+(-2611333969/10000000000 : ℝ)*X 1 1+(1195780621/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5515610589/10000000000 : ℝ)*X 2 0+(956624497/2000000000 : ℝ)*X 2 1+(-2611333937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4199297707/10000000000 : ℝ)*X 0 0+(3120125633/10000000000 : ℝ)*X 0 1+(706238891/1250000000 : ℝ)*X 0 2+(4199297707/10000000000 : ℝ)*X 1 0+(3120125633/10000000000 : ℝ)*X 1 1+(706238891/1250000000 : ℝ)*X 1 2+(4199297707/10000000000 : ℝ)*X 2 0+(3120125633/10000000000 : ℝ)*X 2 1+(706238891/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-236283267/1250000000 : ℝ)*X 0 0+(4815780407/10000000000 : ℝ)*X 0 1+(6015681551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5171408973/10000000000 : ℝ)*X 1 0+(-1378775051/10000000000 : ℝ)*X 1 1+(6015681343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((323213059/625000000 : ℝ)*X 2 0+(240627257/400000000 : ℝ)*X 2 1+(-1378774963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4209454223/10000000000 : ℝ)*X 0 0+(1116934213/2000000000 : ℝ)*X 0 1+(3187662461/10000000000 : ℝ)*X 0 2+(4209454223/10000000000 : ℝ)*X 1 0+(1116934213/2000000000 : ℝ)*X 1 1+(3187662461/10000000000 : ℝ)*X 1 2+(4209454223/10000000000 : ℝ)*X 2 0+(1116934213/2000000000 : ℝ)*X 2 1+(3187662461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (110803683856846489356219/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5862497/25000000000000 : ℝ)*(base1) + (535072057/100000000000000 : ℝ)*(base19) + (499357881/100000000000000 : ℝ)*(base23) + (19575113/50000000000000 : ℝ)*(base24) + (24334917/20000000000000 : ℝ)*(upper3) + (592477805729467/100000000000000 : ℝ)*(major0) + (592477805729467/100000000000000 : ℝ)*(major1) + (592477805729467/100000000000000 : ℝ)*(major2) + (197415616767677/25000000000000 : ℝ)*(sp0) + (394831537940273/50000000000000 : ℝ)*(sp1) + (49353942027781/6250000000000 : ℝ)*(sp2) + (19764548653871/5000000000000 : ℝ)*(sp3) + (583665941/50000000000000 : ℝ)*(sp4) + (930109793/100000000000000 : ℝ)*(sp7) + (988229816593/250000000000 : ℝ)*(f.failure) + (394831805476301/50000000000000 : ℝ)*(f.sum) + (512365796697927/200000000000000000000000000000 : ℝ)*base66 + (2726950694097927/400000000000000000000000000000 : ℝ)*base68 + (2845318860497927/400000000000000000000000000000 : ℝ)*base70 + (3568603277297927/400000000000000000000000000000 : ℝ)*base72 + (259519035897927/200000000000000000000000000000 : ℝ)*base74 + (4511145808497927/400000000000000000000000000000 : ℝ)*base76 + (3591323138897927/400000000000000000000000000000 : ℝ)*base78 + (4078718755697927/400000000000000000000000000000 : ℝ)*base80 + (31526914102073/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (174137/25000000000000000000 : ℝ)*base89 + (174137/25000000000000000000 : ℝ)*base91 + (174137/25000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (351278209984713735429543/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84652311/100000000000000 : ℝ)*(base1) + (174440591/10000000000000 : ℝ)*(base19) + (1740103887/100000000000000 : ℝ)*(base23) + (189003363/100000000000000 : ℝ)*(upper3) + (51619517/25000000000000 : ℝ)*(upper5) + (156323617324199/25000000000000 : ℝ)*(major0) + (156323617324199/25000000000000 : ℝ)*(major1) + (156323617324199/25000000000000 : ℝ)*(major2) + (3551673327/100000000000000 : ℝ)*(sp1) + (3557254063/100000000000000 : ℝ)*(sp2) + (833402097687923/100000000000000 : ℝ)*(sp4) + (104174589619547/12500000000000 : ℝ)*(sp5) + (833396715677663/100000000000000 : ℝ)*(sp6) + (41718660672019/10000000000000 : ℝ)*(sp7) + (417186691372501/100000000000000 : ℝ)*(f.failure) + (208350503258903/25000000000000 : ℝ)*(f.sum) + (55555493893181/50000000000000000000000000000 : ℝ)*base65 + (294322134893181/100000000000000000000000000000 : ℝ)*base67 + (596894780306819/100000000000000000000000000000 : ℝ)*base70 + (372927561306819/100000000000000000000000000000 : ℝ)*base72 + (308455720443181/50000000000000000000000000000 : ℝ)*base73 + (686721646606819/100000000000000000000000000000 : ℝ)*base76 + (290870498906819/100000000000000000000000000000 : ℝ)*base78 + (466227032006819/100000000000000000000000000000 : ℝ)*base80 + (54255168506819/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (13236109/10000000000000000000000 : ℝ)*base89 + (13236109/10000000000000000000000 : ℝ)*base91 + (13236109/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1163_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1/200 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5547/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1163_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1163_s1_0 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1044161751/5000000000 : ℝ)*x 0 + (1423983713/2500000000 : ℝ)*x 1 + (25033167/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044161751/5000000000 : ℝ)^2089 ≤ (12559099460493/100000000000000 : ℝ)^1577 := by
    have hnat : (1044161751 : ℕ)^2089*100000000000000^1577 ≤ 12559099460493^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044161751 5000000000 12559099460493 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1423983713/2500000000 : ℝ)^2089 ≤ (23723295692519/50000000000000 : ℝ)^1577 := by
    have hnat : (1423983713 : ℕ)^2089*50000000000000^1577 ≤ 23723295692519^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423983713 2500000000 23723295692519 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25033167/50000000 : ℝ)^2089 ≤ (3999430913579/10000000000000 : ℝ)^1577 := by
    have hnat : (25033167 : ℕ)^2089*10000000000000^1577 ≤ 3999430913579^1577*50000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25033167 50000000 3999430913579 10000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1044161751/5000000000 : ℝ), (1423983713/2500000000 : ℝ), (25033167/50000000 : ℝ)] ![(12559099460493/100000000000000 : ℝ), (23723295692519/50000000000000 : ℝ), (3999430913579/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1044161751/5000000000 : ℝ)|^2089 ≤ (12559099460493/100000000000000 : ℝ)^1577
        have hw : |(-1044161751/5000000000 : ℝ)|=(1044161751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1423983713/2500000000 : ℝ)|^2089 ≤ (23723295692519/50000000000000 : ℝ)^1577
        have hw : |(1423983713/2500000000 : ℝ)|=(1423983713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25033167/50000000 : ℝ)|^2089 ≤ (3999430913579/10000000000000 : ℝ)^1577
        have hw : |(25033167/50000000 : ℝ)|=(25033167/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s1_1 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5417971583/10000000000 : ℝ)*x 0 + (-1229956549/5000000000 : ℝ)*x 1 + (9778579/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417971583/10000000000 : ℝ)^2089 ≤ (44404017623577/100000000000000 : ℝ)^1577 := by
    have hnat : (5417971583 : ℕ)^2089*100000000000000^1577 ≤ 44404017623577^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417971583 10000000000 44404017623577 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1229956549/5000000000 : ℝ)^2089 ≤ (3900420824393/25000000000000 : ℝ)^1577 := by
    have hnat : (1229956549 : ℕ)^2089*25000000000000^1577 ≤ 3900420824393^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229956549 5000000000 3900420824393 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9778579/19531250 : ℝ)^2089 ≤ (19997149530963/50000000000000 : ℝ)^1577 := by
    have hnat : (9778579 : ℕ)^2089*50000000000000^1577 ≤ 19997149530963^1577*19531250^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9778579 19531250 19997149530963 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417971583/10000000000 : ℝ), (-1229956549/5000000000 : ℝ), (9778579/19531250 : ℝ)] ![(44404017623577/100000000000000 : ℝ), (3900420824393/25000000000000 : ℝ), (19997149530963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417971583/10000000000 : ℝ)|^2089 ≤ (44404017623577/100000000000000 : ℝ)^1577
        have hw : |(5417971583/10000000000 : ℝ)|=(5417971583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1229956549/5000000000 : ℝ)|^2089 ≤ (3900420824393/25000000000000 : ℝ)^1577
        have hw : |(-1229956549/5000000000 : ℝ)|=(1229956549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9778579/19531250 : ℝ)|^2089 ≤ (19997149530963/50000000000000 : ℝ)^1577
        have hw : |(9778579/19531250 : ℝ)|=(9778579/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s1_2 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5417973693/10000000000 : ℝ)*x 0 + (2503315261/5000000000 : ℝ)*x 1 + (-2459912797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417973693/10000000000 : ℝ)^2089 ≤ (44404040530923/100000000000000 : ℝ)^1577 := by
    have hnat : (5417973693 : ℕ)^2089*100000000000000^1577 ≤ 44404040530923^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417973693 10000000000 44404040530923 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2503315261/5000000000 : ℝ)^2089 ≤ (39994278681401/100000000000000 : ℝ)^1577 := by
    have hnat : (2503315261 : ℕ)^2089*100000000000000^1577 ≤ 39994278681401^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503315261 5000000000 39994278681401 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2459912797/10000000000 : ℝ)^2089 ≤ (15601680768711/100000000000000 : ℝ)^1577 := by
    have hnat : (2459912797 : ℕ)^2089*100000000000000^1577 ≤ 15601680768711^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2459912797 10000000000 15601680768711 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417973693/10000000000 : ℝ), (2503315261/5000000000 : ℝ), (-2459912797/10000000000 : ℝ)] ![(44404040530923/100000000000000 : ℝ), (39994278681401/100000000000000 : ℝ), (15601680768711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417973693/10000000000 : ℝ)|^2089 ≤ (44404040530923/100000000000000 : ℝ)^1577
        have hw : |(5417973693/10000000000 : ℝ)|=(5417973693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2503315261/5000000000 : ℝ)|^2089 ≤ (39994278681401/100000000000000 : ℝ)^1577
        have hw : |(2503315261/5000000000 : ℝ)|=(2503315261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2459912797/10000000000 : ℝ)|^2089 ≤ (15601680768711/100000000000000 : ℝ)^1577
        have hw : |(-2459912797/10000000000 : ℝ)|=(2459912797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s1_3 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2157827689/5000000000 : ℝ)*x 0 + (368096497/1000000000 : ℝ)*x 1 + (1264489681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157827689/5000000000 : ℝ)^2089 ≤ (6570349107137/20000000000000 : ℝ)^1577 := by
    have hnat : (2157827689 : ℕ)^2089*20000000000000^1577 ≤ 6570349107137^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157827689 5000000000 6570349107137 20000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (368096497/1000000000 : ℝ)^2089 ≤ (26609929742881/100000000000000 : ℝ)^1577 := by
    have hnat : (368096497 : ℕ)^2089*100000000000000^1577 ≤ 26609929742881^1577*1000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368096497 1000000000 26609929742881 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1264489681/2500000000 : ℝ)^2089 ≤ (40538324704353/100000000000000 : ℝ)^1577 := by
    have hnat : (1264489681 : ℕ)^2089*100000000000000^1577 ≤ 40538324704353^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264489681 2500000000 40538324704353 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157827689/5000000000 : ℝ), (368096497/1000000000 : ℝ), (1264489681/2500000000 : ℝ)] ![(6570349107137/20000000000000 : ℝ), (26609929742881/100000000000000 : ℝ), (40538324704353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157827689/5000000000 : ℝ)|^2089 ≤ (6570349107137/20000000000000 : ℝ)^1577
        have hw : |(2157827689/5000000000 : ℝ)|=(2157827689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(368096497/1000000000 : ℝ)|^2089 ≤ (26609929742881/100000000000000 : ℝ)^1577
        have hw : |(368096497/1000000000 : ℝ)|=(368096497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1264489681/2500000000 : ℝ)|^2089 ≤ (40538324704353/100000000000000 : ℝ)^1577
        have hw : |(1264489681/2500000000 : ℝ)|=(1264489681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s1_4 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-104455257/500000000 : ℝ)*x 0 + (2507985033/5000000000 : ℝ)*x 1 + (5686411467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104455257/500000000 : ℝ)^2089 ≤ (12565326756643/100000000000000 : ℝ)^1577 := by
    have hnat : (104455257 : ℕ)^2089*100000000000000^1577 ≤ 12565326756643^1577*500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104455257 500000000 12565326756643 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2507985033/5000000000 : ℝ)^2089 ≤ (40093137674803/100000000000000 : ℝ)^1577 := by
    have hnat : (2507985033 : ℕ)^2089*100000000000000^1577 ≤ 40093137674803^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507985033 5000000000 40093137674803 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5686411467/10000000000 : ℝ)^2089 ≤ (47341535555067/100000000000000 : ℝ)^1577 := by
    have hnat : (5686411467 : ℕ)^2089*100000000000000^1577 ≤ 47341535555067^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5686411467 10000000000 47341535555067 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104455257/500000000 : ℝ), (2507985033/5000000000 : ℝ), (5686411467/10000000000 : ℝ)] ![(12565326756643/100000000000000 : ℝ), (40093137674803/100000000000000 : ℝ), (47341535555067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104455257/500000000 : ℝ)|^2089 ≤ (12565326756643/100000000000000 : ℝ)^1577
        have hw : |(-104455257/500000000 : ℝ)|=(104455257/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2507985033/5000000000 : ℝ)|^2089 ≤ (40093137674803/100000000000000 : ℝ)^1577
        have hw : |(2507985033/5000000000 : ℝ)|=(2507985033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5686411467/10000000000 : ℝ)|^2089 ≤ (47341535555067/100000000000000 : ℝ)^1577
        have hw : |(5686411467/10000000000 : ℝ)|=(5686411467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s1_5 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5241061817/10000000000 : ℝ)*x 0 + (-111258161/625000000 : ℝ)*x 1 + (1137282947/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241061817/10000000000 : ℝ)^2089 ≤ (10623410558079/25000000000000 : ℝ)^1577 := by
    have hnat : (5241061817 : ℕ)^2089*25000000000000^1577 ≤ 10623410558079^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241061817 10000000000 10623410558079 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111258161/625000000 : ℝ)^2089 ≤ (2541196540543/25000000000000 : ℝ)^1577 := by
    have hnat : (111258161 : ℕ)^2089*25000000000000^1577 ≤ 2541196540543^1577*625000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111258161 625000000 2541196540543 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1137282947/2000000000 : ℝ)^2089 ≤ (2367078579787/5000000000000 : ℝ)^1577 := by
    have hnat : (1137282947 : ℕ)^2089*5000000000000^1577 ≤ 2367078579787^1577*2000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137282947 2000000000 2367078579787 5000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241061817/10000000000 : ℝ), (-111258161/625000000 : ℝ), (1137282947/2000000000 : ℝ)] ![(10623410558079/25000000000000 : ℝ), (2541196540543/25000000000000 : ℝ), (2367078579787/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241061817/10000000000 : ℝ)|^2089 ≤ (10623410558079/25000000000000 : ℝ)^1577
        have hw : |(5241061817/10000000000 : ℝ)|=(5241061817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111258161/625000000 : ℝ)|^2089 ≤ (2541196540543/25000000000000 : ℝ)^1577
        have hw : |(-111258161/625000000 : ℝ)|=(111258161/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1137282947/2000000000 : ℝ)|^2089 ≤ (2367078579787/5000000000000 : ℝ)^1577
        have hw : |(1137282947/2000000000 : ℝ)|=(1137282947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s1_6 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5241060897/10000000000 : ℝ)*x 0 + (1421604043/2500000000 : ℝ)*x 1 + (-1780129787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241060897/10000000000 : ℝ)^2089 ≤ (21246816175677/50000000000000 : ℝ)^1577 := by
    have hnat : (5241060897 : ℕ)^2089*50000000000000^1577 ≤ 21246816175677^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241060897 10000000000 21246816175677 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1421604043/2500000000 : ℝ)^2089 ≤ (11835396860873/25000000000000 : ℝ)^1577 := by
    have hnat : (1421604043 : ℕ)^2089*25000000000000^1577 ≤ 11835396860873^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1421604043 2500000000 11835396860873 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1780129787/10000000000 : ℝ)^2089 ≤ (5082390097077/50000000000000 : ℝ)^1577 := by
    have hnat : (1780129787 : ℕ)^2089*50000000000000^1577 ≤ 5082390097077^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1780129787 10000000000 5082390097077 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241060897/10000000000 : ℝ), (1421604043/2500000000 : ℝ), (-1780129787/10000000000 : ℝ)] ![(21246816175677/50000000000000 : ℝ), (11835396860873/25000000000000 : ℝ), (5082390097077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241060897/10000000000 : ℝ)|^2089 ≤ (21246816175677/50000000000000 : ℝ)^1577
        have hw : |(5241060897/10000000000 : ℝ)|=(5241060897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1421604043/2500000000 : ℝ)|^2089 ≤ (11835396860873/25000000000000 : ℝ)^1577
        have hw : |(1421604043/2500000000 : ℝ)|=(1421604043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1780129787/10000000000 : ℝ)|^2089 ≤ (5082390097077/50000000000000 : ℝ)^1577
        have hw : |(-1780129787/10000000000 : ℝ)|=(1780129787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s1_7 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (134912659/312500000 : ℝ)*x 0 + (5039309403/10000000000 : ℝ)*x 1 + (3699980947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134912659/312500000 : ℝ)^2089 ≤ (8216843301029/25000000000000 : ℝ)^1577 := by
    have hnat : (134912659 : ℕ)^2089*25000000000000^1577 ≤ 8216843301029^1577*312500000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134912659 312500000 8216843301029 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5039309403/10000000000 : ℝ)^2089 ≤ (40340445548673/100000000000000 : ℝ)^1577 := by
    have hnat : (5039309403 : ℕ)^2089*100000000000000^1577 ≤ 40340445548673^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5039309403 10000000000 40340445548673 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3699980947/10000000000 : ℝ)^2089 ≤ (26792181224091/100000000000000 : ℝ)^1577 := by
    have hnat : (3699980947 : ℕ)^2089*100000000000000^1577 ≤ 26792181224091^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3699980947 10000000000 26792181224091 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134912659/312500000 : ℝ), (5039309403/10000000000 : ℝ), (3699980947/10000000000 : ℝ)] ![(8216843301029/25000000000000 : ℝ), (40340445548673/100000000000000 : ℝ), (26792181224091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134912659/312500000 : ℝ)|^2089 ≤ (8216843301029/25000000000000 : ℝ)^1577
        have hw : |(134912659/312500000 : ℝ)|=(134912659/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5039309403/10000000000 : ℝ)|^2089 ≤ (40340445548673/100000000000000 : ℝ)^1577
        have hw : |(5039309403/10000000000 : ℝ)|=(5039309403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3699980947/10000000000 : ℝ)|^2089 ≤ (26792181224091/100000000000000 : ℝ)^1577
        have hw : |(3699980947/10000000000 : ℝ)|=(3699980947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1163_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5547/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1/200 : ℝ)*pair X i i ≤ pair X i h) :
    (2883/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20343/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5547/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1/200 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5547/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1/200 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5547/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1/200 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5547/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1/200 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5547/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1/200 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5547/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1/200 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (1/200 : ℝ) ^ (8355/2048 : ℝ) ≤ (40995991983/100000000000000000000 : ℝ) := by
    have hpowers : (1/200 : ℝ)^8355 ≤ (40995991983/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1 : ℕ)^8355*100000000000000000000^2048 ≤ 40995991983^2048*200^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 200 40995991983 100000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1/200 : ℝ)) (X := (40995991983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5547/20000 : ℝ) ^ (8355/2048 : ℝ) ≤ (53429779261597217/10000000000000000000 : ℝ) := by
    have hpowers : (5547/20000 : ℝ)^8355 ≤ (53429779261597217/10000000000000000000 : ℝ)^2048 := by
      have hnat : (5547 : ℕ)^8355*10000000000000000000^2048 ≤ 53429779261597217^2048*20000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5547 20000 53429779261597217 10000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5547/20000 : ℝ)) (X := (53429779261597217/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000040995991983/50000000000000000000 : ℝ) ≤ (1000000000200981/1000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (50000000040995991983/50000000000000000000 : ℝ)^2048 ≤ (1000000000200981/1000000000000000 : ℝ)^8355 := by
      have hnat : (50000000040995991983 : ℕ)^2048*1000000000000000^8355 ≤ 1000000000200981^8355*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000040995991983 50000000000000000000 1000000000200981 1000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000000200981/1000000000000000 : ℝ)) (X := (50000000040995991983/50000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100534297833611964153/100000000000000000000 : ℝ) ≤ (10013070522268299/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (100534297833611964153/100000000000000000000 : ℝ)^2048 ≤ (10013070522268299/10000000000000000 : ℝ)^8355 := by
      have hnat : (100534297833611964153 : ℕ)^2048*10000000000000000^8355 ≤ 10013070522268299^8355*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100534297833611964153 100000000000000000000 10013070522268299 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013070522268299/10000000000000000 : ℝ)) (X := (100534297833611964153/100000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5053429779261597217/5000000000000000000 : ℝ) ≤ (2506535260631697/2500000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (5053429779261597217/5000000000000000000 : ℝ)^2048 ≤ (2506535260631697/2500000000000000 : ℝ)^8355 := by
      have hnat : (5053429779261597217 : ℕ)^2048*2500000000000000^8355 ≤ 2506535260631697^8355*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5053429779261597217 5000000000000000000 2506535260631697 2500000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506535260631697/2500000000000000 : ℝ)) (X := (5053429779261597217/5000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(40995991983/100000000000000000000 : ℝ) ≤ ((5446738590689573727/5447000000000000000 : ℝ)+2*(13070520258489/2723500000000000 : ℝ)*(1/200 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (5446738590689573727/5447000000000000000 : ℝ)+2*(13070520258489/2723500000000000 : ℝ)*(1/200 : ℝ)=(1000000000200981/1000000000000000 : ℝ) by norm_num, show 1+2*(40995991983/100000000000000000000 : ℝ)=(50000000040995991983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(53429779261597217/10000000000000000000 : ℝ)+(40995991983/100000000000000000000 : ℝ) ≤ ((5446738590689573727/5447000000000000000 : ℝ)+(13070520258489/2723500000000000 : ℝ)*((5547/20000 : ℝ)+(1/200 : ℝ)))^(8355/2048 : ℝ) := by
    rw [show (5446738590689573727/5447000000000000000 : ℝ)+(13070520258489/2723500000000000 : ℝ)*((5547/20000 : ℝ)+(1/200 : ℝ))=(10013070522268299/10000000000000000 : ℝ) by norm_num, show 1+(53429779261597217/10000000000000000000 : ℝ)+(40995991983/100000000000000000000 : ℝ)=(100534297833611964153/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(53429779261597217/10000000000000000000 : ℝ) ≤ ((5446738590689573727/5447000000000000000 : ℝ)+2*(13070520258489/2723500000000000 : ℝ)*(5547/20000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (5446738590689573727/5447000000000000000 : ℝ)+2*(13070520258489/2723500000000000 : ℝ)*(5547/20000 : ℝ)=(2506535260631697/2500000000000000 : ℝ) by norm_num, show 1+2*(53429779261597217/10000000000000000000 : ℝ)=(5053429779261597217/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5446738590689573727/5447000000000000000 : ℝ)*(X 1 0+X 2 0)+(13070520258489/2723500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (1/200 : ℝ)) (hi := (5547/20000 : ℝ)) (c := (5446738590689573727/5447000000000000000 : ℝ)) (alpha := (13070520258489/2723500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5446738590689573727/5447000000000000000 : ℝ)*(X 0 1+X 2 1)+(13070520258489/2723500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (1/200 : ℝ)) (hi := (5547/20000 : ℝ)) (c := (5446738590689573727/5447000000000000000 : ℝ)) (alpha := (13070520258489/2723500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5446738590689573727/5447000000000000000 : ℝ)*(X 0 2+X 1 2)+(13070520258489/2723500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (1/200 : ℝ)) (hi := (5547/20000 : ℝ)) (c := (5446738590689573727/5447000000000000000 : ℝ)) (alpha := (13070520258489/2723500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1044161751/5000000000 : ℝ)*X 0 0+(1423983713/2500000000 : ℝ)*X 0 1+(25033167/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5417971583/10000000000 : ℝ)*X 1 0+(-1229956549/5000000000 : ℝ)*X 1 1+(9778579/19531250 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5417973693/10000000000 : ℝ)*X 2 0+(2503315261/5000000000 : ℝ)*X 2 1+(-2459912797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2157827689/5000000000 : ℝ)*X 0 0+(368096497/1000000000 : ℝ)*X 0 1+(1264489681/2500000000 : ℝ)*X 0 2+(2157827689/5000000000 : ℝ)*X 1 0+(368096497/1000000000 : ℝ)*X 1 1+(1264489681/2500000000 : ℝ)*X 1 2+(2157827689/5000000000 : ℝ)*X 2 0+(368096497/1000000000 : ℝ)*X 2 1+(1264489681/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-104455257/500000000 : ℝ)*X 0 0+(2507985033/5000000000 : ℝ)*X 0 1+(5686411467/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5241061817/10000000000 : ℝ)*X 1 0+(-111258161/625000000 : ℝ)*X 1 1+(1137282947/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5241060897/10000000000 : ℝ)*X 2 0+(1421604043/2500000000 : ℝ)*X 2 1+(-1780129787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((134912659/312500000 : ℝ)*X 0 0+(5039309403/10000000000 : ℝ)*X 0 1+(3699980947/10000000000 : ℝ)*X 0 2+(134912659/312500000 : ℝ)*X 1 0+(5039309403/10000000000 : ℝ)*X 1 1+(3699980947/10000000000 : ℝ)*X 1 2+(134912659/312500000 : ℝ)*X 2 0+(5039309403/10000000000 : ℝ)*X 2 1+(3699980947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (369620066101623645014397753/54470000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (182372883/25000000000000 : ℝ)*(base1) + (1139238107/100000000000000 : ℝ)*(base19) + (11119067/625000000000 : ℝ)*(base23) + (110830187/100000000000000 : ℝ)*(base37) + (3898987/4000000000000 : ℝ)*(upper3) + (217696560968529/20000000000000 : ℝ)*(major0) + (217696560968529/20000000000000 : ℝ)*(major1) + (217696560968529/20000000000000 : ℝ)*(major2) + (1450745585987881/100000000000000 : ℝ)*(sp0) + (1450743247237209/100000000000000 : ℝ)*(sp1) + (725372449536029/50000000000000 : ℝ)*(sp2) + (145243573009791/20000000000000 : ℝ)*(sp3) + (1821626429/100000000000000 : ℝ)*(sp4) + (1145823731/50000000000000 : ℝ)*(sp5) + (29048748214827/4000000000000 : ℝ)*(f.failure) + (725373339061389/50000000000000 : ℝ)*(f.sum) + (8274306724701/27235000000000000000000000000 : ℝ)*base65 + (780566214930159583/108940000000000000000000000000000 : ℝ)*base67 + (1327291312900379583/108940000000000000000000000000000 : ℝ)*base69 + (726007862956059583/108940000000000000000000000000000 : ℝ)*base71 + (529109836979/27235000000000000000000000000 : ℝ)*base74 + (1239178085276919583/108940000000000000000000000000000 : ℝ)*base75 + (985287253412639583/108940000000000000000000000000000 : ℝ)*base77 + (614525166861159583/108940000000000000000000000000000 : ℝ)*base79 + (100486528164091/27235000000000000000000000000 : ℝ)*base81 + (1929357/400000000000000000000 : ℝ)*base90 + (1929357/400000000000000000000 : ℝ)*base92 + (1929357/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (896254027663544486094369459/272350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2424000931/100000000000000 : ℝ)*(base19) + (385409819/12500000000000 : ℝ)*(base23) + (373066513/100000000000000 : ℝ)*(upper2) + (1206161/195312500000 : ℝ)*(upper3) + (64665547/20000000000000 : ℝ)*(upper5) + (1119096439149439/100000000000000 : ℝ)*(major0) + (1119096439149439/100000000000000 : ℝ)*(major1) + (1119096439149439/100000000000000 : ℝ)*(major2) + (6733753657/50000000000000 : ℝ)*(sp1) + (19667348191/100000000000000 : ℝ)*(sp2) + (1491549125169991/100000000000000 : ℝ)*(sp4) + (745766616830873/50000000000000 : ℝ)*(sp5) + (1491526374543247/100000000000000 : ℝ)*(sp6) + (37332182171749/5000000000000 : ℝ)*(sp7) + (37332182171749/5000000000000 : ℝ)*(f.failure) + (1491549125169991/100000000000000 : ℝ)*(f.sum) + (477458215550171/136175000000000000000000000000 : ℝ)*base65 + (4282382150629668847/544700000000000000000000000000000 : ℝ)*base68 + (1430554377171368847/544700000000000000000000000000000 : ℝ)*base70 + (1891629814608268847/544700000000000000000000000000000 : ℝ)*base72 + (398997852036929/136175000000000000000000000000 : ℝ)*base74 + (60145076559131153/544700000000000000000000000000000 : ℝ)*base75 + (3094858266795131153/544700000000000000000000000000000 : ℝ)*base77 + (2484211309695668847/544700000000000000000000000000000 : ℝ)*base80 + (224102167849029/136175000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2962141/500000000000000000000 : ℝ)*base89 + (2962141/500000000000000000000 : ℝ)*base91 + (2962141/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1163_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5547/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1/200 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2883/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20343/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1163_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1163_s2_0 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-535109517/2500000000 : ℝ)*x 0 + (1101373103/2000000000 : ℝ)*x 1 + (5162543203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535109517/2500000000 : ℝ)^2089 ≤ (12975942598251/100000000000000 : ℝ)^1577 := by
    have hnat : (535109517 : ℕ)^2089*100000000000000^1577 ≤ 12975942598251^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535109517 2500000000 12975942598251 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101373103/2000000000 : ℝ)^2089 ≤ (11342915265693/25000000000000 : ℝ)^1577 := by
    have hnat : (1101373103 : ℕ)^2089*25000000000000^1577 ≤ 11342915265693^1577*2000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101373103 2000000000 11342915265693 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5162543203/10000000000 : ℝ)^2089 ≤ (10413099079799/25000000000000 : ℝ)^1577 := by
    have hnat : (5162543203 : ℕ)^2089*25000000000000^1577 ≤ 10413099079799^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5162543203 10000000000 10413099079799 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535109517/2500000000 : ℝ), (1101373103/2000000000 : ℝ), (5162543203/10000000000 : ℝ)] ![(12975942598251/100000000000000 : ℝ), (11342915265693/25000000000000 : ℝ), (10413099079799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535109517/2500000000 : ℝ)|^2089 ≤ (12975942598251/100000000000000 : ℝ)^1577
        have hw : |(-535109517/2500000000 : ℝ)|=(535109517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1101373103/2000000000 : ℝ)|^2089 ≤ (11342915265693/25000000000000 : ℝ)^1577
        have hw : |(1101373103/2000000000 : ℝ)|=(1101373103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5162543203/10000000000 : ℝ)|^2089 ≤ (10413099079799/25000000000000 : ℝ)^1577
        have hw : |(5162543203/10000000000 : ℝ)|=(5162543203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s2_1 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2686484223/5000000000 : ℝ)*x 0 + (-579826599/2500000000 : ℝ)*x 1 + (516254581/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686484223/5000000000 : ℝ)^2089 ≤ (10979024584107/25000000000000 : ℝ)^1577 := by
    have hnat : (2686484223 : ℕ)^2089*25000000000000^1577 ≤ 10979024584107^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686484223 5000000000 10979024584107 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (579826599/2500000000 : ℝ)^2089 ≤ (3607869365813/25000000000000 : ℝ)^1577 := by
    have hnat : (579826599 : ℕ)^2089*25000000000000^1577 ≤ 3607869365813^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579826599 2500000000 3607869365813 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516254581/1000000000 : ℝ)^2089 ≤ (8330484836391/20000000000000 : ℝ)^1577 := by
    have hnat : (516254581 : ℕ)^2089*20000000000000^1577 ≤ 8330484836391^1577*1000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516254581 1000000000 8330484836391 20000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686484223/5000000000 : ℝ), (-579826599/2500000000 : ℝ), (516254581/1000000000 : ℝ)] ![(10979024584107/25000000000000 : ℝ), (3607869365813/25000000000000 : ℝ), (8330484836391/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686484223/5000000000 : ℝ)|^2089 ≤ (10979024584107/25000000000000 : ℝ)^1577
        have hw : |(2686484223/5000000000 : ℝ)|=(2686484223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-579826599/2500000000 : ℝ)|^2089 ≤ (3607869365813/25000000000000 : ℝ)^1577
        have hw : |(-579826599/2500000000 : ℝ)|=(579826599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516254581/1000000000 : ℝ)|^2089 ≤ (8330484836391/20000000000000 : ℝ)^1577
        have hw : |(516254581/1000000000 : ℝ)|=(516254581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s2_2 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5372968811/10000000000 : ℝ)*x 0 + (5162545127/10000000000 : ℝ)*x 1 + (-2319306803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372968811/10000000000 : ℝ)^2089 ≤ (10979025572089/25000000000000 : ℝ)^1577 := by
    have hnat : (5372968811 : ℕ)^2089*25000000000000^1577 ≤ 10979025572089^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372968811 10000000000 10979025572089 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5162545127/10000000000 : ℝ)^2089 ≤ (1666096675291/4000000000000 : ℝ)^1577 := by
    have hnat : (5162545127 : ℕ)^2089*4000000000000^1577 ≤ 1666096675291^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5162545127 10000000000 1666096675291 4000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2319306803/10000000000 : ℝ)^2089 ≤ (14431480817953/100000000000000 : ℝ)^1577 := by
    have hnat : (2319306803 : ℕ)^2089*100000000000000^1577 ≤ 14431480817953^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2319306803 10000000000 14431480817953 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372968811/10000000000 : ℝ), (5162545127/10000000000 : ℝ), (-2319306803/10000000000 : ℝ)] ![(10979025572089/25000000000000 : ℝ), (1666096675291/4000000000000 : ℝ), (14431480817953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372968811/10000000000 : ℝ)|^2089 ≤ (10979025572089/25000000000000 : ℝ)^1577
        have hw : |(5372968811/10000000000 : ℝ)|=(5372968811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5162545127/10000000000 : ℝ)|^2089 ≤ (1666096675291/4000000000000 : ℝ)^1577
        have hw : |(5162545127/10000000000 : ℝ)|=(5162545127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2319306803/10000000000 : ℝ)|^2089 ≤ (14431480817953/100000000000000 : ℝ)^1577
        have hw : |(-2319306803/10000000000 : ℝ)|=(2319306803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s2_3 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4351456927/10000000000 : ℝ)*x 0 + (251308849/625000000 : ℝ)*x 1 + (2354389931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351456927/10000000000 : ℝ)^2089 ≤ (33213241647747/100000000000000 : ℝ)^1577 := by
    have hnat : (4351456927 : ℕ)^2089*100000000000000^1577 ≤ 33213241647747^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351456927 10000000000 33213241647747 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (251308849/625000000 : ℝ)^2089 ≤ (29913415984383/100000000000000 : ℝ)^1577 := by
    have hnat : (251308849 : ℕ)^2089*100000000000000^1577 ≤ 29913415984383^1577*625000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251308849 625000000 29913415984383 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2354389931/5000000000 : ℝ)^2089 ≤ (36873342347947/100000000000000 : ℝ)^1577 := by
    have hnat : (2354389931 : ℕ)^2089*100000000000000^1577 ≤ 36873342347947^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2354389931 5000000000 36873342347947 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351456927/10000000000 : ℝ), (251308849/625000000 : ℝ), (2354389931/5000000000 : ℝ)] ![(33213241647747/100000000000000 : ℝ), (29913415984383/100000000000000 : ℝ), (36873342347947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351456927/10000000000 : ℝ)|^2089 ≤ (33213241647747/100000000000000 : ℝ)^1577
        have hw : |(4351456927/10000000000 : ℝ)|=(4351456927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(251308849/625000000 : ℝ)|^2089 ≤ (29913415984383/100000000000000 : ℝ)^1577
        have hw : |(251308849/625000000 : ℝ)|=(251308849/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2354389931/5000000000 : ℝ)|^2089 ≤ (36873342347947/100000000000000 : ℝ)^1577
        have hw : |(2354389931/5000000000 : ℝ)|=(2354389931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s2_4 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-107026721/500000000 : ℝ)*x 0 + (1032976711/2000000000 : ℝ)*x 1 + (1376125621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107026721/500000000 : ℝ)^2089 ≤ (12976716359371/100000000000000 : ℝ)^1577 := by
    have hnat : (107026721 : ℕ)^2089*100000000000000^1577 ≤ 12976716359371^1577*500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107026721 500000000 12976716359371 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032976711/2000000000 : ℝ)^2089 ≤ (20838705534909/50000000000000 : ℝ)^1577 := by
    have hnat : (1032976711 : ℕ)^2089*50000000000000^1577 ≤ 20838705534909^1577*2000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032976711 2000000000 20838705534909 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1376125621/2500000000 : ℝ)^2089 ≤ (72553396097/160000000000 : ℝ)^1577 := by
    have hnat : (1376125621 : ℕ)^2089*160000000000^1577 ≤ 72553396097^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376125621 2500000000 72553396097 160000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107026721/500000000 : ℝ), (1032976711/2000000000 : ℝ), (1376125621/2500000000 : ℝ)] ![(12976716359371/100000000000000 : ℝ), (20838705534909/50000000000000 : ℝ), (72553396097/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107026721/500000000 : ℝ)|^2089 ≤ (12976716359371/100000000000000 : ℝ)^1577
        have hw : |(-107026721/500000000 : ℝ)|=(107026721/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032976711/2000000000 : ℝ)|^2089 ≤ (20838705534909/50000000000000 : ℝ)^1577
        have hw : |(1032976711/2000000000 : ℝ)|=(1032976711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1376125621/2500000000 : ℝ)|^2089 ≤ (72553396097/160000000000 : ℝ)^1577
        have hw : |(1376125621/2500000000 : ℝ)|=(1376125621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s2_5 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (330342691/625000000 : ℝ)*x 0 + (-123584289/625000000 : ℝ)*x 1 + (5504502477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330342691/625000000 : ℝ)^2089 ≤ (21485694677469/50000000000000 : ℝ)^1577 := by
    have hnat : (330342691 : ℕ)^2089*50000000000000^1577 ≤ 21485694677469^1577*625000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330342691 625000000 21485694677469 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123584289/625000000 : ℝ)^2089 ≤ (11682738137213/100000000000000 : ℝ)^1577 := by
    have hnat : (123584289 : ℕ)^2089*100000000000000^1577 ≤ 11682738137213^1577*625000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123584289 625000000 11682738137213 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5504502477/10000000000 : ℝ)^2089 ≤ (45345872484237/100000000000000 : ℝ)^1577 := by
    have hnat : (5504502477 : ℕ)^2089*100000000000000^1577 ≤ 45345872484237^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504502477 10000000000 45345872484237 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330342691/625000000 : ℝ), (-123584289/625000000 : ℝ), (5504502477/10000000000 : ℝ)] ![(21485694677469/50000000000000 : ℝ), (11682738137213/100000000000000 : ℝ), (45345872484237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330342691/625000000 : ℝ)|^2089 ≤ (21485694677469/50000000000000 : ℝ)^1577
        have hw : |(330342691/625000000 : ℝ)|=(330342691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123584289/625000000 : ℝ)|^2089 ≤ (11682738137213/100000000000000 : ℝ)^1577
        have hw : |(-123584289/625000000 : ℝ)|=(123584289/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5504502477/10000000000 : ℝ)|^2089 ≤ (45345872484237/100000000000000 : ℝ)^1577
        have hw : |(5504502477/10000000000 : ℝ)|=(5504502477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s2_6 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (660685397/1250000000 : ℝ)*x 0 + (688062809/1250000000 : ℝ)*x 1 + (-1977348467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660685397/1250000000 : ℝ)^2089 ≤ (41964248679/97656250000 : ℝ)^1577 := by
    have hnat : (660685397 : ℕ)^2089*97656250000^1577 ≤ 41964248679^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660685397 1250000000 41964248679 97656250000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688062809/1250000000 : ℝ)^2089 ≤ (1813834897187/4000000000000 : ℝ)^1577 := by
    have hnat : (688062809 : ℕ)^2089*4000000000000^1577 ≤ 1813834897187^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688062809 1250000000 1813834897187 4000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1977348467/10000000000 : ℝ)^2089 ≤ (11682736908451/100000000000000 : ℝ)^1577 := by
    have hnat : (1977348467 : ℕ)^2089*100000000000000^1577 ≤ 11682736908451^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977348467 10000000000 11682736908451 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660685397/1250000000 : ℝ), (688062809/1250000000 : ℝ), (-1977348467/10000000000 : ℝ)] ![(41964248679/97656250000 : ℝ), (1813834897187/4000000000000 : ℝ), (11682736908451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660685397/1250000000 : ℝ)|^2089 ≤ (41964248679/97656250000 : ℝ)^1577
        have hw : |(660685397/1250000000 : ℝ)|=(660685397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688062809/1250000000 : ℝ)|^2089 ≤ (1813834897187/4000000000000 : ℝ)^1577
        have hw : |(688062809/1250000000 : ℝ)|=(688062809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1977348467/10000000000 : ℝ)|^2089 ≤ (11682736908451/100000000000000 : ℝ)^1577
        have hw : |(-1977348467/10000000000 : ℝ)|=(1977348467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s2_7 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4351651003/10000000000 : ℝ)*x 0 + (9187709/19531250 : ℝ)*x 1 + (503207431/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351651003/10000000000 : ℝ)^2089 ≤ (33215203915649/100000000000000 : ℝ)^1577 := by
    have hnat : (4351651003 : ℕ)^2089*100000000000000^1577 ≤ 33215203915649^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351651003 10000000000 33215203915649 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9187709/19531250 : ℝ)^2089 ≤ (1150777434993/3125000000000 : ℝ)^1577 := by
    have hnat : (9187709 : ℕ)^2089*3125000000000^1577 ≤ 1150777434993^1577*19531250^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9187709 19531250 1150777434993 3125000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503207431/1250000000 : ℝ)^2089 ≤ (3744989767713/12500000000000 : ℝ)^1577 := by
    have hnat : (503207431 : ℕ)^2089*12500000000000^1577 ≤ 3744989767713^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503207431 1250000000 3744989767713 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351651003/10000000000 : ℝ), (9187709/19531250 : ℝ), (503207431/1250000000 : ℝ)] ![(33215203915649/100000000000000 : ℝ), (1150777434993/3125000000000 : ℝ), (3744989767713/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351651003/10000000000 : ℝ)|^2089 ≤ (33215203915649/100000000000000 : ℝ)^1577
        have hw : |(4351651003/10000000000 : ℝ)|=(4351651003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9187709/19531250 : ℝ)|^2089 ≤ (1150777434993/3125000000000 : ℝ)^1577
        have hw : |(9187709/19531250 : ℝ)|=(9187709/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(503207431/1250000000 : ℝ)|^2089 ≤ (3744989767713/12500000000000 : ℝ)^1577
        have hw : |(503207431/1250000000 : ℝ)|=(503207431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1163_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20343/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2883/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2291/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16441/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20343/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2883/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20343/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2883/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20343/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2883/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20343/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2883/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20343/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2883/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20343/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2883/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2883/50000 : ℝ) ^ (8355/2048 : ℝ) ≤ (880798889203019/100000000000000000000 : ℝ) := by
    have hpowers : (2883/50000 : ℝ)^8355 ≤ (880798889203019/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2883 : ℕ)^8355*100000000000000000000^2048 ≤ 880798889203019^2048*50000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2883 50000 880798889203019 100000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2883/50000 : ℝ)) (X := (880798889203019/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20343/100000 : ℝ) ^ (8355/2048 : ℝ) ≤ (75437425502959747/50000000000000000000 : ℝ) := by
    have hpowers : (20343/100000 : ℝ)^8355 ≤ (75437425502959747/50000000000000000000 : ℝ)^2048 := by
      have hnat : (20343 : ℕ)^8355*50000000000000000000^2048 ≤ 75437425502959747^2048*100000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20343 100000 75437425502959747 50000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20343/100000 : ℝ)) (X := (75437425502959747/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000880798889203019/50000000000000000000 : ℝ) ≤ (10000043180469931/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (50000880798889203019/50000000000000000000 : ℝ)^2048 ≤ (10000043180469931/10000000000000000 : ℝ)^8355 := by
      have hnat : (50000880798889203019 : ℕ)^2048*10000000000000000^8355 ≤ 10000043180469931^8355*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000880798889203019 50000000000000000000 10000043180469931 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000043180469931/10000000000000000 : ℝ)) (X := (50000880798889203019/50000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100151755649895122513/100000000000000000000 : ℝ) ≤ (1000371774637901/1000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (100151755649895122513/100000000000000000000 : ℝ)^2048 ≤ (1000371774637901/1000000000000000 : ℝ)^8355 := by
      have hnat : (100151755649895122513 : ℕ)^2048*1000000000000000^8355 ≤ 1000371774637901^8355*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100151755649895122513 100000000000000000000 1000371774637901 1000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000371774637901/1000000000000000 : ℝ)) (X := (100151755649895122513/100000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25075437425502959747/25000000000000000000 : ℝ) ≤ (10007392312288089/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (25075437425502959747/25000000000000000000 : ℝ)^2048 ≤ (10007392312288089/10000000000000000 : ℝ)^8355 := by
      have hnat : (25075437425502959747 : ℕ)^2048*10000000000000000^8355 ≤ 10007392312288089^8355*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25075437425502959747 25000000000000000000 10007392312288089 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007392312288089/10000000000000000 : ℝ)) (X := (25075437425502959747/25000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(880798889203019/100000000000000000000 : ℝ) ≤ ((48576084782548895053/48590000000000000000 : ℝ)+2*(3674565909079/1457700000000000 : ℝ)*(2883/50000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (48576084782548895053/48590000000000000000 : ℝ)+2*(3674565909079/1457700000000000 : ℝ)*(2883/50000 : ℝ)=(10000043180469931/10000000000000000 : ℝ) by norm_num, show 1+2*(880798889203019/100000000000000000000 : ℝ)=(50000880798889203019/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(75437425502959747/50000000000000000000 : ℝ)+(880798889203019/100000000000000000000 : ℝ) ≤ ((48576084782548895053/48590000000000000000 : ℝ)+(3674565909079/1457700000000000 : ℝ)*((20343/100000 : ℝ)+(2883/50000 : ℝ)))^(8355/2048 : ℝ) := by
    rw [show (48576084782548895053/48590000000000000000 : ℝ)+(3674565909079/1457700000000000 : ℝ)*((20343/100000 : ℝ)+(2883/50000 : ℝ))=(1000371774637901/1000000000000000 : ℝ) by norm_num, show 1+(75437425502959747/50000000000000000000 : ℝ)+(880798889203019/100000000000000000000 : ℝ)=(100151755649895122513/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(75437425502959747/50000000000000000000 : ℝ) ≤ ((48576084782548895053/48590000000000000000 : ℝ)+2*(3674565909079/1457700000000000 : ℝ)*(20343/100000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (48576084782548895053/48590000000000000000 : ℝ)+2*(3674565909079/1457700000000000 : ℝ)*(20343/100000 : ℝ)=(10007392312288089/10000000000000000 : ℝ) by norm_num, show 1+2*(75437425502959747/50000000000000000000 : ℝ)=(25075437425502959747/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (48576084782548895053/48590000000000000000 : ℝ)*(X 1 0+X 2 0)+(3674565909079/1457700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (2883/50000 : ℝ)) (hi := (20343/100000 : ℝ)) (c := (48576084782548895053/48590000000000000000 : ℝ)) (alpha := (3674565909079/1457700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (48576084782548895053/48590000000000000000 : ℝ)*(X 0 1+X 2 1)+(3674565909079/1457700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (2883/50000 : ℝ)) (hi := (20343/100000 : ℝ)) (c := (48576084782548895053/48590000000000000000 : ℝ)) (alpha := (3674565909079/1457700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (48576084782548895053/48590000000000000000 : ℝ)*(X 0 2+X 1 2)+(3674565909079/1457700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (2883/50000 : ℝ)) (hi := (20343/100000 : ℝ)) (c := (48576084782548895053/48590000000000000000 : ℝ)) (alpha := (3674565909079/1457700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-535109517/2500000000 : ℝ)*X 0 0+(1101373103/2000000000 : ℝ)*X 0 1+(5162543203/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686484223/5000000000 : ℝ)*X 1 0+(-579826599/2500000000 : ℝ)*X 1 1+(516254581/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5372968811/10000000000 : ℝ)*X 2 0+(5162545127/10000000000 : ℝ)*X 2 1+(-2319306803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351456927/10000000000 : ℝ)*X 0 0+(251308849/625000000 : ℝ)*X 0 1+(2354389931/5000000000 : ℝ)*X 0 2+(4351456927/10000000000 : ℝ)*X 1 0+(251308849/625000000 : ℝ)*X 1 1+(2354389931/5000000000 : ℝ)*X 1 2+(4351456927/10000000000 : ℝ)*X 2 0+(251308849/625000000 : ℝ)*X 2 1+(2354389931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-107026721/500000000 : ℝ)*X 0 0+(1032976711/2000000000 : ℝ)*X 0 1+(1376125621/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330342691/625000000 : ℝ)*X 1 0+(-123584289/625000000 : ℝ)*X 1 1+(5504502477/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660685397/1250000000 : ℝ)*X 2 0+(688062809/1250000000 : ℝ)*X 2 1+(-1977348467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351651003/10000000000 : ℝ)*X 0 0+(9187709/19531250 : ℝ)*X 0 1+(503207431/1250000000 : ℝ)*X 0 2+(4351651003/10000000000 : ℝ)*X 1 0+(9187709/19531250 : ℝ)*X 1 1+(503207431/1250000000 : ℝ)*X 1 2+(4351651003/10000000000 : ℝ)*X 2 0+(9187709/19531250 : ℝ)*X 2 1+(503207431/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9406713708449039639394132771/1214750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143005751/20000000000000 : ℝ)*(base19) + (176115977/25000000000000 : ℝ)*(base23) + (53746633/100000000000000 : ℝ)*(upper2) + (189192513/50000000000000 : ℝ)*(upper3) + (165430117/100000000000000 : ℝ)*(upper4) + (1089536669425269/50000000000000 : ℝ)*(major0) + (1089536669425269/50000000000000 : ℝ)*(major1) + (1089536669425269/50000000000000 : ℝ)*(major2) + (2904281573526451/100000000000000 : ℝ)*(sp0) + (1452151024934197/50000000000000 : ℝ)*(sp1) + (72607551510831/2500000000000 : ℝ)*(sp2) + (22716171092239/1562500000000 : ℝ)*(sp3) + (21191370697/100000000000000 : ℝ)*(sp4) + (68006061/781250000000 : ℝ)*(sp7) + (22716307104361/1562500000000 : ℝ)*(f.failure) + (726075691224287/25000000000000 : ℝ)*(f.sum) + (65912793836263/12147500000000000000000000000 : ℝ)*base66 + (7538859334077005743/2429500000000000000000000000000000 : ℝ)*base68 + (8134368458357494257/2429500000000000000000000000000000 : ℝ)*base69 + (13631836669181005743/2429500000000000000000000000000000 : ℝ)*base72 + (13230162117077/12147500000000000000000000000 : ℝ)*base73 + (23799113744793005743/2429500000000000000000000000000000 : ℝ)*base76 + (4528456234103005743/2429500000000000000000000000000000 : ℝ)*base78 + (12202294660712994257/2429500000000000000000000000000000 : ℝ)*base79 + (30168003086557/12147500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (693849/156250000000000000000 : ℝ)*base89 + (693849/156250000000000000000 : ℝ)*base91 + (693849/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1081477456489244817962520253/151843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (819271121/50000000000000 : ℝ)*(base19) + (439348569/25000000000000 : ℝ)*(base23) + (19411489/10000000000000 : ℝ)*(upper3) + (7917233/100000000000000 : ℝ)*(lower4) + (154267363/100000000000000 : ℝ)*(upper5) + (276151886001967/12500000000000 : ℝ)*(major0) + (276151886001967/12500000000000 : ℝ)*(major1) + (276151886001967/12500000000000 : ℝ)*(major2) + (15804056113/100000000000000 : ℝ)*(sp1) + (18040735039/100000000000000 : ℝ)*(sp2) + (736119045066223/25000000000000 : ℝ)*(sp4) + (2944458737666537/100000000000000 : ℝ)*(sp5) + (2944456382135577/100000000000000 : ℝ)*(sp6) + (1473953758356417/100000000000000 : ℝ)*(sp7) + (1473953758356417/100000000000000 : ℝ)*(f.failure) + (736119045066223/25000000000000 : ℝ)*(f.sum) + (400194531670591/72885000000000000000000000000 : ℝ)*base66 + (4467697476943492247/1822125000000000000000000000000000 : ℝ)*base68 + (10949448258617992247/1822125000000000000000000000000000 : ℝ)*base70 + (23863347718384117247/1822125000000000000000000000000000 : ℝ)*base72 + (1907575358839/18221250000000000000000000000 : ℝ)*base74 + (17322434217958867247/1822125000000000000000000000000000 : ℝ)*base76 + (18382967339039992247/1822125000000000000000000000000000 : ℝ)*base78 + (837236816212882753/1822125000000000000000000000000000 : ℝ)*base79 + (22521557374157/9110625000000000000000000000 : ℝ)*base82 + (88268953/10000000000000000000000 : ℝ)*base89 + (88268953/10000000000000000000000 : ℝ)*base91 + (88268953/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1163_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20343/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2883/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2291/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16441/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1163_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1163_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2291/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16441/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1163_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1163_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1163_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2291/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16441/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1163_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

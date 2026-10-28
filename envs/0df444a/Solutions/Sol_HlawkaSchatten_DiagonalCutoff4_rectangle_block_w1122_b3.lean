-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1122_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:09:44.205502+00:00
-- url     : https://prove2.me/submissions/09f22c02-8f89-4ebc-88ae-bfa0c198acfc

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
theorem support_rectangle_w1122_box_0 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-256115969/1250000000 : ℝ)*x 0 + (5376595309/10000000000 : ℝ)*x 1 + (2688297517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256115969/1250000000 : ℝ)^8315 ≤ (1525631592577/12500000000000 : ℝ)^6267 := by
    have hnat : (256115969 : ℕ)^8315*12500000000000^6267 ≤ 1525631592577^6267*1250000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256115969 1250000000 1525631592577 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376595309/10000000000 : ℝ)^8315 ≤ (351179800897/800000000000 : ℝ)^6267 := by
    have hnat : (5376595309 : ℕ)^8315*800000000000^6267 ≤ 351179800897^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376595309 10000000000 351179800897 800000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688297517/5000000000 : ℝ)^8315 ≤ (21948736066573/50000000000000 : ℝ)^6267 := by
    have hnat : (2688297517 : ℕ)^8315*50000000000000^6267 ≤ 21948736066573^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688297517 5000000000 21948736066573 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-256115969/1250000000 : ℝ), (5376595309/10000000000 : ℝ), (2688297517/5000000000 : ℝ)] ![(1525631592577/12500000000000 : ℝ), (351179800897/800000000000 : ℝ), (21948736066573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-256115969/1250000000 : ℝ)|^8315 ≤ (1525631592577/12500000000000 : ℝ)^6267
        have hw : |(-256115969/1250000000 : ℝ)|=(256115969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376595309/10000000000 : ℝ)|^8315 ≤ (351179800897/800000000000 : ℝ)^6267
        have hw : |(5376595309/10000000000 : ℝ)|=(5376595309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688297517/5000000000 : ℝ)|^8315 ≤ (21948736066573/50000000000000 : ℝ)^6267
        have hw : |(2688297517/5000000000 : ℝ)|=(2688297517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_box_1 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (529579367/1000000000 : ℝ)*x 0 + (-2158457989/10000000000 : ℝ)*x 1 + (5376595241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529579367/1000000000 : ℝ)^8315 ≤ (10756083951427/25000000000000 : ℝ)^6267 := by
    have hnat : (529579367 : ℕ)^8315*25000000000000^6267 ≤ 10756083951427^6267*1000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529579367 1000000000 10756083951427 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2158457989/10000000000 : ℝ)^8315 ≤ (10462551847/80000000000 : ℝ)^6267 := by
    have hnat : (2158457989 : ℕ)^8315*80000000000^6267 ≤ 10462551847^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158457989 10000000000 10462551847 80000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376595241/10000000000 : ℝ)^8315 ≤ (8779494875101/20000000000000 : ℝ)^6267 := by
    have hnat : (5376595241 : ℕ)^8315*20000000000000^6267 ≤ 8779494875101^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376595241 10000000000 8779494875101 20000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529579367/1000000000 : ℝ), (-2158457989/10000000000 : ℝ), (5376595241/10000000000 : ℝ)] ![(10756083951427/25000000000000 : ℝ), (10462551847/80000000000 : ℝ), (8779494875101/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529579367/1000000000 : ℝ)|^8315 ≤ (10756083951427/25000000000000 : ℝ)^6267
        have hw : |(529579367/1000000000 : ℝ)|=(529579367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2158457989/10000000000 : ℝ)|^8315 ≤ (10462551847/80000000000 : ℝ)^6267
        have hw : |(-2158457989/10000000000 : ℝ)|=(2158457989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376595241/10000000000 : ℝ)|^8315 ≤ (8779494875101/20000000000000 : ℝ)^6267
        have hw : |(5376595241/10000000000 : ℝ)|=(5376595241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_box_2 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295793519/10000000000 : ℝ)*x 0 + (537659509/1000000000 : ℝ)*x 1 + (-1079229197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295793519/10000000000 : ℝ)^8315 ≤ (10756083544513/25000000000000 : ℝ)^6267 := by
    have hnat : (5295793519 : ℕ)^8315*25000000000000^6267 ≤ 10756083544513^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295793519 10000000000 10756083544513 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537659509/1000000000 : ℝ)^8315 ≤ (1755898909591/4000000000000 : ℝ)^6267 := by
    have hnat : (537659509 : ℕ)^8315*4000000000000^6267 ≤ 1755898909591^6267*1000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537659509 1000000000 1755898909591 4000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079229197/5000000000 : ℝ)^8315 ≤ (13078193064579/100000000000000 : ℝ)^6267 := by
    have hnat : (1079229197 : ℕ)^8315*100000000000000^6267 ≤ 13078193064579^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079229197 5000000000 13078193064579 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295793519/10000000000 : ℝ), (537659509/1000000000 : ℝ), (-1079229197/5000000000 : ℝ)] ![(10756083544513/25000000000000 : ℝ), (1755898909591/4000000000000 : ℝ), (13078193064579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295793519/10000000000 : ℝ)|^8315 ≤ (10756083544513/25000000000000 : ℝ)^6267
        have hw : |(5295793519/10000000000 : ℝ)|=(5295793519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537659509/1000000000 : ℝ)|^8315 ≤ (1755898909591/4000000000000 : ℝ)^6267
        have hw : |(537659509/1000000000 : ℝ)|=(537659509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1079229197/5000000000 : ℝ)|^8315 ≤ (13078193064579/100000000000000 : ℝ)^6267
        have hw : |(-1079229197/5000000000 : ℝ)|=(1079229197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_box_3 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4475263451/10000000000 : ℝ)*x 0 + (4315740787/10000000000 : ℝ)*x 1 + (1078935477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4475263451/10000000000 : ℝ)^8315 ≤ (34411945394699/100000000000000 : ℝ)^6267 := by
    have hnat : (4475263451 : ℕ)^8315*100000000000000^6267 ≤ 34411945394699^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475263451 10000000000 34411945394699 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4315740787/10000000000 : ℝ)^8315 ≤ (8198505409913/25000000000000 : ℝ)^6267 := by
    have hnat : (4315740787 : ℕ)^8315*25000000000000^6267 ≤ 8198505409913^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315740787 10000000000 8198505409913 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078935477/2500000000 : ℝ)^8315 ≤ (655880658829/2000000000000 : ℝ)^6267 := by
    have hnat : (1078935477 : ℕ)^8315*2000000000000^6267 ≤ 655880658829^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078935477 2500000000 655880658829 2000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4475263451/10000000000 : ℝ), (4315740787/10000000000 : ℝ), (1078935477/2500000000 : ℝ)] ![(34411945394699/100000000000000 : ℝ), (8198505409913/25000000000000 : ℝ), (655880658829/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4475263451/10000000000 : ℝ)|^8315 ≤ (34411945394699/100000000000000 : ℝ)^6267
        have hw : |(4475263451/10000000000 : ℝ)|=(4475263451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4315740787/10000000000 : ℝ)|^8315 ≤ (8198505409913/25000000000000 : ℝ)^6267
        have hw : |(4315740787/10000000000 : ℝ)|=(4315740787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078935477/2500000000 : ℝ)|^8315 ≤ (655880658829/2000000000000 : ℝ)^6267
        have hw : |(1078935477/2500000000 : ℝ)|=(1078935477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_box_4 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1152717163/5000000000 : ℝ)*x 0 + (41256873/78125000 : ℝ)*x 1 + (5280880143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1152717163/5000000000 : ℝ)^8315 ≤ (7136347892199/50000000000000 : ℝ)^6267 := by
    have hnat : (1152717163 : ℕ)^8315*50000000000000^6267 ≤ 7136347892199^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152717163 5000000000 7136347892199 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41256873/78125000 : ℝ)^8315 ≤ (42863649950987/100000000000000 : ℝ)^6267 := by
    have hnat : (41256873 : ℕ)^8315*100000000000000^6267 ≤ 42863649950987^6267*78125000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41256873 78125000 42863649950987 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280880143/10000000000 : ℝ)^8315 ≤ (42863654247917/100000000000000 : ℝ)^6267 := by
    have hnat : (5280880143 : ℕ)^8315*100000000000000^6267 ≤ 42863654247917^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280880143 10000000000 42863654247917 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1152717163/5000000000 : ℝ), (41256873/78125000 : ℝ), (5280880143/10000000000 : ℝ)] ![(7136347892199/50000000000000 : ℝ), (42863649950987/100000000000000 : ℝ), (42863654247917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1152717163/5000000000 : ℝ)|^8315 ≤ (7136347892199/50000000000000 : ℝ)^6267
        have hw : |(-1152717163/5000000000 : ℝ)|=(1152717163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41256873/78125000 : ℝ)|^8315 ≤ (42863649950987/100000000000000 : ℝ)^6267
        have hw : |(41256873/78125000 : ℝ)|=(41256873/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280880143/10000000000 : ℝ)|^8315 ≤ (42863654247917/100000000000000 : ℝ)^6267
        have hw : |(5280880143/10000000000 : ℝ)|=(5280880143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_box_5 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1340861627/2500000000 : ℝ)*x 0 + (-2196049639/10000000000 : ℝ)*x 1 + (21123521/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340861627/2500000000 : ℝ)^8315 ≤ (8751019137577/20000000000000 : ℝ)^6267 := by
    have hnat : (1340861627 : ℕ)^8315*20000000000000^6267 ≤ 8751019137577^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340861627 2500000000 8751019137577 20000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2196049639/10000000000 : ℝ)^8315 ≤ (1338124889913/10000000000000 : ℝ)^6267 := by
    have hnat : (2196049639 : ℕ)^8315*10000000000000^6267 ≤ 1338124889913^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196049639 10000000000 1338124889913 10000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21123521/40000000 : ℝ)^8315 ≤ (42863655400227/100000000000000 : ℝ)^6267 := by
    have hnat : (21123521 : ℕ)^8315*100000000000000^6267 ≤ 42863655400227^6267*40000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21123521 40000000 42863655400227 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340861627/2500000000 : ℝ), (-2196049639/10000000000 : ℝ), (21123521/40000000 : ℝ)] ![(8751019137577/20000000000000 : ℝ), (1338124889913/10000000000000 : ℝ), (42863655400227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340861627/2500000000 : ℝ)|^8315 ≤ (8751019137577/20000000000000 : ℝ)^6267
        have hw : |(1340861627/2500000000 : ℝ)|=(1340861627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2196049639/10000000000 : ℝ)|^8315 ≤ (1338124889913/10000000000000 : ℝ)^6267
        have hw : |(-2196049639/10000000000 : ℝ)|=(2196049639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21123521/40000000 : ℝ)|^8315 ≤ (42863655400227/100000000000000 : ℝ)^6267
        have hw : |(21123521/40000000 : ℝ)|=(21123521/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_box_6 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536344683/1000000000 : ℝ)*x 0 + (2640439999/5000000000 : ℝ)*x 1 + (-274506193/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536344683/1000000000 : ℝ)^8315 ≤ (43755099173209/100000000000000 : ℝ)^6267 := by
    have hnat : (536344683 : ℕ)^8315*100000000000000^6267 ≤ 43755099173209^6267*1000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536344683 1000000000 43755099173209 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640439999/5000000000 : ℝ)^8315 ≤ (5357956585797/12500000000000 : ℝ)^6267 := by
    have hnat : (2640439999 : ℕ)^8315*12500000000000^6267 ≤ 5357956585797^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640439999 5000000000 5357956585797 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274506193/1250000000 : ℝ)^8315 ≤ (2676249626219/20000000000000 : ℝ)^6267 := by
    have hnat : (274506193 : ℕ)^8315*20000000000000^6267 ≤ 2676249626219^6267*1250000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274506193 1250000000 2676249626219 20000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536344683/1000000000 : ℝ), (2640439999/5000000000 : ℝ), (-274506193/1250000000 : ℝ)] ![(43755099173209/100000000000000 : ℝ), (5357956585797/12500000000000 : ℝ), (2676249626219/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536344683/1000000000 : ℝ)|^8315 ≤ (43755099173209/100000000000000 : ℝ)^6267
        have hw : |(536344683/1000000000 : ℝ)|=(536344683/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640439999/5000000000 : ℝ)|^8315 ≤ (5357956585797/12500000000000 : ℝ)^6267
        have hw : |(2640439999/5000000000 : ℝ)|=(2640439999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-274506193/1250000000 : ℝ)|^8315 ≤ (2676249626219/20000000000000 : ℝ)^6267
        have hw : |(-274506193/1250000000 : ℝ)|=(274506193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_box_7 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4259384971/10000000000 : ℝ)*x 0 + (4423659391/10000000000 : ℝ)*x 1 + (2211829893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259384971/10000000000 : ℝ)^8315 ≤ (2014191527989/6250000000000 : ℝ)^6267 := by
    have hnat : (4259384971 : ℕ)^8315*6250000000000^6267 ≤ 2014191527989^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259384971 10000000000 2014191527989 6250000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4423659391/10000000000 : ℝ)^8315 ≤ (33886465761283/100000000000000 : ℝ)^6267 := by
    have hnat : (4423659391 : ℕ)^8315*100000000000000^6267 ≤ 33886465761283^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4423659391 10000000000 33886465761283 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2211829893/5000000000 : ℝ)^8315 ≤ (33886469775901/100000000000000 : ℝ)^6267 := by
    have hnat : (2211829893 : ℕ)^8315*100000000000000^6267 ≤ 33886469775901^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211829893 5000000000 33886469775901 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259384971/10000000000 : ℝ), (4423659391/10000000000 : ℝ), (2211829893/5000000000 : ℝ)] ![(2014191527989/6250000000000 : ℝ), (33886465761283/100000000000000 : ℝ), (33886469775901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259384971/10000000000 : ℝ)|^8315 ≤ (2014191527989/6250000000000 : ℝ)^6267
        have hw : |(4259384971/10000000000 : ℝ)|=(4259384971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4423659391/10000000000 : ℝ)|^8315 ≤ (33886465761283/100000000000000 : ℝ)^6267
        have hw : |(4423659391/10000000000 : ℝ)|=(4423659391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2211829893/5000000000 : ℝ)|^8315 ≤ (33886469775901/100000000000000 : ℝ)^6267
        have hw : |(2211829893/5000000000 : ℝ)|=(2211829893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_box_8 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2251818113/10000000000 : ℝ)*x 0 + (5215822753/10000000000 : ℝ)*x 1 + (5386202547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2251818113/10000000000 : ℝ)^8315 ≤ (6916986719409/50000000000000 : ℝ)^6267 := by
    have hnat : (2251818113 : ℕ)^8315*50000000000000^6267 ≤ 6916986719409^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251818113 10000000000 6916986719409 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215822753/10000000000 : ℝ)^8315 ≤ (10541112300461/25000000000000 : ℝ)^6267 := by
    have hnat : (5215822753 : ℕ)^8315*25000000000000^6267 ≤ 10541112300461^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215822753 10000000000 10541112300461 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386202547/10000000000 : ℝ)^8315 ≤ (44001577341621/100000000000000 : ℝ)^6267 := by
    have hnat : (5386202547 : ℕ)^8315*100000000000000^6267 ≤ 44001577341621^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386202547 10000000000 44001577341621 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2251818113/10000000000 : ℝ), (5215822753/10000000000 : ℝ), (5386202547/10000000000 : ℝ)] ![(6916986719409/50000000000000 : ℝ), (10541112300461/25000000000000 : ℝ), (44001577341621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2251818113/10000000000 : ℝ)|^8315 ≤ (6916986719409/50000000000000 : ℝ)^6267
        have hw : |(-2251818113/10000000000 : ℝ)|=(2251818113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215822753/10000000000 : ℝ)|^8315 ≤ (10541112300461/25000000000000 : ℝ)^6267
        have hw : |(5215822753/10000000000 : ℝ)|=(5215822753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386202547/10000000000 : ℝ)|^8315 ≤ (44001577341621/100000000000000 : ℝ)^6267
        have hw : |(5386202547/10000000000 : ℝ)|=(5386202547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_box_9 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644499863/5000000000 : ℝ)*x 0 + (-1077307487/5000000000 : ℝ)*x 1 + (16831883/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644499863/5000000000 : ℝ)^8315 ≤ (10737779505959/25000000000000 : ℝ)^6267 := by
    have hnat : (2644499863 : ℕ)^8315*25000000000000^6267 ≤ 10737779505959^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644499863 5000000000 10737779505959 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077307487/5000000000 : ℝ)^8315 ≤ (815456529851/6250000000000 : ℝ)^6267 := by
    have hnat : (1077307487 : ℕ)^8315*6250000000000^6267 ≤ 815456529851^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077307487 5000000000 815456529851 6250000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16831883/31250000 : ℝ)^8315 ≤ (1375049296329/3125000000000 : ℝ)^6267 := by
    have hnat : (16831883 : ℕ)^8315*3125000000000^6267 ≤ 1375049296329^6267*31250000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16831883 31250000 1375049296329 3125000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644499863/5000000000 : ℝ), (-1077307487/5000000000 : ℝ), (16831883/31250000 : ℝ)] ![(10737779505959/25000000000000 : ℝ), (815456529851/6250000000000 : ℝ), (1375049296329/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644499863/5000000000 : ℝ)|^8315 ≤ (10737779505959/25000000000000 : ℝ)^6267
        have hw : |(2644499863/5000000000 : ℝ)|=(2644499863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1077307487/5000000000 : ℝ)|^8315 ≤ (815456529851/6250000000000 : ℝ)^6267
        have hw : |(-1077307487/5000000000 : ℝ)|=(1077307487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16831883/31250000 : ℝ)|^8315 ≤ (1375049296329/3125000000000 : ℝ)^6267
        have hw : |(16831883/31250000 : ℝ)|=(16831883/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_box_10 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644499757/5000000000 : ℝ)*x 0 + (269310117/500000000 : ℝ)*x 1 + (-538653889/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644499757/5000000000 : ℝ)^8315 ≤ (42951115739609/100000000000000 : ℝ)^6267 := by
    have hnat : (2644499757 : ℕ)^8315*100000000000000^6267 ≤ 42951115739609^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644499757 5000000000 42951115739609 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269310117/500000000 : ℝ)^8315 ≤ (22000787548977/50000000000000 : ℝ)^6267 := by
    have hnat : (269310117 : ℕ)^8315*50000000000000^6267 ≤ 22000787548977^6267*500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269310117 500000000 22000787548977 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538653889/2500000000 : ℝ)^8315 ≤ (13047309153639/100000000000000 : ℝ)^6267 := by
    have hnat : (538653889 : ℕ)^8315*100000000000000^6267 ≤ 13047309153639^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538653889 2500000000 13047309153639 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644499757/5000000000 : ℝ), (269310117/500000000 : ℝ), (-538653889/2500000000 : ℝ)] ![(42951115739609/100000000000000 : ℝ), (22000787548977/50000000000000 : ℝ), (13047309153639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644499757/5000000000 : ℝ)|^8315 ≤ (42951115739609/100000000000000 : ℝ)^6267
        have hw : |(2644499757/5000000000 : ℝ)|=(2644499757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269310117/500000000 : ℝ)|^8315 ≤ (22000787548977/50000000000000 : ℝ)^6267
        have hw : |(269310117/500000000 : ℝ)|=(269310117/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-538653889/2500000000 : ℝ)|^8315 ≤ (13047309153639/100000000000000 : ℝ)^6267
        have hw : |(-538653889/2500000000 : ℝ)|=(538653889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_box_11 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4496658867/10000000000 : ℝ)*x 0 + (2152451533/5000000000 : ℝ)*x 1 + (1076225783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4496658867/10000000000 : ℝ)^8315 ≤ (17315197854123/50000000000000 : ℝ)^6267 := by
    have hnat : (4496658867 : ℕ)^8315*50000000000000^6267 ≤ 17315197854123^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496658867 10000000000 17315197854123 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2152451533/5000000000 : ℝ)^8315 ≤ (32684801804847/100000000000000 : ℝ)^6267 := by
    have hnat : (2152451533 : ℕ)^8315*100000000000000^6267 ≤ 32684801804847^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152451533 5000000000 32684801804847 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076225783/2500000000 : ℝ)^8315 ≤ (6536960493941/20000000000000 : ℝ)^6267 := by
    have hnat : (1076225783 : ℕ)^8315*20000000000000^6267 ≤ 6536960493941^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076225783 2500000000 6536960493941 20000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4496658867/10000000000 : ℝ), (2152451533/5000000000 : ℝ), (1076225783/2500000000 : ℝ)] ![(17315197854123/50000000000000 : ℝ), (32684801804847/100000000000000 : ℝ), (6536960493941/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4496658867/10000000000 : ℝ)|^8315 ≤ (17315197854123/50000000000000 : ℝ)^6267
        have hw : |(4496658867/10000000000 : ℝ)|=(4496658867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2152451533/5000000000 : ℝ)|^8315 ≤ (32684801804847/100000000000000 : ℝ)^6267
        have hw : |(2152451533/5000000000 : ℝ)|=(2152451533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1076225783/2500000000 : ℝ)|^8315 ≤ (6536960493941/20000000000000 : ℝ)^6267
        have hw : |(1076225783/2500000000 : ℝ)|=(1076225783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_box_12 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2102875637/10000000000 : ℝ)*x 0 + (5440359719/10000000000 : ℝ)*x 1 + (5272850513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102875637/10000000000 : ℝ)^8315 ≤ (12633249649319/100000000000000 : ℝ)^6267 := by
    have hnat : (2102875637 : ℕ)^8315*100000000000000^6267 ≤ 12633249649319^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102875637 10000000000 12633249649319 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440359719/10000000000 : ℝ)^8315 ≤ (44589547685331/100000000000000 : ℝ)^6267 := by
    have hnat : (5440359719 : ℕ)^8315*100000000000000^6267 ≤ 44589547685331^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440359719 10000000000 44589547685331 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272850513/10000000000 : ℝ)^8315 ≤ (42777202649647/100000000000000 : ℝ)^6267 := by
    have hnat : (5272850513 : ℕ)^8315*100000000000000^6267 ≤ 42777202649647^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272850513 10000000000 42777202649647 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2102875637/10000000000 : ℝ), (5440359719/10000000000 : ℝ), (5272850513/10000000000 : ℝ)] ![(12633249649319/100000000000000 : ℝ), (44589547685331/100000000000000 : ℝ), (42777202649647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2102875637/10000000000 : ℝ)|^8315 ≤ (12633249649319/100000000000000 : ℝ)^6267
        have hw : |(-2102875637/10000000000 : ℝ)|=(2102875637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440359719/10000000000 : ℝ)|^8315 ≤ (44589547685331/100000000000000 : ℝ)^6267
        have hw : |(5440359719/10000000000 : ℝ)|=(5440359719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272850513/10000000000 : ℝ)|^8315 ≤ (42777202649647/100000000000000 : ℝ)^6267
        have hw : |(5272850513/10000000000 : ℝ)|=(5272850513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_box_13 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369120027/10000000000 : ℝ)*x 0 + (-439829021/2000000000 : ℝ)*x 1 + (659106323/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369120027/10000000000 : ℝ)^8315 ≤ (8763303278569/20000000000000 : ℝ)^6267 := by
    have hnat : (5369120027 : ℕ)^8315*20000000000000^6267 ≤ 8763303278569^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369120027 10000000000 8763303278569 20000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (439829021/2000000000 : ℝ)^8315 ≤ (6703140090053/50000000000000 : ℝ)^6267 := by
    have hnat : (439829021 : ℕ)^8315*50000000000000^6267 ≤ 6703140090053^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439829021 2000000000 6703140090053 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659106323/1250000000 : ℝ)^8315 ≤ (10694300853471/25000000000000 : ℝ)^6267 := by
    have hnat : (659106323 : ℕ)^8315*25000000000000^6267 ≤ 10694300853471^6267*1250000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659106323 1250000000 10694300853471 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369120027/10000000000 : ℝ), (-439829021/2000000000 : ℝ), (659106323/1250000000 : ℝ)] ![(8763303278569/20000000000000 : ℝ), (6703140090053/50000000000000 : ℝ), (10694300853471/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369120027/10000000000 : ℝ)|^8315 ≤ (8763303278569/20000000000000 : ℝ)^6267
        have hw : |(5369120027/10000000000 : ℝ)|=(5369120027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-439829021/2000000000 : ℝ)|^8315 ≤ (6703140090053/50000000000000 : ℝ)^6267
        have hw : |(-439829021/2000000000 : ℝ)|=(439829021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659106323/1250000000 : ℝ)|^8315 ≤ (10694300853471/25000000000000 : ℝ)^6267
        have hw : |(659106323/1250000000 : ℝ)|=(659106323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_box_14 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684560001/5000000000 : ℝ)*x 0 + (2636425261/5000000000 : ℝ)*x 1 + (-2199145221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684560001/5000000000 : ℝ)^8315 ≤ (5477064515269/12500000000000 : ℝ)^6267 := by
    have hnat : (2684560001 : ℕ)^8315*12500000000000^6267 ≤ 5477064515269^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684560001 5000000000 5477064515269 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636425261/5000000000 : ℝ)^8315 ≤ (21388601373261/50000000000000 : ℝ)^6267 := by
    have hnat : (2636425261 : ℕ)^8315*50000000000000^6267 ≤ 21388601373261^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636425261 5000000000 21388601373261 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2199145221/10000000000 : ℝ)^8315 ≤ (3351570279587/25000000000000 : ℝ)^6267 := by
    have hnat : (2199145221 : ℕ)^8315*25000000000000^6267 ≤ 3351570279587^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199145221 10000000000 3351570279587 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684560001/5000000000 : ℝ), (2636425261/5000000000 : ℝ), (-2199145221/10000000000 : ℝ)] ![(5477064515269/12500000000000 : ℝ), (21388601373261/50000000000000 : ℝ), (3351570279587/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684560001/5000000000 : ℝ)|^8315 ≤ (5477064515269/12500000000000 : ℝ)^6267
        have hw : |(2684560001/5000000000 : ℝ)|=(2684560001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636425261/5000000000 : ℝ)|^8315 ≤ (21388601373261/50000000000000 : ℝ)^6267
        have hw : |(2636425261/5000000000 : ℝ)|=(2636425261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2199145221/10000000000 : ℝ)|^8315 ≤ (3351570279587/25000000000000 : ℝ)^6267
        have hw : |(-2199145221/10000000000 : ℝ)|=(2199145221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_box_15 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4241044143/10000000000 : ℝ)*x 0 + (2216353943/5000000000 : ℝ)*x 1 + (2216353949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4241044143/10000000000 : ℝ)^8315 ≤ (16021538247597/50000000000000 : ℝ)^6267 := by
    have hnat : (4241044143 : ℕ)^8315*50000000000000^6267 ≤ 16021538247597^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241044143 10000000000 16021538247597 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2216353943/5000000000 : ℝ)^8315 ≤ (33978461680921/100000000000000 : ℝ)^6267 := by
    have hnat : (2216353943 : ℕ)^8315*100000000000000^6267 ≤ 33978461680921^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216353943 5000000000 33978461680921 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216353949/5000000000 : ℝ)^8315 ≤ (16989230901483/50000000000000 : ℝ)^6267 := by
    have hnat : (2216353949 : ℕ)^8315*50000000000000^6267 ≤ 16989230901483^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216353949 5000000000 16989230901483 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4241044143/10000000000 : ℝ), (2216353943/5000000000 : ℝ), (2216353949/5000000000 : ℝ)] ![(16021538247597/50000000000000 : ℝ), (33978461680921/100000000000000 : ℝ), (16989230901483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4241044143/10000000000 : ℝ)|^8315 ≤ (16021538247597/50000000000000 : ℝ)^6267
        have hw : |(4241044143/10000000000 : ℝ)|=(4241044143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2216353943/5000000000 : ℝ)|^8315 ≤ (33978461680921/100000000000000 : ℝ)^6267
        have hw : |(2216353943/5000000000 : ℝ)|=(2216353943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2216353949/5000000000 : ℝ)|^8315 ≤ (16989230901483/50000000000000 : ℝ)^6267
        have hw : |(2216353949/5000000000 : ℝ)|=(2216353949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1122_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    -(62229/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59283/100000 : ℝ) ∧ (79747/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2077/2500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14037/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (354/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14037/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (354/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14037/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (354/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14037/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (354/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14037/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (354/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14037/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (354/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (354/3125 : ℝ) ^ (4157/1024 : ℝ) ≤ (14463339292034063/100000000000000000000 : ℝ) := by
    have hpowers : (354/3125 : ℝ)^4157 ≤ (14463339292034063/100000000000000000000 : ℝ)^1024 := by
      have hnat : (354 : ℕ)^4157*100000000000000000000^1024 ≤ 14463339292034063^1024*3125^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        354 3125 14463339292034063 100000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (354/3125 : ℝ)) (X := (14463339292034063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14037/100000 : ℝ) ^ (4157/1024 : ℝ) ≤ (8634557220600249/25000000000000000000 : ℝ) := by
    have hpowers : (14037/100000 : ℝ)^4157 ≤ (8634557220600249/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14037 : ℕ)^4157*25000000000000000000^1024 ≤ 8634557220600249^1024*100000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14037 100000 8634557220600249 25000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14037/100000 : ℝ)) (X := (8634557220600249/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014463339292034063/50000000000000000000 : ℝ) ≤ (312522264922547/312500000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (50014463339292034063/50000000000000000000 : ℝ)^1024 ≤ (312522264922547/312500000000000 : ℝ)^4157 := by
      have hnat : (50014463339292034063 : ℕ)^1024*312500000000000^4157 ≤ 312522264922547^4157*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014463339292034063 50000000000000000000 312522264922547 312500000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312522264922547/312500000000000 : ℝ)) (X := (50014463339292034063/50000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049001568174435059/100000000000000000000 : ℝ) ≤ (1000120684009943/1000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (100049001568174435059/100000000000000000000 : ℝ)^1024 ≤ (1000120684009943/1000000000000000 : ℝ)^4157 := by
      have hnat : (100049001568174435059 : ℕ)^1024*1000000000000000^4157 ≤ 1000120684009943^4157*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049001568174435059 100000000000000000000 1000120684009943 1000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000120684009943/1000000000000000 : ℝ)) (X := (100049001568174435059/100000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508634557220600249/12500000000000000000 : ℝ) ≤ (2500425300669339/2500000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (12508634557220600249/12500000000000000000 : ℝ)^1024 ≤ (2500425300669339/2500000000000000 : ℝ)^4157 := by
      have hnat : (12508634557220600249 : ℕ)^1024*2500000000000000^4157 ≤ 2500425300669339^4157*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508634557220600249 12500000000000000000 2500425300669339 2500000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500425300669339/2500000000000000 : ℝ)) (X := (12508634557220600249/12500000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14463339292034063/100000000000000000000 : ℝ) ≤ ((8059741018761983/8062500000000000 : ℝ)+2*(35311612709/19350000000000 : ℝ)*(354/3125 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (8059741018761983/8062500000000000 : ℝ)+2*(35311612709/19350000000000 : ℝ)*(354/3125 : ℝ)=(312522264922547/312500000000000 : ℝ) by norm_num, show 1+2*(14463339292034063/100000000000000000000 : ℝ)=(50014463339292034063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8634557220600249/25000000000000000000 : ℝ)+(14463339292034063/100000000000000000000 : ℝ) ≤ ((8059741018761983/8062500000000000 : ℝ)+(35311612709/19350000000000 : ℝ)*((14037/100000 : ℝ)+(354/3125 : ℝ)))^(4157/1024 : ℝ) := by
    rw [show (8059741018761983/8062500000000000 : ℝ)+(35311612709/19350000000000 : ℝ)*((14037/100000 : ℝ)+(354/3125 : ℝ))=(1000120684009943/1000000000000000 : ℝ) by norm_num, show 1+(8634557220600249/25000000000000000000 : ℝ)+(14463339292034063/100000000000000000000 : ℝ)=(100049001568174435059/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8634557220600249/25000000000000000000 : ℝ) ≤ ((8059741018761983/8062500000000000 : ℝ)+2*(35311612709/19350000000000 : ℝ)*(14037/100000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (8059741018761983/8062500000000000 : ℝ)+2*(35311612709/19350000000000 : ℝ)*(14037/100000 : ℝ)=(2500425300669339/2500000000000000 : ℝ) by norm_num, show 1+2*(8634557220600249/25000000000000000000 : ℝ)=(12508634557220600249/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8059741018761983/8062500000000000 : ℝ)*(X 1 0+X 2 0)+(35311612709/19350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (14037/100000 : ℝ)) (c := (8059741018761983/8062500000000000 : ℝ)) (alpha := (35311612709/19350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8059741018761983/8062500000000000 : ℝ)*(X 0 1+X 2 1)+(35311612709/19350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (14037/100000 : ℝ)) (c := (8059741018761983/8062500000000000 : ℝ)) (alpha := (35311612709/19350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8059741018761983/8062500000000000 : ℝ)*(X 0 2+X 1 2)+(35311612709/19350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (14037/100000 : ℝ)) (c := (8059741018761983/8062500000000000 : ℝ)) (alpha := (35311612709/19350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-256115969/1250000000 : ℝ)*X 0 0+(5376595309/10000000000 : ℝ)*X 0 1+(2688297517/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((529579367/1000000000 : ℝ)*X 1 0+(-2158457989/10000000000 : ℝ)*X 1 1+(5376595241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295793519/10000000000 : ℝ)*X 2 0+(537659509/1000000000 : ℝ)*X 2 1+(-1079229197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4475263451/10000000000 : ℝ)*X 0 0+(4315740787/10000000000 : ℝ)*X 0 1+(1078935477/2500000000 : ℝ)*X 0 2+(4475263451/10000000000 : ℝ)*X 1 0+(4315740787/10000000000 : ℝ)*X 1 1+(1078935477/2500000000 : ℝ)*X 1 2+(4475263451/10000000000 : ℝ)*X 2 0+(4315740787/10000000000 : ℝ)*X 2 1+(1078935477/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1152717163/5000000000 : ℝ)*X 0 0+(41256873/78125000 : ℝ)*X 0 1+(5280880143/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1340861627/2500000000 : ℝ)*X 1 0+(-2196049639/10000000000 : ℝ)*X 1 1+(21123521/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((536344683/1000000000 : ℝ)*X 2 0+(2640439999/5000000000 : ℝ)*X 2 1+(-274506193/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4259384971/10000000000 : ℝ)*X 0 0+(4423659391/10000000000 : ℝ)*X 0 1+(2211829893/5000000000 : ℝ)*X 0 2+(4259384971/10000000000 : ℝ)*X 1 0+(4423659391/10000000000 : ℝ)*X 1 1+(2211829893/5000000000 : ℝ)*X 1 2+(4259384971/10000000000 : ℝ)*X 2 0+(4423659391/10000000000 : ℝ)*X 2 1+(2211829893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2251818113/10000000000 : ℝ)*X 0 0+(5215822753/10000000000 : ℝ)*X 0 1+(5386202547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644499863/5000000000 : ℝ)*X 1 0+(-1077307487/5000000000 : ℝ)*X 1 1+(16831883/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644499757/5000000000 : ℝ)*X 2 0+(269310117/500000000 : ℝ)*X 2 1+(-538653889/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4496658867/10000000000 : ℝ)*X 0 0+(2152451533/5000000000 : ℝ)*X 0 1+(1076225783/2500000000 : ℝ)*X 0 2+(4496658867/10000000000 : ℝ)*X 1 0+(2152451533/5000000000 : ℝ)*X 1 1+(1076225783/2500000000 : ℝ)*X 1 2+(4496658867/10000000000 : ℝ)*X 2 0+(2152451533/5000000000 : ℝ)*X 2 1+(1076225783/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2102875637/10000000000 : ℝ)*X 0 0+(5440359719/10000000000 : ℝ)*X 0 1+(5272850513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369120027/10000000000 : ℝ)*X 1 0+(-439829021/2000000000 : ℝ)*X 1 1+(659106323/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684560001/5000000000 : ℝ)*X 2 0+(2636425261/5000000000 : ℝ)*X 2 1+(-2199145221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4241044143/10000000000 : ℝ)*X 0 0+(2216353943/5000000000 : ℝ)*X 0 1+(2216353949/5000000000 : ℝ)*X 0 2+(4241044143/10000000000 : ℝ)*X 1 0+(2216353943/5000000000 : ℝ)*X 1 1+(2216353949/5000000000 : ℝ)*X 1 2+(4241044143/10000000000 : ℝ)*X 2 0+(2216353943/5000000000 : ℝ)*X 2 1+(2216353949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62229/100000 : ℝ) ≤ (-125425120714021348473806171257/201562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (26768483/100000000000000 : ℝ)*(lower2) + (36819/500000000000 : ℝ)*(lower3) + (223429921/100000000000000 : ℝ)*(upper5) + (1951840397027609/50000000000000 : ℝ)*(major0) + (1951840397027609/50000000000000 : ℝ)*(major1) + (1951840397027609/50000000000000 : ℝ)*(major2) + (14021408257/100000000000000 : ℝ)*(sp2) + (7458954003/100000000000000 : ℝ)*(sp3) + (2604825376073273/50000000000000 : ℝ)*(sp4) + (5209572159733793/100000000000000 : ℝ)*(sp5) + (5209639433354379/100000000000000 : ℝ)*(sp6) + (2618442813219883/100000000000000 : ℝ)*(sp7) + (270261609/10000000000000 : ℝ)*(sp12) + (81295028843/100000000000000 : ℝ)*(sp13) + (1309225136086943/50000000000000 : ℝ)*(f.failure) + (1302413363690659/25000000000000 : ℝ)*(f.sum) + (21620411143/60468750000000000000000000 : ℝ)*base66 + (7046053511254691/1209375000000000000000000000000 : ℝ)*base67 + (1621462691226559/1209375000000000000000000000000 : ℝ)*base70 + (1141482087250783/604687500000000000000000000000 : ℝ)*base71 + (186574973981/120937500000000000000000000 : ℝ)*base74 + (1009300041529691/1209375000000000000000000000000 : ℝ)*base75 + (2218750194007033/604687500000000000000000000000 : ℝ)*base77 + (4227935912798441/1209375000000000000000000000000 : ℝ)*base79 + (583949988389/483750000000000000000000000 : ℝ)*base82 + (33696081/5000000000000000000000 : ℝ)*base90 + (33696081/5000000000000000000000 : ℝ)*base92 + (33696081/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59283/100000 : ℝ) ≤ (39832452811187536855056707207/67187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (144923011/100000000000000 : ℝ)*(upper0) + (4113123/12500000000000 : ℝ)*(lower1) + (15305803/6250000000000 : ℝ)*(upper2) + (1983749519819893/50000000000000 : ℝ)*(major0) + (1983749519819893/50000000000000 : ℝ)*(major1) + (1983749519819893/50000000000000 : ℝ)*(major2) + (2626983861918651/50000000000000 : ℝ)*(sp0) + (2626979428204177/50000000000000 : ℝ)*(sp1) + (656741933154171/12500000000000 : ℝ)*(sp2) + (266125246062209/10000000000000 : ℝ)*(sp3) + (20103712199/100000000000000 : ℝ)*(sp5) + (4821483309/100000000000000 : ℝ)*(sp7) + (21747443593/50000000000000 : ℝ)*(sp10) + (11236283251/100000000000000 : ℝ)*(sp12) + (1330628641052699/50000000000000 : ℝ)*(f.failure) + (5253978960120553/100000000000000 : ℝ)*(f.sum) + (2364189076991/967500000000000000000000000 : ℝ)*base66 + (14706082778032793/1209375000000000000000000000000 : ℝ)*base68 + (1789745486807417/302343750000000000000000000000 : ℝ)*base70 + (845447449594823/75585937500000000000000000000 : ℝ)*base72 + (1860878881811/967500000000000000000000000 : ℝ)*base74 + (2619468359014043/1209375000000000000000000000000 : ℝ)*base76 + (2385234359619917/302343750000000000000000000000 : ℝ)*base78 + (5470929512282417/302343750000000000000000000000 : ℝ)*base80 + (1672796692181/967500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (11375467/5000000000000000000000 : ℝ)*base89 + (11375467/5000000000000000000000 : ℝ)*base91 + (11375467/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79747/100000 : ℝ) ≤ (107162985642080101369719884953/134375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12977981/100000000000000 : ℝ)*(upper0) + (8964607/50000000000000 : ℝ)*(upper1) + (279230761/100000000000000 : ℝ)*(upper2) + (229426661/100000000000000 : ℝ)*(lower5) + (4435499427542841/100000000000000 : ℝ)*(major0) + (4435499427542841/100000000000000 : ℝ)*(major1) + (4435499427542841/100000000000000 : ℝ)*(major2) + (22785419309/10000000000000 : ℝ)*(sp1) + (26155514381/25000000000000 : ℝ)*(sp3) + (4589421581/25000000000000 : ℝ)*(sp4) + (1173844425945697/20000000000000 : ℝ)*(sp8) + (5869012633221719/100000000000000 : ℝ)*(sp9) + (5869240487414809/100000000000000 : ℝ)*(sp10) + (595014135881511/20000000000000 : ℝ)*(sp11) + (1487587650732539/50000000000000 : ℝ)*(f.failure) + (5869240487414809/100000000000000 : ℝ)*(f.sum) + (1164700872877/322500000000000000000000000 : ℝ)*base66 + (3148965359801297/806250000000000000000000000000 : ℝ)*base68 + (4947675569801297/806250000000000000000000000000 : ℝ)*base70 + (2274074086473703/806250000000000000000000000000 : ℝ)*base71 + (162392068993/80625000000000000000000000 : ℝ)*base74 + (7652458642845047/806250000000000000000000000000 : ℝ)*base76 + (3362984426298703/806250000000000000000000000000 : ℝ)*base77 + (3063351928995047/806250000000000000000000000000 : ℝ)*base80 + (2052356377057/322500000000000000000000000 : ℝ)*base82 + (24565813/5000000000000000000000 : ℝ)*base90 + (24565813/5000000000000000000000 : ℝ)*base92 + (24565813/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-2077/2500 : ℝ) ≤ (-55817409230873206725961506687/67187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (31804907/100000000000000 : ℝ)*(lower0) + (2632767/100000000000000 : ℝ)*(upper3) + (2884987/4000000000000 : ℝ)*(lower4) + (4470341490114489/100000000000000 : ℝ)*(major0) + (4470341490114489/100000000000000 : ℝ)*(major1) + (4470341490114489/100000000000000 : ℝ)*(major2) + (1109189/800000000000 : ℝ)*(sp4) + (6301600867/6250000000000 : ℝ)*(sp6) + (1133337827/2500000000000 : ℝ)*(sp7) + (3497219089/100000000000000 : ℝ)*(sp8) + (2984912792140983/50000000000000 : ℝ)*(sp12) + (74622865251871/1250000000000 : ℝ)*(sp13) + (46638503082311/781250000000 : ℝ)*(sp14) + (1499250392317117/50000000000000 : ℝ)*(sp15) + (1499273059073657/50000000000000 : ℝ)*(f.failure) + (74622865251871/1250000000000 : ℝ)*(f.sum) + (5979624091117/215000000000000000000000000 : ℝ)*base66 + (3323025164262229/268750000000000000000000000000 : ℝ)*base67 + (3832605411268479/268750000000000000000000000000 : ℝ)*base69 + (7767410761119021/268750000000000000000000000000 : ℝ)*base72 + (93116146759/107500000000000000000000000 : ℝ)*base73 + (1040268319568479/268750000000000000000000000000 : ℝ)*base75 + (296482434580979/268750000000000000000000000000 : ℝ)*base77 + (478571815368479/268750000000000000000000000000 : ℝ)*base79 + (40403965519/107500000000000000000000000 : ℝ)*base81 + (49844119/5000000000000000000000 : ℝ)*base90 + (49844119/5000000000000000000000 : ℝ)*base92 + (49844119/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1122_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59283/100000 : ℝ) else (79747/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2077/2500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1122_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1122_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59283/100000 : ℝ) else (79747/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2077/2500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1122_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59283/100000 : ℝ) else (79747/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2077/2500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1122_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

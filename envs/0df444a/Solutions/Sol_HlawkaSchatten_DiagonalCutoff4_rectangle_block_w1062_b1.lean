-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1062_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:03:57.038321+00:00
-- url     : https://prove2.me/submissions/eef4d8f1-6802-430f-b462-9be5a6da7ae0

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
theorem support_rectangle_w1062_s3_0 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-550236353/2500000000 : ℝ)*x 0 + (217520143/400000000 : ℝ)*x 1 + (522393681/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550236353/2500000000 : ℝ)^8255 ≤ (6678411382921/50000000000000 : ℝ)^6207 := by
    have hnat : (550236353 : ℕ)^8255*50000000000000^6207 ≤ 6678411382921^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550236353 2500000000 6678411382921 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217520143/400000000 : ℝ)^8255 ≤ (44478254260263/100000000000000 : ℝ)^6207 := by
    have hnat : (217520143 : ℕ)^8255*100000000000000^6207 ≤ 44478254260263^6207*400000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217520143 400000000 44478254260263 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522393681/1000000000 : ℝ)^8255 ≤ (42164922955199/100000000000000 : ℝ)^6207 := by
    have hnat : (522393681 : ℕ)^8255*100000000000000^6207 ≤ 42164922955199^6207*1000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522393681 1000000000 42164922955199 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-550236353/2500000000 : ℝ), (217520143/400000000 : ℝ), (522393681/1000000000 : ℝ)] ![(6678411382921/50000000000000 : ℝ), (44478254260263/100000000000000 : ℝ), (42164922955199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-550236353/2500000000 : ℝ)|^8255 ≤ (6678411382921/50000000000000 : ℝ)^6207
        have hw : |(-550236353/2500000000 : ℝ)|=(550236353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217520143/400000000 : ℝ)|^8255 ≤ (44478254260263/100000000000000 : ℝ)^6207
        have hw : |(217520143/400000000 : ℝ)|=(217520143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522393681/1000000000 : ℝ)|^8255 ≤ (42164922955199/100000000000000 : ℝ)^6207
        have hw : |(522393681/1000000000 : ℝ)|=(522393681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s3_1 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167368577/312500000 : ℝ)*x 0 + (-11552879/50000000 : ℝ)*x 1 + (5223936719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167368577/312500000 : ℝ)^8255 ≤ (8717246540669/20000000000000 : ℝ)^6207 := by
    have hnat : (167368577 : ℕ)^8255*20000000000000^6207 ≤ 8717246540669^6207*312500000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167368577 312500000 8717246540669 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11552879/50000000 : ℝ)^8255 ≤ (7124422648487/50000000000000 : ℝ)^6207 := by
    have hnat : (11552879 : ℕ)^8255*50000000000000^6207 ≤ 7124422648487^6207*50000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11552879 50000000 7124422648487 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5223936719/10000000000 : ℝ)^8255 ≤ (5270615247293/12500000000000 : ℝ)^6207 := by
    have hnat : (5223936719 : ℕ)^8255*12500000000000^6207 ≤ 5270615247293^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223936719 10000000000 5270615247293 12500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167368577/312500000 : ℝ), (-11552879/50000000 : ℝ), (5223936719/10000000000 : ℝ)] ![(8717246540669/20000000000000 : ℝ), (7124422648487/50000000000000 : ℝ), (5270615247293/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167368577/312500000 : ℝ)|^8255 ≤ (8717246540669/20000000000000 : ℝ)^6207
        have hw : |(167368577/312500000 : ℝ)|=(167368577/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11552879/50000000 : ℝ)|^8255 ≤ (7124422648487/50000000000000 : ℝ)^6207
        have hw : |(-11552879/50000000 : ℝ)|=(11552879/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5223936719/10000000000 : ℝ)|^8255 ≤ (5270615247293/12500000000000 : ℝ)^6207
        have hw : |(5223936719/10000000000 : ℝ)|=(5223936719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s3_2 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (535579439/1000000000 : ℝ)*x 0 + (65299207/125000000 : ℝ)*x 1 + (-2310576107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535579439/1000000000 : ℝ)^8255 ≤ (43586231902419/100000000000000 : ℝ)^6207 := by
    have hnat : (535579439 : ℕ)^8255*100000000000000^6207 ≤ 43586231902419^6207*1000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535579439 1000000000 43586231902419 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65299207/125000000 : ℝ)^8255 ≤ (10541230067883/25000000000000 : ℝ)^6207 := by
    have hnat : (65299207 : ℕ)^8255*25000000000000^6207 ≤ 10541230067883^6207*125000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65299207 125000000 10541230067883 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2310576107/10000000000 : ℝ)^8255 ≤ (3562211953711/25000000000000 : ℝ)^6207 := by
    have hnat : (2310576107 : ℕ)^8255*25000000000000^6207 ≤ 3562211953711^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2310576107 10000000000 3562211953711 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535579439/1000000000 : ℝ), (65299207/125000000 : ℝ), (-2310576107/10000000000 : ℝ)] ![(43586231902419/100000000000000 : ℝ), (10541230067883/25000000000000 : ℝ), (3562211953711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535579439/1000000000 : ℝ)|^8255 ≤ (43586231902419/100000000000000 : ℝ)^6207
        have hw : |(535579439/1000000000 : ℝ)|=(535579439/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65299207/125000000 : ℝ)|^8255 ≤ (10541230067883/25000000000000 : ℝ)^6207
        have hw : |(65299207/125000000 : ℝ)|=(65299207/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2310576107/10000000000 : ℝ)|^8255 ≤ (3562211953711/25000000000000 : ℝ)^6207
        have hw : |(-2310576107/10000000000 : ℝ)|=(2310576107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s3_3 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4373233011/10000000000 : ℝ)*x 0 + (4168714303/10000000000 : ℝ)*x 1 + (573490403/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373233011/10000000000 : ℝ)^8255 ≤ (8321956278827/25000000000000 : ℝ)^6207 := by
    have hnat : (4373233011 : ℕ)^8255*25000000000000^6207 ≤ 8321956278827^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373233011 10000000000 8321956278827 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4168714303/10000000000 : ℝ)^8255 ≤ (49973733583/160000000000 : ℝ)^6207 := by
    have hnat : (4168714303 : ℕ)^8255*160000000000^6207 ≤ 49973733583^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168714303 10000000000 49973733583 160000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (573490403/1250000000 : ℝ)^8255 ≤ (35478591376583/100000000000000 : ℝ)^6207 := by
    have hnat : (573490403 : ℕ)^8255*100000000000000^6207 ≤ 35478591376583^6207*1250000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573490403 1250000000 35478591376583 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373233011/10000000000 : ℝ), (4168714303/10000000000 : ℝ), (573490403/1250000000 : ℝ)] ![(8321956278827/25000000000000 : ℝ), (49973733583/160000000000 : ℝ), (35478591376583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373233011/10000000000 : ℝ)|^8255 ≤ (8321956278827/25000000000000 : ℝ)^6207
        have hw : |(4373233011/10000000000 : ℝ)|=(4373233011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4168714303/10000000000 : ℝ)|^8255 ≤ (49973733583/160000000000 : ℝ)^6207
        have hw : |(4168714303/10000000000 : ℝ)|=(4168714303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(573490403/1250000000 : ℝ)|^8255 ≤ (35478591376583/100000000000000 : ℝ)^6207
        have hw : |(573490403/1250000000 : ℝ)|=(573490403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s3_4 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-8597531/39062500 : ℝ)*x 0 + (5224816083/10000000000 : ℝ)*x 1 + (5437119117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8597531/39062500 : ℝ)^8255 ≤ (6678502279069/50000000000000 : ℝ)^6207 := by
    have hnat : (8597531 : ℕ)^8255*50000000000000^6207 ≤ 6678502279069^6207*39062500^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8597531 39062500 6678502279069 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5224816083/10000000000 : ℝ)^8255 ≤ (10543590480859/25000000000000 : ℝ)^6207 := by
    have hnat : (5224816083 : ℕ)^8255*25000000000000^6207 ≤ 10543590480859^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224816083 10000000000 10543590480859 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437119117/10000000000 : ℝ)^8255 ≤ (22234316752827/50000000000000 : ℝ)^6207 := by
    have hnat : (5437119117 : ℕ)^8255*50000000000000^6207 ≤ 22234316752827^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437119117 10000000000 22234316752827 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8597531/39062500 : ℝ), (5224816083/10000000000 : ℝ), (5437119117/10000000000 : ℝ)] ![(6678502279069/50000000000000 : ℝ), (10543590480859/25000000000000 : ℝ), (22234316752827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8597531/39062500 : ℝ)|^8255 ≤ (6678502279069/50000000000000 : ℝ)^6207
        have hw : |(-8597531/39062500 : ℝ)|=(8597531/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5224816083/10000000000 : ℝ)|^8255 ≤ (10543590480859/25000000000000 : ℝ)^6207
        have hw : |(5224816083/10000000000 : ℝ)|=(5224816083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437119117/10000000000 : ℝ)|^8255 ≤ (22234316752827/50000000000000 : ℝ)^6207
        have hw : |(5437119117/10000000000 : ℝ)|=(5437119117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s3_5 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301888391/10000000000 : ℝ)*x 0 + (-1048697/5000000 : ℝ)*x 1 + (2718559259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301888391/10000000000 : ℝ)^8255 ≤ (344030085191/800000000000 : ℝ)^6207 := by
    have hnat : (5301888391 : ℕ)^8255*800000000000^6207 ≤ 344030085191^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301888391 10000000000 344030085191 800000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048697/5000000 : ℝ)^8255 ≤ (1252761234407/10000000000000 : ℝ)^6207 := by
    have hnat : (1048697 : ℕ)^8255*10000000000000^6207 ≤ 1252761234407^6207*5000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048697 5000000 1252761234407 10000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718559259/5000000000 : ℝ)^8255 ≤ (11117156747541/25000000000000 : ℝ)^6207 := by
    have hnat : (2718559259 : ℕ)^8255*25000000000000^6207 ≤ 11117156747541^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718559259 5000000000 11117156747541 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301888391/10000000000 : ℝ), (-1048697/5000000 : ℝ), (2718559259/5000000000 : ℝ)] ![(344030085191/800000000000 : ℝ), (1252761234407/10000000000000 : ℝ), (11117156747541/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301888391/10000000000 : ℝ)|^8255 ≤ (344030085191/800000000000 : ℝ)^6207
        have hw : |(5301888391/10000000000 : ℝ)|=(5301888391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1048697/5000000 : ℝ)|^8255 ≤ (1252761234407/10000000000000 : ℝ)^6207
        have hw : |(-1048697/5000000 : ℝ)|=(1048697/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718559259/5000000000 : ℝ)|^8255 ≤ (11117156747541/25000000000000 : ℝ)^6207
        have hw : |(2718559259/5000000000 : ℝ)|=(2718559259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s3_6 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301888129/10000000000 : ℝ)*x 0 + (5437118941/10000000000 : ℝ)*x 1 + (-2097393777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301888129/10000000000 : ℝ)^8255 ≤ (43003757822613/100000000000000 : ℝ)^6207 := by
    have hnat : (5301888129 : ℕ)^8255*100000000000000^6207 ≤ 43003757822613^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301888129 10000000000 43003757822613 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437118941/10000000000 : ℝ)^8255 ≤ (44468631591253/100000000000000 : ℝ)^6207 := by
    have hnat : (5437118941 : ℕ)^8255*100000000000000^6207 ≤ 44468631591253^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437118941 10000000000 44468631591253 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2097393777/10000000000 : ℝ)^8255 ≤ (6263805286311/50000000000000 : ℝ)^6207 := by
    have hnat : (2097393777 : ℕ)^8255*50000000000000^6207 ≤ 6263805286311^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097393777 10000000000 6263805286311 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301888129/10000000000 : ℝ), (5437118941/10000000000 : ℝ), (-2097393777/10000000000 : ℝ)] ![(43003757822613/100000000000000 : ℝ), (44468631591253/100000000000000 : ℝ), (6263805286311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301888129/10000000000 : ℝ)|^8255 ≤ (43003757822613/100000000000000 : ℝ)^6207
        have hw : |(5301888129/10000000000 : ℝ)|=(5301888129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437118941/10000000000 : ℝ)|^8255 ≤ (44468631591253/100000000000000 : ℝ)^6207
        have hw : |(5437118941/10000000000 : ℝ)|=(5437118941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2097393777/10000000000 : ℝ)|^8255 ≤ (6263805286311/50000000000000 : ℝ)^6207
        have hw : |(-2097393777/10000000000 : ℝ)|=(2097393777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s3_7 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4373277227/10000000000 : ℝ)*x 0 + (1146549999/2500000000 : ℝ)*x 1 + (2085223867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373277227/10000000000 : ℝ)^8255 ≤ (16644136361897/50000000000000 : ℝ)^6207 := by
    have hnat : (4373277227 : ℕ)^8255*50000000000000^6207 ≤ 16644136361897^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373277227 10000000000 16644136361897 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1146549999/2500000000 : ℝ)^8255 ≤ (17730434919753/50000000000000 : ℝ)^6207 := by
    have hnat : (1146549999 : ℕ)^8255*50000000000000^6207 ≤ 17730434919753^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146549999 2500000000 17730434919753 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085223867/5000000000 : ℝ)^8255 ≤ (31250857427599/100000000000000 : ℝ)^6207 := by
    have hnat : (2085223867 : ℕ)^8255*100000000000000^6207 ≤ 31250857427599^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085223867 5000000000 31250857427599 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373277227/10000000000 : ℝ), (1146549999/2500000000 : ℝ), (2085223867/5000000000 : ℝ)] ![(16644136361897/50000000000000 : ℝ), (17730434919753/50000000000000 : ℝ), (31250857427599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373277227/10000000000 : ℝ)|^8255 ≤ (16644136361897/50000000000000 : ℝ)^6207
        have hw : |(4373277227/10000000000 : ℝ)|=(4373277227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1146549999/2500000000 : ℝ)|^8255 ≤ (17730434919753/50000000000000 : ℝ)^6207
        have hw : |(1146549999/2500000000 : ℝ)|=(1146549999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085223867/5000000000 : ℝ)|^8255 ≤ (31250857427599/100000000000000 : ℝ)^6207
        have hw : |(2085223867/5000000000 : ℝ)|=(2085223867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1062_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2173/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10383/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (466/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2173/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2173/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2173/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2173/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2173/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2173/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2173/25000 : ℝ) ^ (4127/1024 : ℝ) ≤ (5301055823777163/100000000000000000000 : ℝ) := by
    have hpowers : (2173/25000 : ℝ)^4127 ≤ (5301055823777163/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2173 : ℕ)^4127*100000000000000000000^1024 ≤ 5301055823777163^1024*25000^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2173 25000 5301055823777163 100000000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2173/25000 : ℝ)) (X := (5301055823777163/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8377/50000 : ℝ) ^ (4127/1024 : ℝ) ≤ (74642374167417969/100000000000000000000 : ℝ) := by
    have hpowers : (8377/50000 : ℝ)^4127 ≤ (74642374167417969/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8377 : ℕ)^4127*100000000000000000000^1024 ≤ 74642374167417969^1024*50000^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8377 50000 74642374167417969 100000000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8377/50000 : ℝ)) (X := (74642374167417969/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005301055823777163/50000000000000000000 : ℝ) ≤ (5000131525680141/5000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (50005301055823777163/50000000000000000000 : ℝ)^1024 ≤ (5000131525680141/5000000000000000 : ℝ)^4127 := by
      have hnat : (50005301055823777163 : ℕ)^1024*5000000000000000^4127 ≤ 5000131525680141^4127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005301055823777163 50000000000000000000 5000131525680141 5000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000131525680141/5000000000000000 : ℝ)) (X := (50005301055823777163/50000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25019985857497798783/25000000000000000000 : ℝ) ≤ (5000991488745907/5000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (25019985857497798783/25000000000000000000 : ℝ)^1024 ≤ (5000991488745907/5000000000000000 : ℝ)^4127 := by
      have hnat : (25019985857497798783 : ℕ)^1024*5000000000000000^4127 ≤ 5000991488745907^4127*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019985857497798783 25000000000000000000 5000991488745907 5000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000991488745907/5000000000000000 : ℝ)) (X := (25019985857497798783/25000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50074642374167417969/50000000000000000000 : ℝ) ≤ (5001851451811673/5000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (50074642374167417969/50000000000000000000 : ℝ)^1024 ≤ (5001851451811673/5000000000000000 : ℝ)^4127 := by
      have hnat : (50074642374167417969 : ℕ)^1024*5000000000000000^4127 ≤ 5001851451811673^4127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50074642374167417969 50000000000000000000 5001851451811673 5000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001851451811673/5000000000000000 : ℝ)) (X := (50074642374167417969/50000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5301055823777163/100000000000000000000 : ℝ) ≤ ((20148055381049010299/20155000000000000000 : ℝ)+2*(429981532883/201550000000000 : ℝ)*(2173/25000 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (20148055381049010299/20155000000000000000 : ℝ)+2*(429981532883/201550000000000 : ℝ)*(2173/25000 : ℝ)=(5000131525680141/5000000000000000 : ℝ) by norm_num, show 1+2*(5301055823777163/100000000000000000000 : ℝ)=(50005301055823777163/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(74642374167417969/100000000000000000000 : ℝ)+(5301055823777163/100000000000000000000 : ℝ) ≤ ((20148055381049010299/20155000000000000000 : ℝ)+(429981532883/201550000000000 : ℝ)*((8377/50000 : ℝ)+(2173/25000 : ℝ)))^(4127/1024 : ℝ) := by
    rw [show (20148055381049010299/20155000000000000000 : ℝ)+(429981532883/201550000000000 : ℝ)*((8377/50000 : ℝ)+(2173/25000 : ℝ))=(5000991488745907/5000000000000000 : ℝ) by norm_num, show 1+(74642374167417969/100000000000000000000 : ℝ)+(5301055823777163/100000000000000000000 : ℝ)=(25019985857497798783/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(74642374167417969/100000000000000000000 : ℝ) ≤ ((20148055381049010299/20155000000000000000 : ℝ)+2*(429981532883/201550000000000 : ℝ)*(8377/50000 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (20148055381049010299/20155000000000000000 : ℝ)+2*(429981532883/201550000000000 : ℝ)*(8377/50000 : ℝ)=(5001851451811673/5000000000000000 : ℝ) by norm_num, show 1+2*(74642374167417969/100000000000000000000 : ℝ)=(50074642374167417969/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20148055381049010299/20155000000000000000 : ℝ)*(X 1 0+X 2 0)+(429981532883/201550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (2173/25000 : ℝ)) (hi := (8377/50000 : ℝ)) (c := (20148055381049010299/20155000000000000000 : ℝ)) (alpha := (429981532883/201550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20148055381049010299/20155000000000000000 : ℝ)*(X 0 1+X 2 1)+(429981532883/201550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (2173/25000 : ℝ)) (hi := (8377/50000 : ℝ)) (c := (20148055381049010299/20155000000000000000 : ℝ)) (alpha := (429981532883/201550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20148055381049010299/20155000000000000000 : ℝ)*(X 0 2+X 1 2)+(429981532883/201550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (2173/25000 : ℝ)) (hi := (8377/50000 : ℝ)) (c := (20148055381049010299/20155000000000000000 : ℝ)) (alpha := (429981532883/201550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-550236353/2500000000 : ℝ)*X 0 0+(217520143/400000000 : ℝ)*X 0 1+(522393681/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167368577/312500000 : ℝ)*X 1 0+(-11552879/50000000 : ℝ)*X 1 1+(5223936719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535579439/1000000000 : ℝ)*X 2 0+(65299207/125000000 : ℝ)*X 2 1+(-2310576107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4373233011/10000000000 : ℝ)*X 0 0+(4168714303/10000000000 : ℝ)*X 0 1+(573490403/1250000000 : ℝ)*X 0 2+(4373233011/10000000000 : ℝ)*X 1 0+(4168714303/10000000000 : ℝ)*X 1 1+(573490403/1250000000 : ℝ)*X 1 2+(4373233011/10000000000 : ℝ)*X 2 0+(4168714303/10000000000 : ℝ)*X 2 1+(573490403/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-8597531/39062500 : ℝ)*X 0 0+(5224816083/10000000000 : ℝ)*X 0 1+(5437119117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301888391/10000000000 : ℝ)*X 1 0+(-1048697/5000000 : ℝ)*X 1 1+(2718559259/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301888129/10000000000 : ℝ)*X 2 0+(5437118941/10000000000 : ℝ)*X 2 1+(-2097393777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373277227/10000000000 : ℝ)*X 0 0+(1146549999/2500000000 : ℝ)*X 0 1+(2085223867/5000000000 : ℝ)*X 0 2+(4373277227/10000000000 : ℝ)*X 1 0+(1146549999/2500000000 : ℝ)*X 1 1+(2085223867/5000000000 : ℝ)*X 1 2+(4373277227/10000000000 : ℝ)*X 2 0+(1146549999/2500000000 : ℝ)*X 2 1+(2085223867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (566920061752225118987339709/201550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67638953/12500000000000 : ℝ)*(base19) + (265097259/50000000000000 : ℝ)*(base23) + (2065269/5000000000000 : ℝ)*(upper2) + (623237/390625000000 : ℝ)*(upper3) + (3528454031427007/100000000000000 : ℝ)*(major0) + (3528454031427007/100000000000000 : ℝ)*(major1) + (55132094241047/1562500000000 : ℝ)*(major2) + (4671448460004557/100000000000000 : ℝ)*(sp0) + (467145056355233/10000000000000 : ℝ)*(sp1) + (2335724120058241/50000000000000 : ℝ)*(sp2) + (1192725179369691/50000000000000 : ℝ)*(sp3) + (2644659397/100000000000000 : ℝ)*(sp4) + (466870591/20000000000000 : ℝ)*(sp6) + (1626422657/25000000000000 : ℝ)*(sp7) + (2385456864430011/100000000000000 : ℝ)*(f.failure) + (2335725552331977/50000000000000 : ℝ)*(f.sum) + (14551360035907/4031000000000000000000000000 : ℝ)*base65 + (36358055602786145093/2015500000000000000000000000000000 : ℝ)*base67 + (567834240594099303/31492187500000000000000000000000 : ℝ)*base69 + (30173740916807145093/2015500000000000000000000000000000 : ℝ)*base71 + (1466792229559/806200000000000000000000000 : ℝ)*base73 + (1368548820825995481/62984375000000000000000000000000 : ℝ)*base75 + (32016432359666345093/2015500000000000000000000000000000 : ℝ)*base77 + (1179751303411654907/2015500000000000000000000000000000 : ℝ)*base80 + (93234462196157/20155000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (60397541/10000000000000000000000 : ℝ)*base89 + (60397541/10000000000000000000000 : ℝ)*base91 + (39602459/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30770644890419695684924893/3149218750000000000000000000000 : ℝ) := by norm_num
    linear_combination (95795401/5000000000000 : ℝ)*(base19) + (859354679/50000000000000 : ℝ)*(base23) + (36712191/100000000000000 : ℝ)*(upper3) + (8744343/25000000000000 : ℝ)*(lower4) + (196990613/50000000000000 : ℝ)*(upper5) + (44472064423151/1250000000000 : ℝ)*(major0) + (44472064423151/1250000000000 : ℝ)*(major1) + (44472064423151/1250000000000 : ℝ)*(major2) + (5210102767/20000000000000 : ℝ)*(sp1) + (23059821569/100000000000000 : ℝ)*(sp2) + (471025695515389/10000000000000 : ℝ)*(sp4) + (942045797746407/20000000000000 : ℝ)*(sp5) + (4710232176622963/100000000000000 : ℝ)*(sp6) + (2405273026854199/100000000000000 : ℝ)*(sp7) + (2405273026854199/100000000000000 : ℝ)*(f.failure) + (471025695515389/10000000000000 : ℝ)*(f.sum) + (8885723637533/4031000000000000000000000000 : ℝ)*base65 + (196658215513005351/25193750000000000000000000000000 : ℝ)*base68 + (28083159049142851/25193750000000000000000000000000 : ℝ)*base70 + (24952428249844649/25193750000000000000000000000000 : ℝ)*base71 + (4543640260917/1007750000000000000000000000 : ℝ)*base74 + (89913876155138399/25193750000000000000000000000000 : ℝ)*base75 + (87537388671230351/25193750000000000000000000000000 : ℝ)*base78 + (113682397153899101/25193750000000000000000000000000 : ℝ)*base80 + (581551947309/1007750000000000000000000000 : ℝ)*base82 + (48404969/10000000000000000000000 : ℝ)*base89 + (48404969/10000000000000000000000 : ℝ)*base91 + (48404969/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1062_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2173/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10383/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (466/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1062_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1062_s4_0 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2204659707/10000000000 : ℝ)*x 0 + (5406038011/10000000000 : ℝ)*x 1 + (1313369091/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2204659707/10000000000 : ℝ)^8255 ≤ (6693404656721/50000000000000 : ℝ)^6207 := by
    have hnat : (2204659707 : ℕ)^8255*50000000000000^6207 ≤ 6693404656721^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204659707 10000000000 6693404656721 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406038011/10000000000 : ℝ)^8255 ≤ (11032718721083/25000000000000 : ℝ)^6207 := by
    have hnat : (5406038011 : ℕ)^8255*25000000000000^6207 ≤ 11032718721083^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406038011 10000000000 11032718721083 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313369091/2500000000 : ℝ)^8255 ≤ (10620578945363/25000000000000 : ℝ)^6207 := by
    have hnat : (1313369091 : ℕ)^8255*25000000000000^6207 ≤ 10620578945363^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313369091 2500000000 10620578945363 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2204659707/10000000000 : ℝ), (5406038011/10000000000 : ℝ), (1313369091/2500000000 : ℝ)] ![(6693404656721/50000000000000 : ℝ), (11032718721083/25000000000000 : ℝ), (10620578945363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2204659707/10000000000 : ℝ)|^8255 ≤ (6693404656721/50000000000000 : ℝ)^6207
        have hw : |(-2204659707/10000000000 : ℝ)|=(2204659707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406038011/10000000000 : ℝ)|^8255 ≤ (11032718721083/25000000000000 : ℝ)^6207
        have hw : |(5406038011/10000000000 : ℝ)|=(5406038011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313369091/2500000000 : ℝ)|^8255 ≤ (10620578945363/25000000000000 : ℝ)^6207
        have hw : |(1313369091/2500000000 : ℝ)|=(1313369091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s4_1 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336970079/2500000000 : ℝ)*x 0 + (-1141130307/5000000000 : ℝ)*x 1 + (5253476339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336970079/2500000000 : ℝ)^8255 ≤ (1740023847333/4000000000000 : ℝ)^6207 := by
    have hnat : (1336970079 : ℕ)^8255*4000000000000^6207 ≤ 1740023847333^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336970079 2500000000 1740023847333 4000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141130307/5000000000 : ℝ)^8255 ≤ (14017088287561/100000000000000 : ℝ)^6207 := by
    have hnat : (1141130307 : ℕ)^8255*100000000000000^6207 ≤ 14017088287561^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141130307 5000000000 14017088287561 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253476339/10000000000 : ℝ)^8255 ≤ (8496463102517/20000000000000 : ℝ)^6207 := by
    have hnat : (5253476339 : ℕ)^8255*20000000000000^6207 ≤ 8496463102517^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253476339 10000000000 8496463102517 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336970079/2500000000 : ℝ), (-1141130307/5000000000 : ℝ), (5253476339/10000000000 : ℝ)] ![(1740023847333/4000000000000 : ℝ), (14017088287561/100000000000000 : ℝ), (8496463102517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336970079/2500000000 : ℝ)|^8255 ≤ (1740023847333/4000000000000 : ℝ)^6207
        have hw : |(1336970079/2500000000 : ℝ)|=(1336970079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1141130307/5000000000 : ℝ)|^8255 ≤ (14017088287561/100000000000000 : ℝ)^6207
        have hw : |(-1141130307/5000000000 : ℝ)|=(1141130307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253476339/10000000000 : ℝ)|^8255 ≤ (8496463102517/20000000000000 : ℝ)^6207
        have hw : |(5253476339/10000000000 : ℝ)|=(5253476339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s4_2 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069576081/2000000000 : ℝ)*x 0 + (2626738153/5000000000 : ℝ)*x 1 + (-114113027/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069576081/2000000000 : ℝ)^8255 ≤ (43500597146131/100000000000000 : ℝ)^6207 := by
    have hnat : (1069576081 : ℕ)^8255*100000000000000^6207 ≤ 43500597146131^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069576081 2000000000 43500597146131 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626738153/5000000000 : ℝ)^8255 ≤ (21241157578841/50000000000000 : ℝ)^6207 := by
    have hnat : (2626738153 : ℕ)^8255*50000000000000^6207 ≤ 21241157578841^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626738153 5000000000 21241157578841 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114113027/500000000 : ℝ)^8255 ≤ (1752135960389/12500000000000 : ℝ)^6207 := by
    have hnat : (114113027 : ℕ)^8255*12500000000000^6207 ≤ 1752135960389^6207*500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114113027 500000000 1752135960389 12500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069576081/2000000000 : ℝ), (2626738153/5000000000 : ℝ), (-114113027/500000000 : ℝ)] ![(43500597146131/100000000000000 : ℝ), (21241157578841/50000000000000 : ℝ), (1752135960389/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069576081/2000000000 : ℝ)|^8255 ≤ (43500597146131/100000000000000 : ℝ)^6207
        have hw : |(1069576081/2000000000 : ℝ)|=(1069576081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626738153/5000000000 : ℝ)|^8255 ≤ (21241157578841/50000000000000 : ℝ)^6207
        have hw : |(2626738153/5000000000 : ℝ)|=(2626738153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-114113027/500000000 : ℝ)|^8255 ≤ (1752135960389/12500000000000 : ℝ)^6207
        have hw : |(-114113027/500000000 : ℝ)|=(114113027/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s4_3 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4375443801/10000000000 : ℝ)*x 0 + (211432371/500000000 : ℝ)*x 1 + (4527409657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375443801/10000000000 : ℝ)^8255 ≤ (2081887954209/6250000000000 : ℝ)^6207 := by
    have hnat : (4375443801 : ℕ)^8255*6250000000000^6207 ≤ 2081887954209^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375443801 10000000000 2081887954209 6250000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211432371/500000000 : ℝ)^8255 ≤ (497378098289/1562500000000 : ℝ)^6207 := by
    have hnat : (211432371 : ℕ)^8255*1562500000000^6207 ≤ 497378098289^6207*500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211432371 500000000 497378098289 1562500000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4527409657/10000000000 : ℝ)^8255 ≤ (6971518886983/20000000000000 : ℝ)^6207 := by
    have hnat : (4527409657 : ℕ)^8255*20000000000000^6207 ≤ 6971518886983^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527409657 10000000000 6971518886983 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375443801/10000000000 : ℝ), (211432371/500000000 : ℝ), (4527409657/10000000000 : ℝ)] ![(2081887954209/6250000000000 : ℝ), (497378098289/1562500000000 : ℝ), (6971518886983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375443801/10000000000 : ℝ)|^8255 ≤ (2081887954209/6250000000000 : ℝ)^6207
        have hw : |(4375443801/10000000000 : ℝ)|=(4375443801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211432371/500000000 : ℝ)|^8255 ≤ (497378098289/1562500000000 : ℝ)^6207
        have hw : |(211432371/500000000 : ℝ)|=(211432371/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4527409657/10000000000 : ℝ)|^8255 ≤ (6971518886983/20000000000000 : ℝ)^6207
        have hw : |(4527409657/10000000000 : ℝ)|=(4527409657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s4_4 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-22046677/100000000 : ℝ)*x 0 + (328370277/625000000 : ℝ)*x 1 + (2702794099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22046677/100000000 : ℝ)^8255 ≤ (13386873861163/100000000000000 : ℝ)^6207 := by
    have hnat : (22046677 : ℕ)^8255*100000000000000^6207 ≤ 13386873861163^6207*100000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22046677 100000000 13386873861163 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328370277/625000000 : ℝ)^8255 ≤ (42487134668777/100000000000000 : ℝ)^6207 := by
    have hnat : (328370277 : ℕ)^8255*100000000000000^6207 ≤ 42487134668777^6207*625000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328370277 625000000 42487134668777 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702794099/5000000000 : ℝ)^8255 ≤ (1378937233001/3125000000000 : ℝ)^6207 := by
    have hnat : (2702794099 : ℕ)^8255*3125000000000^6207 ≤ 1378937233001^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702794099 5000000000 1378937233001 3125000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22046677/100000000 : ℝ), (328370277/625000000 : ℝ), (2702794099/5000000000 : ℝ)] ![(13386873861163/100000000000000 : ℝ), (42487134668777/100000000000000 : ℝ), (1378937233001/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22046677/100000000 : ℝ)|^8255 ≤ (13386873861163/100000000000000 : ℝ)^6207
        have hw : |(-22046677/100000000 : ℝ)|=(22046677/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328370277/625000000 : ℝ)|^8255 ≤ (42487134668777/100000000000000 : ℝ)^6207
        have hw : |(328370277/625000000 : ℝ)|=(328370277/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702794099/5000000000 : ℝ)|^8255 ≤ (1378937233001/3125000000000 : ℝ)^6207
        have hw : |(2702794099/5000000000 : ℝ)|=(2702794099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s4_5 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061893431/2000000000 : ℝ)*x 0 + (-2130148933/10000000000 : ℝ)*x 1 + (135139701/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061893431/2000000000 : ℝ)^8255 ≤ (10771383506897/25000000000000 : ℝ)^6207 := by
    have hnat : (1061893431 : ℕ)^8255*25000000000000^6207 ≤ 10771383506897^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061893431 2000000000 10771383506897 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2130148933/10000000000 : ℝ)^8255 ≤ (6394238111057/50000000000000 : ℝ)^6207 := by
    have hnat : (2130148933 : ℕ)^8255*50000000000000^6207 ≤ 6394238111057^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130148933 10000000000 6394238111057 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135139701/250000000 : ℝ)^8255 ≤ (44125989740717/100000000000000 : ℝ)^6207 := by
    have hnat : (135139701 : ℕ)^8255*100000000000000^6207 ≤ 44125989740717^6207*250000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135139701 250000000 44125989740717 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061893431/2000000000 : ℝ), (-2130148933/10000000000 : ℝ), (135139701/250000000 : ℝ)] ![(10771383506897/25000000000000 : ℝ), (6394238111057/50000000000000 : ℝ), (44125989740717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061893431/2000000000 : ℝ)|^8255 ≤ (10771383506897/25000000000000 : ℝ)^6207
        have hw : |(1061893431/2000000000 : ℝ)|=(1061893431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2130148933/10000000000 : ℝ)|^8255 ≤ (6394238111057/50000000000000 : ℝ)^6207
        have hw : |(-2130148933/10000000000 : ℝ)|=(2130148933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135139701/250000000 : ℝ)|^8255 ≤ (44125989740717/100000000000000 : ℝ)^6207
        have hw : |(135139701/250000000 : ℝ)|=(135139701/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s4_6 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2654733433/5000000000 : ℝ)*x 0 + (5405588563/10000000000 : ℝ)*x 1 + (-2130148611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654733433/5000000000 : ℝ)^8255 ≤ (215427654543/500000000000 : ℝ)^6207 := by
    have hnat : (2654733433 : ℕ)^8255*500000000000^6207 ≤ 215427654543^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654733433 5000000000 215427654543 500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405588563/10000000000 : ℝ)^8255 ≤ (44125995418627/100000000000000 : ℝ)^6207 := by
    have hnat : (5405588563 : ℕ)^8255*100000000000000^6207 ≤ 44125995418627^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405588563 10000000000 44125995418627 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2130148611/10000000000 : ℝ)^8255 ≤ (6394236825563/50000000000000 : ℝ)^6207 := by
    have hnat : (2130148611 : ℕ)^8255*50000000000000^6207 ≤ 6394236825563^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130148611 10000000000 6394236825563 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654733433/5000000000 : ℝ), (5405588563/10000000000 : ℝ), (-2130148611/10000000000 : ℝ)] ![(215427654543/500000000000 : ℝ), (44125995418627/100000000000000 : ℝ), (6394236825563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654733433/5000000000 : ℝ)|^8255 ≤ (215427654543/500000000000 : ℝ)^6207
        have hw : |(2654733433/5000000000 : ℝ)|=(2654733433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405588563/10000000000 : ℝ)|^8255 ≤ (44125995418627/100000000000000 : ℝ)^6207
        have hw : |(5405588563/10000000000 : ℝ)|=(5405588563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2130148611/10000000000 : ℝ)|^8255 ≤ (6394236825563/50000000000000 : ℝ)^6207
        have hw : |(-2130148611/10000000000 : ℝ)|=(2130148611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s4_7 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4375459943/10000000000 : ℝ)*x 0 + (113163321/250000000 : ℝ)*x 1 + (1057381957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375459943/10000000000 : ℝ)^8255 ≤ (3331037070351/10000000000000 : ℝ)^6207 := by
    have hnat : (4375459943 : ℕ)^8255*10000000000000^6207 ≤ 3331037070351^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375459943 10000000000 3331037070351 10000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113163321/250000000 : ℝ)^8255 ≤ (6969723293451/20000000000000 : ℝ)^6207 := by
    have hnat : (113163321 : ℕ)^8255*20000000000000^6207 ≤ 6969723293451^6207*250000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113163321 250000000 6969723293451 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057381957/2500000000 : ℝ)^8255 ≤ (15920506412523/50000000000000 : ℝ)^6207 := by
    have hnat : (1057381957 : ℕ)^8255*50000000000000^6207 ≤ 15920506412523^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057381957 2500000000 15920506412523 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375459943/10000000000 : ℝ), (113163321/250000000 : ℝ), (1057381957/2500000000 : ℝ)] ![(3331037070351/10000000000000 : ℝ), (6969723293451/20000000000000 : ℝ), (15920506412523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375459943/10000000000 : ℝ)|^8255 ≤ (3331037070351/10000000000000 : ℝ)^6207
        have hw : |(4375459943/10000000000 : ℝ)|=(4375459943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113163321/250000000 : ℝ)|^8255 ≤ (6969723293451/20000000000000 : ℝ)^6207
        have hw : |(113163321/250000000 : ℝ)|=(113163321/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1057381957/2500000000 : ℝ)|^8255 ≤ (15920506412523/50000000000000 : ℝ)^6207
        have hw : |(1057381957/2500000000 : ℝ)|=(1057381957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1062_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (466/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11013/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3561/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (466/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (466/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (466/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (466/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (466/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (466/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10383/100000 : ℝ) ^ (4127/1024 : ℝ) ≤ (678253658149869/6250000000000000000 : ℝ) := by
    have hpowers : (10383/100000 : ℝ)^4127 ≤ (678253658149869/6250000000000000000 : ℝ)^1024 := by
      have hnat : (10383 : ℕ)^4127*6250000000000000000^1024 ≤ 678253658149869^1024*100000^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10383 100000 678253658149869 6250000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10383/100000 : ℝ)) (X := (678253658149869/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (466/3125 : ℝ) ^ (4127/1024 : ℝ) ≤ (23339614307225117/50000000000000000000 : ℝ) := by
    have hpowers : (466/3125 : ℝ)^4127 ≤ (23339614307225117/50000000000000000000 : ℝ)^1024 := by
      have hnat : (466 : ℕ)^4127*50000000000000000000^1024 ≤ 23339614307225117^1024*3125^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        466 3125 23339614307225117 50000000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (466/3125 : ℝ)) (X := (23339614307225117/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125678253658149869/3125000000000000000 : ℝ) ≤ (2000107696644861/2000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (3125678253658149869/3125000000000000000 : ℝ)^1024 ≤ (2000107696644861/2000000000000000 : ℝ)^4127 := by
      have hnat : (3125678253658149869 : ℕ)^1024*2000000000000000^4127 ≤ 2000107696644861^4127*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125678253658149869 3125000000000000000 2000107696644861 2000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000107696644861/2000000000000000 : ℝ)) (X := (3125678253658149869/3125000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50028765643572424069/50000000000000000000 : ℝ) ≤ (5000713584936659/5000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (50028765643572424069/50000000000000000000 : ℝ)^1024 ≤ (5000713584936659/5000000000000000 : ℝ)^4127 := by
      have hnat : (50028765643572424069 : ℕ)^1024*5000000000000000^4127 ≤ 5000713584936659^4127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028765643572424069 50000000000000000000 5000713584936659 5000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000713584936659/5000000000000000 : ℝ)) (X := (50028765643572424069/50000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25023339614307225117/25000000000000000000 : ℝ) ≤ (10002315856522331/10000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (25023339614307225117/25000000000000000000 : ℝ)^1024 ≤ (10002315856522331/10000000000000000 : ℝ)^4127 := by
      have hnat : (25023339614307225117 : ℕ)^1024*10000000000000000^4127 ≤ 10002315856522331^4127*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25023339614307225117 25000000000000000000 10002315856522331 10000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002315856522331/10000000000000000 : ℝ)) (X := (25023339614307225117/25000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(678253658149869/6250000000000000000 : ℝ) ≤ ((45273984323569473387/45290000000000000000 : ℝ)+2*(888686649013/452900000000000 : ℝ)*(10383/100000 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (45273984323569473387/45290000000000000000 : ℝ)+2*(888686649013/452900000000000 : ℝ)*(10383/100000 : ℝ)=(2000107696644861/2000000000000000 : ℝ) by norm_num, show 1+2*(678253658149869/6250000000000000000 : ℝ)=(3125678253658149869/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23339614307225117/50000000000000000000 : ℝ)+(678253658149869/6250000000000000000 : ℝ) ≤ ((45273984323569473387/45290000000000000000 : ℝ)+(888686649013/452900000000000 : ℝ)*((466/3125 : ℝ)+(10383/100000 : ℝ)))^(4127/1024 : ℝ) := by
    rw [show (45273984323569473387/45290000000000000000 : ℝ)+(888686649013/452900000000000 : ℝ)*((466/3125 : ℝ)+(10383/100000 : ℝ))=(5000713584936659/5000000000000000 : ℝ) by norm_num, show 1+(23339614307225117/50000000000000000000 : ℝ)+(678253658149869/6250000000000000000 : ℝ)=(50028765643572424069/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23339614307225117/50000000000000000000 : ℝ) ≤ ((45273984323569473387/45290000000000000000 : ℝ)+2*(888686649013/452900000000000 : ℝ)*(466/3125 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (45273984323569473387/45290000000000000000 : ℝ)+2*(888686649013/452900000000000 : ℝ)*(466/3125 : ℝ)=(10002315856522331/10000000000000000 : ℝ) by norm_num, show 1+2*(23339614307225117/50000000000000000000 : ℝ)=(25023339614307225117/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45273984323569473387/45290000000000000000 : ℝ)*(X 1 0+X 2 0)+(888686649013/452900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (10383/100000 : ℝ)) (hi := (466/3125 : ℝ)) (c := (45273984323569473387/45290000000000000000 : ℝ)) (alpha := (888686649013/452900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45273984323569473387/45290000000000000000 : ℝ)*(X 0 1+X 2 1)+(888686649013/452900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (10383/100000 : ℝ)) (hi := (466/3125 : ℝ)) (c := (45273984323569473387/45290000000000000000 : ℝ)) (alpha := (888686649013/452900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45273984323569473387/45290000000000000000 : ℝ)*(X 0 2+X 1 2)+(888686649013/452900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (10383/100000 : ℝ)) (hi := (466/3125 : ℝ)) (c := (45273984323569473387/45290000000000000000 : ℝ)) (alpha := (888686649013/452900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2204659707/10000000000 : ℝ)*X 0 0+(5406038011/10000000000 : ℝ)*X 0 1+(1313369091/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336970079/2500000000 : ℝ)*X 1 0+(-1141130307/5000000000 : ℝ)*X 1 1+(5253476339/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069576081/2000000000 : ℝ)*X 2 0+(2626738153/5000000000 : ℝ)*X 2 1+(-114113027/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4375443801/10000000000 : ℝ)*X 0 0+(211432371/500000000 : ℝ)*X 0 1+(4527409657/10000000000 : ℝ)*X 0 2+(4375443801/10000000000 : ℝ)*X 1 0+(211432371/500000000 : ℝ)*X 1 1+(4527409657/10000000000 : ℝ)*X 1 2+(4375443801/10000000000 : ℝ)*X 2 0+(211432371/500000000 : ℝ)*X 2 1+(4527409657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-22046677/100000000 : ℝ)*X 0 0+(328370277/625000000 : ℝ)*X 0 1+(2702794099/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061893431/2000000000 : ℝ)*X 1 0+(-2130148933/10000000000 : ℝ)*X 1 1+(135139701/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2654733433/5000000000 : ℝ)*X 2 0+(5405588563/10000000000 : ℝ)*X 2 1+(-2130148611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4375459943/10000000000 : ℝ)*X 0 0+(113163321/250000000 : ℝ)*X 0 1+(1057381957/2500000000 : ℝ)*X 0 2+(4375459943/10000000000 : ℝ)*X 1 0+(113163321/250000000 : ℝ)*X 1 1+(1057381957/2500000000 : ℝ)*X 1 2+(4375459943/10000000000 : ℝ)*X 2 0+(113163321/250000000 : ℝ)*X 2 1+(1057381957/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3108938445754962015910532493/283062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78387051/4000000000000 : ℝ)*(base19) + (881141613/50000000000000 : ℝ)*(base23) + (1024383/625000000000 : ℝ)*(lower2) + (242288679/100000000000000 : ℝ)*(upper3) + (130815013/100000000000000 : ℝ)*(upper5) + (618875274646413/12500000000000 : ℝ)*(major0) + (618875274646413/12500000000000 : ℝ)*(major1) + (618875274646413/12500000000000 : ℝ)*(major2) + (819346372658433/12500000000000 : ℝ)*(sp0) + (1638703291509307/25000000000000 : ℝ)*(sp1) + (6554813363430277/100000000000000 : ℝ)*(sp2) + (3347164071567247/100000000000000 : ℝ)*(sp3) + (1103611151/2500000000000 : ℝ)*(sp4) + (24830954431/100000000000000 : ℝ)*(sp7) + (1673594451260839/50000000000000 : ℝ)*(f.failure) + (6554815125713503/100000000000000 : ℝ)*(f.sum) + (179977704957/1415312500000000000000000000 : ℝ)*base65 + (8690038353019089169/566125000000000000000000000000000 : ℝ)*base68 + (6272161955852964169/566125000000000000000000000000000 : ℝ)*base70 + (3104398402488589169/566125000000000000000000000000000 : ℝ)*base72 + (29942906529673/5661250000000000000000000000 : ℝ)*base73 + (1804691632296535831/566125000000000000000000000000000 : ℝ)*base75 + (2212863779702285831/566125000000000000000000000000000 : ℝ)*base77 + (3651125816639339169/566125000000000000000000000000000 : ℝ)*base80 + (55564346616763/22645000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (41938809/5000000000000000000000 : ℝ)*base89 + (41938809/5000000000000000000000 : ℝ)*base91 + (41938809/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23743174896403351950304992879/2264500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (800141333/100000000000000 : ℝ)*(base19) + (1308558707/100000000000000 : ℝ)*(base23) + (1277057/100000000000000 : ℝ)*(lower2) + (131720191/50000000000000 : ℝ)*(upper3) + (324182623/100000000000000 : ℝ)*(lower4) + (2490115829594681/50000000000000 : ℝ)*(major0) + (2490115829594681/50000000000000 : ℝ)*(major1) + (4980231659189363/100000000000000 : ℝ)*(major2) + (4477245021/12500000000000 : ℝ)*(sp2) + (991347747/100000000000000 : ℝ)*(sp3) + (6593513111505999/100000000000000 : ℝ)*(sp4) + (1318702462272933/20000000000000 : ℝ)*(sp5) + (6593475984987123/100000000000000 : ℝ)*(sp6) + (67338977320531/2000000000000 : ℝ)*(sp7) + (1683474928687149/50000000000000 : ℝ)*(f.failure) + (6593513111505999/100000000000000 : ℝ)*(f.sum) + (27167793616259/9058000000000000000000000000 : ℝ)*base65 + (383246128828029221/323500000000000000000000000000000 : ℝ)*base67 + (9321431182756417519/4529000000000000000000000000000000 : ℝ)*base70 + (7265903128674029221/323500000000000000000000000000000 : ℝ)*base71 + (233289435137/362320000000000000000000000 : ℝ)*base74 + (68207519970898417519/4529000000000000000000000000000000 : ℝ)*base76 + (27089917432514054547/2264500000000000000000000000000000 : ℝ)*base77 + (36220402170805054547/2264500000000000000000000000000000 : ℝ)*base79 + (7419651035583/2830625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (71066419/5000000000000000000000 : ℝ)*base89 + (71066419/5000000000000000000000 : ℝ)*base91 + (21066419/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1062_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (466/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11013/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3561/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1062_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1062_s5_0 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2205503467/10000000000 : ℝ)*x 0 + (5397116297/10000000000 : ℝ)*x 1 + (5261844487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2205503467/10000000000 : ℝ)^8255 ≤ (6696811774913/50000000000000 : ℝ)^6207 := by
    have hnat : (2205503467 : ℕ)^8255*50000000000000^6207 ≤ 6696811774913^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205503467 10000000000 6696811774913 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397116297/10000000000 : ℝ)^8255 ≤ (44034040684113/100000000000000 : ℝ)^6207 := by
    have hnat : (5397116297 : ℕ)^8255*100000000000000^6207 ≤ 44034040684113^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397116297 10000000000 44034040684113 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261844487/10000000000 : ℝ)^8255 ≤ (42572335750179/100000000000000 : ℝ)^6207 := by
    have hnat : (5261844487 : ℕ)^8255*100000000000000^6207 ≤ 42572335750179^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261844487 10000000000 42572335750179 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2205503467/10000000000 : ℝ), (5397116297/10000000000 : ℝ), (5261844487/10000000000 : ℝ)] ![(6696811774913/50000000000000 : ℝ), (44034040684113/100000000000000 : ℝ), (42572335750179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2205503467/10000000000 : ℝ)|^8255 ≤ (6696811774913/50000000000000 : ℝ)^6207
        have hw : |(-2205503467/10000000000 : ℝ)|=(2205503467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397116297/10000000000 : ℝ)|^8255 ≤ (44034040684113/100000000000000 : ℝ)^6207
        have hw : |(5397116297/10000000000 : ℝ)|=(5397116297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261844487/10000000000 : ℝ)|^8255 ≤ (42572335750179/100000000000000 : ℝ)^6207
        have hw : |(5261844487/10000000000 : ℝ)|=(5261844487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s5_1 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672829317/5000000000 : ℝ)*x 0 + (-2274177137/10000000000 : ℝ)*x 1 + (2630922311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672829317/5000000000 : ℝ)^8255 ≤ (21738281785251/50000000000000 : ℝ)^6207 := by
    have hnat : (2672829317 : ℕ)^8255*50000000000000^6207 ≤ 21738281785251^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672829317 5000000000 21738281785251 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2274177137/10000000000 : ℝ)^8255 ≤ (13951099208123/100000000000000 : ℝ)^6207 := by
    have hnat : (2274177137 : ℕ)^8255*100000000000000^6207 ≤ 13951099208123^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274177137 10000000000 13951099208123 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630922311/5000000000 : ℝ)^8255 ≤ (42572337202821/100000000000000 : ℝ)^6207 := by
    have hnat : (2630922311 : ℕ)^8255*100000000000000^6207 ≤ 42572337202821^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630922311 5000000000 42572337202821 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672829317/5000000000 : ℝ), (-2274177137/10000000000 : ℝ), (2630922311/5000000000 : ℝ)] ![(21738281785251/50000000000000 : ℝ), (13951099208123/100000000000000 : ℝ), (42572337202821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672829317/5000000000 : ℝ)|^8255 ≤ (21738281785251/50000000000000 : ℝ)^6207
        have hw : |(2672829317/5000000000 : ℝ)|=(2672829317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2274177137/10000000000 : ℝ)|^8255 ≤ (13951099208123/100000000000000 : ℝ)^6207
        have hw : |(-2274177137/10000000000 : ℝ)|=(2274177137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630922311/5000000000 : ℝ)|^8255 ≤ (42572337202821/100000000000000 : ℝ)^6207
        have hw : |(2630922311/5000000000 : ℝ)|=(2630922311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s5_2 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345658361/10000000000 : ℝ)*x 0 + (65773057/125000000 : ℝ)*x 1 + (-1137088791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345658361/10000000000 : ℝ)^8255 ≤ (2173828030879/5000000000000 : ℝ)^6207 := by
    have hnat : (5345658361 : ℕ)^8255*5000000000000^6207 ≤ 2173828030879^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345658361 10000000000 2173828030879 5000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65773057/125000000 : ℝ)^8255 ≤ (42572336535681/100000000000000 : ℝ)^6207 := by
    have hnat : (65773057 : ℕ)^8255*100000000000000^6207 ≤ 42572336535681^6207*125000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65773057 125000000 42572336535681 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1137088791/5000000000 : ℝ)^8255 ≤ (3487775709683/25000000000000 : ℝ)^6207 := by
    have hnat : (1137088791 : ℕ)^8255*25000000000000^6207 ≤ 3487775709683^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137088791 5000000000 3487775709683 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345658361/10000000000 : ℝ), (65773057/125000000 : ℝ), (-1137088791/5000000000 : ℝ)] ![(2173828030879/5000000000000 : ℝ), (42572336535681/100000000000000 : ℝ), (3487775709683/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345658361/10000000000 : ℝ)|^8255 ≤ (2173828030879/5000000000000 : ℝ)^6207
        have hw : |(5345658361/10000000000 : ℝ)|=(5345658361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65773057/125000000 : ℝ)|^8255 ≤ (42572336535681/100000000000000 : ℝ)^6207
        have hw : |(65773057/125000000 : ℝ)|=(65773057/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1137088791/5000000000 : ℝ)|^8255 ≤ (3487775709683/25000000000000 : ℝ)^6207
        have hw : |(-1137088791/5000000000 : ℝ)|=(1137088791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s5_3 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4375931793/10000000000 : ℝ)*x 0 + (4245512101/10000000000 : ℝ)*x 1 + (45104167/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375931793/10000000000 : ℝ)^8255 ≤ (4164393528293/12500000000000 : ℝ)^6207 := by
    have hnat : (4375931793 : ℕ)^8255*12500000000000^6207 ≤ 4164393528293^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375931793 10000000000 4164393528293 12500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4245512101/10000000000 : ℝ)^8255 ≤ (6400230110937/20000000000000 : ℝ)^6207 := by
    have hnat : (4245512101 : ℕ)^8255*20000000000000^6207 ≤ 6400230110937^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245512101 10000000000 6400230110937 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45104167/100000000 : ℝ)^8255 ≤ (693674024037/2000000000000 : ℝ)^6207 := by
    have hnat : (45104167 : ℕ)^8255*2000000000000^6207 ≤ 693674024037^6207*100000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45104167 100000000 693674024037 2000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375931793/10000000000 : ℝ), (4245512101/10000000000 : ℝ), (45104167/100000000 : ℝ)] ![(4164393528293/12500000000000 : ℝ), (6400230110937/20000000000000 : ℝ), (693674024037/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375931793/10000000000 : ℝ)|^8255 ≤ (4164393528293/12500000000000 : ℝ)^6207
        have hw : |(4375931793/10000000000 : ℝ)|=(4375931793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4245512101/10000000000 : ℝ)|^8255 ≤ (6400230110937/20000000000000 : ℝ)^6207
        have hw : |(4245512101/10000000000 : ℝ)|=(4245512101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(45104167/100000000 : ℝ)|^8255 ≤ (693674024037/2000000000000 : ℝ)^6207
        have hw : |(45104167/100000000 : ℝ)|=(45104167/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s5_4 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-441101853/2000000000 : ℝ)*x 0 + (5262196691/10000000000 : ℝ)*x 1 + (5396762707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441101853/2000000000 : ℝ)^8255 ≤ (13393670377661/100000000000000 : ℝ)^6207 := by
    have hnat : (441101853 : ℕ)^8255*100000000000000^6207 ≤ 13393670377661^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441101853 2000000000 13393670377661 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262196691/10000000000 : ℝ)^8255 ≤ (42576125616417/100000000000000 : ℝ)^6207 := by
    have hnat : (5262196691 : ℕ)^8255*100000000000000^6207 ≤ 42576125616417^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262196691 10000000000 42576125616417 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396762707/10000000000 : ℝ)^8255 ≤ (44030203988237/100000000000000 : ℝ)^6207 := by
    have hnat : (5396762707 : ℕ)^8255*100000000000000^6207 ≤ 44030203988237^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396762707 10000000000 44030203988237 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-441101853/2000000000 : ℝ), (5262196691/10000000000 : ℝ), (5396762707/10000000000 : ℝ)] ![(13393670377661/100000000000000 : ℝ), (42576125616417/100000000000000 : ℝ), (44030203988237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-441101853/2000000000 : ℝ)|^8255 ≤ (13393670377661/100000000000000 : ℝ)^6207
        have hw : |(-441101853/2000000000 : ℝ)|=(441101853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262196691/10000000000 : ℝ)|^8255 ≤ (42576125616417/100000000000000 : ℝ)^6207
        have hw : |(5262196691/10000000000 : ℝ)|=(5262196691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396762707/10000000000 : ℝ)|^8255 ≤ (44030203988237/100000000000000 : ℝ)^6207
        have hw : |(5396762707/10000000000 : ℝ)|=(5396762707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s5_5 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311597707/10000000000 : ℝ)*x 0 + (-66851849/312500000 : ℝ)*x 1 + (1349190659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311597707/10000000000 : ℝ)^8255 ≤ (43108529204713/100000000000000 : ℝ)^6207 := by
    have hnat : (5311597707 : ℕ)^8255*100000000000000^6207 ≤ 43108529204713^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311597707 10000000000 43108529204713 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66851849/312500000 : ℝ)^8255 ≤ (12861267570937/100000000000000 : ℝ)^6207 := by
    have hnat : (66851849 : ℕ)^8255*100000000000000^6207 ≤ 12861267570937^6207*312500000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66851849 312500000 12861267570937 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349190659/2500000000 : ℝ)^8255 ≤ (44030203217847/100000000000000 : ℝ)^6207 := by
    have hnat : (1349190659 : ℕ)^8255*100000000000000^6207 ≤ 44030203217847^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349190659 2500000000 44030203217847 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311597707/10000000000 : ℝ), (-66851849/312500000 : ℝ), (1349190659/2500000000 : ℝ)] ![(43108529204713/100000000000000 : ℝ), (12861267570937/100000000000000 : ℝ), (44030203217847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311597707/10000000000 : ℝ)|^8255 ≤ (43108529204713/100000000000000 : ℝ)^6207
        have hw : |(5311597707/10000000000 : ℝ)|=(5311597707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-66851849/312500000 : ℝ)|^8255 ≤ (12861267570937/100000000000000 : ℝ)^6207
        have hw : |(-66851849/312500000 : ℝ)|=(66851849/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349190659/2500000000 : ℝ)|^8255 ≤ (44030203217847/100000000000000 : ℝ)^6207
        have hw : |(1349190659/2500000000 : ℝ)|=(1349190659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s5_6 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655798843/5000000000 : ℝ)*x 0 + (84324417/156250000 : ℝ)*x 1 + (-17114073/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655798843/5000000000 : ℝ)^8255 ≤ (10777132244511/25000000000000 : ℝ)^6207 := by
    have hnat : (2655798843 : ℕ)^8255*25000000000000^6207 ≤ 10777132244511^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655798843 5000000000 10777132244511 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84324417/156250000 : ℝ)^8255 ≤ (11007550945519/25000000000000 : ℝ)^6207 := by
    have hnat : (84324417 : ℕ)^8255*25000000000000^6207 ≤ 11007550945519^6207*156250000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84324417 156250000 11007550945519 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17114073/80000000 : ℝ)^8255 ≤ (12861267227123/100000000000000 : ℝ)^6207 := by
    have hnat : (17114073 : ℕ)^8255*100000000000000^6207 ≤ 12861267227123^6207*80000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17114073 80000000 12861267227123 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655798843/5000000000 : ℝ), (84324417/156250000 : ℝ), (-17114073/80000000 : ℝ)] ![(10777132244511/25000000000000 : ℝ), (11007550945519/25000000000000 : ℝ), (12861267227123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655798843/5000000000 : ℝ)|^8255 ≤ (10777132244511/25000000000000 : ℝ)^6207
        have hw : |(2655798843/5000000000 : ℝ)|=(2655798843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84324417/156250000 : ℝ)|^8255 ≤ (11007550945519/25000000000000 : ℝ)^6207
        have hw : |(84324417/156250000 : ℝ)|=(84324417/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17114073/80000000 : ℝ)|^8255 ≤ (12861267227123/100000000000000 : ℝ)^6207
        have hw : |(-17114073/80000000 : ℝ)|=(17114073/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s5_7 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187971513/5000000000 : ℝ)*x 0 + (90194527/200000000 : ℝ)*x 1 + (2123102497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187971513/5000000000 : ℝ)^8255 ≤ (3331526196353/10000000000000 : ℝ)^6207 := by
    have hnat : (2187971513 : ℕ)^8255*10000000000000^6207 ≤ 3331526196353^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187971513 5000000000 3331526196353 10000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90194527/200000000 : ℝ)^8255 ≤ (3467664123821/10000000000000 : ℝ)^6207 := by
    have hnat : (90194527 : ℕ)^8255*10000000000000^6207 ≤ 3467664123821^6207*200000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90194527 200000000 3467664123821 10000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123102497/5000000000 : ℝ)^8255 ≤ (16004048388739/50000000000000 : ℝ)^6207 := by
    have hnat : (2123102497 : ℕ)^8255*50000000000000^6207 ≤ 16004048388739^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123102497 5000000000 16004048388739 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187971513/5000000000 : ℝ), (90194527/200000000 : ℝ), (2123102497/5000000000 : ℝ)] ![(3331526196353/10000000000000 : ℝ), (3467664123821/10000000000000 : ℝ), (16004048388739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187971513/5000000000 : ℝ)|^8255 ≤ (3331526196353/10000000000000 : ℝ)^6207
        have hw : |(2187971513/5000000000 : ℝ)|=(2187971513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(90194527/200000000 : ℝ)|^8255 ≤ (3467664123821/10000000000000 : ℝ)^6207
        have hw : |(90194527/200000000 : ℝ)|=(90194527/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123102497/5000000000 : ℝ)|^8255 ≤ (16004048388739/50000000000000 : ℝ)^6207
        have hw : |(2123102497/5000000000 : ℝ)|=(2123102497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1062_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3561/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11013/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1399/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14057/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3561/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11013/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3561/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11013/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3561/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11013/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3561/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11013/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3561/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11013/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3561/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11013/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11013/100000 : ℝ) ^ (4127/1024 : ℝ) ≤ (6879989120583861/50000000000000000000 : ℝ) := by
    have hpowers : (11013/100000 : ℝ)^4127 ≤ (6879989120583861/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11013 : ℕ)^4127*50000000000000000000^1024 ≤ 6879989120583861^1024*100000^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11013 100000 6879989120583861 50000000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11013/100000 : ℝ)) (X := (6879989120583861/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3561/25000 : ℝ) ^ (4127/1024 : ℝ) ≤ (38806581776223723/100000000000000000000 : ℝ) := by
    have hpowers : (3561/25000 : ℝ)^4127 ≤ (38806581776223723/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3561 : ℕ)^4127*100000000000000000000^1024 ≤ 38806581776223723^1024*25000^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3561 25000 38806581776223723 100000000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3561/25000 : ℝ)) (X := (38806581776223723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006879989120583861/25000000000000000000 : ℝ) ≤ (2500170690092127/2500000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (25006879989120583861/25000000000000000000 : ℝ)^1024 ≤ (2500170690092127/2500000000000000 : ℝ)^4127 := by
      have hnat : (25006879989120583861 : ℕ)^1024*2500000000000000^4127 ≤ 2500170690092127^4127*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006879989120583861 25000000000000000000 2500170690092127 2500000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500170690092127/2500000000000000 : ℝ)) (X := (25006879989120583861/25000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010513312003478289/20000000000000000000 : ℝ) ≤ (5000652017486069/5000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (20010513312003478289/20000000000000000000 : ℝ)^1024 ≤ (5000652017486069/5000000000000000 : ℝ)^4127 := by
      have hnat : (20010513312003478289 : ℕ)^1024*5000000000000000^4127 ≤ 5000652017486069^4127*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010513312003478289 20000000000000000000 5000652017486069 5000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000652017486069/5000000000000000 : ℝ)) (X := (20010513312003478289/20000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038806581776223723/50000000000000000000 : ℝ) ≤ (1250240663696971/1250000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (50038806581776223723/50000000000000000000 : ℝ)^1024 ≤ (1250240663696971/1250000000000000 : ℝ)^4127 := by
      have hnat : (50038806581776223723 : ℕ)^1024*1250000000000000^4127 ≤ 1250240663696971^4127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038806581776223723 50000000000000000000 1250240663696971 1250000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250240663696971/1250000000000000 : ℝ)) (X := (50038806581776223723/50000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6879989120583861/50000000000000000000 : ℝ) ≤ ((1345771741847128957/1346250000000000000 : ℝ)+2*(62127460363/32310000000000 : ℝ)*(11013/100000 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (1345771741847128957/1346250000000000000 : ℝ)+2*(62127460363/32310000000000 : ℝ)*(11013/100000 : ℝ)=(2500170690092127/2500000000000000 : ℝ) by norm_num, show 1+2*(6879989120583861/50000000000000000000 : ℝ)=(25006879989120583861/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38806581776223723/100000000000000000000 : ℝ)+(6879989120583861/50000000000000000000 : ℝ) ≤ ((1345771741847128957/1346250000000000000 : ℝ)+(62127460363/32310000000000 : ℝ)*((3561/25000 : ℝ)+(11013/100000 : ℝ)))^(4127/1024 : ℝ) := by
    rw [show (1345771741847128957/1346250000000000000 : ℝ)+(62127460363/32310000000000 : ℝ)*((3561/25000 : ℝ)+(11013/100000 : ℝ))=(5000652017486069/5000000000000000 : ℝ) by norm_num, show 1+(38806581776223723/100000000000000000000 : ℝ)+(6879989120583861/50000000000000000000 : ℝ)=(20010513312003478289/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38806581776223723/100000000000000000000 : ℝ) ≤ ((1345771741847128957/1346250000000000000 : ℝ)+2*(62127460363/32310000000000 : ℝ)*(3561/25000 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (1345771741847128957/1346250000000000000 : ℝ)+2*(62127460363/32310000000000 : ℝ)*(3561/25000 : ℝ)=(1250240663696971/1250000000000000 : ℝ) by norm_num, show 1+2*(38806581776223723/100000000000000000000 : ℝ)=(50038806581776223723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1345771741847128957/1346250000000000000 : ℝ)*(X 1 0+X 2 0)+(62127460363/32310000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (11013/100000 : ℝ)) (hi := (3561/25000 : ℝ)) (c := (1345771741847128957/1346250000000000000 : ℝ)) (alpha := (62127460363/32310000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1345771741847128957/1346250000000000000 : ℝ)*(X 0 1+X 2 1)+(62127460363/32310000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (11013/100000 : ℝ)) (hi := (3561/25000 : ℝ)) (c := (1345771741847128957/1346250000000000000 : ℝ)) (alpha := (62127460363/32310000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1345771741847128957/1346250000000000000 : ℝ)*(X 0 2+X 1 2)+(62127460363/32310000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (11013/100000 : ℝ)) (hi := (3561/25000 : ℝ)) (c := (1345771741847128957/1346250000000000000 : ℝ)) (alpha := (62127460363/32310000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2205503467/10000000000 : ℝ)*X 0 0+(5397116297/10000000000 : ℝ)*X 0 1+(5261844487/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672829317/5000000000 : ℝ)*X 1 0+(-2274177137/10000000000 : ℝ)*X 1 1+(2630922311/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345658361/10000000000 : ℝ)*X 2 0+(65773057/125000000 : ℝ)*X 2 1+(-1137088791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4375931793/10000000000 : ℝ)*X 0 0+(4245512101/10000000000 : ℝ)*X 0 1+(45104167/100000000 : ℝ)*X 0 2+(4375931793/10000000000 : ℝ)*X 1 0+(4245512101/10000000000 : ℝ)*X 1 1+(45104167/100000000 : ℝ)*X 1 2+(4375931793/10000000000 : ℝ)*X 2 0+(4245512101/10000000000 : ℝ)*X 2 1+(45104167/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-441101853/2000000000 : ℝ)*X 0 0+(5262196691/10000000000 : ℝ)*X 0 1+(5396762707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311597707/10000000000 : ℝ)*X 1 0+(-66851849/312500000 : ℝ)*X 1 1+(1349190659/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655798843/5000000000 : ℝ)*X 2 0+(84324417/156250000 : ℝ)*X 2 1+(-17114073/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2187971513/5000000000 : ℝ)*X 0 0+(90194527/200000000 : ℝ)*X 0 1+(2123102497/5000000000 : ℝ)*X 0 2+(2187971513/5000000000 : ℝ)*X 1 0+(90194527/200000000 : ℝ)*X 1 1+(2123102497/5000000000 : ℝ)*X 1 2+(2187971513/5000000000 : ℝ)*X 2 0+(90194527/200000000 : ℝ)*X 2 1+(2123102497/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1135534661208713286479/179500000000000000000000000 : ℝ) := by norm_num
    linear_combination (740366917/100000000000000 : ℝ)*(base19) + (517405967/100000000000000 : ℝ)*(base23) + (25464127/20000000000000 : ℝ)*(upper3) + (68904797/50000000000000 : ℝ)*(lower4) + (5583789158397877/100000000000000 : ℝ)*(major0) + (5583789158397877/100000000000000 : ℝ)*(major1) + (5583789158397877/100000000000000 : ℝ)*(major2) + (3696280727243483/50000000000000 : ℝ)*(sp0) + (3696292337525489/50000000000000 : ℝ)*(sp1) + (184814217442603/2500000000000 : ℝ)*(sp2) + (1887484435278001/50000000000000 : ℝ)*(sp3) + (23960930929/100000000000000 : ℝ)*(sp4) + (16200307809/100000000000000 : ℝ)*(sp6) + (23819951899/100000000000000 : ℝ)*(sp7) + (1887496345253951/50000000000000 : ℝ)*(f.failure) + (1478517083083579/20000000000000 : ℝ)*(f.sum) + (13446939109859/3231000000000000000000000000 : ℝ)*base65 + (215979072660572867/403875000000000000000000000000000 : ℝ)*base67 + (2252204320048322867/403875000000000000000000000000000 : ℝ)*base69 + (56661721425552133/403875000000000000000000000000000 : ℝ)*base72 + (720176033291/201937500000000000000000000 : ℝ)*base73 + (5855432457251802133/403875000000000000000000000000000 : ℝ)*base76 + (9467343552961697867/403875000000000000000000000000000 : ℝ)*base77 + (7943013593424552133/403875000000000000000000000000000 : ℝ)*base80 + (4965039434231/3231000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (65827681/5000000000000000000000 : ℝ)*base89 + (65827681/5000000000000000000000 : ℝ)*base91 + (65827681/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (248355107795858973805795981/33656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16895731/1250000000000 : ℝ)*(base19) + (782286857/50000000000000 : ℝ)*(base23) + (139574277/100000000000000 : ℝ)*(upper3) + (100005169/100000000000000 : ℝ)*(lower4) + (111383131/100000000000000 : ℝ)*(upper5) + (2806512941927411/50000000000000 : ℝ)*(major0) + (2806512941927411/50000000000000 : ℝ)*(major1) + (2806512941927411/50000000000000 : ℝ)*(major2) + (31861129067/100000000000000 : ℝ)*(sp1) + (10071329151/25000000000000 : ℝ)*(sp2) + (3715646482917653/50000000000000 : ℝ)*(sp4) + (7431259753047759/100000000000000 : ℝ)*(sp5) + (1857812778986247/25000000000000 : ℝ)*(sp6) + (1897379277951039/50000000000000 : ℝ)*(sp7) + (1897379277951039/50000000000000 : ℝ)*(f.failure) + (3715646482917653/50000000000000 : ℝ)*(f.sum) + (8654481698453/1615500000000000000000000000 : ℝ)*base66 + (1759905872183329019/201937500000000000000000000000000 : ℝ)*base68 + (1304519291156170981/201937500000000000000000000000000 : ℝ)*base69 + (2976394208318516519/201937500000000000000000000000000 : ℝ)*base72 + (11171070405907/3231000000000000000000000000 : ℝ)*base74 + (3240730965035170981/201937500000000000000000000000000 : ℝ)*base75 + (291841267665454019/201937500000000000000000000000000 : ℝ)*base78 + (1850759479513204019/201937500000000000000000000000000 : ℝ)*base80 + (8443932719413/807750000000000000000000000 : ℝ)*base82 + (40375009/5000000000000000000000 : ℝ)*base89 + (40375009/5000000000000000000000 : ℝ)*base91 + (40375009/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1062_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3561/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11013/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1062_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1062_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2173/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1062_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1062_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1062_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2173/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1062_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

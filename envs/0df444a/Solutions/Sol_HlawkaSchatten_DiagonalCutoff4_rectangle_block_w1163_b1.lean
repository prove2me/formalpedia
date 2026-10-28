-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1163_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:41:05.776338+00:00
-- url     : https://prove2.me/submissions/0bcaa2be-2afb-44dc-8934-37b226114fed

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
theorem support_rectangle_w1163_s3_0 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2153305149/10000000000 : ℝ)*x 0 + (2713526817/5000000000 : ℝ)*x 1 + (5234015793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153305149/10000000000 : ℝ)^2089 ≤ (13079372487939/100000000000000 : ℝ)^1577 := by
    have hnat : (2153305149 : ℕ)^2089*100000000000000^1577 ≤ 13079372487939^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153305149 10000000000 13079372487939 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713526817/5000000000 : ℝ)^2089 ≤ (44502644287839/100000000000000 : ℝ)^1577 := by
    have hnat : (2713526817 : ℕ)^2089*100000000000000^1577 ≤ 44502644287839^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713526817 5000000000 44502644287839 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234015793/10000000000 : ℝ)^2089 ≤ (21208991605381/50000000000000 : ℝ)^1577 := by
    have hnat : (5234015793 : ℕ)^2089*50000000000000^1577 ≤ 21208991605381^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234015793 10000000000 21208991605381 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2153305149/10000000000 : ℝ), (2713526817/5000000000 : ℝ), (5234015793/10000000000 : ℝ)] ![(13079372487939/100000000000000 : ℝ), (44502644287839/100000000000000 : ℝ), (21208991605381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2153305149/10000000000 : ℝ)|^2089 ≤ (13079372487939/100000000000000 : ℝ)^1577
        have hw : |(-2153305149/10000000000 : ℝ)|=(2153305149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713526817/5000000000 : ℝ)|^2089 ≤ (44502644287839/100000000000000 : ℝ)^1577
        have hw : |(2713526817/5000000000 : ℝ)|=(2713526817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234015793/10000000000 : ℝ)|^2089 ≤ (21208991605381/50000000000000 : ℝ)^1577
        have hw : |(5234015793/10000000000 : ℝ)|=(5234015793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s3_1 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2676647411/5000000000 : ℝ)*x 0 + (-2251935007/10000000000 : ℝ)*x 1 + (5234015599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676647411/5000000000 : ℝ)^2089 ≤ (43703214769647/100000000000000 : ℝ)^1577 := by
    have hnat : (2676647411 : ℕ)^2089*100000000000000^1577 ≤ 43703214769647^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676647411 5000000000 43703214769647 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251935007/10000000000 : ℝ)^2089 ≤ (3469701020737/25000000000000 : ℝ)^1577 := by
    have hnat : (2251935007 : ℕ)^2089*25000000000000^1577 ≤ 3469701020737^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251935007 10000000000 3469701020737 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234015599/10000000000 : ℝ)^2089 ≤ (21208990564039/50000000000000 : ℝ)^1577 := by
    have hnat : (5234015599 : ℕ)^2089*50000000000000^1577 ≤ 21208990564039^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234015599 10000000000 21208990564039 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676647411/5000000000 : ℝ), (-2251935007/10000000000 : ℝ), (5234015599/10000000000 : ℝ)] ![(43703214769647/100000000000000 : ℝ), (3469701020737/25000000000000 : ℝ), (21208990564039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676647411/5000000000 : ℝ)|^2089 ≤ (43703214769647/100000000000000 : ℝ)^1577
        have hw : |(2676647411/5000000000 : ℝ)|=(2676647411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2251935007/10000000000 : ℝ)|^2089 ≤ (3469701020737/25000000000000 : ℝ)^1577
        have hw : |(-2251935007/10000000000 : ℝ)|=(2251935007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234015599/10000000000 : ℝ)|^2089 ≤ (21208990564039/50000000000000 : ℝ)^1577
        have hw : |(5234015599/10000000000 : ℝ)|=(5234015599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s3_2 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (669161863/1250000000 : ℝ)*x 0 + (5234015621/10000000000 : ℝ)*x 1 + (-2251934871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669161863/1250000000 : ℝ)^2089 ≤ (2185160782821/5000000000000 : ℝ)^1577 := by
    have hnat : (669161863 : ℕ)^2089*5000000000000^1577 ≤ 2185160782821^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669161863 1250000000 2185160782821 5000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5234015621/10000000000 : ℝ)^2089 ≤ (21208990682129/50000000000000 : ℝ)^1577 := by
    have hnat : (5234015621 : ℕ)^2089*50000000000000^1577 ≤ 21208990682129^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234015621 10000000000 21208990682129 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251934871/10000000000 : ℝ)^2089 ≤ (3469700743161/25000000000000 : ℝ)^1577 := by
    have hnat : (2251934871 : ℕ)^2089*25000000000000^1577 ≤ 3469700743161^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251934871 10000000000 3469700743161 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669161863/1250000000 : ℝ), (5234015621/10000000000 : ℝ), (-2251934871/10000000000 : ℝ)] ![(2185160782821/5000000000000 : ℝ), (21208990682129/50000000000000 : ℝ), (3469700743161/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669161863/1250000000 : ℝ)|^2089 ≤ (2185160782821/5000000000000 : ℝ)^1577
        have hw : |(669161863/1250000000 : ℝ)|=(669161863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5234015621/10000000000 : ℝ)|^2089 ≤ (21208990682129/50000000000000 : ℝ)^1577
        have hw : |(5234015621/10000000000 : ℝ)|=(5234015621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2251934871/10000000000 : ℝ)|^2089 ≤ (3469700743161/25000000000000 : ℝ)^1577
        have hw : |(-2251934871/10000000000 : ℝ)|=(2251934871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s3_3 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (544949487/1250000000 : ℝ)*x 0 + (2085499649/5000000000 : ℝ)*x 1 + (4556625593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544949487/1250000000 : ℝ)^2089 ≤ (1331822307787/4000000000000 : ℝ)^1577 := by
    have hnat : (544949487 : ℕ)^2089*4000000000000^1577 ≤ 1331822307787^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544949487 1250000000 1331822307787 4000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085499649/5000000000 : ℝ)^2089 ≤ (31401079670977/100000000000000 : ℝ)^1577 := by
    have hnat : (2085499649 : ℕ)^2089*100000000000000^1577 ≤ 31401079670977^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085499649 5000000000 31401079670977 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4556625593/10000000000 : ℝ)^2089 ≤ (17651681306853/50000000000000 : ℝ)^1577 := by
    have hnat : (4556625593 : ℕ)^2089*50000000000000^1577 ≤ 17651681306853^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4556625593 10000000000 17651681306853 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544949487/1250000000 : ℝ), (2085499649/5000000000 : ℝ), (4556625593/10000000000 : ℝ)] ![(1331822307787/4000000000000 : ℝ), (31401079670977/100000000000000 : ℝ), (17651681306853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544949487/1250000000 : ℝ)|^2089 ≤ (1331822307787/4000000000000 : ℝ)^1577
        have hw : |(544949487/1250000000 : ℝ)|=(544949487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085499649/5000000000 : ℝ)|^2089 ≤ (31401079670977/100000000000000 : ℝ)^1577
        have hw : |(2085499649/5000000000 : ℝ)|=(2085499649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4556625593/10000000000 : ℝ)|^2089 ≤ (17651681306853/50000000000000 : ℝ)^1577
        have hw : |(4556625593/10000000000 : ℝ)|=(4556625593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s3_4 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-538330549/2500000000 : ℝ)*x 0 + (163586059/312500000 : ℝ)*x 1 + (5426311507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538330549/2500000000 : ℝ)^2089 ≤ (13079509650819/100000000000000 : ℝ)^1577 := by
    have hnat : (538330549 : ℕ)^2089*100000000000000^1577 ≤ 13079509650819^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538330549 2500000000 13079509650819 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163586059/312500000 : ℝ)^2089 ≤ (10606476800281/25000000000000 : ℝ)^1577 := by
    have hnat : (163586059 : ℕ)^2089*25000000000000^1577 ≤ 10606476800281^1577*312500000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163586059 312500000 10606476800281 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426311507/10000000000 : ℝ)^2089 ≤ (44494583137119/100000000000000 : ℝ)^1577 := by
    have hnat : (5426311507 : ℕ)^2089*100000000000000^1577 ≤ 44494583137119^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426311507 10000000000 44494583137119 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-538330549/2500000000 : ℝ), (163586059/312500000 : ℝ), (5426311507/10000000000 : ℝ)] ![(13079509650819/100000000000000 : ℝ), (10606476800281/25000000000000 : ℝ), (44494583137119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-538330549/2500000000 : ℝ)|^2089 ≤ (13079509650819/100000000000000 : ℝ)^1577
        have hw : |(-538330549/2500000000 : ℝ)|=(538330549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163586059/312500000 : ℝ)|^2089 ≤ (10606476800281/25000000000000 : ℝ)^1577
        have hw : |(163586059/312500000 : ℝ)|=(163586059/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426311507/10000000000 : ℝ)|^2089 ≤ (44494583137119/100000000000000 : ℝ)^1577
        have hw : |(5426311507/10000000000 : ℝ)|=(5426311507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s3_5 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1060862963/2000000000 : ℝ)*x 0 + (-2059639727/10000000000 : ℝ)*x 1 + (1356577821/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060862963/2000000000 : ℝ)^2089 ≤ (21587158977473/50000000000000 : ℝ)^1577 := by
    have hnat : (1060862963 : ℕ)^2089*50000000000000^1577 ≤ 21587158977473^1577*2000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060862963 2000000000 21587158977473 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2059639727/10000000000 : ℝ)^2089 ≤ (3082775326591/25000000000000 : ℝ)^1577 := by
    have hnat : (2059639727 : ℕ)^2089*25000000000000^1577 ≤ 3082775326591^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059639727 10000000000 3082775326591 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356577821/2500000000 : ℝ)^2089 ≤ (44494580714897/100000000000000 : ℝ)^1577 := by
    have hnat : (1356577821 : ℕ)^2089*100000000000000^1577 ≤ 44494580714897^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356577821 2500000000 44494580714897 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060862963/2000000000 : ℝ), (-2059639727/10000000000 : ℝ), (1356577821/2500000000 : ℝ)] ![(21587158977473/50000000000000 : ℝ), (3082775326591/25000000000000 : ℝ), (44494580714897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060862963/2000000000 : ℝ)|^2089 ≤ (21587158977473/50000000000000 : ℝ)^1577
        have hw : |(1060862963/2000000000 : ℝ)|=(1060862963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2059639727/10000000000 : ℝ)|^2089 ≤ (3082775326591/25000000000000 : ℝ)^1577
        have hw : |(-2059639727/10000000000 : ℝ)|=(2059639727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356577821/2500000000 : ℝ)|^2089 ≤ (44494580714897/100000000000000 : ℝ)^1577
        have hw : |(1356577821/2500000000 : ℝ)|=(1356577821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s3_6 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326078973/2500000000 : ℝ)*x 0 + (2713155191/5000000000 : ℝ)*x 1 + (-4119279/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326078973/2500000000 : ℝ)^2089 ≤ (43174329567257/100000000000000 : ℝ)^1577 := by
    have hnat : (1326078973 : ℕ)^2089*100000000000000^1577 ≤ 43174329567257^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326078973 2500000000 43174329567257 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713155191/5000000000 : ℝ)^2089 ≤ (11123642729347/25000000000000 : ℝ)^1577 := by
    have hnat : (2713155191 : ℕ)^2089*25000000000000^1577 ≤ 11123642729347^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713155191 5000000000 11123642729347 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4119279/20000000 : ℝ)^2089 ≤ (12331099506071/100000000000000 : ℝ)^1577 := by
    have hnat : (4119279 : ℕ)^2089*100000000000000^1577 ≤ 12331099506071^1577*20000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119279 20000000 12331099506071 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326078973/2500000000 : ℝ), (2713155191/5000000000 : ℝ), (-4119279/20000000 : ℝ)] ![(43174329567257/100000000000000 : ℝ), (11123642729347/25000000000000 : ℝ), (12331099506071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326078973/2500000000 : ℝ)|^2089 ≤ (43174329567257/100000000000000 : ℝ)^1577
        have hw : |(1326078973/2500000000 : ℝ)|=(1326078973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713155191/5000000000 : ℝ)|^2089 ≤ (11123642729347/25000000000000 : ℝ)^1577
        have hw : |(2713155191/5000000000 : ℝ)|=(2713155191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4119279/20000000 : ℝ)|^2089 ≤ (12331099506071/100000000000000 : ℝ)^1577
        have hw : |(-4119279/20000000 : ℝ)|=(4119279/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s3_7 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4359629693/10000000000 : ℝ)*x 0 + (4555151281/10000000000 : ℝ)*x 1 + (4172482099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359629693/10000000000 : ℝ)^2089 ≤ (33295899615461/100000000000000 : ℝ)^1577 := by
    have hnat : (4359629693 : ℕ)^2089*100000000000000^1577 ≤ 33295899615461^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359629693 10000000000 33295899615461 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4555151281/10000000000 : ℝ)^2089 ≤ (35288232365151/100000000000000 : ℝ)^1577 := by
    have hnat : (4555151281 : ℕ)^2089*100000000000000^1577 ≤ 35288232365151^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4555151281 10000000000 35288232365151 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172482099/10000000000 : ℝ)^2089 ≤ (7853967000313/25000000000000 : ℝ)^1577 := by
    have hnat : (4172482099 : ℕ)^2089*25000000000000^1577 ≤ 7853967000313^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172482099 10000000000 7853967000313 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359629693/10000000000 : ℝ), (4555151281/10000000000 : ℝ), (4172482099/10000000000 : ℝ)] ![(33295899615461/100000000000000 : ℝ), (35288232365151/100000000000000 : ℝ), (7853967000313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359629693/10000000000 : ℝ)|^2089 ≤ (33295899615461/100000000000000 : ℝ)^1577
        have hw : |(4359629693/10000000000 : ℝ)|=(4359629693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4555151281/10000000000 : ℝ)|^2089 ≤ (35288232365151/100000000000000 : ℝ)^1577
        have hw : |(4555151281/10000000000 : ℝ)|=(4555151281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172482099/10000000000 : ℝ)|^2089 ≤ (7853967000313/25000000000000 : ℝ)^1577
        have hw : |(4172482099/10000000000 : ℝ)|=(4172482099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1163_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16441/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1337/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14781/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16441/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2291/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16441/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2291/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16441/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2291/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16441/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2291/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16441/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2291/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16441/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2291/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2291/25000 : ℝ) ^ (8355/2048 : ℝ) ≤ (5830862977155381/100000000000000000000 : ℝ) := by
    have hpowers : (2291/25000 : ℝ)^8355 ≤ (5830862977155381/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2291 : ℕ)^8355*100000000000000000000^2048 ≤ 5830862977155381^2048*25000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2291 25000 5830862977155381 100000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2291/25000 : ℝ)) (X := (5830862977155381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16441/100000 : ℝ) ^ (8355/2048 : ℝ) ≤ (15821540829084341/25000000000000000000 : ℝ) := by
    have hpowers : (16441/100000 : ℝ)^8355 ≤ (15821540829084341/25000000000000000000 : ℝ)^2048 := by
      have hnat : (16441 : ℕ)^8355*25000000000000000000^2048 ≤ 15821540829084341^2048*100000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16441 100000 15821540829084341 25000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16441/100000 : ℝ)) (X := (15821540829084341/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005830862977155381/50000000000000000000 : ℝ) ≤ (625017865173239/625000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (50005830862977155381/50000000000000000000 : ℝ)^2048 ≤ (625017865173239/625000000000000 : ℝ)^8355 := by
      have hnat : (50005830862977155381 : ℕ)^2048*625000000000000^8355 ≤ 625017865173239^8355*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005830862977155381 50000000000000000000 625017865173239 625000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625017865173239/625000000000000 : ℝ)) (X := (50005830862977155381/50000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20013823405258698549/20000000000000000000 : ℝ) ≤ (10001693773280289/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (20013823405258698549/20000000000000000000 : ℝ)^2048 ≤ (10001693773280289/10000000000000000 : ℝ)^8355 := by
      have hnat : (20013823405258698549 : ℕ)^2048*10000000000000000^8355 ≤ 10001693773280289^8355*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20013823405258698549 20000000000000000000 10001693773280289 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001693773280289/10000000000000000 : ℝ)) (X := (20013823405258698549/20000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12515821540829084341/12500000000000000000 : ℝ) ≤ (5001550851894377/5000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (12515821540829084341/12500000000000000000 : ℝ)^2048 ≤ (5001550851894377/5000000000000000 : ℝ)^8355 := by
      have hnat : (12515821540829084341 : ℕ)^2048*5000000000000000^8355 ≤ 5001550851894377^8355*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12515821540829084341 12500000000000000000 5001550851894377 5000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001550851894377/5000000000000000 : ℝ)) (X := (12515821540829084341/12500000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5830862977155381/100000000000000000000 : ℝ) ≤ ((9093284440936427091/9096250000000000000 : ℝ)+2*(281586101693/145540000000000 : ℝ)*(2291/25000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (9093284440936427091/9096250000000000000 : ℝ)+2*(281586101693/145540000000000 : ℝ)*(2291/25000 : ℝ)=(625017865173239/625000000000000 : ℝ) by norm_num, show 1+2*(5830862977155381/100000000000000000000 : ℝ)=(50005830862977155381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15821540829084341/25000000000000000000 : ℝ)+(5830862977155381/100000000000000000000 : ℝ) ≤ ((9093284440936427091/9096250000000000000 : ℝ)+(281586101693/145540000000000 : ℝ)*((16441/100000 : ℝ)+(2291/25000 : ℝ)))^(8355/2048 : ℝ) := by
    rw [show (9093284440936427091/9096250000000000000 : ℝ)+(281586101693/145540000000000 : ℝ)*((16441/100000 : ℝ)+(2291/25000 : ℝ))=(10001693773280289/10000000000000000 : ℝ) by norm_num, show 1+(15821540829084341/25000000000000000000 : ℝ)+(5830862977155381/100000000000000000000 : ℝ)=(20013823405258698549/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15821540829084341/25000000000000000000 : ℝ) ≤ ((9093284440936427091/9096250000000000000 : ℝ)+2*(281586101693/145540000000000 : ℝ)*(16441/100000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (9093284440936427091/9096250000000000000 : ℝ)+2*(281586101693/145540000000000 : ℝ)*(16441/100000 : ℝ)=(5001550851894377/5000000000000000 : ℝ) by norm_num, show 1+2*(15821540829084341/25000000000000000000 : ℝ)=(12515821540829084341/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9093284440936427091/9096250000000000000 : ℝ)*(X 1 0+X 2 0)+(281586101693/145540000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (2291/25000 : ℝ)) (hi := (16441/100000 : ℝ)) (c := (9093284440936427091/9096250000000000000 : ℝ)) (alpha := (281586101693/145540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9093284440936427091/9096250000000000000 : ℝ)*(X 0 1+X 2 1)+(281586101693/145540000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (2291/25000 : ℝ)) (hi := (16441/100000 : ℝ)) (c := (9093284440936427091/9096250000000000000 : ℝ)) (alpha := (281586101693/145540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9093284440936427091/9096250000000000000 : ℝ)*(X 0 2+X 1 2)+(281586101693/145540000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (2291/25000 : ℝ)) (hi := (16441/100000 : ℝ)) (c := (9093284440936427091/9096250000000000000 : ℝ)) (alpha := (281586101693/145540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2153305149/10000000000 : ℝ)*X 0 0+(2713526817/5000000000 : ℝ)*X 0 1+(5234015793/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676647411/5000000000 : ℝ)*X 1 0+(-2251935007/10000000000 : ℝ)*X 1 1+(5234015599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669161863/1250000000 : ℝ)*X 2 0+(5234015621/10000000000 : ℝ)*X 2 1+(-2251934871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544949487/1250000000 : ℝ)*X 0 0+(2085499649/5000000000 : ℝ)*X 0 1+(4556625593/10000000000 : ℝ)*X 0 2+(544949487/1250000000 : ℝ)*X 1 0+(2085499649/5000000000 : ℝ)*X 1 1+(4556625593/10000000000 : ℝ)*X 1 2+(544949487/1250000000 : ℝ)*X 2 0+(2085499649/5000000000 : ℝ)*X 2 1+(4556625593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-538330549/2500000000 : ℝ)*X 0 0+(163586059/312500000 : ℝ)*X 0 1+(5426311507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060862963/2000000000 : ℝ)*X 1 0+(-2059639727/10000000000 : ℝ)*X 1 1+(1356577821/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326078973/2500000000 : ℝ)*X 2 0+(2713155191/5000000000 : ℝ)*X 2 1+(-4119279/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359629693/10000000000 : ℝ)*X 0 0+(4555151281/10000000000 : ℝ)*X 0 1+(4172482099/10000000000 : ℝ)*X 0 2+(4359629693/10000000000 : ℝ)*X 1 0+(4555151281/10000000000 : ℝ)*X 1 1+(4172482099/10000000000 : ℝ)*X 1 2+(4359629693/10000000000 : ℝ)*X 2 0+(4555151281/10000000000 : ℝ)*X 2 1+(4172482099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (930413607282560430990936147/113703125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1940047071/100000000000000 : ℝ)*(base19) + (37132799/2000000000000 : ℝ)*(base23) + (43564763/50000000000000 : ℝ)*(lower2) + (4116467/2500000000000 : ℝ)*(upper3) + (101058823/50000000000000 : ℝ)*(upper5) + (242925413713917/6250000000000 : ℝ)*(major0) + (242925413713917/6250000000000 : ℝ)*(major1) + (242925413713917/6250000000000 : ℝ)*(major2) + (1295090519583547/25000000000000 : ℝ)*(sp0) + (5180394432605229/100000000000000 : ℝ)*(sp1) + (103607890320247/2000000000000 : ℝ)*(sp2) + (129660006474361/5000000000000 : ℝ)*(sp3) + (1071697441/3125000000000 : ℝ)*(sp4) + (3292788947/20000000000000 : ℝ)*(sp7) + (648304148357989/25000000000000 : ℝ)*(f.failure) + (5180396372652299/100000000000000 : ℝ)*(f.sum) + (31648150056149/7277000000000000000000000000 : ℝ)*base65 + (263641770081870981/113703125000000000000000000000000 : ℝ)*base68 + (1183676171997035269/113703125000000000000000000000000 : ℝ)*base69 + (1142888175391722769/113703125000000000000000000000000 : ℝ)*base71 + (7326287892897/1819250000000000000000000000 : ℝ)*base74 + (943918601452181697/56851562500000000000000000000000 : ℝ)*base75 + (1224727118221816519/113703125000000000000000000000000 : ℝ)*base77 + (444016837286035269/113703125000000000000000000000000 : ℝ)*base79 + (34532419103821/7277000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (15302301/2500000000000000000000 : ℝ)*base89 + (15302301/2500000000000000000000 : ℝ)*base91 + (15302301/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (173675293259469180593471637/56851562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (49258853/20000000000000 : ℝ)*(base19) + (356472371/25000000000000 : ℝ)*(base23) + (14192857/100000000000000 : ℝ)*(upper2) + (2504841/100000000000000 : ℝ)*(upper4) + (25899177/100000000000000 : ℝ)*(upper5) + (1958399243220537/50000000000000 : ℝ)*(major0) + (1958399243220537/50000000000000 : ℝ)*(major1) + (1958399243220537/50000000000000 : ℝ)*(major2) + (39178457/20000000000000 : ℝ)*(sp0) + (2114077337/20000000000000 : ℝ)*(sp2) + (5220369977075349/100000000000000 : ℝ)*(sp4) + (5220369926673369/100000000000000 : ℝ)*(sp5) + (2610179088345733/50000000000000 : ℝ)*(sp6) + (653306674521207/25000000000000 : ℝ)*(sp7) + (653306674521207/25000000000000 : ℝ)*(f.failure) + (2610185086483817/50000000000000 : ℝ)*(f.sum) + (41407650059287/7277000000000000000000000000 : ℝ)*base65 + (1237424661393805367/454812500000000000000000000000000 : ℝ)*base67 + (4523169061890680367/454812500000000000000000000000000 : ℝ)*base69 + (2288689976674242867/454812500000000000000000000000000 : ℝ)*base71 + (34927777726903/7277000000000000000000000000 : ℝ)*base74 + (5030104053147180367/454812500000000000000000000000000 : ℝ)*base75 + (600219523390069633/454812500000000000000000000000000 : ℝ)*base78 + (1037995840755367867/454812500000000000000000000000000 : ℝ)*base79 + (13503270452067/7277000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2196063/2500000000000000000000 : ℝ)*base89 + (2196063/2500000000000000000000 : ℝ)*base91 + (2196063/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1163_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16441/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1337/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14781/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1163_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1163_s4_0 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-539036073/2500000000 : ℝ)*x 0 + (5400903413/10000000000 : ℝ)*x 1 + (5258307951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539036073/2500000000 : ℝ)^2089 ≤ (1310222154389/10000000000000 : ℝ)^1577 := by
    have hnat : (539036073 : ℕ)^2089*10000000000000^1577 ≤ 1310222154389^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539036073 2500000000 1310222154389 10000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400903413/10000000000 : ℝ)^2089 ≤ (22109405409609/50000000000000 : ℝ)^1577 := by
    have hnat : (5400903413 : ℕ)^2089*50000000000000^1577 ≤ 22109405409609^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400903413 10000000000 22109405409609 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258307951/10000000000 : ℝ)^2089 ≤ (42678967626323/100000000000000 : ℝ)^1577 := by
    have hnat : (5258307951 : ℕ)^2089*100000000000000^1577 ≤ 42678967626323^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258307951 10000000000 42678967626323 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-539036073/2500000000 : ℝ), (5400903413/10000000000 : ℝ), (5258307951/10000000000 : ℝ)] ![(1310222154389/10000000000000 : ℝ), (22109405409609/50000000000000 : ℝ), (42678967626323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-539036073/2500000000 : ℝ)|^2089 ≤ (1310222154389/10000000000000 : ℝ)^1577
        have hw : |(-539036073/2500000000 : ℝ)|=(539036073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400903413/10000000000 : ℝ)|^2089 ≤ (22109405409609/50000000000000 : ℝ)^1577
        have hw : |(5400903413/10000000000 : ℝ)|=(5400903413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258307951/10000000000 : ℝ)|^2089 ≤ (42678967626323/100000000000000 : ℝ)^1577
        have hw : |(5258307951/10000000000 : ℝ)|=(5258307951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s4_1 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (16708591/31250000 : ℝ)*x 0 + (-1114298181/5000000000 : ℝ)*x 1 + (2629154073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16708591/31250000 : ℝ)^2089 ≤ (1745297661939/4000000000000 : ℝ)^1577 := by
    have hnat : (16708591 : ℕ)^2089*4000000000000^1577 ≤ 1745297661939^1577*31250000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16708591 31250000 1745297661939 4000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114298181/5000000000 : ℝ)^2089 ≤ (6844294359529/50000000000000 : ℝ)^1577 := by
    have hnat : (1114298181 : ℕ)^2089*50000000000000^1577 ≤ 6844294359529^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114298181 5000000000 6844294359529 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629154073/5000000000 : ℝ)^2089 ≤ (10669742430723/25000000000000 : ℝ)^1577 := by
    have hnat : (2629154073 : ℕ)^2089*25000000000000^1577 ≤ 10669742430723^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629154073 5000000000 10669742430723 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16708591/31250000 : ℝ), (-1114298181/5000000000 : ℝ), (2629154073/5000000000 : ℝ)] ![(1745297661939/4000000000000 : ℝ), (6844294359529/50000000000000 : ℝ), (10669742430723/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16708591/31250000 : ℝ)|^2089 ≤ (1745297661939/4000000000000 : ℝ)^1577
        have hw : |(16708591/31250000 : ℝ)|=(16708591/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1114298181/5000000000 : ℝ)|^2089 ≤ (6844294359529/50000000000000 : ℝ)^1577
        have hw : |(-1114298181/5000000000 : ℝ)|=(1114298181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629154073/5000000000 : ℝ)|^2089 ≤ (10669742430723/25000000000000 : ℝ)^1577
        have hw : |(2629154073/5000000000 : ℝ)|=(2629154073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s4_2 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673375261/5000000000 : ℝ)*x 0 + (5258306573/10000000000 : ℝ)*x 1 + (-1114298289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673375261/5000000000 : ℝ)^2089 ≤ (21816228352061/50000000000000 : ℝ)^1577 := by
    have hnat : (2673375261 : ℕ)^2089*50000000000000^1577 ≤ 21816228352061^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673375261 5000000000 21816228352061 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258306573/10000000000 : ℝ)^2089 ≤ (21339476405283/50000000000000 : ℝ)^1577 := by
    have hnat : (5258306573 : ℕ)^2089*50000000000000^1577 ≤ 21339476405283^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258306573 10000000000 21339476405283 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1114298289/5000000000 : ℝ)^2089 ≤ (855536904783/6250000000000 : ℝ)^1577 := by
    have hnat : (1114298289 : ℕ)^2089*6250000000000^1577 ≤ 855536904783^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114298289 5000000000 855536904783 6250000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673375261/5000000000 : ℝ), (5258306573/10000000000 : ℝ), (-1114298289/5000000000 : ℝ)] ![(21816228352061/50000000000000 : ℝ), (21339476405283/50000000000000 : ℝ), (855536904783/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673375261/5000000000 : ℝ)|^2089 ≤ (21816228352061/50000000000000 : ℝ)^1577
        have hw : |(2673375261/5000000000 : ℝ)|=(2673375261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258306573/10000000000 : ℝ)|^2089 ≤ (21339476405283/50000000000000 : ℝ)^1577
        have hw : |(5258306573/10000000000 : ℝ)|=(5258306573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1114298289/5000000000 : ℝ)|^2089 ≤ (855536904783/6250000000000 : ℝ)^1577
        have hw : |(-1114298289/5000000000 : ℝ)|=(1114298289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s4_3 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2180645679/5000000000 : ℝ)*x 0 + (4221162391/10000000000 : ℝ)*x 1 + (1126506101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180645679/5000000000 : ℝ)^2089 ≤ (33312711571227/100000000000000 : ℝ)^1577 := by
    have hnat : (2180645679 : ℕ)^2089*100000000000000^1577 ≤ 33312711571227^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180645679 5000000000 33312711571227 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4221162391/10000000000 : ℝ)^2089 ≤ (31902313409317/100000000000000 : ℝ)^1577 := by
    have hnat : (4221162391 : ℕ)^2089*100000000000000^1577 ≤ 31902313409317^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221162391 10000000000 31902313409317 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126506101/2500000000 : ℝ)^2089 ≤ (34784975002581/100000000000000 : ℝ)^1577 := by
    have hnat : (1126506101 : ℕ)^2089*100000000000000^1577 ≤ 34784975002581^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126506101 2500000000 34784975002581 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180645679/5000000000 : ℝ), (4221162391/10000000000 : ℝ), (1126506101/2500000000 : ℝ)] ![(33312711571227/100000000000000 : ℝ), (31902313409317/100000000000000 : ℝ), (34784975002581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180645679/5000000000 : ℝ)|^2089 ≤ (33312711571227/100000000000000 : ℝ)^1577
        have hw : |(2180645679/5000000000 : ℝ)|=(2180645679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4221162391/10000000000 : ℝ)|^2089 ≤ (31902313409317/100000000000000 : ℝ)^1577
        have hw : |(4221162391/10000000000 : ℝ)|=(4221162391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126506101/2500000000 : ℝ)|^2089 ≤ (34784975002581/100000000000000 : ℝ)^1577
        have hw : |(1126506101/2500000000 : ℝ)|=(1126506101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s4_4 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-431230473/2000000000 : ℝ)*x 0 + (5258710463/10000000000 : ℝ)*x 1 + (270024919/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431230473/2000000000 : ℝ)^2089 ≤ (2620457305657/20000000000000 : ℝ)^1577 := by
    have hnat : (431230473 : ℕ)^2089*20000000000000^1577 ≤ 2620457305657^1577*2000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431230473 2000000000 2620457305657 20000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258710463/10000000000 : ℝ)^2089 ≤ (5335411917929/12500000000000 : ℝ)^1577 := by
    have hnat : (5258710463 : ℕ)^2089*12500000000000^1577 ≤ 5335411917929^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258710463 10000000000 5335411917929 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270024919/500000000 : ℝ)^2089 ≤ (44214418109383/100000000000000 : ℝ)^1577 := by
    have hnat : (270024919 : ℕ)^2089*100000000000000^1577 ≤ 44214418109383^1577*500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270024919 500000000 44214418109383 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431230473/2000000000 : ℝ), (5258710463/10000000000 : ℝ), (270024919/500000000 : ℝ)] ![(2620457305657/20000000000000 : ℝ), (5335411917929/12500000000000 : ℝ), (44214418109383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431230473/2000000000 : ℝ)|^2089 ≤ (2620457305657/20000000000000 : ℝ)^1577
        have hw : |(-431230473/2000000000 : ℝ)|=(431230473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258710463/10000000000 : ℝ)|^2089 ≤ (5335411917929/12500000000000 : ℝ)^1577
        have hw : |(5258710463/10000000000 : ℝ)|=(5258710463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270024919/500000000 : ℝ)|^2089 ≤ (44214418109383/100000000000000 : ℝ)^1577
        have hw : |(270024919/500000000 : ℝ)|=(270024919/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s4_5 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5310569553/10000000000 : ℝ)*x 0 + (-2086404349/10000000000 : ℝ)*x 1 + (5400498293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310569553/10000000000 : ℝ)^2089 ≤ (43241770006877/100000000000000 : ℝ)^1577 := by
    have hnat : (5310569553 : ℕ)^2089*100000000000000^1577 ≤ 43241770006877^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310569553 10000000000 43241770006877 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2086404349/10000000000 : ℝ)^2089 ≤ (6271906406307/50000000000000 : ℝ)^1577 := by
    have hnat : (2086404349 : ℕ)^2089*50000000000000^1577 ≤ 6271906406307^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086404349 10000000000 6271906406307 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400498293/10000000000 : ℝ)^2089 ≤ (44214417165853/100000000000000 : ℝ)^1577 := by
    have hnat : (5400498293 : ℕ)^2089*100000000000000^1577 ≤ 44214417165853^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400498293 10000000000 44214417165853 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310569553/10000000000 : ℝ), (-2086404349/10000000000 : ℝ), (5400498293/10000000000 : ℝ)] ![(43241770006877/100000000000000 : ℝ), (6271906406307/50000000000000 : ℝ), (44214417165853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310569553/10000000000 : ℝ)|^2089 ≤ (43241770006877/100000000000000 : ℝ)^1577
        have hw : |(5310569553/10000000000 : ℝ)|=(5310569553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2086404349/10000000000 : ℝ)|^2089 ≤ (6271906406307/50000000000000 : ℝ)^1577
        have hw : |(-2086404349/10000000000 : ℝ)|=(2086404349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400498293/10000000000 : ℝ)|^2089 ≤ (44214417165853/100000000000000 : ℝ)^1577
        have hw : |(5400498293/10000000000 : ℝ)|=(5400498293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s4_6 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062113863/2000000000 : ℝ)*x 0 + (5400498279/10000000000 : ℝ)*x 1 + (-2086404691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062113863/2000000000 : ℝ)^2089 ≤ (43241767439757/100000000000000 : ℝ)^1577 := by
    have hnat : (1062113863 : ℕ)^2089*100000000000000^1577 ≤ 43241767439757^1577*2000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062113863 2000000000 43241767439757 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400498279/10000000000 : ℝ)^2089 ≤ (2210720850701/5000000000000 : ℝ)^1577 := by
    have hnat : (5400498279 : ℕ)^2089*5000000000000^1577 ≤ 2210720850701^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400498279 10000000000 2210720850701 5000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086404691/10000000000 : ℝ)^2089 ≤ (1567976942043/12500000000000 : ℝ)^1577 := by
    have hnat : (2086404691 : ℕ)^2089*12500000000000^1577 ≤ 1567976942043^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086404691 10000000000 1567976942043 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062113863/2000000000 : ℝ), (5400498279/10000000000 : ℝ), (-2086404691/10000000000 : ℝ)] ![(43241767439757/100000000000000 : ℝ), (2210720850701/5000000000000 : ℝ), (1567976942043/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062113863/2000000000 : ℝ)|^2089 ≤ (43241767439757/100000000000000 : ℝ)^1577
        have hw : |(1062113863/2000000000 : ℝ)|=(1062113863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400498279/10000000000 : ℝ)|^2089 ≤ (2210720850701/5000000000000 : ℝ)^1577
        have hw : |(5400498279/10000000000 : ℝ)|=(5400498279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2086404691/10000000000 : ℝ)|^2089 ≤ (1567976942043/12500000000000 : ℝ)^1577
        have hw : |(-2086404691/10000000000 : ℝ)|=(2086404691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s4_7 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2180652427/5000000000 : ℝ)*x 0 + (901043543/2000000000 : ℝ)*x 1 + (4221972677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180652427/5000000000 : ℝ)^2089 ≤ (33312848126011/100000000000000 : ℝ)^1577 := by
    have hnat : (2180652427 : ℕ)^2089*100000000000000^1577 ≤ 33312848126011^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180652427 5000000000 33312848126011 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901043543/2000000000 : ℝ)^2089 ≤ (17388363028717/50000000000000 : ℝ)^1577 := by
    have hnat : (901043543 : ℕ)^2089*50000000000000^1577 ≤ 17388363028717^1577*2000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901043543 2000000000 17388363028717 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4221972677/10000000000 : ℝ)^2089 ≤ (7977606449411/25000000000000 : ℝ)^1577 := by
    have hnat : (4221972677 : ℕ)^2089*25000000000000^1577 ≤ 7977606449411^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221972677 10000000000 7977606449411 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180652427/5000000000 : ℝ), (901043543/2000000000 : ℝ), (4221972677/10000000000 : ℝ)] ![(33312848126011/100000000000000 : ℝ), (17388363028717/50000000000000 : ℝ), (7977606449411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180652427/5000000000 : ℝ)|^2089 ≤ (33312848126011/100000000000000 : ℝ)^1577
        have hw : |(2180652427/5000000000 : ℝ)|=(2180652427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901043543/2000000000 : ℝ)|^2089 ≤ (17388363028717/50000000000000 : ℝ)^1577
        have hw : |(901043543/2000000000 : ℝ)|=(901043543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4221972677/10000000000 : ℝ)|^2089 ≤ (7977606449411/25000000000000 : ℝ)^1577
        have hw : |(4221972677/10000000000 : ℝ)|=(4221972677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1163_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1337/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2243/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1337/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1337/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1337/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1337/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1337/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1337/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (1337/12500 : ℝ) ^ (8355/2048 : ℝ) ≤ (2738807245626341/25000000000000000000 : ℝ) := by
    have hpowers : (1337/12500 : ℝ)^8355 ≤ (2738807245626341/25000000000000000000 : ℝ)^2048 := by
      have hnat : (1337 : ℕ)^8355*25000000000000000000^2048 ≤ 2738807245626341^2048*12500^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1337 12500 2738807245626341 25000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1337/12500 : ℝ)) (X := (2738807245626341/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14781/100000 : ℝ) ^ (8355/2048 : ℝ) ≤ (40995116460135487/100000000000000000000 : ℝ) := by
    have hpowers : (14781/100000 : ℝ)^8355 ≤ (40995116460135487/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14781 : ℕ)^8355*100000000000000000000^2048 ≤ 40995116460135487^2048*100000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14781 100000 40995116460135487 100000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14781/100000 : ℝ)) (X := (40995116460135487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502738807245626341/12500000000000000000 : ℝ) ≤ (10000537030610269/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (12502738807245626341/12500000000000000000 : ℝ)^2048 ≤ (10000537030610269/10000000000000000 : ℝ)^8355 := by
      have hnat : (12502738807245626341 : ℕ)^2048*10000000000000000^8355 ≤ 10000537030610269^8355*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502738807245626341 12500000000000000000 10000537030610269 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537030610269/10000000000000000 : ℝ)) (X := (12502738807245626341/12500000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051950345442640851/100000000000000000000 : ℝ) ≤ (10001273171178157/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (100051950345442640851/100000000000000000000 : ℝ)^2048 ≤ (10001273171178157/10000000000000000 : ℝ)^8355 := by
      have hnat : (100051950345442640851 : ℕ)^2048*10000000000000000^8355 ≤ 10001273171178157^8355*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051950345442640851 100000000000000000000 10001273171178157 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001273171178157/10000000000000000 : ℝ)) (X := (100051950345442640851/100000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50040995116460135487/50000000000000000000 : ℝ) ≤ (2000401862349209/2000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (50040995116460135487/50000000000000000000 : ℝ)^2048 ≤ (2000401862349209/2000000000000000 : ℝ)^8355 := by
      have hnat : (50040995116460135487 : ℕ)^2048*2000000000000000^8355 ≤ 2000401862349209^8355*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040995116460135487 50000000000000000000 2000401862349209 2000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000401862349209/2000000000000000 : ℝ)) (X := (50040995116460135487/50000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2738807245626341/25000000000000000000 : ℝ) ≤ ((40836446251014688769/40850000000000000000 : ℝ)+2*(46008785493/25531250000000 : ℝ)*(1337/12500 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (40836446251014688769/40850000000000000000 : ℝ)+2*(46008785493/25531250000000 : ℝ)*(1337/12500 : ℝ)=(10000537030610269/10000000000000000 : ℝ) by norm_num, show 1+2*(2738807245626341/25000000000000000000 : ℝ)=(12502738807245626341/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40995116460135487/100000000000000000000 : ℝ)+(2738807245626341/25000000000000000000 : ℝ) ≤ ((40836446251014688769/40850000000000000000 : ℝ)+(46008785493/25531250000000 : ℝ)*((14781/100000 : ℝ)+(1337/12500 : ℝ)))^(8355/2048 : ℝ) := by
    rw [show (40836446251014688769/40850000000000000000 : ℝ)+(46008785493/25531250000000 : ℝ)*((14781/100000 : ℝ)+(1337/12500 : ℝ))=(10001273171178157/10000000000000000 : ℝ) by norm_num, show 1+(40995116460135487/100000000000000000000 : ℝ)+(2738807245626341/25000000000000000000 : ℝ)=(100051950345442640851/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40995116460135487/100000000000000000000 : ℝ) ≤ ((40836446251014688769/40850000000000000000 : ℝ)+2*(46008785493/25531250000000 : ℝ)*(14781/100000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (40836446251014688769/40850000000000000000 : ℝ)+2*(46008785493/25531250000000 : ℝ)*(14781/100000 : ℝ)=(2000401862349209/2000000000000000 : ℝ) by norm_num, show 1+2*(40995116460135487/100000000000000000000 : ℝ)=(50040995116460135487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40836446251014688769/40850000000000000000 : ℝ)*(X 1 0+X 2 0)+(46008785493/25531250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (1337/12500 : ℝ)) (hi := (14781/100000 : ℝ)) (c := (40836446251014688769/40850000000000000000 : ℝ)) (alpha := (46008785493/25531250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40836446251014688769/40850000000000000000 : ℝ)*(X 0 1+X 2 1)+(46008785493/25531250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (1337/12500 : ℝ)) (hi := (14781/100000 : ℝ)) (c := (40836446251014688769/40850000000000000000 : ℝ)) (alpha := (46008785493/25531250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40836446251014688769/40850000000000000000 : ℝ)*(X 0 2+X 1 2)+(46008785493/25531250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (1337/12500 : ℝ)) (hi := (14781/100000 : ℝ)) (c := (40836446251014688769/40850000000000000000 : ℝ)) (alpha := (46008785493/25531250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-539036073/2500000000 : ℝ)*X 0 0+(5400903413/10000000000 : ℝ)*X 0 1+(5258307951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((16708591/31250000 : ℝ)*X 1 0+(-1114298181/5000000000 : ℝ)*X 1 1+(2629154073/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673375261/5000000000 : ℝ)*X 2 0+(5258306573/10000000000 : ℝ)*X 2 1+(-1114298289/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180645679/5000000000 : ℝ)*X 0 0+(4221162391/10000000000 : ℝ)*X 0 1+(1126506101/2500000000 : ℝ)*X 0 2+(2180645679/5000000000 : ℝ)*X 1 0+(4221162391/10000000000 : ℝ)*X 1 1+(1126506101/2500000000 : ℝ)*X 1 2+(2180645679/5000000000 : ℝ)*X 2 0+(4221162391/10000000000 : ℝ)*X 2 1+(1126506101/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-431230473/2000000000 : ℝ)*X 0 0+(5258710463/10000000000 : ℝ)*X 0 1+(270024919/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310569553/10000000000 : ℝ)*X 1 0+(-2086404349/10000000000 : ℝ)*X 1 1+(5400498293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062113863/2000000000 : ℝ)*X 2 0+(5400498279/10000000000 : ℝ)*X 2 1+(-2086404691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180652427/5000000000 : ℝ)*X 0 0+(901043543/2000000000 : ℝ)*X 0 1+(4221972677/10000000000 : ℝ)*X 0 2+(2180652427/5000000000 : ℝ)*X 1 0+(901043543/2000000000 : ℝ)*X 1 1+(4221972677/10000000000 : ℝ)*X 1 2+(2180652427/5000000000 : ℝ)*X 2 0+(901043543/2000000000 : ℝ)*X 2 1+(4221972677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38165178510151550914213353/63828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4352649/1000000000000 : ℝ)*(base8) + (3600371/10000000000000 : ℝ)*(base21) + (697720211/100000000000000 : ℝ)*(base29) + (627247641/100000000000000 : ℝ)*(lower2) + (56113211/25000000000000 : ℝ)*(upper4) + (5261648638399917/100000000000000 : ℝ)*(major0) + (82213270876877/1562500000000 : ℝ)*(major1) + (82213270876877/1562500000000 : ℝ)*(major2) + (7012808063233771/100000000000000 : ℝ)*(sp0) + (7012807800778461/100000000000000 : ℝ)*(sp1) + (3506383395400053/50000000000000 : ℝ)*(sp2) + (70209462173231/2000000000000 : ℝ)*(sp3) + (8194794929/20000000000000 : ℝ)*(sp6) + (17045148483/100000000000000 : ℝ)*(sp7) + (3510490153810033/100000000000000 : ℝ)*(f.failure) + (7012808498498671/100000000000000 : ℝ)*(f.sum) + (13503354728421707/10212500000000000000000000000 : ℝ)*base65 + (327281826353861837/63828125000000000000000000000000 : ℝ)*base68 + (120860112314643087/63828125000000000000000000000000 : ℝ)*base70 + (152579788290227748089/95000000000000000000000000000000 : ℝ)*base72 + (10457815719109/4085000000000000000000000000 : ℝ)*base74 + (3456110554294839/7978515625000000000000000000000 : ℝ)*base76 + (30465122137007251911/95000000000000000000000000000000 : ℝ)*base77 + (20371146436969413/63828125000000000000000000000000 : ℝ)*base79 + (2289272319971/1021250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (46449097/10000000000000000000000 : ℝ)*base89 + (46449097/10000000000000000000000 : ℝ)*base91 + (46449097/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (769043793059112925270262661/2042500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1117473853/100000000000000 : ℝ)*(base19) + (521610877/50000000000000 : ℝ)*(base23) + (182130453/100000000000000 : ℝ)*(upper2) + (110922629/100000000000000 : ℝ)*(upper5) + (5291650489056823/100000000000000 : ℝ)*(major0) + (5291650489056823/100000000000000 : ℝ)*(major1) + (5291650489056823/100000000000000 : ℝ)*(major2) + (1128179183/20000000000000 : ℝ)*(sp0) + (18736569647/50000000000000 : ℝ)*(sp1) + (11313902837/50000000000000 : ℝ)*(sp2) + (440799304424041/6250000000000 : ℝ)*(sp4) + (220398622533357/3125000000000 : ℝ)*(sp5) + (7052770840653143/100000000000000 : ℝ)*(sp6) + (1765253226941187/50000000000000 : ℝ)*(sp7) + (1765253226941187/50000000000000 : ℝ)*(f.failure) + (7052794511680571/100000000000000 : ℝ)*(f.sum) + (15609859443753/2553125000000000000000000000 : ℝ)*base65 + (24602773175878320887/4085000000000000000000000000000000 : ℝ)*base67 + (40020716070971679113/4085000000000000000000000000000000 : ℝ)*base70 + (5371474438896679113/4085000000000000000000000000000000 : ℝ)*base72 + (23123199738637/10212500000000000000000000000 : ℝ)*base73 + (28656322505406679113/4085000000000000000000000000000000 : ℝ)*base76 + (43804956056818320887/4085000000000000000000000000000000 : ℝ)*base77 + (36427218638581679113/4085000000000000000000000000000000 : ℝ)*base80 + (64617187730701/20425000000000000000000000000 : ℝ)*base82 + (11696117/5000000000000000000000 : ℝ)*base90 + (11696117/5000000000000000000000 : ℝ)*base92 + (11696117/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1163_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1337/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1163_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1163_s5_0 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1078367803/5000000000 : ℝ)*x 0 + (5394364009/10000000000 : ℝ)*x 1 + (2632229609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078367803/5000000000 : ℝ)^2089 ≤ (655349079609/5000000000000 : ℝ)^1577 := by
    have hnat : (1078367803 : ℕ)^2089*5000000000000^1577 ≤ 655349079609^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078367803 5000000000 655349079609 5000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394364009/10000000000 : ℝ)^2089 ≤ (44147902013657/100000000000000 : ℝ)^1577 := by
    have hnat : (5394364009 : ℕ)^2089*100000000000000^1577 ≤ 44147902013657^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394364009 10000000000 44147902013657 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632229609/5000000000 : ℝ)^2089 ≤ (10686279094661/25000000000000 : ℝ)^1577 := by
    have hnat : (2632229609 : ℕ)^2089*25000000000000^1577 ≤ 10686279094661^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632229609 5000000000 10686279094661 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1078367803/5000000000 : ℝ), (5394364009/10000000000 : ℝ), (2632229609/5000000000 : ℝ)] ![(655349079609/5000000000000 : ℝ), (44147902013657/100000000000000 : ℝ), (10686279094661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1078367803/5000000000 : ℝ)|^2089 ≤ (655349079609/5000000000000 : ℝ)^1577
        have hw : |(-1078367803/5000000000 : ℝ)|=(1078367803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394364009/10000000000 : ℝ)|^2089 ≤ (44147902013657/100000000000000 : ℝ)^1577
        have hw : |(5394364009/10000000000 : ℝ)|=(5394364009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632229609/5000000000 : ℝ)|^2089 ≤ (10686279094661/25000000000000 : ℝ)^1577
        have hw : |(2632229609/5000000000 : ℝ)|=(2632229609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s5_1 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345107437/10000000000 : ℝ)*x 0 + (-222264533/1000000000 : ℝ)*x 1 + (2632229527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345107437/10000000000 : ℝ)^2089 ≤ (8722939161747/20000000000000 : ℝ)^1577 := by
    have hnat : (5345107437 : ℕ)^2089*20000000000000^1577 ≤ 8722939161747^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345107437 10000000000 8722939161747 20000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222264533/1000000000 : ℝ)^2089 ≤ (6820094776539/50000000000000 : ℝ)^1577 := by
    have hnat : (222264533 : ℕ)^2089*50000000000000^1577 ≤ 6820094776539^1577*1000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222264533 1000000000 6820094776539 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632229527/5000000000 : ℝ)^2089 ≤ (21372557307353/50000000000000 : ℝ)^1577 := by
    have hnat : (2632229527 : ℕ)^2089*50000000000000^1577 ≤ 21372557307353^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632229527 5000000000 21372557307353 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345107437/10000000000 : ℝ), (-222264533/1000000000 : ℝ), (2632229527/5000000000 : ℝ)] ![(8722939161747/20000000000000 : ℝ), (6820094776539/50000000000000 : ℝ), (21372557307353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345107437/10000000000 : ℝ)|^2089 ≤ (8722939161747/20000000000000 : ℝ)^1577
        have hw : |(5345107437/10000000000 : ℝ)|=(5345107437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222264533/1000000000 : ℝ)|^2089 ≤ (6820094776539/50000000000000 : ℝ)^1577
        have hw : |(-222264533/1000000000 : ℝ)|=(222264533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632229527/5000000000 : ℝ)|^2089 ≤ (21372557307353/50000000000000 : ℝ)^1577
        have hw : |(2632229527/5000000000 : ℝ)|=(2632229527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s5_2 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345107527/10000000000 : ℝ)*x 0 + (5264458861/10000000000 : ℝ)*x 1 + (-555661367/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345107527/10000000000 : ℝ)^2089 ≤ (2180734839077/5000000000000 : ℝ)^1577 := by
    have hnat : (5345107527 : ℕ)^2089*5000000000000^1577 ≤ 2180734839077^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345107527 10000000000 2180734839077 5000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264458861/10000000000 : ℝ)^2089 ≤ (10686278134713/25000000000000 : ℝ)^1577 := by
    have hnat : (5264458861 : ℕ)^2089*25000000000000^1577 ≤ 10686278134713^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264458861 10000000000 10686278134713 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (555661367/2500000000 : ℝ)^2089 ≤ (13640190674931/100000000000000 : ℝ)^1577 := by
    have hnat : (555661367 : ℕ)^2089*100000000000000^1577 ≤ 13640190674931^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555661367 2500000000 13640190674931 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345107527/10000000000 : ℝ), (5264458861/10000000000 : ℝ), (-555661367/2500000000 : ℝ)] ![(2180734839077/5000000000000 : ℝ), (10686278134713/25000000000000 : ℝ), (13640190674931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345107527/10000000000 : ℝ)|^2089 ≤ (2180734839077/5000000000000 : ℝ)^1577
        have hw : |(5345107527/10000000000 : ℝ)|=(5345107527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264458861/10000000000 : ℝ)|^2089 ≤ (10686278134713/25000000000000 : ℝ)^1577
        have hw : |(5264458861/10000000000 : ℝ)|=(5264458861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-555661367/2500000000 : ℝ)|^2089 ≤ (13640190674931/100000000000000 : ℝ)^1577
        have hw : |(-555661367/2500000000 : ℝ)|=(555661367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s5_3 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2180818731/5000000000 : ℝ)*x 0 + (4233794933/10000000000 : ℝ)*x 1 + (4493302583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180818731/5000000000 : ℝ)^2089 ≤ (4164526694087/12500000000000 : ℝ)^1577 := by
    have hnat : (2180818731 : ℕ)^2089*12500000000000^1577 ≤ 4164526694087^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180818731 5000000000 4164526694087 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233794933/10000000000 : ℝ)^2089 ≤ (6405768967287/20000000000000 : ℝ)^1577 := by
    have hnat : (4233794933 : ℕ)^2089*20000000000000^1577 ≤ 6405768967287^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233794933 10000000000 6405768967287 20000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493302583/10000000000 : ℝ)^2089 ≤ (1732747079393/5000000000000 : ℝ)^1577 := by
    have hnat : (4493302583 : ℕ)^2089*5000000000000^1577 ≤ 1732747079393^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493302583 10000000000 1732747079393 5000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180818731/5000000000 : ℝ), (4233794933/10000000000 : ℝ), (4493302583/10000000000 : ℝ)] ![(4164526694087/12500000000000 : ℝ), (6405768967287/20000000000000 : ℝ), (1732747079393/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180818731/5000000000 : ℝ)|^2089 ≤ (4164526694087/12500000000000 : ℝ)^1577
        have hw : |(2180818731/5000000000 : ℝ)|=(2180818731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233794933/10000000000 : ℝ)|^2089 ≤ (6405768967287/20000000000000 : ℝ)^1577
        have hw : |(4233794933/10000000000 : ℝ)|=(4233794933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493302583/10000000000 : ℝ)|^2089 ≤ (1732747079393/5000000000000 : ℝ)^1577
        have hw : |(4493302583/10000000000 : ℝ)|=(4493302583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s5_4 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-269592637/1250000000 : ℝ)*x 0 + (1316198617/2500000000 : ℝ)*x 1 + (5394027319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269592637/1250000000 : ℝ)^2089 ≤ (1638378223549/12500000000000 : ℝ)^1577 := by
    have hnat : (269592637 : ℕ)^2089*12500000000000^1577 ≤ 1638378223549^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269592637 1250000000 1638378223549 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316198617/2500000000 : ℝ)^2089 ≤ (2671795141939/6250000000000 : ℝ)^1577 := by
    have hnat : (1316198617 : ℕ)^2089*6250000000000^1577 ≤ 2671795141939^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316198617 2500000000 2671795141939 6250000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394027319/10000000000 : ℝ)^2089 ≤ (44144251933643/100000000000000 : ℝ)^1577 := by
    have hnat : (5394027319 : ℕ)^2089*100000000000000^1577 ≤ 44144251933643^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394027319 10000000000 44144251933643 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269592637/1250000000 : ℝ), (1316198617/2500000000 : ℝ), (5394027319/10000000000 : ℝ)] ![(1638378223549/12500000000000 : ℝ), (2671795141939/6250000000000 : ℝ), (44144251933643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269592637/1250000000 : ℝ)|^2089 ≤ (1638378223549/12500000000000 : ℝ)^1577
        have hw : |(-269592637/1250000000 : ℝ)|=(269592637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316198617/2500000000 : ℝ)|^2089 ≤ (2671795141939/6250000000000 : ℝ)^1577
        have hw : |(1316198617/2500000000 : ℝ)|=(1316198617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394027319/10000000000 : ℝ)|^2089 ≤ (44144251933643/100000000000000 : ℝ)^1577
        have hw : |(5394027319/10000000000 : ℝ)|=(5394027319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s5_5 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656072807/5000000000 : ℝ)*x 0 + (-1046538107/5000000000 : ℝ)*x 1 + (1078805493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656072807/5000000000 : ℝ)^2089 ≤ (43258770559997/100000000000000 : ℝ)^1577 := by
    have hnat : (2656072807 : ℕ)^2089*100000000000000^1577 ≤ 43258770559997^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656072807 5000000000 43258770559997 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046538107/5000000000 : ℝ)^2089 ≤ (62984879569/500000000000 : ℝ)^1577 := by
    have hnat : (1046538107 : ℕ)^2089*500000000000^1577 ≤ 62984879569^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046538107 5000000000 62984879569 500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078805493/2000000000 : ℝ)^2089 ≤ (5518031689553/12500000000000 : ℝ)^1577 := by
    have hnat : (1078805493 : ℕ)^2089*12500000000000^1577 ≤ 5518031689553^1577*2000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078805493 2000000000 5518031689553 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656072807/5000000000 : ℝ), (-1046538107/5000000000 : ℝ), (1078805493/2000000000 : ℝ)] ![(43258770559997/100000000000000 : ℝ), (62984879569/500000000000 : ℝ), (5518031689553/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656072807/5000000000 : ℝ)|^2089 ≤ (43258770559997/100000000000000 : ℝ)^1577
        have hw : |(2656072807/5000000000 : ℝ)|=(2656072807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1046538107/5000000000 : ℝ)|^2089 ≤ (62984879569/500000000000 : ℝ)^1577
        have hw : |(-1046538107/5000000000 : ℝ)|=(1046538107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078805493/2000000000 : ℝ)|^2089 ≤ (5518031689553/12500000000000 : ℝ)^1577
        have hw : |(1078805493/2000000000 : ℝ)|=(1078805493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s5_6 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328036309/2500000000 : ℝ)*x 0 + (5394027753/10000000000 : ℝ)*x 1 + (-1046538167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328036309/2500000000 : ℝ)^2089 ≤ (21629383241207/50000000000000 : ℝ)^1577 := by
    have hnat : (1328036309 : ℕ)^2089*50000000000000^1577 ≤ 21629383241207^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328036309 2500000000 21629383241207 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394027753/10000000000 : ℝ)^2089 ≤ (2207212831931/5000000000000 : ℝ)^1577 := by
    have hnat : (5394027753 : ℕ)^2089*5000000000000^1577 ≤ 2207212831931^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394027753 10000000000 2207212831931 5000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046538167/5000000000 : ℝ)^2089 ≤ (6298488435243/50000000000000 : ℝ)^1577 := by
    have hnat : (1046538167 : ℕ)^2089*50000000000000^1577 ≤ 6298488435243^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046538167 5000000000 6298488435243 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328036309/2500000000 : ℝ), (5394027753/10000000000 : ℝ), (-1046538167/5000000000 : ℝ)] ![(21629383241207/50000000000000 : ℝ), (2207212831931/5000000000000 : ℝ), (6298488435243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328036309/2500000000 : ℝ)|^2089 ≤ (21629383241207/50000000000000 : ℝ)^1577
        have hw : |(1328036309/2500000000 : ℝ)|=(1328036309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394027753/10000000000 : ℝ)|^2089 ≤ (2207212831931/5000000000000 : ℝ)^1577
        have hw : |(5394027753/10000000000 : ℝ)|=(5394027753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1046538167/5000000000 : ℝ)|^2089 ≤ (6298488435243/50000000000000 : ℝ)^1577
        have hw : |(-1046538167/5000000000 : ℝ)|=(1046538167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s5_7 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (436164833/1000000000 : ℝ)*x 0 + (17970531/40000000 : ℝ)*x 1 + (4234466823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436164833/1000000000 : ℝ)^2089 ≤ (16658161759879/50000000000000 : ℝ)^1577 := by
    have hnat : (436164833 : ℕ)^2089*50000000000000^1577 ≤ 16658161759879^1577*1000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436164833 1000000000 16658161759879 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17970531/40000000 : ℝ)^2089 ≤ (34648098339817/100000000000000 : ℝ)^1577 := by
    have hnat : (17970531 : ℕ)^2089*100000000000000^1577 ≤ 34648098339817^1577*40000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17970531 40000000 34648098339817 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4234466823/10000000000 : ℝ)^2089 ≤ (3203557813029/10000000000000 : ℝ)^1577 := by
    have hnat : (4234466823 : ℕ)^2089*10000000000000^1577 ≤ 3203557813029^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234466823 10000000000 3203557813029 10000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436164833/1000000000 : ℝ), (17970531/40000000 : ℝ), (4234466823/10000000000 : ℝ)] ![(16658161759879/50000000000000 : ℝ), (34648098339817/100000000000000 : ℝ), (3203557813029/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436164833/1000000000 : ℝ)|^2089 ≤ (16658161759879/50000000000000 : ℝ)^1577
        have hw : |(436164833/1000000000 : ℝ)|=(436164833/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17970531/40000000 : ℝ)|^2089 ≤ (34648098339817/100000000000000 : ℝ)^1577
        have hw : |(17970531/40000000 : ℝ)|=(17970531/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4234466823/10000000000 : ℝ)|^2089 ≤ (3203557813029/10000000000000 : ℝ)^1577
        have hw : |(4234466823/10000000000 : ℝ)|=(4234466823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1163_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5673/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14097/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2243/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2243/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2243/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2243/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2243/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2243/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (2243/20000 : ℝ) ^ (8355/2048 : ℝ) ≤ (13291401730209931/100000000000000000000 : ℝ) := by
    have hpowers : (2243/20000 : ℝ)^8355 ≤ (13291401730209931/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2243 : ℕ)^8355*100000000000000000000^2048 ≤ 13291401730209931^2048*20000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2243 20000 13291401730209931 100000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2243/20000 : ℝ)) (X := (13291401730209931/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (8355/2048 : ℝ) ≤ (17574835772405719/50000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^8355 ≤ (17574835772405719/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7117 : ℕ)^8355*50000000000000000000^2048 ≤ 17574835772405719^2048*50000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 17574835772405719 50000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (17574835772405719/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013291401730209931/50000000000000000000 : ℝ) ≤ (10000651539437543/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (50013291401730209931/50000000000000000000 : ℝ)^2048 ≤ (10000651539437543/10000000000000000 : ℝ)^8355 := by
      have hnat : (50013291401730209931 : ℕ)^2048*10000000000000000^8355 ≤ 10000651539437543^8355*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013291401730209931 50000000000000000000 10000651539437543 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000651539437543/10000000000000000 : ℝ)) (X := (50013291401730209931/50000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048441073275021369/100000000000000000000 : ℝ) ≤ (10001187183538023/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (100048441073275021369/100000000000000000000 : ℝ)^2048 ≤ (10001187183538023/10000000000000000 : ℝ)^8355 := by
      have hnat : (100048441073275021369 : ℕ)^2048*10000000000000000^8355 ≤ 10001187183538023^8355*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048441073275021369 100000000000000000000 10001187183538023 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001187183538023/10000000000000000 : ℝ)) (X := (100048441073275021369/100000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017574835772405719/25000000000000000000 : ℝ) ≤ (10001722827638503/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (25017574835772405719/25000000000000000000 : ℝ)^2048 ≤ (10001722827638503/10000000000000000 : ℝ)^8355 := by
      have hnat : (25017574835772405719 : ℕ)^2048*10000000000000000^8355 ≤ 10001722827638503^8355*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017574835772405719 25000000000000000000 10001722827638503 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001722827638503/10000000000000000 : ℝ)) (X := (25017574835772405719/25000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13291401730209931/100000000000000000000 : ℝ) ≤ ((30179952500388175917/30190000000000000000 : ℝ)+2*(836943907/471718750000 : ℝ)*(2243/20000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (30179952500388175917/30190000000000000000 : ℝ)+2*(836943907/471718750000 : ℝ)*(2243/20000 : ℝ)=(10000651539437543/10000000000000000 : ℝ) by norm_num, show 1+2*(13291401730209931/100000000000000000000 : ℝ)=(50013291401730209931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17574835772405719/50000000000000000000 : ℝ)+(13291401730209931/100000000000000000000 : ℝ) ≤ ((30179952500388175917/30190000000000000000 : ℝ)+(836943907/471718750000 : ℝ)*((7117/50000 : ℝ)+(2243/20000 : ℝ)))^(8355/2048 : ℝ) := by
    rw [show (30179952500388175917/30190000000000000000 : ℝ)+(836943907/471718750000 : ℝ)*((7117/50000 : ℝ)+(2243/20000 : ℝ))=(10001187183538023/10000000000000000 : ℝ) by norm_num, show 1+(17574835772405719/50000000000000000000 : ℝ)+(13291401730209931/100000000000000000000 : ℝ)=(100048441073275021369/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17574835772405719/50000000000000000000 : ℝ) ≤ ((30179952500388175917/30190000000000000000 : ℝ)+2*(836943907/471718750000 : ℝ)*(7117/50000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (30179952500388175917/30190000000000000000 : ℝ)+2*(836943907/471718750000 : ℝ)*(7117/50000 : ℝ)=(10001722827638503/10000000000000000 : ℝ) by norm_num, show 1+2*(17574835772405719/50000000000000000000 : ℝ)=(25017574835772405719/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30179952500388175917/30190000000000000000 : ℝ)*(X 1 0+X 2 0)+(836943907/471718750000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (2243/20000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (30179952500388175917/30190000000000000000 : ℝ)) (alpha := (836943907/471718750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30179952500388175917/30190000000000000000 : ℝ)*(X 0 1+X 2 1)+(836943907/471718750000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (2243/20000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (30179952500388175917/30190000000000000000 : ℝ)) (alpha := (836943907/471718750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30179952500388175917/30190000000000000000 : ℝ)*(X 0 2+X 1 2)+(836943907/471718750000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (2243/20000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (30179952500388175917/30190000000000000000 : ℝ)) (alpha := (836943907/471718750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1078367803/5000000000 : ℝ)*X 0 0+(5394364009/10000000000 : ℝ)*X 0 1+(2632229609/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345107437/10000000000 : ℝ)*X 1 0+(-222264533/1000000000 : ℝ)*X 1 1+(2632229527/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345107527/10000000000 : ℝ)*X 2 0+(5264458861/10000000000 : ℝ)*X 2 1+(-555661367/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180818731/5000000000 : ℝ)*X 0 0+(4233794933/10000000000 : ℝ)*X 0 1+(4493302583/10000000000 : ℝ)*X 0 2+(2180818731/5000000000 : ℝ)*X 1 0+(4233794933/10000000000 : ℝ)*X 1 1+(4493302583/10000000000 : ℝ)*X 1 2+(2180818731/5000000000 : ℝ)*X 2 0+(4233794933/10000000000 : ℝ)*X 2 1+(4493302583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-269592637/1250000000 : ℝ)*X 0 0+(1316198617/2500000000 : ℝ)*X 0 1+(5394027319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656072807/5000000000 : ℝ)*X 1 0+(-1046538107/5000000000 : ℝ)*X 1 1+(1078805493/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328036309/2500000000 : ℝ)*X 2 0+(5394027753/10000000000 : ℝ)*X 2 1+(-1046538167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436164833/1000000000 : ℝ)*X 0 0+(17970531/40000000 : ℝ)*X 0 1+(4234466823/10000000000 : ℝ)*X 0 2+(436164833/1000000000 : ℝ)*X 1 0+(17970531/40000000 : ℝ)*X 1 1+(4234466823/10000000000 : ℝ)*X 1 2+(436164833/1000000000 : ℝ)*X 2 0+(17970531/40000000 : ℝ)*X 2 1+(4234466823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9564676445461418914592304927/1509500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62828043/50000000000000 : ℝ)*(base8) + (67725681/100000000000000 : ℝ)*(base21) + (29876159/20000000000000 : ℝ)*(lower2) + (10331649/12500000000000 : ℝ)*(lower4) + (5775699006118941/100000000000000 : ℝ)*(major0) + (5775699006118941/100000000000000 : ℝ)*(major1) + (5775699006118941/100000000000000 : ℝ)*(major2) + (7697941620600653/100000000000000 : ℝ)*(sp0) + (1924484277039429/25000000000000 : ℝ)*(sp1) + (3848963350788887/50000000000000 : ℝ)*(sp2) + (240840791783699/6250000000000 : ℝ)*(sp3) + (289881189/6250000000000 : ℝ)*(sp5) + (2995390657/20000000000000 : ℝ)*(sp6) + (211639453/6250000000000 : ℝ)*(sp7) + (3853456054770433/100000000000000 : ℝ)*(f.failure) + (384897087312837/5000000000000 : ℝ)*(f.sum) + (9240209249067/1509500000000000000000000000 : ℝ)*base66 + (13057657014270743897/3019000000000000000000000000000000 : ℝ)*base67 + (111146349169831743897/3019000000000000000000000000000000 : ℝ)*base69 + (1841417111657743897/3019000000000000000000000000000000 : ℝ)*base71 + (808171226309/377375000000000000000000000 : ℝ)*base73 + (51614128235901743897/3019000000000000000000000000000000 : ℝ)*base75 + (12435720501587743897/3019000000000000000000000000000000 : ℝ)*base77 + (30615025441572743897/3019000000000000000000000000000000 : ℝ)*base79 + (1555054704921/301900000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (64532697/10000000000000000000000 : ℝ)*base89 + (64532697/10000000000000000000000 : ℝ)*base91 + (64532697/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (294873118460776489403988603/150950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (247080889/25000000000000 : ℝ)*(base19) + (477696611/50000000000000 : ℝ)*(base23) + (13251787/50000000000000 : ℝ)*(upper3) + (131059091/50000000000000 : ℝ)*(lower4) + (1161144306417853/20000000000000 : ℝ)*(major0) + (1161144306417853/20000000000000 : ℝ)*(major1) + (1161144306417853/20000000000000 : ℝ)*(major2) + (41807235243/100000000000000 : ℝ)*(sp1) + (45715186461/100000000000000 : ℝ)*(sp2) + (3381836343/50000000000000 : ℝ)*(sp3) + (7737956384466983/100000000000000 : ℝ)*(sp4) + (967239198613523/12500000000000 : ℝ)*(sp5) + (7737909713887301/100000000000000 : ℝ)*(sp6) + (242092490682743/6250000000000 : ℝ)*(sp7) + (3873486614596573/100000000000000 : ℝ)*(f.failure) + (7737956384466983/100000000000000 : ℝ)*(f.sum) + (2186729040491/754750000000000000000000000 : ℝ)*base65 + (720818364905846201/603800000000000000000000000000000 : ℝ)*base67 + (2560316729870753799/603800000000000000000000000000000 : ℝ)*base70 + (5334869990510753799/603800000000000000000000000000000 : ℝ)*base72 + (264991659717/188687500000000000000000000 : ℝ)*base73 + (7404607212269753799/603800000000000000000000000000000 : ℝ)*base76 + (1407472704811553799/603800000000000000000000000000000 : ℝ)*base78 + (2153206556108153799/603800000000000000000000000000000 : ℝ)*base80 + (86804804077/18868750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (59728043/10000000000000000000000 : ℝ)*base90 + (59728043/10000000000000000000000 : ℝ)*base92 + (59728043/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1163_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1163_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1163_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16441/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1163_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1163_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1163_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16441/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1163_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

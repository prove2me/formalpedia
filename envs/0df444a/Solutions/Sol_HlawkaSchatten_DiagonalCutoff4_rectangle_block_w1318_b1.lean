-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1318_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:42:52.404175+00:00
-- url     : https://prove2.me/submissions/ce75744b-f57d-46f7-833c-4a95671e1825

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
theorem support_rectangle_w1318_s3_0 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1031431279/5000000000 : ℝ)*x 0 + (5430359507/10000000000 : ℝ)*x 1 + (5228755327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031431279/5000000000 : ℝ)^2139 ≤ (12552817513231/100000000000000 : ℝ)^1627 := by
    have hnat : (1031431279 : ℕ)^2139*100000000000000^1627 ≤ 12552817513231^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031431279 5000000000 12552817513231 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430359507/10000000000 : ℝ)^2139 ≤ (44810716841991/100000000000000 : ℝ)^1627 := by
    have hnat : (5430359507 : ℕ)^2139*100000000000000^1627 ≤ 44810716841991^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430359507 10000000000 44810716841991 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228755327/10000000000 : ℝ)^2139 ≤ (21318232812773/50000000000000 : ℝ)^1627 := by
    have hnat : (5228755327 : ℕ)^2139*50000000000000^1627 ≤ 21318232812773^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228755327 10000000000 21318232812773 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1031431279/5000000000 : ℝ), (5430359507/10000000000 : ℝ), (5228755327/10000000000 : ℝ)] ![(12552817513231/100000000000000 : ℝ), (44810716841991/100000000000000 : ℝ), (21318232812773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1031431279/5000000000 : ℝ)|^2139 ≤ (12552817513231/100000000000000 : ℝ)^1627
        have hw : |(-1031431279/5000000000 : ℝ)|=(1031431279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430359507/10000000000 : ℝ)|^2139 ≤ (44810716841991/100000000000000 : ℝ)^1627
        have hw : |(5430359507/10000000000 : ℝ)|=(5430359507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228755327/10000000000 : ℝ)|^2139 ≤ (21318232812773/50000000000000 : ℝ)^1627
        have hw : |(5228755327/10000000000 : ℝ)|=(5228755327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s3_1 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5353567971/10000000000 : ℝ)*x 0 + (-1082981551/5000000000 : ℝ)*x 1 + (1307188841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353567971/10000000000 : ℝ)^2139 ≤ (43979490399617/100000000000000 : ℝ)^1627 := by
    have hnat : (5353567971 : ℕ)^2139*100000000000000^1627 ≤ 43979490399617^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353567971 10000000000 43979490399617 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082981551/5000000000 : ℝ)^2139 ≤ (13384043559527/100000000000000 : ℝ)^1627 := by
    have hnat : (1082981551 : ℕ)^2139*100000000000000^1627 ≤ 13384043559527^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082981551 5000000000 13384043559527 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307188841/2500000000 : ℝ)^2139 ≤ (10659116505549/25000000000000 : ℝ)^1627 := by
    have hnat : (1307188841 : ℕ)^2139*25000000000000^1627 ≤ 10659116505549^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307188841 2500000000 10659116505549 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353567971/10000000000 : ℝ), (-1082981551/5000000000 : ℝ), (1307188841/2500000000 : ℝ)] ![(43979490399617/100000000000000 : ℝ), (13384043559527/100000000000000 : ℝ), (10659116505549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353567971/10000000000 : ℝ)|^2139 ≤ (43979490399617/100000000000000 : ℝ)^1627
        have hw : |(5353567971/10000000000 : ℝ)|=(5353567971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1082981551/5000000000 : ℝ)|^2139 ≤ (13384043559527/100000000000000 : ℝ)^1627
        have hw : |(-1082981551/5000000000 : ℝ)|=(1082981551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307188841/2500000000 : ℝ)|^2139 ≤ (10659116505549/25000000000000 : ℝ)^1627
        have hw : |(1307188841/2500000000 : ℝ)|=(1307188841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s3_2 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2676783917/5000000000 : ℝ)*x 0 + (522875563/1000000000 : ℝ)*x 1 + (-1082981467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676783917/5000000000 : ℝ)^2139 ≤ (10994872229999/25000000000000 : ℝ)^1627 := by
    have hnat : (2676783917 : ℕ)^2139*25000000000000^1627 ≤ 10994872229999^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676783917 5000000000 10994872229999 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522875563/1000000000 : ℝ)^2139 ≤ (4263646887379/10000000000000 : ℝ)^1627 := by
    have hnat : (522875563 : ℕ)^2139*10000000000000^1627 ≤ 4263646887379^1627*1000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522875563 1000000000 4263646887379 10000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082981467/5000000000 : ℝ)^2139 ≤ (13384042194727/100000000000000 : ℝ)^1627 := by
    have hnat : (1082981467 : ℕ)^2139*100000000000000^1627 ≤ 13384042194727^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082981467 5000000000 13384042194727 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676783917/5000000000 : ℝ), (522875563/1000000000 : ℝ), (-1082981467/5000000000 : ℝ)] ![(10994872229999/25000000000000 : ℝ), (4263646887379/10000000000000 : ℝ), (13384042194727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676783917/5000000000 : ℝ)|^2139 ≤ (10994872229999/25000000000000 : ℝ)^1627
        have hw : |(2676783917/5000000000 : ℝ)|=(2676783917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522875563/1000000000 : ℝ)|^2139 ≤ (4263646887379/10000000000000 : ℝ)^1627
        have hw : |(522875563/1000000000 : ℝ)|=(522875563/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1082981467/5000000000 : ℝ)|^2139 ≤ (13384042194727/100000000000000 : ℝ)^1627
        have hw : |(-1082981467/5000000000 : ℝ)|=(1082981467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s3_3 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4331712039/10000000000 : ℝ)*x 0 + (2063625477/5000000000 : ℝ)*x 1 + (4545715259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331712039/10000000000 : ℝ)^2139 ≤ (416131061691/1250000000000 : ℝ)^1627 := by
    have hnat : (4331712039 : ℕ)^2139*1250000000000^1627 ≤ 416131061691^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331712039 10000000000 416131061691 1250000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063625477/5000000000 : ℝ)^2139 ≤ (7810041747351/25000000000000 : ℝ)^1627 := by
    have hnat : (2063625477 : ℕ)^2139*25000000000000^1627 ≤ 7810041747351^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063625477 5000000000 7810041747351 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4545715259/10000000000 : ℝ)^2139 ≤ (17734674031421/50000000000000 : ℝ)^1627 := by
    have hnat : (4545715259 : ℕ)^2139*50000000000000^1627 ≤ 17734674031421^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4545715259 10000000000 17734674031421 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331712039/10000000000 : ℝ), (2063625477/5000000000 : ℝ), (4545715259/10000000000 : ℝ)] ![(416131061691/1250000000000 : ℝ), (7810041747351/25000000000000 : ℝ), (17734674031421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331712039/10000000000 : ℝ)|^2139 ≤ (416131061691/1250000000000 : ℝ)^1627
        have hw : |(4331712039/10000000000 : ℝ)|=(4331712039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2063625477/5000000000 : ℝ)|^2139 ≤ (7810041747351/25000000000000 : ℝ)^1627
        have hw : |(2063625477/5000000000 : ℝ)|=(2063625477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4545715259/10000000000 : ℝ)|^2139 ≤ (17734674031421/50000000000000 : ℝ)^1627
        have hw : |(4545715259/10000000000 : ℝ)|=(4545715259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s3_4 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2062883287/10000000000 : ℝ)*x 0 + (2614804101/5000000000 : ℝ)*x 1 + (5429501397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2062883287/10000000000 : ℝ)^2139 ≤ (3138245836771/25000000000000 : ℝ)^1627 := by
    have hnat : (2062883287 : ℕ)^2139*25000000000000^1627 ≤ 3138245836771^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062883287 10000000000 3138245836771 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614804101/5000000000 : ℝ)^2139 ≤ (42645608918561/100000000000000 : ℝ)^1627 := by
    have hnat : (2614804101 : ℕ)^2139*100000000000000^1627 ≤ 42645608918561^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614804101 5000000000 42645608918561 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429501397/10000000000 : ℝ)^2139 ≤ (44801407720351/100000000000000 : ℝ)^1627 := by
    have hnat : (5429501397 : ℕ)^2139*100000000000000^1627 ≤ 44801407720351^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429501397 10000000000 44801407720351 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2062883287/10000000000 : ℝ), (2614804101/5000000000 : ℝ), (5429501397/10000000000 : ℝ)] ![(3138245836771/25000000000000 : ℝ), (42645608918561/100000000000000 : ℝ), (44801407720351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2062883287/10000000000 : ℝ)|^2139 ≤ (3138245836771/25000000000000 : ℝ)^1627
        have hw : |(-2062883287/10000000000 : ℝ)|=(2062883287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614804101/5000000000 : ℝ)|^2139 ≤ (42645608918561/100000000000000 : ℝ)^1627
        have hw : |(2614804101/5000000000 : ℝ)|=(2614804101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429501397/10000000000 : ℝ)|^2139 ≤ (44801407720351/100000000000000 : ℝ)^1627
        have hw : |(5429501397/10000000000 : ℝ)|=(5429501397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s3_5 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5301783679/10000000000 : ℝ)*x 0 + (-245652123/1250000000 : ℝ)*x 1 + (5429501357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301783679/10000000000 : ℝ)^2139 ≤ (43421064967069/100000000000000 : ℝ)^1627 := by
    have hnat : (5301783679 : ℕ)^2139*100000000000000^1627 ≤ 43421064967069^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301783679 10000000000 43421064967069 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245652123/1250000000 : ℝ)^2139 ≤ (2355505545697/20000000000000 : ℝ)^1627 := by
    have hnat : (245652123 : ℕ)^2139*20000000000000^1627 ≤ 2355505545697^1627*1250000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245652123 1250000000 2355505545697 20000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429501357/10000000000 : ℝ)^2139 ≤ (1792056291457/4000000000000 : ℝ)^1627 := by
    have hnat : (5429501357 : ℕ)^2139*4000000000000^1627 ≤ 1792056291457^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429501357 10000000000 1792056291457 4000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301783679/10000000000 : ℝ), (-245652123/1250000000 : ℝ), (5429501357/10000000000 : ℝ)] ![(43421064967069/100000000000000 : ℝ), (2355505545697/20000000000000 : ℝ), (1792056291457/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301783679/10000000000 : ℝ)|^2139 ≤ (43421064967069/100000000000000 : ℝ)^1627
        have hw : |(5301783679/10000000000 : ℝ)|=(5301783679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-245652123/1250000000 : ℝ)|^2139 ≤ (2355505545697/20000000000000 : ℝ)^1627
        have hw : |(-245652123/1250000000 : ℝ)|=(245652123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429501357/10000000000 : ℝ)|^2139 ≤ (1792056291457/4000000000000 : ℝ)^1627
        have hw : |(5429501357/10000000000 : ℝ)|=(5429501357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s3_6 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5301783823/10000000000 : ℝ)*x 0 + (542950123/1000000000 : ℝ)*x 1 + (-1965216963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301783823/10000000000 : ℝ)^2139 ≤ (21710533258771/50000000000000 : ℝ)^1627 := by
    have hnat : (5301783823 : ℕ)^2139*50000000000000^1627 ≤ 21710533258771^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301783823 10000000000 21710533258771 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542950123/1000000000 : ℝ)^2139 ≤ (44801405908713/100000000000000 : ℝ)^1627 := by
    have hnat : (542950123 : ℕ)^2139*100000000000000^1627 ≤ 44801405908713^1627*1000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542950123 1000000000 44801405908713 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1965216963/10000000000 : ℝ)^2139 ≤ (11777527563027/100000000000000 : ℝ)^1627 := by
    have hnat : (1965216963 : ℕ)^2139*100000000000000^1627 ≤ 11777527563027^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965216963 10000000000 11777527563027 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301783823/10000000000 : ℝ), (542950123/1000000000 : ℝ), (-1965216963/10000000000 : ℝ)] ![(21710533258771/50000000000000 : ℝ), (44801405908713/100000000000000 : ℝ), (11777527563027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301783823/10000000000 : ℝ)|^2139 ≤ (21710533258771/50000000000000 : ℝ)^1627
        have hw : |(5301783823/10000000000 : ℝ)|=(5301783823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542950123/1000000000 : ℝ)|^2139 ≤ (44801405908713/100000000000000 : ℝ)^1627
        have hw : |(542950123/1000000000 : ℝ)|=(542950123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1965216963/10000000000 : ℝ)|^2139 ≤ (11777527563027/100000000000000 : ℝ)^1627
        have hw : |(-1965216963/10000000000 : ℝ)|=(1965216963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s3_7 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4331755209/10000000000 : ℝ)*x 0 + (4543944957/10000000000 : ℝ)*x 1 + (2064515909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331755209/10000000000 : ℝ)^2139 ≤ (33290921116039/100000000000000 : ℝ)^1627 := by
    have hnat : (4331755209 : ℕ)^2139*100000000000000^1627 ≤ 33290921116039^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331755209 10000000000 33290921116039 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4543944957/10000000000 : ℝ)^2139 ≤ (35451188936343/100000000000000 : ℝ)^1627 := by
    have hnat : (4543944957 : ℕ)^2139*100000000000000^1627 ≤ 35451188936343^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543944957 10000000000 35451188936343 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064515909/5000000000 : ℝ)^2139 ≤ (7814472484093/25000000000000 : ℝ)^1627 := by
    have hnat : (2064515909 : ℕ)^2139*25000000000000^1627 ≤ 7814472484093^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064515909 5000000000 7814472484093 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331755209/10000000000 : ℝ), (4543944957/10000000000 : ℝ), (2064515909/5000000000 : ℝ)] ![(33290921116039/100000000000000 : ℝ), (35451188936343/100000000000000 : ℝ), (7814472484093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331755209/10000000000 : ℝ)|^2139 ≤ (33290921116039/100000000000000 : ℝ)^1627
        have hw : |(4331755209/10000000000 : ℝ)|=(4331755209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4543944957/10000000000 : ℝ)|^2139 ≤ (35451188936343/100000000000000 : ℝ)^1627
        have hw : |(4543944957/10000000000 : ℝ)|=(4543944957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2064515909/5000000000 : ℝ)|^2139 ≤ (7814472484093/25000000000000 : ℝ)^1627
        have hw : |(2064515909/5000000000 : ℝ)|=(2064515909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1318_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16203/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (969/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10769/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3007/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16203/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (969/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16203/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (969/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16203/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (969/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16203/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (969/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16203/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (969/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16203/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (969/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (969/10000 : ℝ) ^ (4277/1024 : ℝ) ≤ (2918031130574911/50000000000000000000 : ℝ) := by
    have hpowers : (969/10000 : ℝ)^4277 ≤ (2918031130574911/50000000000000000000 : ℝ)^1024 := by
      have hnat : (969 : ℕ)^4277*50000000000000000000^1024 ≤ 2918031130574911^1024*10000^4277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        969 10000 2918031130574911 50000000000000000000 4277 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (969/10000 : ℝ)) (X := (2918031130574911/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16203/100000 : ℝ) ^ (4277/1024 : ℝ) ≤ (1249141261737031/2500000000000000000 : ℝ) := by
    have hpowers : (16203/100000 : ℝ)^4277 ≤ (1249141261737031/2500000000000000000 : ℝ)^1024 := by
      have hnat : (16203 : ℕ)^4277*2500000000000000000^1024 ≤ 1249141261737031^1024*100000^4277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16203 100000 1249141261737031 2500000000000000000 4277 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16203/100000 : ℝ)) (X := (1249141261737031/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002918031130574911/25000000000000000000 : ℝ) ≤ (2500069860445473/2500000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (25002918031130574911/25000000000000000000 : ℝ)^1024 ≤ (2500069860445473/2500000000000000 : ℝ)^4277 := by
      have hnat : (25002918031130574911 : ℕ)^1024*2500000000000000^4277 ≤ 2500069860445473^4277*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002918031130574911 25000000000000000000 2500069860445473 2500000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500069860445473/2500000000000000 : ℝ)) (X := (25002918031130574911/25000000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50027900856365315531/50000000000000000000 : ℝ) ≤ (10001335722048667/10000000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (50027900856365315531/50000000000000000000 : ℝ)^1024 ≤ (10001335722048667/10000000000000000 : ℝ)^4277 := by
      have hnat : (50027900856365315531 : ℕ)^1024*10000000000000000^4277 ≤ 10001335722048667^4277*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027900856365315531 50000000000000000000 10001335722048667 10000000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001335722048667/10000000000000000 : ℝ)) (X := (50027900856365315531/50000000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1251249141261737031/1250000000000000000 : ℝ) ≤ (5001196001157721/5000000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (1251249141261737031/1250000000000000000 : ℝ)^1024 ≤ (5001196001157721/5000000000000000 : ℝ)^4277 := by
      have hnat : (1251249141261737031 : ℕ)^1024*5000000000000000^4277 ≤ 5001196001157721^4277*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1251249141261737031 1250000000000000000 5001196001157721 5000000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001196001157721/5000000000000000 : ℝ)) (X := (1251249141261737031/1250000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2918031130574911/50000000000000000000 : ℝ) ≤ ((2712972887198140129/2713750000000000000 : ℝ)+2*(42251210671/26052000000000 : ℝ)*(969/10000 : ℝ))^(4277/1024 : ℝ) := by
    rw [show (2712972887198140129/2713750000000000000 : ℝ)+2*(42251210671/26052000000000 : ℝ)*(969/10000 : ℝ)=(2500069860445473/2500000000000000 : ℝ) by norm_num, show 1+2*(2918031130574911/50000000000000000000 : ℝ)=(25002918031130574911/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1249141261737031/2500000000000000000 : ℝ)+(2918031130574911/50000000000000000000 : ℝ) ≤ ((2712972887198140129/2713750000000000000 : ℝ)+(42251210671/26052000000000 : ℝ)*((16203/100000 : ℝ)+(969/10000 : ℝ)))^(4277/1024 : ℝ) := by
    rw [show (2712972887198140129/2713750000000000000 : ℝ)+(42251210671/26052000000000 : ℝ)*((16203/100000 : ℝ)+(969/10000 : ℝ))=(10001335722048667/10000000000000000 : ℝ) by norm_num, show 1+(1249141261737031/2500000000000000000 : ℝ)+(2918031130574911/50000000000000000000 : ℝ)=(50027900856365315531/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1249141261737031/2500000000000000000 : ℝ) ≤ ((2712972887198140129/2713750000000000000 : ℝ)+2*(42251210671/26052000000000 : ℝ)*(16203/100000 : ℝ))^(4277/1024 : ℝ) := by
    rw [show (2712972887198140129/2713750000000000000 : ℝ)+2*(42251210671/26052000000000 : ℝ)*(16203/100000 : ℝ)=(5001196001157721/5000000000000000 : ℝ) by norm_num, show 1+2*(1249141261737031/2500000000000000000 : ℝ)=(1251249141261737031/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2712972887198140129/2713750000000000000 : ℝ)*(X 1 0+X 2 0)+(42251210671/26052000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (969/10000 : ℝ)) (hi := (16203/100000 : ℝ)) (c := (2712972887198140129/2713750000000000000 : ℝ)) (alpha := (42251210671/26052000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2712972887198140129/2713750000000000000 : ℝ)*(X 0 1+X 2 1)+(42251210671/26052000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (969/10000 : ℝ)) (hi := (16203/100000 : ℝ)) (c := (2712972887198140129/2713750000000000000 : ℝ)) (alpha := (42251210671/26052000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2712972887198140129/2713750000000000000 : ℝ)*(X 0 2+X 1 2)+(42251210671/26052000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (969/10000 : ℝ)) (hi := (16203/100000 : ℝ)) (c := (2712972887198140129/2713750000000000000 : ℝ)) (alpha := (42251210671/26052000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1031431279/5000000000 : ℝ)*X 0 0+(5430359507/10000000000 : ℝ)*X 0 1+(5228755327/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353567971/10000000000 : ℝ)*X 1 0+(-1082981551/5000000000 : ℝ)*X 1 1+(1307188841/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676783917/5000000000 : ℝ)*X 2 0+(522875563/1000000000 : ℝ)*X 2 1+(-1082981467/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4331712039/10000000000 : ℝ)*X 0 0+(2063625477/5000000000 : ℝ)*X 0 1+(4545715259/10000000000 : ℝ)*X 0 2+(4331712039/10000000000 : ℝ)*X 1 0+(2063625477/5000000000 : ℝ)*X 1 1+(4545715259/10000000000 : ℝ)*X 1 2+(4331712039/10000000000 : ℝ)*X 2 0+(2063625477/5000000000 : ℝ)*X 2 1+(4545715259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2062883287/10000000000 : ℝ)*X 0 0+(2614804101/5000000000 : ℝ)*X 0 1+(5429501397/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301783679/10000000000 : ℝ)*X 1 0+(-245652123/1250000000 : ℝ)*X 1 1+(5429501357/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301783823/10000000000 : ℝ)*X 2 0+(542950123/1000000000 : ℝ)*X 2 1+(-1965216963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4331755209/10000000000 : ℝ)*X 0 0+(4543944957/10000000000 : ℝ)*X 0 1+(2064515909/5000000000 : ℝ)*X 0 2+(4331755209/10000000000 : ℝ)*X 1 0+(4543944957/10000000000 : ℝ)*X 1 1+(2064515909/5000000000 : ℝ)*X 1 2+(4331755209/10000000000 : ℝ)*X 2 0+(4543944957/10000000000 : ℝ)*X 2 1+(2064515909/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (241721541291718090982343459/33921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1126102313/100000000000000 : ℝ)*(base19) + (993795323/100000000000000 : ℝ)*(base23) + (29949841/50000000000000 : ℝ)*(upper3) + (2875901/100000000000000 : ℝ)*(upper4) + (51956289/25000000000000 : ℝ)*(upper5) + (1837492573151493/50000000000000 : ℝ)*(major0) + (1837492573151493/50000000000000 : ℝ)*(major1) + (1837492573151493/50000000000000 : ℝ)*(major2) + (310014698506527/6250000000000 : ℝ)*(sp0) + (2480129372546419/50000000000000 : ℝ)*(sp1) + (1240064719349957/25000000000000 : ℝ)*(sp2) + (1194850604931013/50000000000000 : ℝ)*(sp3) + (24695090719/100000000000000 : ℝ)*(sp4) + (8974021087/100000000000000 : ℝ)*(sp7) + (298713772985389/12500000000000 : ℝ)*(f.failure) + (310016241949697/6250000000000 : ℝ)*(f.sum) + (3421431298369/1085500000000000000000000000 : ℝ)*base66 + (991114988161437597/135687500000000000000000000000000 : ℝ)*base67 + (948759961085062597/135687500000000000000000000000000 : ℝ)*base69 + (429454651117937403/135687500000000000000000000000000 : ℝ)*base72 + (6111353724633/2171000000000000000000000000 : ℝ)*base73 + (190275068924125097/135687500000000000000000000000000 : ℝ)*base75 + (1225981580504937597/135687500000000000000000000000000 : ℝ)*base77 + (222646202559062597/135687500000000000000000000000000 : ℝ)*base79 + (3590956829349/1085500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (17889087/1250000000000000000000 : ℝ)*base90 + (17889087/1250000000000000000000 : ℝ)*base92 + (17889087/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45156540612267531757421661/4240234375000000000000000000000 : ℝ) := by norm_num
    linear_combination (13967419/625000000000 : ℝ)*(base19) + (1251192039/50000000000000 : ℝ)*(base23) + (245613597/100000000000000 : ℝ)*(upper3) + (27736089/50000000000000 : ℝ)*(lower4) + (125862221/50000000000000 : ℝ)*(upper5) + (926601886884633/25000000000000 : ℝ)*(major0) + (926601886884633/25000000000000 : ℝ)*(major1) + (926601886884633/25000000000000 : ℝ)*(major2) + (37648812743/100000000000000 : ℝ)*(sp1) + (40422758771/100000000000000 : ℝ)*(sp2) + (250133585147363/5000000000000 : ℝ)*(sp4) + (5002631819347477/100000000000000 : ℝ)*(sp5) + (5002628777804411/100000000000000 : ℝ)*(sp6) + (241014303714517/10000000000000 : ℝ)*(sp7) + (241014303714517/10000000000000 : ℝ)*(f.failure) + (250133585147363/5000000000000 : ℝ)*(f.sum) + (667736075001/217100000000000000000000000 : ℝ)*base65 + (44355051099887343/67843750000000000000000000000000 : ℝ)*base68 + (788126562005199843/67843750000000000000000000000000 : ℝ)*base70 + (151401542417887343/67843750000000000000000000000000 : ℝ)*base72 + (304431062241/542750000000000000000000000 : ℝ)*base73 + (532457900383043593/67843750000000000000000000000000 : ℝ)*base76 + (733157148455418593/67843750000000000000000000000000 : ℝ)*base78 + (841697525023012343/67843750000000000000000000000000 : ℝ)*base80 + (8692148088457/2171000000000000000000000000 : ℝ)*base81 + (11119689/1000000000000000000000 : ℝ)*base89 + (11119689/1000000000000000000000 : ℝ)*base91 + (11119689/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1318_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16203/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (969/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3007/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1318_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1318_s4_0 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2064528677/10000000000 : ℝ)*x 0 + (5416982961/10000000000 : ℝ)*x 1 + (262051939/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2064528677/10000000000 : ℝ)^2139 ≤ (12566148286701/100000000000000 : ℝ)^1627 := by
    have hnat : (2064528677 : ℕ)^2139*100000000000000^1627 ≤ 12566148286701^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064528677 10000000000 12566148286701 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416982961/10000000000 : ℝ)^2139 ≤ (44665655371911/100000000000000 : ℝ)^1627 := by
    have hnat : (5416982961 : ℕ)^2139*100000000000000^1627 ≤ 44665655371911^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416982961 10000000000 44665655371911 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262051939/500000000 : ℝ)^2139 ≤ (42768196323157/100000000000000 : ℝ)^1627 := by
    have hnat : (262051939 : ℕ)^2139*100000000000000^1627 ≤ 42768196323157^1627*500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262051939 500000000 42768196323157 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2064528677/10000000000 : ℝ), (5416982961/10000000000 : ℝ), (262051939/500000000 : ℝ)] ![(12566148286701/100000000000000 : ℝ), (44665655371911/100000000000000 : ℝ), (42768196323157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2064528677/10000000000 : ℝ)|^2139 ≤ (12566148286701/100000000000000 : ℝ)^1627
        have hw : |(-2064528677/10000000000 : ℝ)|=(2064528677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416982961/10000000000 : ℝ)|^2139 ≤ (44665655371911/100000000000000 : ℝ)^1627
        have hw : |(5416982961/10000000000 : ℝ)|=(5416982961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262051939/500000000 : ℝ)|^2139 ≤ (42768196323157/100000000000000 : ℝ)^1627
        have hw : |(262051939/500000000 : ℝ)|=(262051939/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s4_1 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350172563/10000000000 : ℝ)*x 0 + (-1077125847/5000000000 : ℝ)*x 1 + (2620519257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350172563/10000000000 : ℝ)^2139 ≤ (21971411558629/50000000000000 : ℝ)^1627 := by
    have hnat : (5350172563 : ℕ)^2139*50000000000000^1627 ≤ 21971411558629^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350172563 10000000000 21971411558629 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077125847/5000000000 : ℝ)^2139 ≤ (13288983401519/100000000000000 : ℝ)^1627 := by
    have hnat : (1077125847 : ℕ)^2139*100000000000000^1627 ≤ 13288983401519^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077125847 5000000000 13288983401519 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620519257/5000000000 : ℝ)^2139 ≤ (2673012091841/6250000000000 : ℝ)^1627 := by
    have hnat : (2620519257 : ℕ)^2139*6250000000000^1627 ≤ 2673012091841^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620519257 5000000000 2673012091841 6250000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350172563/10000000000 : ℝ), (-1077125847/5000000000 : ℝ), (2620519257/5000000000 : ℝ)] ![(21971411558629/50000000000000 : ℝ), (13288983401519/100000000000000 : ℝ), (2673012091841/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350172563/10000000000 : ℝ)|^2139 ≤ (21971411558629/50000000000000 : ℝ)^1627
        have hw : |(5350172563/10000000000 : ℝ)|=(5350172563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1077125847/5000000000 : ℝ)|^2139 ≤ (13288983401519/100000000000000 : ℝ)^1627
        have hw : |(-1077125847/5000000000 : ℝ)|=(1077125847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620519257/5000000000 : ℝ)|^2139 ≤ (2673012091841/6250000000000 : ℝ)^1627
        have hw : |(2620519257/5000000000 : ℝ)|=(2620519257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s4_2 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350172473/10000000000 : ℝ)*x 0 + (1310259549/2500000000 : ℝ)*x 1 + (-430850447/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350172473/10000000000 : ℝ)^2139 ≤ (21971411072719/50000000000000 : ℝ)^1627 := by
    have hnat : (5350172473 : ℕ)^2139*50000000000000^1627 ≤ 21971411072719^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350172473 10000000000 21971411072719 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310259549/2500000000 : ℝ)^2139 ≤ (42768190057889/100000000000000 : ℝ)^1627 := by
    have hnat : (1310259549 : ℕ)^2139*100000000000000^1627 ≤ 42768190057889^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310259549 2500000000 42768190057889 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430850447/2000000000 : ℝ)^2139 ≤ (6644493894503/50000000000000 : ℝ)^1627 := by
    have hnat : (430850447 : ℕ)^2139*50000000000000^1627 ≤ 6644493894503^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430850447 2000000000 6644493894503 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350172473/10000000000 : ℝ), (1310259549/2500000000 : ℝ), (-430850447/2000000000 : ℝ)] ![(21971411072719/50000000000000 : ℝ), (42768190057889/100000000000000 : ℝ), (6644493894503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350172473/10000000000 : ℝ)|^2139 ≤ (21971411072719/50000000000000 : ℝ)^1627
        have hw : |(5350172473/10000000000 : ℝ)|=(5350172473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310259549/2500000000 : ℝ)|^2139 ≤ (42768190057889/100000000000000 : ℝ)^1627
        have hw : |(1310259549/2500000000 : ℝ)|=(1310259549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-430850447/2000000000 : ℝ)|^2139 ≤ (6644493894503/50000000000000 : ℝ)^1627
        have hw : |(-430850447/2000000000 : ℝ)|=(430850447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s4_3 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (866544421/2000000000 : ℝ)*x 0 + (4153754999/10000000000 : ℝ)*x 1 + (4518958929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866544421/2000000000 : ℝ)^2139 ≤ (6660138158369/20000000000000 : ℝ)^1627 := by
    have hnat : (866544421 : ℕ)^2139*20000000000000^1627 ≤ 6660138158369^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866544421 2000000000 6660138158369 20000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4153754999/10000000000 : ℝ)^2139 ≤ (15752090149297/50000000000000 : ℝ)^1627 := by
    have hnat : (4153754999 : ℕ)^2139*50000000000000^1627 ≤ 15752090149297^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153754999 10000000000 15752090149297 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4518958929/10000000000 : ℝ)^2139 ≤ (17597564448147/50000000000000 : ℝ)^1627 := by
    have hnat : (4518958929 : ℕ)^2139*50000000000000^1627 ≤ 17597564448147^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518958929 10000000000 17597564448147 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866544421/2000000000 : ℝ), (4153754999/10000000000 : ℝ), (4518958929/10000000000 : ℝ)] ![(6660138158369/20000000000000 : ℝ), (15752090149297/50000000000000 : ℝ), (17597564448147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866544421/2000000000 : ℝ)|^2139 ≤ (6660138158369/20000000000000 : ℝ)^1627
        have hw : |(866544421/2000000000 : ℝ)|=(866544421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4153754999/10000000000 : ℝ)|^2139 ≤ (15752090149297/50000000000000 : ℝ)^1627
        have hw : |(4153754999/10000000000 : ℝ)|=(4153754999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4518958929/10000000000 : ℝ)|^2139 ≤ (17597564448147/50000000000000 : ℝ)^1627
        have hw : |(4518958929/10000000000 : ℝ)|=(4518958929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s4_4 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2064542437/10000000000 : ℝ)*x 0 + (2620844359/5000000000 : ℝ)*x 1 + (5416329559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2064542437/10000000000 : ℝ)^2139 ≤ (3141564598961/25000000000000 : ℝ)^1627 := by
    have hnat : (2064542437 : ℕ)^2139*25000000000000^1627 ≤ 3141564598961^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064542437 10000000000 3141564598961 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620844359/5000000000 : ℝ)^2139 ≤ (5346896140371/12500000000000 : ℝ)^1627 := by
    have hnat : (2620844359 : ℕ)^2139*12500000000000^1627 ≤ 5346896140371^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620844359 5000000000 5346896140371 12500000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416329559/10000000000 : ℝ)^2139 ≤ (348895097363/781250000000 : ℝ)^1627 := by
    have hnat : (5416329559 : ℕ)^2139*781250000000^1627 ≤ 348895097363^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416329559 10000000000 348895097363 781250000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2064542437/10000000000 : ℝ), (2620844359/5000000000 : ℝ), (5416329559/10000000000 : ℝ)] ![(3141564598961/25000000000000 : ℝ), (5346896140371/12500000000000 : ℝ), (348895097363/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2064542437/10000000000 : ℝ)|^2139 ≤ (3141564598961/25000000000000 : ℝ)^1627
        have hw : |(-2064542437/10000000000 : ℝ)|=(2064542437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620844359/5000000000 : ℝ)|^2139 ≤ (5346896140371/12500000000000 : ℝ)^1627
        have hw : |(2620844359/5000000000 : ℝ)|=(2620844359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416329559/10000000000 : ℝ)|^2139 ≤ (348895097363/781250000000 : ℝ)^1627
        have hw : |(5416329559/10000000000 : ℝ)|=(5416329559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s4_5 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652490399/5000000000 : ℝ)*x 0 + (-989480543/5000000000 : ℝ)*x 1 + (5416329553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652490399/5000000000 : ℝ)^2139 ≤ (21727746083427/50000000000000 : ℝ)^1627 := by
    have hnat : (2652490399 : ℕ)^2139*50000000000000^1627 ≤ 21727746083427^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652490399 5000000000 21727746083427 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (989480543/5000000000 : ℝ)^2139 ≤ (2377187084713/20000000000000 : ℝ)^1627 := by
    have hnat : (989480543 : ℕ)^2139*20000000000000^1627 ≤ 2377187084713^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989480543 5000000000 2377187084713 20000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416329553/10000000000 : ℝ)^2139 ≤ (1786342895897/4000000000000 : ℝ)^1627 := by
    have hnat : (5416329553 : ℕ)^2139*4000000000000^1627 ≤ 1786342895897^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416329553 10000000000 1786342895897 4000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652490399/5000000000 : ℝ), (-989480543/5000000000 : ℝ), (5416329553/10000000000 : ℝ)] ![(21727746083427/50000000000000 : ℝ), (2377187084713/20000000000000 : ℝ), (1786342895897/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652490399/5000000000 : ℝ)|^2139 ≤ (21727746083427/50000000000000 : ℝ)^1627
        have hw : |(2652490399/5000000000 : ℝ)|=(2652490399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-989480543/5000000000 : ℝ)|^2139 ≤ (2377187084713/20000000000000 : ℝ)^1627
        have hw : |(-989480543/5000000000 : ℝ)|=(989480543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416329553/10000000000 : ℝ)|^2139 ≤ (1786342895897/4000000000000 : ℝ)^1627
        have hw : |(5416329553/10000000000 : ℝ)|=(5416329553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s4_6 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1060996161/2000000000 : ℝ)*x 0 + (677041193/1250000000 : ℝ)*x 1 + (-30921267/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060996161/2000000000 : ℝ)^2139 ≤ (43455492242239/100000000000000 : ℝ)^1627 := by
    have hnat : (1060996161 : ℕ)^2139*100000000000000^1627 ≤ 43455492242239^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060996161 2000000000 43455492242239 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677041193/1250000000 : ℝ)^2139 ≤ (22329286149933/50000000000000 : ℝ)^1627 := by
    have hnat : (677041193 : ℕ)^2139*50000000000000^1627 ≤ 22329286149933^1627*1250000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677041193 1250000000 22329286149933 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30921267/156250000 : ℝ)^2139 ≤ (11885935439357/100000000000000 : ℝ)^1627 := by
    have hnat : (30921267 : ℕ)^2139*100000000000000^1627 ≤ 11885935439357^1627*156250000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30921267 156250000 11885935439357 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060996161/2000000000 : ℝ), (677041193/1250000000 : ℝ), (-30921267/156250000 : ℝ)] ![(43455492242239/100000000000000 : ℝ), (22329286149933/50000000000000 : ℝ), (11885935439357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060996161/2000000000 : ℝ)|^2139 ≤ (43455492242239/100000000000000 : ℝ)^1627
        have hw : |(1060996161/2000000000 : ℝ)|=(1060996161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677041193/1250000000 : ℝ)|^2139 ≤ (22329286149933/50000000000000 : ℝ)^1627
        have hw : |(677041193/1250000000 : ℝ)|=(677041193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30921267/156250000 : ℝ)|^2139 ≤ (11885935439357/100000000000000 : ℝ)^1627
        have hw : |(-30921267/156250000 : ℝ)|=(30921267/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s4_7 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2166375391/5000000000 : ℝ)*x 0 + (141175289/312500000 : ℝ)*x 1 + (831022351/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166375391/5000000000 : ℝ)^2139 ≤ (6660196111887/20000000000000 : ℝ)^1627 := by
    have hnat : (2166375391 : ℕ)^2139*20000000000000^1627 ≤ 6660196111887^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166375391 5000000000 6660196111887 20000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141175289/312500000 : ℝ)^2139 ≤ (703626196969/2000000000000 : ℝ)^1627 := by
    have hnat : (141175289 : ℕ)^2139*2000000000000^1627 ≤ 703626196969^1627*312500000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141175289 312500000 703626196969 2000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (831022351/2000000000 : ℝ)^2139 ≤ (7879427394047/25000000000000 : ℝ)^1627 := by
    have hnat : (831022351 : ℕ)^2139*25000000000000^1627 ≤ 7879427394047^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831022351 2000000000 7879427394047 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166375391/5000000000 : ℝ), (141175289/312500000 : ℝ), (831022351/2000000000 : ℝ)] ![(6660196111887/20000000000000 : ℝ), (703626196969/2000000000000 : ℝ), (7879427394047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166375391/5000000000 : ℝ)|^2139 ≤ (6660196111887/20000000000000 : ℝ)^1627
        have hw : |(2166375391/5000000000 : ℝ)|=(2166375391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141175289/312500000 : ℝ)|^2139 ≤ (703626196969/2000000000000 : ℝ)^1627
        have hw : |(141175289/312500000 : ℝ)|=(141175289/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(831022351/2000000000 : ℝ)|^2139 ≤ (7879427394047/25000000000000 : ℝ)^1627
        have hw : |(831022351/2000000000 : ℝ)|=(831022351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1318_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3007/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11031/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2951/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3007/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10769/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3007/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10769/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3007/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10769/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3007/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10769/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3007/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10769/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3007/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10769/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10769/100000 : ℝ) ^ (4277/1024 : ℝ) ≤ (4535247043977491/50000000000000000000 : ℝ) := by
    have hpowers : (10769/100000 : ℝ)^4277 ≤ (4535247043977491/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10769 : ℕ)^4277*50000000000000000000^1024 ≤ 4535247043977491^1024*100000^4277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10769 100000 4535247043977491 50000000000000000000 4277 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10769/100000 : ℝ)) (X := (4535247043977491/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3007/20000 : ℝ) ^ (4277/1024 : ℝ) ≤ (36556140055823097/100000000000000000000 : ℝ) := by
    have hpowers : (3007/20000 : ℝ)^4277 ≤ (36556140055823097/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3007 : ℕ)^4277*100000000000000000000^1024 ≤ 36556140055823097^1024*20000^4277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3007 20000 36556140055823097 100000000000000000000 4277 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3007/20000 : ℝ)) (X := (36556140055823097/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004535247043977491/25000000000000000000 : ℝ) ≤ (10000434301858203/10000000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (25004535247043977491/25000000000000000000 : ℝ)^1024 ≤ (10000434301858203/10000000000000000 : ℝ)^4277 := by
      have hnat : (25004535247043977491 : ℕ)^1024*10000000000000000^4277 ≤ 10000434301858203^4277*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004535247043977491 25000000000000000000 10000434301858203 10000000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000434301858203/10000000000000000 : ℝ)) (X := (25004535247043977491/25000000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045626634143778079/100000000000000000000 : ℝ) ≤ (5000546102042233/5000000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (100045626634143778079/100000000000000000000 : ℝ)^1024 ≤ (5000546102042233/5000000000000000 : ℝ)^4277 := by
      have hnat : (100045626634143778079 : ℕ)^1024*5000000000000000^4277 ≤ 5000546102042233^4277*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045626634143778079 100000000000000000000 5000546102042233 5000000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000546102042233/5000000000000000 : ℝ)) (X := (100045626634143778079/100000000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036556140055823097/50000000000000000000 : ℝ) ≤ (10001750106310729/10000000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (50036556140055823097/50000000000000000000 : ℝ)^1024 ≤ (10001750106310729/10000000000000000 : ℝ)^4277 := by
      have hnat : (50036556140055823097 : ℕ)^1024*10000000000000000^4277 ≤ 10001750106310729^4277*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036556140055823097 50000000000000000000 10001750106310729 10000000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001750106310729/10000000000000000 : ℝ)) (X := (50036556140055823097/50000000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4535247043977491/50000000000000000000 : ℝ) ≤ ((1332740088549307547/1333125000000000000 : ℝ)+2*(657902226263/426600000000000 : ℝ)*(10769/100000 : ℝ))^(4277/1024 : ℝ) := by
    rw [show (1332740088549307547/1333125000000000000 : ℝ)+2*(657902226263/426600000000000 : ℝ)*(10769/100000 : ℝ)=(10000434301858203/10000000000000000 : ℝ) by norm_num, show 1+2*(4535247043977491/50000000000000000000 : ℝ)=(25004535247043977491/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36556140055823097/100000000000000000000 : ℝ)+(4535247043977491/50000000000000000000 : ℝ) ≤ ((1332740088549307547/1333125000000000000 : ℝ)+(657902226263/426600000000000 : ℝ)*((3007/20000 : ℝ)+(10769/100000 : ℝ)))^(4277/1024 : ℝ) := by
    rw [show (1332740088549307547/1333125000000000000 : ℝ)+(657902226263/426600000000000 : ℝ)*((3007/20000 : ℝ)+(10769/100000 : ℝ))=(5000546102042233/5000000000000000 : ℝ) by norm_num, show 1+(36556140055823097/100000000000000000000 : ℝ)+(4535247043977491/50000000000000000000 : ℝ)=(100045626634143778079/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36556140055823097/100000000000000000000 : ℝ) ≤ ((1332740088549307547/1333125000000000000 : ℝ)+2*(657902226263/426600000000000 : ℝ)*(3007/20000 : ℝ))^(4277/1024 : ℝ) := by
    rw [show (1332740088549307547/1333125000000000000 : ℝ)+2*(657902226263/426600000000000 : ℝ)*(3007/20000 : ℝ)=(10001750106310729/10000000000000000 : ℝ) by norm_num, show 1+2*(36556140055823097/100000000000000000000 : ℝ)=(50036556140055823097/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1332740088549307547/1333125000000000000 : ℝ)*(X 1 0+X 2 0)+(657902226263/426600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (10769/100000 : ℝ)) (hi := (3007/20000 : ℝ)) (c := (1332740088549307547/1333125000000000000 : ℝ)) (alpha := (657902226263/426600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1332740088549307547/1333125000000000000 : ℝ)*(X 0 1+X 2 1)+(657902226263/426600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (10769/100000 : ℝ)) (hi := (3007/20000 : ℝ)) (c := (1332740088549307547/1333125000000000000 : ℝ)) (alpha := (657902226263/426600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1332740088549307547/1333125000000000000 : ℝ)*(X 0 2+X 1 2)+(657902226263/426600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (10769/100000 : ℝ)) (hi := (3007/20000 : ℝ)) (c := (1332740088549307547/1333125000000000000 : ℝ)) (alpha := (657902226263/426600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2064528677/10000000000 : ℝ)*X 0 0+(5416982961/10000000000 : ℝ)*X 0 1+(262051939/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350172563/10000000000 : ℝ)*X 1 0+(-1077125847/5000000000 : ℝ)*X 1 1+(2620519257/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350172473/10000000000 : ℝ)*X 2 0+(1310259549/2500000000 : ℝ)*X 2 1+(-430850447/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((866544421/2000000000 : ℝ)*X 0 0+(4153754999/10000000000 : ℝ)*X 0 1+(4518958929/10000000000 : ℝ)*X 0 2+(866544421/2000000000 : ℝ)*X 1 0+(4153754999/10000000000 : ℝ)*X 1 1+(4518958929/10000000000 : ℝ)*X 1 2+(866544421/2000000000 : ℝ)*X 2 0+(4153754999/10000000000 : ℝ)*X 2 1+(4518958929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2064542437/10000000000 : ℝ)*X 0 0+(2620844359/5000000000 : ℝ)*X 0 1+(5416329559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652490399/5000000000 : ℝ)*X 1 0+(-989480543/5000000000 : ℝ)*X 1 1+(5416329553/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060996161/2000000000 : ℝ)*X 2 0+(677041193/1250000000 : ℝ)*X 2 1+(-30921267/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2166375391/5000000000 : ℝ)*X 0 0+(141175289/312500000 : ℝ)*X 0 1+(831022351/2000000000 : ℝ)*X 0 2+(2166375391/5000000000 : ℝ)*X 1 0+(141175289/312500000 : ℝ)*X 1 1+(831022351/2000000000 : ℝ)*X 1 2+(2166375391/5000000000 : ℝ)*X 2 0+(141175289/312500000 : ℝ)*X 2 1+(831022351/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37462862187988199808297277/4443750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2246062179/100000000000000 : ℝ)*(base19) + (132656149/6250000000000 : ℝ)*(base23) + (318114859/100000000000000 : ℝ)*(upper3) + (12244861/50000000000000 : ℝ)*(lower4) + (842194614709517/20000000000000 : ℝ)*(major0) + (842194614709517/20000000000000 : ℝ)*(major1) + (842194614709517/20000000000000 : ℝ)*(major2) + (45469343002221/800000000000 : ℝ)*(sp0) + (2841849917361487/50000000000000 : ℝ)*(sp1) + (5683691229866901/100000000000000 : ℝ)*(sp2) + (684554500760541/25000000000000 : ℝ)*(sp3) + (4275688441/12500000000000 : ℝ)*(sp4) + (2182104967/25000000000000 : ℝ)*(sp6) + (6445563117/25000000000000 : ℝ)*(sp7) + (342280473161829/12500000000000 : ℝ)*(f.failure) + (5683702080785153/100000000000000 : ℝ)*(f.sum) + (20203091713861/4266000000000000000000000000 : ℝ)*base65 + (6115816110567531/493750000000000000000000000000 : ℝ)*base67 + (6867677518061281/493750000000000000000000000000 : ℝ)*base69 + (4148859826873781/493750000000000000000000000000 : ℝ)*base71 + (5562851260133/4266000000000000000000000000 : ℝ)*base74 + (6443100419711281/493750000000000000000000000000 : ℝ)*base75 + (5776216598567531/493750000000000000000000000000 : ℝ)*base77 + (2214197706063719/493750000000000000000000000000 : ℝ)*base80 + (16894270165489/4266000000000000000000000000 : ℝ)*base81 + (6361607/1250000000000000000000 : ℝ)*base90 + (6361607/1250000000000000000000 : ℝ)*base92 + (6361607/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2101801085079102602545853/444375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (844990949/100000000000000 : ℝ)*(base19) + (918724963/100000000000000 : ℝ)*(base23) + (97312919/100000000000000 : ℝ)*(upper3) + (7667323/25000000000000 : ℝ)*(lower4) + (102437933/100000000000000 : ℝ)*(upper5) + (42423383965463/1000000000000 : ℝ)*(major0) + (42423383965463/1000000000000 : ℝ)*(major1) + (42423383965463/1000000000000 : ℝ)*(major2) + (16348095331/100000000000000 : ℝ)*(sp1) + (8665111079/50000000000000 : ℝ)*(sp2) + (357877319549577/6250000000000 : ℝ)*(sp4) + (5726019919706953/100000000000000 : ℝ)*(sp5) + (178938089495191/3125000000000 : ℝ)*(sp6) + (2758639522639643/100000000000000 : ℝ)*(sp7) + (2758639522639643/100000000000000 : ℝ)*(f.failure) + (357877319549577/6250000000000 : ℝ)*(f.sum) + (777989011613/266625000000000000000000000 : ℝ)*base65 + (160412707114859/24687500000000000000000000000 : ℝ)*base67 + (490108929275343/49375000000000000000000000000 : ℝ)*base69 + (613309699850343/49375000000000000000000000000 : ℝ)*base71 + (1959552579823/1066500000000000000000000000 : ℝ)*base74 + (184787385657641/24687500000000000000000000000 : ℝ)*base76 + (92776050327359/24687500000000000000000000000 : ℝ)*base77 + (24682399847641/24687500000000000000000000000 : ℝ)*base80 + (6586253255983/2133000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (47906969/10000000000000000000000 : ℝ)*base90 + (47906969/10000000000000000000000 : ℝ)*base92 + (47906969/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1318_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3007/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11031/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1318_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1318_s5_0 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-129051881/625000000 : ℝ)*x 0 + (5414424889/10000000000 : ℝ)*x 1 + (262169919/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129051881/625000000 : ℝ)^2139 ≤ (3142140082491/25000000000000 : ℝ)^1627 := by
    have hnat : (129051881 : ℕ)^2139*25000000000000^1627 ≤ 3142140082491^1627*625000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129051881 625000000 3142140082491 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414424889/10000000000 : ℝ)^2139 ≤ (44637927281419/100000000000000 : ℝ)^1627 := by
    have hnat : (5414424889 : ℕ)^2139*100000000000000^1627 ≤ 44637927281419^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414424889 10000000000 44637927281419 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262169919/500000000 : ℝ)^2139 ≤ (21396756186491/50000000000000 : ℝ)^1627 := by
    have hnat : (262169919 : ℕ)^2139*50000000000000^1627 ≤ 21396756186491^1627*500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262169919 500000000 21396756186491 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129051881/625000000 : ℝ), (5414424889/10000000000 : ℝ), (262169919/500000000 : ℝ)] ![(3142140082491/25000000000000 : ℝ), (44637927281419/100000000000000 : ℝ), (21396756186491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129051881/625000000 : ℝ)|^2139 ≤ (3142140082491/25000000000000 : ℝ)^1627
        have hw : |(-129051881/625000000 : ℝ)|=(129051881/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414424889/10000000000 : ℝ)|^2139 ≤ (44637927281419/100000000000000 : ℝ)^1627
        have hw : |(5414424889/10000000000 : ℝ)|=(5414424889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262169919/500000000 : ℝ)|^2139 ≤ (21396756186491/50000000000000 : ℝ)^1627
        have hw : |(262169919/500000000 : ℝ)|=(262169919/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s5_1 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349520159/10000000000 : ℝ)*x 0 + (-2151997969/10000000000 : ℝ)*x 1 + (5243398401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349520159/10000000000 : ℝ)^2139 ≤ (43935778592843/100000000000000 : ℝ)^1627 := by
    have hnat : (5349520159 : ℕ)^2139*100000000000000^1627 ≤ 43935778592843^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349520159 10000000000 43935778592843 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2151997969/10000000000 : ℝ)^2139 ≤ (3317677199563/25000000000000 : ℝ)^1627 := by
    have hnat : (2151997969 : ℕ)^2139*25000000000000^1627 ≤ 3317677199563^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151997969 10000000000 3317677199563 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243398401/10000000000 : ℝ)^2139 ≤ (21396756299153/50000000000000 : ℝ)^1627 := by
    have hnat : (5243398401 : ℕ)^2139*50000000000000^1627 ≤ 21396756299153^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243398401 10000000000 21396756299153 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349520159/10000000000 : ℝ), (-2151997969/10000000000 : ℝ), (5243398401/10000000000 : ℝ)] ![(43935778592843/100000000000000 : ℝ), (3317677199563/25000000000000 : ℝ), (21396756299153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349520159/10000000000 : ℝ)|^2139 ≤ (43935778592843/100000000000000 : ℝ)^1627
        have hw : |(5349520159/10000000000 : ℝ)|=(5349520159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2151997969/10000000000 : ℝ)|^2139 ≤ (3317677199563/25000000000000 : ℝ)^1627
        have hw : |(-2151997969/10000000000 : ℝ)|=(2151997969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243398401/10000000000 : ℝ)|^2139 ≤ (21396756299153/50000000000000 : ℝ)^1627
        have hw : |(5243398401/10000000000 : ℝ)|=(5243398401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s5_2 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674760057/5000000000 : ℝ)*x 0 + (1310849607/2500000000 : ℝ)*x 1 + (-2151997993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674760057/5000000000 : ℝ)^2139 ≤ (43935778106951/100000000000000 : ℝ)^1627 := by
    have hnat : (2674760057 : ℕ)^2139*100000000000000^1627 ≤ 43935778106951^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674760057 5000000000 43935778106951 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310849607/2500000000 : ℝ)^2139 ≤ (42793512888009/100000000000000 : ℝ)^1627 := by
    have hnat : (1310849607 : ℕ)^2139*100000000000000^1627 ≤ 42793512888009^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310849607 2500000000 42793512888009 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2151997993/10000000000 : ℝ)^2139 ≤ (13270708992827/100000000000000 : ℝ)^1627 := by
    have hnat : (2151997993 : ℕ)^2139*100000000000000^1627 ≤ 13270708992827^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151997993 10000000000 13270708992827 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674760057/5000000000 : ℝ), (1310849607/2500000000 : ℝ), (-2151997993/10000000000 : ℝ)] ![(43935778106951/100000000000000 : ℝ), (42793512888009/100000000000000 : ℝ), (13270708992827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674760057/5000000000 : ℝ)|^2139 ≤ (43935778106951/100000000000000 : ℝ)^1627
        have hw : |(2674760057/5000000000 : ℝ)|=(2674760057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310849607/2500000000 : ℝ)|^2139 ≤ (42793512888009/100000000000000 : ℝ)^1627
        have hw : |(1310849607/2500000000 : ℝ)|=(1310849607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2151997993/10000000000 : ℝ)|^2139 ≤ (13270708992827/100000000000000 : ℝ)^1627
        have hw : |(-2151997993/10000000000 : ℝ)|=(2151997993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s5_3 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1083225037/2500000000 : ℝ)*x 0 + (4158837057/10000000000 : ℝ)*x 1 + (4513832299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083225037/2500000000 : ℝ)^2139 ≤ (33302489842331/100000000000000 : ℝ)^1627 := by
    have hnat : (1083225037 : ℕ)^2139*100000000000000^1627 ≤ 33302489842331^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083225037 2500000000 33302489842331 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4158837057/10000000000 : ℝ)^2139 ≤ (6310972926197/20000000000000 : ℝ)^1627 := by
    have hnat : (4158837057 : ℕ)^2139*20000000000000^1627 ≤ 6310972926197^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158837057 10000000000 6310972926197 20000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4513832299/10000000000 : ℝ)^2139 ≤ (3514264551319/10000000000000 : ℝ)^1627 := by
    have hnat : (4513832299 : ℕ)^2139*10000000000000^1627 ≤ 3514264551319^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513832299 10000000000 3514264551319 10000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083225037/2500000000 : ℝ), (4158837057/10000000000 : ℝ), (4513832299/10000000000 : ℝ)] ![(33302489842331/100000000000000 : ℝ), (6310972926197/20000000000000 : ℝ), (3514264551319/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083225037/2500000000 : ℝ)|^2139 ≤ (33302489842331/100000000000000 : ℝ)^1627
        have hw : |(1083225037/2500000000 : ℝ)|=(1083225037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4158837057/10000000000 : ℝ)|^2139 ≤ (6310972926197/20000000000000 : ℝ)^1627
        have hw : |(4158837057/10000000000 : ℝ)|=(4158837057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4513832299/10000000000 : ℝ)|^2139 ≤ (3514264551319/10000000000000 : ℝ)^1627
        have hw : |(4513832299/10000000000 : ℝ)|=(4513832299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s5_4 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-516210727/2500000000 : ℝ)*x 0 + (5244012567/10000000000 : ℝ)*x 1 + (5413807393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516210727/2500000000 : ℝ)^2139 ≤ (6284331428901/50000000000000 : ℝ)^1627 := by
    have hnat : (516210727 : ℕ)^2139*50000000000000^1627 ≤ 6284331428901^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516210727 2500000000 6284331428901 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244012567/10000000000 : ℝ)^2139 ≤ (21400051273887/50000000000000 : ℝ)^1627 := by
    have hnat : (5244012567 : ℕ)^2139*50000000000000^1627 ≤ 21400051273887^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244012567 10000000000 21400051273887 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413807393/10000000000 : ℝ)^2139 ≤ (44631234582721/100000000000000 : ℝ)^1627 := by
    have hnat : (5413807393 : ℕ)^2139*100000000000000^1627 ≤ 44631234582721^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413807393 10000000000 44631234582721 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-516210727/2500000000 : ℝ), (5244012567/10000000000 : ℝ), (5413807393/10000000000 : ℝ)] ![(6284331428901/50000000000000 : ℝ), (21400051273887/50000000000000 : ℝ), (44631234582721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-516210727/2500000000 : ℝ)|^2139 ≤ (6284331428901/50000000000000 : ℝ)^1627
        have hw : |(-516210727/2500000000 : ℝ)|=(516210727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244012567/10000000000 : ℝ)|^2139 ≤ (21400051273887/50000000000000 : ℝ)^1627
        have hw : |(5244012567/10000000000 : ℝ)|=(5244012567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413807393/10000000000 : ℝ)|^2139 ≤ (44631234582721/100000000000000 : ℝ)^1627
        have hw : |(5413807393/10000000000 : ℝ)|=(5413807393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s5_5 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652795823/5000000000 : ℝ)*x 0 + (-990794531/5000000000 : ℝ)*x 1 + (1082761551/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652795823/5000000000 : ℝ)^2139 ≤ (434620706401/1000000000000 : ℝ)^1627 := by
    have hnat : (2652795823 : ℕ)^2139*1000000000000^1627 ≤ 434620706401^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652795823 5000000000 434620706401 1000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (990794531/5000000000 : ℝ)^2139 ≤ (11906690839739/100000000000000 : ℝ)^1627 := by
    have hnat : (990794531 : ℕ)^2139*100000000000000^1627 ≤ 11906690839739^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990794531 5000000000 11906690839739 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082761551/2000000000 : ℝ)^2139 ≤ (44631238506169/100000000000000 : ℝ)^1627 := by
    have hnat : (1082761551 : ℕ)^2139*100000000000000^1627 ≤ 44631238506169^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082761551 2000000000 44631238506169 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652795823/5000000000 : ℝ), (-990794531/5000000000 : ℝ), (1082761551/2000000000 : ℝ)] ![(434620706401/1000000000000 : ℝ), (11906690839739/100000000000000 : ℝ), (44631238506169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652795823/5000000000 : ℝ)|^2139 ≤ (434620706401/1000000000000 : ℝ)^1627
        have hw : |(2652795823/5000000000 : ℝ)|=(2652795823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-990794531/5000000000 : ℝ)|^2139 ≤ (11906690839739/100000000000000 : ℝ)^1627
        have hw : |(-990794531/5000000000 : ℝ)|=(990794531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082761551/2000000000 : ℝ)|^2139 ≤ (44631238506169/100000000000000 : ℝ)^1627
        have hw : |(1082761551/2000000000 : ℝ)|=(1082761551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s5_6 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305593319/10000000000 : ℝ)*x 0 + (1082761269/2000000000 : ℝ)*x 1 + (-396317743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305593319/10000000000 : ℝ)^2139 ≤ (10865522164413/25000000000000 : ℝ)^1627 := by
    have hnat : (5305593319 : ℕ)^2139*25000000000000^1627 ≤ 10865522164413^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305593319 10000000000 10865522164413 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082761269/2000000000 : ℝ)^2139 ≤ (44631223224231/100000000000000 : ℝ)^1627 := by
    have hnat : (1082761269 : ℕ)^2139*100000000000000^1627 ≤ 44631223224231^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082761269 2000000000 44631223224231 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396317743/2000000000 : ℝ)^2139 ≤ (2381337619721/20000000000000 : ℝ)^1627 := by
    have hnat : (396317743 : ℕ)^2139*20000000000000^1627 ≤ 2381337619721^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396317743 2000000000 2381337619721 20000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305593319/10000000000 : ℝ), (1082761269/2000000000 : ℝ), (-396317743/2000000000 : ℝ)] ![(10865522164413/25000000000000 : ℝ), (44631223224231/100000000000000 : ℝ), (2381337619721/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305593319/10000000000 : ℝ)|^2139 ≤ (10865522164413/25000000000000 : ℝ)^1627
        have hw : |(5305593319/10000000000 : ℝ)|=(5305593319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082761269/2000000000 : ℝ)|^2139 ≤ (44631223224231/100000000000000 : ℝ)^1627
        have hw : |(1082761269/2000000000 : ℝ)|=(1082761269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-396317743/2000000000 : ℝ)|^2139 ≤ (2381337619721/20000000000000 : ℝ)^1627
        have hw : |(-396317743/2000000000 : ℝ)|=(396317743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s5_7 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (135403969/312500000 : ℝ)*x 0 + (4512556523/10000000000 : ℝ)*x 1 + (130003713/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135403969/312500000 : ℝ)^2139 ≤ (16651380626741/50000000000000 : ℝ)^1627 := by
    have hnat : (135403969 : ℕ)^2139*50000000000000^1627 ≤ 16651380626741^1627*312500000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135403969 312500000 16651380626741 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4512556523/10000000000 : ℝ)^2139 ≤ (4391198474057/12500000000000 : ℝ)^1627 := by
    have hnat : (4512556523 : ℕ)^2139*12500000000000^1627 ≤ 4391198474057^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512556523 10000000000 4391198474057 12500000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130003713/312500000 : ℝ)^2139 ≤ (15783825468323/50000000000000 : ℝ)^1627 := by
    have hnat : (130003713 : ℕ)^2139*50000000000000^1627 ≤ 15783825468323^1627*312500000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130003713 312500000 15783825468323 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135403969/312500000 : ℝ), (4512556523/10000000000 : ℝ), (130003713/312500000 : ℝ)] ![(16651380626741/50000000000000 : ℝ), (4391198474057/12500000000000 : ℝ), (15783825468323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135403969/312500000 : ℝ)|^2139 ≤ (16651380626741/50000000000000 : ℝ)^1627
        have hw : |(135403969/312500000 : ℝ)|=(135403969/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4512556523/10000000000 : ℝ)|^2139 ≤ (4391198474057/12500000000000 : ℝ)^1627
        have hw : |(4512556523/10000000000 : ℝ)|=(4512556523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130003713/312500000 : ℝ)|^2139 ≤ (15783825468323/50000000000000 : ℝ)^1627
        have hw : |(130003713/312500000 : ℝ)|=(130003713/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1318_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11031/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5541/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7351/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11031/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11031/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11031/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11031/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11031/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11031/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11031/100000 : ℝ) ^ (4277/1024 : ℝ) ≤ (2507114959817591/25000000000000000000 : ℝ) := by
    have hpowers : (11031/100000 : ℝ)^4277 ≤ (2507114959817591/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11031 : ℕ)^4277*25000000000000000000^1024 ≤ 2507114959817591^1024*100000^4277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11031 100000 2507114959817591 25000000000000000000 4277 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11031/100000 : ℝ)) (X := (2507114959817591/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2951/20000 : ℝ) ^ (4277/1024 : ℝ) ≤ (33795616147537761/100000000000000000000 : ℝ) := by
    have hpowers : (2951/20000 : ℝ)^4277 ≤ (33795616147537761/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2951 : ℕ)^4277*100000000000000000000^1024 ≤ 33795616147537761^1024*20000^4277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2951 20000 33795616147537761 100000000000000000000 4277 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2951/20000 : ℝ)) (X := (33795616147537761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502507114959817591/12500000000000000000 : ℝ) ≤ (5000240083228769/5000000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (12502507114959817591/12500000000000000000 : ℝ)^1024 ≤ (5000240083228769/5000000000000000 : ℝ)^4277 := by
      have hnat : (12502507114959817591 : ℕ)^1024*5000000000000000^4277 ≤ 5000240083228769^4277*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502507114959817591 12500000000000000000 5000240083228769 5000000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000240083228769/5000000000000000 : ℝ)) (X := (12502507114959817591/12500000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (160070118521578893/160000000000000000 : ℝ) ≤ (10001049061884239/10000000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (160070118521578893/160000000000000000 : ℝ)^1024 ≤ (10001049061884239/10000000000000000 : ℝ)^4277 := by
      have hnat : (160070118521578893 : ℕ)^1024*10000000000000000^4277 ≤ 10001049061884239^4277*160000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        160070118521578893 160000000000000000 10001049061884239 10000000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001049061884239/10000000000000000 : ℝ)) (X := (160070118521578893/160000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033795616147537761/50000000000000000000 : ℝ) ≤ (500080897865547/500000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (50033795616147537761/50000000000000000000 : ℝ)^1024 ≤ (500080897865547/500000000000000 : ℝ)^4277 := by
      have hnat : (50033795616147537761 : ℕ)^1024*500000000000000^4277 ≤ 500080897865547^4277*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033795616147537761 50000000000000000000 500080897865547 500000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500080897865547/500000000000000 : ℝ)) (X := (50033795616147537761/50000000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2507114959817591/25000000000000000000 : ℝ) ≤ ((15195607007748569/15200000000000000 : ℝ)+2*(11610110749/7600000000000 : ℝ)*(11031/100000 : ℝ))^(4277/1024 : ℝ) := by
    rw [show (15195607007748569/15200000000000000 : ℝ)+2*(11610110749/7600000000000 : ℝ)*(11031/100000 : ℝ)=(5000240083228769/5000000000000000 : ℝ) by norm_num, show 1+2*(2507114959817591/25000000000000000000 : ℝ)=(12502507114959817591/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33795616147537761/100000000000000000000 : ℝ)+(2507114959817591/25000000000000000000 : ℝ) ≤ ((15195607007748569/15200000000000000 : ℝ)+(11610110749/7600000000000 : ℝ)*((2951/20000 : ℝ)+(11031/100000 : ℝ)))^(4277/1024 : ℝ) := by
    rw [show (15195607007748569/15200000000000000 : ℝ)+(11610110749/7600000000000 : ℝ)*((2951/20000 : ℝ)+(11031/100000 : ℝ))=(10001049061884239/10000000000000000 : ℝ) by norm_num, show 1+(33795616147537761/100000000000000000000 : ℝ)+(2507114959817591/25000000000000000000 : ℝ)=(160070118521578893/160000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33795616147537761/100000000000000000000 : ℝ) ≤ ((15195607007748569/15200000000000000 : ℝ)+2*(11610110749/7600000000000 : ℝ)*(2951/20000 : ℝ))^(4277/1024 : ℝ) := by
    rw [show (15195607007748569/15200000000000000 : ℝ)+2*(11610110749/7600000000000 : ℝ)*(2951/20000 : ℝ)=(500080897865547/500000000000000 : ℝ) by norm_num, show 1+2*(33795616147537761/100000000000000000000 : ℝ)=(50033795616147537761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15195607007748569/15200000000000000 : ℝ)*(X 1 0+X 2 0)+(11610110749/7600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (11031/100000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (15195607007748569/15200000000000000 : ℝ)) (alpha := (11610110749/7600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15195607007748569/15200000000000000 : ℝ)*(X 0 1+X 2 1)+(11610110749/7600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (11031/100000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (15195607007748569/15200000000000000 : ℝ)) (alpha := (11610110749/7600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15195607007748569/15200000000000000 : ℝ)*(X 0 2+X 1 2)+(11610110749/7600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (11031/100000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (15195607007748569/15200000000000000 : ℝ)) (alpha := (11610110749/7600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-129051881/625000000 : ℝ)*X 0 0+(5414424889/10000000000 : ℝ)*X 0 1+(262169919/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349520159/10000000000 : ℝ)*X 1 0+(-2151997969/10000000000 : ℝ)*X 1 1+(5243398401/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674760057/5000000000 : ℝ)*X 2 0+(1310849607/2500000000 : ℝ)*X 2 1+(-2151997993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083225037/2500000000 : ℝ)*X 0 0+(4158837057/10000000000 : ℝ)*X 0 1+(4513832299/10000000000 : ℝ)*X 0 2+(1083225037/2500000000 : ℝ)*X 1 0+(4158837057/10000000000 : ℝ)*X 1 1+(4513832299/10000000000 : ℝ)*X 1 2+(1083225037/2500000000 : ℝ)*X 2 0+(4158837057/10000000000 : ℝ)*X 2 1+(4513832299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-516210727/2500000000 : ℝ)*X 0 0+(5244012567/10000000000 : ℝ)*X 0 1+(5413807393/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652795823/5000000000 : ℝ)*X 1 0+(-990794531/5000000000 : ℝ)*X 1 1+(1082761551/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305593319/10000000000 : ℝ)*X 2 0+(1082761269/2000000000 : ℝ)*X 2 1+(-396317743/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((135403969/312500000 : ℝ)*X 0 0+(4512556523/10000000000 : ℝ)*X 0 1+(130003713/312500000 : ℝ)*X 0 2+(135403969/312500000 : ℝ)*X 1 0+(4512556523/10000000000 : ℝ)*X 1 1+(130003713/312500000 : ℝ)*X 1 2+(135403969/312500000 : ℝ)*X 2 0+(4512556523/10000000000 : ℝ)*X 2 1+(130003713/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1483353439728338314089/380000000000000000000000000 : ℝ) := by norm_num
    linear_combination (370170979/50000000000000 : ℝ)*(base19) + (135701273/20000000000000 : ℝ)*(base23) + (948541/781250000000 : ℝ)*(upper3) + (676723/10000000000000 : ℝ)*(upper4) + (37264131/50000000000000 : ℝ)*(upper5) + (4332015193989271/100000000000000 : ℝ)*(major0) + (4332015193989271/100000000000000 : ℝ)*(major1) + (4332015193989271/100000000000000 : ℝ)*(major2) + (1169412578026407/20000000000000 : ℝ)*(sp0) + (2923538205292193/50000000000000 : ℝ)*(sp1) + (2923538236209989/50000000000000 : ℝ)*(sp2) + (2816945833666847/100000000000000 : ℝ)*(sp3) + (3565198577/25000000000000 : ℝ)*(sp4) + (363663331/5000000000000 : ℝ)*(sp7) + (704238276733367/25000000000000 : ℝ)*(f.failure) + (730884643865793/12500000000000 : ℝ)*(f.sum) + (870189923019/380000000000000000000000000 : ℝ)*base65 + (14969467303221/80000000000000000000000000000 : ℝ)*base67 + (687209430856779/80000000000000000000000000000 : ℝ)*base70 + (32241115303221/80000000000000000000000000000 : ℝ)*base71 + (873827962079/380000000000000000000000000 : ℝ)*base73 + (1008820986216779/80000000000000000000000000000 : ℝ)*base76 + (342862894136779/80000000000000000000000000000 : ℝ)*base78 + (123232920663221/80000000000000000000000000000 : ℝ)*base79 + (717378346759/380000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (20185139/2500000000000000000000 : ℝ)*base89 + (20185139/2500000000000000000000 : ℝ)*base91 + (20185139/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (108607335694159333956909/19000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (806925757/50000000000000 : ℝ)*(base19) + (3756181179/100000000000000 : ℝ)*(base23) + (9018377/6250000000000 : ℝ)*(upper3) + (81068619/100000000000000 : ℝ)*(lower4) + (410466843/100000000000000 : ℝ)*(upper5) + (218171683339287/5000000000000 : ℝ)*(major0) + (218171683339287/5000000000000 : ℝ)*(major1) + (218171683339287/5000000000000 : ℝ)*(major2) + (11869193061/25000000000000 : ℝ)*(sp1) + (31736030143/50000000000000 : ℝ)*(sp2) + (588948373735889/10000000000000 : ℝ)*(sp4) + (5889434646735131/100000000000000 : ℝ)*(sp5) + (368088531819839/6250000000000 : ℝ)*(sp6) + (1418691702836699/50000000000000 : ℝ)*(sp7) + (1418691702836699/50000000000000 : ℝ)*(f.failure) + (588948373735889/10000000000000 : ℝ)*(f.sum) + (20914844253/19000000000000000000000000 : ℝ)*base66 + (33751266943563/4000000000000000000000000000 : ℝ)*base68 + (34685205959563/4000000000000000000000000000 : ℝ)*base70 + (4445946231563/4000000000000000000000000000 : ℝ)*base72 + (135562450361/19000000000000000000000000 : ℝ)*base74 + (24658201875563/4000000000000000000000000000 : ℝ)*base76 + (1152052016437/4000000000000000000000000000 : ℝ)*base77 + (31294127175563/4000000000000000000000000000 : ℝ)*base80 + (33024264373/19000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (16230183/5000000000000000000000 : ℝ)*base89 + (16230183/5000000000000000000000 : ℝ)*base91 + (16230183/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1318_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11031/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5541/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1318_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1318_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16203/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (969/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5541/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1318_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1318_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1318_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16203/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (969/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5541/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1318_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

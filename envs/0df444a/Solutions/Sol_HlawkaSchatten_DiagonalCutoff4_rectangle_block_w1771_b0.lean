-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1771_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:34:04.979668+00:00
-- url     : https://prove2.me/submissions/a022a0aa-705f-438e-ba23-1accb730d23e

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
theorem support_rectangle_w1771_s0_0 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-270820053/2500000000 : ℝ)*x 0 + (5571327477/10000000000 : ℝ)*x 1 + (5005909003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270820053/2500000000 : ℝ)^6111 ≤ (1731317143931/25000000000000 : ℝ)^5087 := by
    have hnat : (270820053 : ℕ)^6111*25000000000000^5087 ≤ 1731317143931^5087*2500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270820053 2500000000 1731317143931 25000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5571327477/10000000000 : ℝ)^6111 ≤ (49524582655421/100000000000000 : ℝ)^5087 := by
    have hnat : (5571327477 : ℕ)^6111*100000000000000^5087 ≤ 49524582655421^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5571327477 10000000000 49524582655421 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5005909003/10000000000 : ℝ)^6111 ≤ (21775074371549/50000000000000 : ℝ)^5087 := by
    have hnat : (5005909003 : ℕ)^6111*50000000000000^5087 ≤ 21775074371549^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5005909003 10000000000 21775074371549 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-270820053/2500000000 : ℝ), (5571327477/10000000000 : ℝ), (5005909003/10000000000 : ℝ)] ![(1731317143931/25000000000000 : ℝ), (49524582655421/100000000000000 : ℝ), (21775074371549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-270820053/2500000000 : ℝ)|^6111 ≤ (1731317143931/25000000000000 : ℝ)^5087
        have hw : |(-270820053/2500000000 : ℝ)|=(270820053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5571327477/10000000000 : ℝ)|^6111 ≤ (49524582655421/100000000000000 : ℝ)^5087
        have hw : |(5571327477/10000000000 : ℝ)|=(5571327477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5005909003/10000000000 : ℝ)|^6111 ≤ (21775074371549/50000000000000 : ℝ)^5087
        have hw : |(5005909003/10000000000 : ℝ)|=(5005909003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s0_1 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348648453/10000000000 : ℝ)*x 0 + (-34595369/250000000 : ℝ)*x 1 + (5005908371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348648453/10000000000 : ℝ)^6111 ≤ (11789090208413/25000000000000 : ℝ)^5087 := by
    have hnat : (5348648453 : ℕ)^6111*25000000000000^5087 ≤ 11789090208413^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348648453 10000000000 11789090208413 25000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34595369/250000000 : ℝ)^6111 ≤ (2323374252209/25000000000000 : ℝ)^5087 := by
    have hnat : (34595369 : ℕ)^6111*25000000000000^5087 ≤ 2323374252209^5087*250000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34595369 250000000 2323374252209 25000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5005908371/10000000000 : ℝ)^6111 ≤ (1742005685523/4000000000000 : ℝ)^5087 := by
    have hnat : (5005908371 : ℕ)^6111*4000000000000^5087 ≤ 1742005685523^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5005908371 10000000000 1742005685523 4000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348648453/10000000000 : ℝ), (-34595369/250000000 : ℝ), (5005908371/10000000000 : ℝ)] ![(11789090208413/25000000000000 : ℝ), (2323374252209/25000000000000 : ℝ), (1742005685523/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348648453/10000000000 : ℝ)|^6111 ≤ (11789090208413/25000000000000 : ℝ)^5087
        have hw : |(5348648453/10000000000 : ℝ)|=(5348648453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34595369/250000000 : ℝ)|^6111 ≤ (2323374252209/25000000000000 : ℝ)^5087
        have hw : |(-34595369/250000000 : ℝ)|=(34595369/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5005908371/10000000000 : ℝ)|^6111 ≤ (1742005685523/4000000000000 : ℝ)^5087
        have hw : |(5005908371/10000000000 : ℝ)|=(5005908371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s0_2 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348645757/10000000000 : ℝ)*x 0 + (5005910149/10000000000 : ℝ)*x 1 + (-1383815997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348645757/10000000000 : ℝ)^6111 ≤ (47156332279673/100000000000000 : ℝ)^5087 := by
    have hnat : (5348645757 : ℕ)^6111*100000000000000^5087 ≤ 47156332279673^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348645757 10000000000 47156332279673 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5005910149/10000000000 : ℝ)^6111 ≤ (5443770089991/12500000000000 : ℝ)^5087 := by
    have hnat : (5005910149 : ℕ)^6111*12500000000000^5087 ≤ 5443770089991^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5005910149 10000000000 5443770089991 12500000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1383815997/10000000000 : ℝ)^6111 ≤ (2323376747157/25000000000000 : ℝ)^5087 := by
    have hnat : (1383815997 : ℕ)^6111*25000000000000^5087 ≤ 2323376747157^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383815997 10000000000 2323376747157 25000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348645757/10000000000 : ℝ), (5005910149/10000000000 : ℝ), (-1383815997/10000000000 : ℝ)] ![(47156332279673/100000000000000 : ℝ), (5443770089991/12500000000000 : ℝ), (2323376747157/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348645757/10000000000 : ℝ)|^6111 ≤ (47156332279673/100000000000000 : ℝ)^5087
        have hw : |(5348645757/10000000000 : ℝ)|=(5348645757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5005910149/10000000000 : ℝ)|^6111 ≤ (5443770089991/12500000000000 : ℝ)^5087
        have hw : |(5005910149/10000000000 : ℝ)|=(5005910149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1383815997/10000000000 : ℝ)|^6111 ≤ (2323376747157/25000000000000 : ℝ)^5087
        have hw : |(-1383815997/10000000000 : ℝ)|=(1383815997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s0_3 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1973744737/5000000000 : ℝ)*x 0 + (750573773/2500000000 : ℝ)*x 1 + (2509948271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1973744737/5000000000 : ℝ)^6111 ≤ (8184675061967/25000000000000 : ℝ)^5087 := by
    have hnat : (1973744737 : ℕ)^6111*25000000000000^5087 ≤ 8184675061967^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973744737 5000000000 8184675061967 25000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (750573773/2500000000 : ℝ)^6111 ≤ (589123158541/2500000000000 : ℝ)^5087 := by
    have hnat : (750573773 : ℕ)^6111*2500000000000^5087 ≤ 589123158541^5087*2500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750573773 2500000000 589123158541 2500000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2509948271/5000000000 : ℝ)^6111 ≤ (5462046673633/12500000000000 : ℝ)^5087 := by
    have hnat : (2509948271 : ℕ)^6111*12500000000000^5087 ≤ 5462046673633^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509948271 5000000000 5462046673633 12500000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1973744737/5000000000 : ℝ), (750573773/2500000000 : ℝ), (2509948271/5000000000 : ℝ)] ![(8184675061967/25000000000000 : ℝ), (589123158541/2500000000000 : ℝ), (5462046673633/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1973744737/5000000000 : ℝ)|^6111 ≤ (8184675061967/25000000000000 : ℝ)^5087
        have hw : |(1973744737/5000000000 : ℝ)|=(1973744737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(750573773/2500000000 : ℝ)|^6111 ≤ (589123158541/2500000000000 : ℝ)^5087
        have hw : |(750573773/2500000000 : ℝ)|=(750573773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2509948271/5000000000 : ℝ)|^6111 ≤ (5462046673633/12500000000000 : ℝ)^5087
        have hw : |(2509948271/5000000000 : ℝ)|=(2509948271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s0_4 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1084276813/10000000000 : ℝ)*x 0 + (2509924461/5000000000 : ℝ)*x 1 + (555696029/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084276813/10000000000 : ℝ)^6111 ≤ (6932922917981/100000000000000 : ℝ)^5087 := by
    have hnat : (1084276813 : ℕ)^6111*100000000000000^5087 ≤ 6932922917981^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084276813 10000000000 6932922917981 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2509924461/5000000000 : ℝ)^6111 ≤ (10923968858501/25000000000000 : ℝ)^5087 := by
    have hnat : (2509924461 : ℕ)^6111*25000000000000^5087 ≤ 10923968858501^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509924461 5000000000 10923968858501 25000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (555696029/1000000000 : ℝ)^6111 ≤ (24685600818857/50000000000000 : ℝ)^5087 := by
    have hnat : (555696029 : ℕ)^6111*50000000000000^5087 ≤ 24685600818857^5087*1000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555696029 1000000000 24685600818857 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1084276813/10000000000 : ℝ), (2509924461/5000000000 : ℝ), (555696029/1000000000 : ℝ)] ![(6932922917981/100000000000000 : ℝ), (10923968858501/25000000000000 : ℝ), (24685600818857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1084276813/10000000000 : ℝ)|^6111 ≤ (6932922917981/100000000000000 : ℝ)^5087
        have hw : |(-1084276813/10000000000 : ℝ)|=(1084276813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2509924461/5000000000 : ℝ)|^6111 ≤ (10923968858501/25000000000000 : ℝ)^5087
        have hw : |(2509924461/5000000000 : ℝ)|=(2509924461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(555696029/1000000000 : ℝ)|^6111 ≤ (24685600818857/50000000000000 : ℝ)^5087
        have hw : |(555696029/1000000000 : ℝ)|=(555696029/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s0_5 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (12998369/25000000 : ℝ)*x 0 + (-832764733/10000000000 : ℝ)*x 1 + (5556960271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12998369/25000000 : ℝ)^6111 ≤ (45579555815151/100000000000000 : ℝ)^5087 := by
    have hnat : (12998369 : ℕ)^6111*100000000000000^5087 ≤ 45579555815151^5087*25000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12998369 25000000 45579555815151 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (832764733/10000000000 : ℝ)^6111 ≤ (252462136403/5000000000000 : ℝ)^5087 := by
    have hnat : (832764733 : ℕ)^6111*5000000000000^5087 ≤ 252462136403^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832764733 10000000000 252462136403 5000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5556960271/10000000000 : ℝ)^6111 ≤ (49371201434927/100000000000000 : ℝ)^5087 := by
    have hnat : (5556960271 : ℕ)^6111*100000000000000^5087 ≤ 49371201434927^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5556960271 10000000000 49371201434927 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(12998369/25000000 : ℝ), (-832764733/10000000000 : ℝ), (5556960271/10000000000 : ℝ)] ![(45579555815151/100000000000000 : ℝ), (252462136403/5000000000000 : ℝ), (49371201434927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(12998369/25000000 : ℝ)|^6111 ≤ (45579555815151/100000000000000 : ℝ)^5087
        have hw : |(12998369/25000000 : ℝ)|=(12998369/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-832764733/10000000000 : ℝ)|^6111 ≤ (252462136403/5000000000000 : ℝ)^5087
        have hw : |(-832764733/10000000000 : ℝ)|=(832764733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5556960271/10000000000 : ℝ)|^6111 ≤ (49371201434927/100000000000000 : ℝ)^5087
        have hw : |(5556960271/10000000000 : ℝ)|=(5556960271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s0_6 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5199348007/10000000000 : ℝ)*x 0 + (1389240019/2500000000 : ℝ)*x 1 + (-52047777/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5199348007/10000000000 : ℝ)^6111 ≤ (45579560101289/100000000000000 : ℝ)^5087 := by
    have hnat : (5199348007 : ℕ)^6111*100000000000000^5087 ≤ 45579560101289^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199348007 10000000000 45579560101289 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1389240019/2500000000 : ℝ)^6111 ≤ (49371199353689/100000000000000 : ℝ)^5087 := by
    have hnat : (1389240019 : ℕ)^6111*100000000000000^5087 ≤ 49371199353689^5087*2500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389240019 2500000000 49371199353689 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52047777/625000000 : ℝ)^6111 ≤ (1009848107131/20000000000000 : ℝ)^5087 := by
    have hnat : (52047777 : ℕ)^6111*20000000000000^5087 ≤ 1009848107131^5087*625000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52047777 625000000 1009848107131 20000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5199348007/10000000000 : ℝ), (1389240019/2500000000 : ℝ), (-52047777/625000000 : ℝ)] ![(45579560101289/100000000000000 : ℝ), (49371199353689/100000000000000 : ℝ), (1009848107131/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5199348007/10000000000 : ℝ)|^6111 ≤ (45579560101289/100000000000000 : ℝ)^5087
        have hw : |(5199348007/10000000000 : ℝ)|=(5199348007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1389240019/2500000000 : ℝ)|^6111 ≤ (49371199353689/100000000000000 : ℝ)^5087
        have hw : |(1389240019/2500000000 : ℝ)|=(1389240019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52047777/625000000 : ℝ)|^6111 ≤ (1009848107131/20000000000000 : ℝ)^5087
        have hw : |(-52047777/625000000 : ℝ)|=(52047777/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s0_7 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (123470081/312500000 : ℝ)*x 0 + (2485078221/5000000000 : ℝ)*x 1 + (610712019/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (123470081/312500000 : ℝ)^6111 ≤ (16387051619767/50000000000000 : ℝ)^5087 := by
    have hnat : (123470081 : ℕ)^6111*50000000000000^5087 ≤ 16387051619767^5087*312500000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123470081 312500000 16387051619767 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2485078221/5000000000 : ℝ)^6111 ≤ (21588384179699/50000000000000 : ℝ)^5087 := by
    have hnat : (2485078221 : ℕ)^6111*50000000000000^5087 ≤ 21588384179699^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2485078221 5000000000 21588384179699 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (610712019/2000000000 : ℝ)^6111 ≤ (12024564194619/50000000000000 : ℝ)^5087 := by
    have hnat : (610712019 : ℕ)^6111*50000000000000^5087 ≤ 12024564194619^5087*2000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610712019 2000000000 12024564194619 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(123470081/312500000 : ℝ), (2485078221/5000000000 : ℝ), (610712019/2000000000 : ℝ)] ![(16387051619767/50000000000000 : ℝ), (21588384179699/50000000000000 : ℝ), (12024564194619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(123470081/312500000 : ℝ)|^6111 ≤ (16387051619767/50000000000000 : ℝ)^5087
        have hw : |(123470081/312500000 : ℝ)|=(123470081/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2485078221/5000000000 : ℝ)|^6111 ≤ (21588384179699/50000000000000 : ℝ)^5087
        have hw : |(2485078221/5000000000 : ℝ)|=(2485078221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(610712019/2000000000 : ℝ)|^6111 ≤ (12024564194619/50000000000000 : ℝ)^5087
        have hw : |(610712019/2000000000 : ℝ)|=(610712019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1771_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11420859/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (7463/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3951/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (6095/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^6095 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^6095*1^1024 ≤ 0^1024*1^6095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 6095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (6095/1024 : ℝ) ≤ (427958837524988791/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^6095 ≤ (427958837524988791/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^6095*100000000000000000000^1024 ≤ 427958837524988791^1024*5^6095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 427958837524988791 100000000000000000000 6095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (427958837524988791/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (6095/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^6095 := by
      have hnat : (1 : ℕ)^1024*1^6095 ≤ 1^6095*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 6095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100427958837524988791/100000000000000000000 : ℝ) ≤ (10007177222380513/10000000000000000 : ℝ) ^ (6095/1024 : ℝ) := by
    have hpowers : (100427958837524988791/100000000000000000000 : ℝ)^1024 ≤ (10007177222380513/10000000000000000 : ℝ)^6095 := by
      have hnat : (100427958837524988791 : ℕ)^1024*10000000000000000^6095 ≤ 10007177222380513^6095*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100427958837524988791 100000000000000000000 10007177222380513 10000000000000000 1024 6095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007177222380513/10000000000000000 : ℝ)) (X := (100427958837524988791/100000000000000000000 : ℝ)) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50427958837524988791/50000000000000000000 : ℝ) ≤ (5007177222380513/5000000000000000 : ℝ) ^ (6095/1024 : ℝ) := by
    have hpowers : (50427958837524988791/50000000000000000000 : ℝ)^1024 ≤ (5007177222380513/5000000000000000 : ℝ)^6095 := by
      have hnat : (50427958837524988791 : ℕ)^1024*5000000000000000^6095 ≤ 5007177222380513^6095*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50427958837524988791 50000000000000000000 5007177222380513 5000000000000000 1024 6095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007177222380513/5000000000000000 : ℝ)) (X := (50427958837524988791/50000000000000000000 : ℝ)) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7177222380513/4000000000000000 : ℝ)*(0 : ℝ))^(6095/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7177222380513/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(427958837524988791/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7177222380513/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(6095/1024 : ℝ) := by
    rw [show (1 : ℝ)+(7177222380513/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10007177222380513/10000000000000000 : ℝ) by norm_num, show 1+(427958837524988791/100000000000000000000 : ℝ)+(0 : ℝ)=(100427958837524988791/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(427958837524988791/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7177222380513/4000000000000000 : ℝ)*(2/5 : ℝ))^(6095/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7177222380513/4000000000000000 : ℝ)*(2/5 : ℝ)=(5007177222380513/5000000000000000 : ℝ) by norm_num, show 1+2*(427958837524988791/100000000000000000000 : ℝ)=(50427958837524988791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7177222380513/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6095/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7177222380513/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7177222380513/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6095/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7177222380513/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7177222380513/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6095/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7177222380513/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-270820053/2500000000 : ℝ)*X 0 0+(5571327477/10000000000 : ℝ)*X 0 1+(5005909003/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348648453/10000000000 : ℝ)*X 1 0+(-34595369/250000000 : ℝ)*X 1 1+(5005908371/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348645757/10000000000 : ℝ)*X 2 0+(5005910149/10000000000 : ℝ)*X 2 1+(-1383815997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1973744737/5000000000 : ℝ)*X 0 0+(750573773/2500000000 : ℝ)*X 0 1+(2509948271/5000000000 : ℝ)*X 0 2+(1973744737/5000000000 : ℝ)*X 1 0+(750573773/2500000000 : ℝ)*X 1 1+(2509948271/5000000000 : ℝ)*X 1 2+(1973744737/5000000000 : ℝ)*X 2 0+(750573773/2500000000 : ℝ)*X 2 1+(2509948271/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1084276813/10000000000 : ℝ)*X 0 0+(2509924461/5000000000 : ℝ)*X 0 1+(555696029/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((12998369/25000000 : ℝ)*X 1 0+(-832764733/10000000000 : ℝ)*X 1 1+(5556960271/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5199348007/10000000000 : ℝ)*X 2 0+(1389240019/2500000000 : ℝ)*X 2 1+(-52047777/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((123470081/312500000 : ℝ)*X 0 0+(2485078221/5000000000 : ℝ)*X 0 1+(610712019/2000000000 : ℝ)*X 0 2+(123470081/312500000 : ℝ)*X 1 0+(2485078221/5000000000 : ℝ)*X 1 1+(610712019/2000000000 : ℝ)*X 1 2+(123470081/312500000 : ℝ)*X 2 0+(2485078221/5000000000 : ℝ)*X 2 1+(610712019/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (539412093412548434367663/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20733989/5000000000000 : ℝ)*(base1) + (2040428153/100000000000000 : ℝ)*(base19) + (546815843/50000000000000 : ℝ)*(base23) + (482915843/100000000000000 : ℝ)*(upper3) + (566064425921483/50000000000000 : ℝ)*(major0) + (566064425921483/50000000000000 : ℝ)*(major1) + (566064425921483/50000000000000 : ℝ)*(major2) + (1768612975995153/100000000000000 : ℝ)*(sp0) + (442153613484123/25000000000000 : ℝ)*(sp1) + (221076677353179/12500000000000 : ℝ)*(sp2) + (495638583645691/100000000000000 : ℝ)*(sp3) + (3933049273/100000000000000 : ℝ)*(sp4) + (1981907527/100000000000000 : ℝ)*(sp6) + (370277549/20000000000000 : ℝ)*(sp7) + (7744388276769/1562500000000 : ℝ)*(f.failure) + (884308247182323/50000000000000 : ℝ)*(f.sum) + (189303668360779/100000000000000000000000000000 : ℝ)*base65 + (795459977460779/200000000000000000000000000000 : ℝ)*base67 + (217047302060779/200000000000000000000000000000 : ℝ)*base69 + (2657793197260779/200000000000000000000000000000 : ℝ)*base71 + (16602106939221/100000000000000000000000000000 : ℝ)*base74 + (1968298721460779/200000000000000000000000000000 : ℝ)*base75 + (1925754429860779/200000000000000000000000000000 : ℝ)*base77 + (2995190230860779/200000000000000000000000000000 : ℝ)*base79 + (164781205639221/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5821/7812500000000000000 : ℝ)*base89 + (5821/7812500000000000000 : ℝ)*base91 + (5821/7812500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (126711603218482388733399/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1939557527/100000000000000 : ℝ)*(base19) + (2123405943/100000000000000 : ℝ)*(base23) + (31657047/20000000000000 : ℝ)*(base32) + (372913839/100000000000000 : ℝ)*(upper3) + (161830579/50000000000000 : ℝ)*(upper5) + (119178457430753/10000000000000 : ℝ)*(major0) + (119178457430753/10000000000000 : ℝ)*(major1) + (119178457430753/10000000000000 : ℝ)*(major2) + (8806826269/100000000000000 : ℝ)*(sp1) + (5067063417/50000000000000 : ℝ)*(sp2) + (1861810873218357/100000000000000 : ℝ)*(sp4) + (1861800126834561/100000000000000 : ℝ)*(sp5) + (93089930784279/5000000000000 : ℝ)*(sp6) + (521757694739449/100000000000000 : ℝ)*(sp7) + (104351570604937/20000000000000 : ℝ)*(f.failure) + (1861810873218357/100000000000000 : ℝ)*(f.sum) + (13069402776289/20000000000000000000000000000 : ℝ)*base65 + (455642849636289/40000000000000000000000000000 : ℝ)*base67 + (406811266716289/40000000000000000000000000000 : ℝ)*base69 + (328255423516289/40000000000000000000000000000 : ℝ)*base71 + (159588258016289/20000000000000000000000000000 : ℝ)*base73 + (244872054716289/40000000000000000000000000000 : ℝ)*base75 + (287192745876289/40000000000000000000000000000 : ℝ)*base77 + (177815601956289/40000000000000000000000000000 : ℝ)*base79 + (95215842176289/20000000000000000000000000000 : ℝ)*base81 + (180883/100000000000000000000 : ℝ)*base89 + (180883/100000000000000000000 : ℝ)*base91 + (180883/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1771_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11420859/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7463/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3951/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1771_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1771_s1_0 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-222812029/2000000000 : ℝ)*x 0 + (2735741071/5000000000 : ℝ)*x 1 + (508493623/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (222812029/2000000000 : ℝ)^6111 ≤ (895290165687/12500000000000 : ℝ)^5087 := by
    have hnat : (222812029 : ℕ)^6111*12500000000000^5087 ≤ 895290165687^5087*2000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222812029 2000000000 895290165687 12500000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735741071/5000000000 : ℝ)^6111 ≤ (48460310696319/100000000000000 : ℝ)^5087 := by
    have hnat : (2735741071 : ℕ)^6111*100000000000000^5087 ≤ 48460310696319^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735741071 5000000000 48460310696319 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508493623/1000000000 : ℝ)^6111 ≤ (554717099559/1250000000000 : ℝ)^5087 := by
    have hnat : (508493623 : ℕ)^6111*1250000000000^5087 ≤ 554717099559^5087*1000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508493623 1000000000 554717099559 1250000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-222812029/2000000000 : ℝ), (2735741071/5000000000 : ℝ), (508493623/1000000000 : ℝ)] ![(895290165687/12500000000000 : ℝ), (48460310696319/100000000000000 : ℝ), (554717099559/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-222812029/2000000000 : ℝ)|^6111 ≤ (895290165687/12500000000000 : ℝ)^5087
        have hw : |(-222812029/2000000000 : ℝ)|=(222812029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735741071/5000000000 : ℝ)|^6111 ≤ (48460310696319/100000000000000 : ℝ)^5087
        have hw : |(2735741071/5000000000 : ℝ)|=(2735741071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(508493623/1000000000 : ℝ)|^6111 ≤ (554717099559/1250000000000 : ℝ)^5087
        have hw : |(508493623/1000000000 : ℝ)|=(508493623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s1_1 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5322207513/10000000000 : ℝ)*x 0 + (-1315630643/10000000000 : ℝ)*x 1 + (2542468301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5322207513/10000000000 : ℝ)^6111 ≤ (23438229017653/50000000000000 : ℝ)^5087 := by
    have hnat : (5322207513 : ℕ)^6111*50000000000000^5087 ≤ 23438229017653^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5322207513 10000000000 23438229017653 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315630643/10000000000 : ℝ)^6111 ≤ (8746170089007/100000000000000 : ℝ)^5087 := by
    have hnat : (1315630643 : ℕ)^6111*100000000000000^5087 ≤ 8746170089007^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315630643 10000000000 8746170089007 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2542468301/5000000000 : ℝ)^6111 ≤ (8875474372953/20000000000000 : ℝ)^5087 := by
    have hnat : (2542468301 : ℕ)^6111*20000000000000^5087 ≤ 8875474372953^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542468301 5000000000 8875474372953 20000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5322207513/10000000000 : ℝ), (-1315630643/10000000000 : ℝ), (2542468301/5000000000 : ℝ)] ![(23438229017653/50000000000000 : ℝ), (8746170089007/100000000000000 : ℝ), (8875474372953/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5322207513/10000000000 : ℝ)|^6111 ≤ (23438229017653/50000000000000 : ℝ)^5087
        have hw : |(5322207513/10000000000 : ℝ)|=(5322207513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1315630643/10000000000 : ℝ)|^6111 ≤ (8746170089007/100000000000000 : ℝ)^5087
        have hw : |(-1315630643/10000000000 : ℝ)|=(1315630643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2542468301/5000000000 : ℝ)|^6111 ≤ (8875474372953/20000000000000 : ℝ)^5087
        have hw : |(2542468301/5000000000 : ℝ)|=(2542468301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s1_2 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2661103993/5000000000 : ℝ)*x 0 + (5084935781/10000000000 : ℝ)*x 1 + (-1315631093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2661103993/5000000000 : ℝ)^6111 ≤ (46876463039967/100000000000000 : ℝ)^5087 := by
    have hnat : (2661103993 : ℕ)^6111*100000000000000^5087 ≤ 46876463039967^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2661103993 5000000000 46876463039967 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5084935781/10000000000 : ℝ)^6111 ≤ (44377363257409/100000000000000 : ℝ)^5087 := by
    have hnat : (5084935781 : ℕ)^6111*100000000000000^5087 ≤ 44377363257409^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084935781 10000000000 44377363257409 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315631093/10000000000 : ℝ)^6111 ≤ (34984694731/400000000000 : ℝ)^5087 := by
    have hnat : (1315631093 : ℕ)^6111*400000000000^5087 ≤ 34984694731^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315631093 10000000000 34984694731 400000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2661103993/5000000000 : ℝ), (5084935781/10000000000 : ℝ), (-1315631093/10000000000 : ℝ)] ![(46876463039967/100000000000000 : ℝ), (44377363257409/100000000000000 : ℝ), (34984694731/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2661103993/5000000000 : ℝ)|^6111 ≤ (46876463039967/100000000000000 : ℝ)^5087
        have hw : |(2661103993/5000000000 : ℝ)|=(2661103993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5084935781/10000000000 : ℝ)|^6111 ≤ (44377363257409/100000000000000 : ℝ)^5087
        have hw : |(5084935781/10000000000 : ℝ)|=(5084935781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1315631093/10000000000 : ℝ)|^6111 ≤ (34984694731/400000000000 : ℝ)^5087
        have hw : |(-1315631093/10000000000 : ℝ)|=(1315631093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s1_3 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1989673751/5000000000 : ℝ)*x 0 + (331928857/1000000000 : ℝ)*x 1 + (2349311833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989673751/5000000000 : ℝ)^6111 ≤ (3305635968343/10000000000000 : ℝ)^5087 := by
    have hnat : (1989673751 : ℕ)^6111*10000000000000^5087 ≤ 3305635968343^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989673751 5000000000 3305635968343 10000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (331928857/1000000000 : ℝ)^6111 ≤ (6646187864699/25000000000000 : ℝ)^5087 := by
    have hnat : (331928857 : ℕ)^6111*25000000000000^5087 ≤ 6646187864699^5087*1000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331928857 1000000000 6646187864699 25000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2349311833/5000000000 : ℝ)^6111 ≤ (20179444421171/50000000000000 : ℝ)^5087 := by
    have hnat : (2349311833 : ℕ)^6111*50000000000000^5087 ≤ 20179444421171^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2349311833 5000000000 20179444421171 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1989673751/5000000000 : ℝ), (331928857/1000000000 : ℝ), (2349311833/5000000000 : ℝ)] ![(3305635968343/10000000000000 : ℝ), (6646187864699/25000000000000 : ℝ), (20179444421171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1989673751/5000000000 : ℝ)|^6111 ≤ (3305635968343/10000000000000 : ℝ)^5087
        have hw : |(1989673751/5000000000 : ℝ)|=(1989673751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(331928857/1000000000 : ℝ)|^6111 ≤ (6646187864699/25000000000000 : ℝ)^5087
        have hw : |(331928857/1000000000 : ℝ)|=(331928857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2349311833/5000000000 : ℝ)|^6111 ≤ (20179444421171/50000000000000 : ℝ)^5087
        have hw : |(2349311833/5000000000 : ℝ)|=(2349311833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s1_4 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-55718873/500000000 : ℝ)*x 0 + (2545736981/5000000000 : ℝ)*x 1 + (1366202033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55718873/500000000 : ℝ)^6111 ≤ (3582386037041/50000000000000 : ℝ)^5087 := by
    have hnat : (55718873 : ℕ)^6111*50000000000000^5087 ≤ 3582386037041^5087*500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55718873 500000000 3582386037041 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2545736981/5000000000 : ℝ)^6111 ≤ (11111479586169/25000000000000 : ℝ)^5087 := by
    have hnat : (2545736981 : ℕ)^6111*25000000000000^5087 ≤ 11111479586169^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2545736981 5000000000 11111479586169 25000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366202033/2500000000 : ℝ)^6111 ≤ (1512165923907/3125000000000 : ℝ)^5087 := by
    have hnat : (1366202033 : ℕ)^6111*3125000000000^5087 ≤ 1512165923907^5087*2500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366202033 2500000000 1512165923907 3125000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55718873/500000000 : ℝ), (2545736981/5000000000 : ℝ), (1366202033/2500000000 : ℝ)] ![(3582386037041/50000000000000 : ℝ), (11111479586169/25000000000000 : ℝ), (1512165923907/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55718873/500000000 : ℝ)|^6111 ≤ (3582386037041/50000000000000 : ℝ)^5087
        have hw : |(-55718873/500000000 : ℝ)|=(55718873/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2545736981/5000000000 : ℝ)|^6111 ≤ (11111479586169/25000000000000 : ℝ)^5087
        have hw : |(2545736981/5000000000 : ℝ)|=(2545736981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1366202033/2500000000 : ℝ)|^6111 ≤ (1512165923907/3125000000000 : ℝ)^5087
        have hw : |(1366202033/2500000000 : ℝ)|=(1366202033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s1_5 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1305120629/2500000000 : ℝ)*x 0 + (-58484917/625000000 : ℝ)*x 1 + (1092961629/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1305120629/2500000000 : ℝ)^6111 ≤ (22901109844841/50000000000000 : ℝ)^5087 := by
    have hnat : (1305120629 : ℕ)^6111*50000000000000^5087 ≤ 22901109844841^5087*2500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305120629 2500000000 22901109844841 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58484917/625000000 : ℝ)^6111 ≤ (5808470595437/100000000000000 : ℝ)^5087 := by
    have hnat : (58484917 : ℕ)^6111*100000000000000^5087 ≤ 5808470595437^5087*625000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58484917 625000000 5808470595437 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092961629/2000000000 : ℝ)^6111 ≤ (48389309703307/100000000000000 : ℝ)^5087 := by
    have hnat : (1092961629 : ℕ)^6111*100000000000000^5087 ≤ 48389309703307^5087*2000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092961629 2000000000 48389309703307 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1305120629/2500000000 : ℝ), (-58484917/625000000 : ℝ), (1092961629/2000000000 : ℝ)] ![(22901109844841/50000000000000 : ℝ), (5808470595437/100000000000000 : ℝ), (48389309703307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1305120629/2500000000 : ℝ)|^6111 ≤ (22901109844841/50000000000000 : ℝ)^5087
        have hw : |(1305120629/2500000000 : ℝ)|=(1305120629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-58484917/625000000 : ℝ)|^6111 ≤ (5808470595437/100000000000000 : ℝ)^5087
        have hw : |(-58484917/625000000 : ℝ)|=(58484917/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092961629/2000000000 : ℝ)|^6111 ≤ (48389309703307/100000000000000 : ℝ)^5087
        have hw : |(1092961629/2000000000 : ℝ)|=(1092961629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s1_6 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1305120587/2500000000 : ℝ)*x 0 + (341550519/625000000 : ℝ)*x 1 + (-467879341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1305120587/2500000000 : ℝ)^6111 ≤ (2290110895951/5000000000000 : ℝ)^5087 := by
    have hnat : (1305120587 : ℕ)^6111*5000000000000^5087 ≤ 2290110895951^5087*2500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305120587 2500000000 2290110895951 5000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341550519/625000000 : ℝ)^6111 ≤ (48389311394613/100000000000000 : ℝ)^5087 := by
    have hnat : (341550519 : ℕ)^6111*100000000000000^5087 ≤ 48389311394613^5087*625000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341550519 625000000 48389311394613 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467879341/5000000000 : ℝ)^6111 ≤ (1452117667501/25000000000000 : ℝ)^5087 := by
    have hnat : (467879341 : ℕ)^6111*25000000000000^5087 ≤ 1452117667501^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467879341 5000000000 1452117667501 25000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1305120587/2500000000 : ℝ), (341550519/625000000 : ℝ), (-467879341/5000000000 : ℝ)] ![(2290110895951/5000000000000 : ℝ), (48389311394613/100000000000000 : ℝ), (1452117667501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1305120587/2500000000 : ℝ)|^6111 ≤ (2290110895951/5000000000000 : ℝ)^5087
        have hw : |(1305120587/2500000000 : ℝ)|=(1305120587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341550519/625000000 : ℝ)|^6111 ≤ (48389311394613/100000000000000 : ℝ)^5087
        have hw : |(341550519/625000000 : ℝ)|=(341550519/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467879341/5000000000 : ℝ)|^6111 ≤ (1452117667501/25000000000000 : ℝ)^5087
        have hw : |(-467879341/5000000000 : ℝ)|=(467879341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s1_7 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3980479741/10000000000 : ℝ)*x 0 + (4675291773/10000000000 : ℝ)*x 1 + (1671553509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3980479741/10000000000 : ℝ)^6111 ≤ (33067658793813/100000000000000 : ℝ)^5087 := by
    have hnat : (3980479741 : ℕ)^6111*100000000000000^5087 ≤ 33067658793813^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3980479741 10000000000 33067658793813 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4675291773/10000000000 : ℝ)^6111 ≤ (4011825779401/10000000000000 : ℝ)^5087 := by
    have hnat : (4675291773 : ℕ)^6111*10000000000000^5087 ≤ 4011825779401^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4675291773 10000000000 4011825779401 10000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1671553509/5000000000 : ℝ)^6111 ≤ (6703520850497/25000000000000 : ℝ)^5087 := by
    have hnat : (1671553509 : ℕ)^6111*25000000000000^5087 ≤ 6703520850497^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1671553509 5000000000 6703520850497 25000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3980479741/10000000000 : ℝ), (4675291773/10000000000 : ℝ), (1671553509/5000000000 : ℝ)] ![(33067658793813/100000000000000 : ℝ), (4011825779401/10000000000000 : ℝ), (6703520850497/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3980479741/10000000000 : ℝ)|^6111 ≤ (33067658793813/100000000000000 : ℝ)^5087
        have hw : |(3980479741/10000000000 : ℝ)|=(3980479741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4675291773/10000000000 : ℝ)|^6111 ≤ (4011825779401/10000000000000 : ℝ)^5087
        have hw : |(4675291773/10000000000 : ℝ)|=(4675291773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1671553509/5000000000 : ℝ)|^6111 ≤ (6703520850497/25000000000000 : ℝ)^5087
        have hw : |(1671553509/5000000000 : ℝ)|=(1671553509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1771_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11420859/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1847/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17601/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7463/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7463/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7463/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7463/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7463/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7463/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7463/100000 : ℝ) ^ (6095/1024 : ℝ) ≤ (19562011172663/100000000000000000000 : ℝ) := by
    have hpowers : (7463/100000 : ℝ)^6095 ≤ (19562011172663/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7463 : ℕ)^6095*100000000000000000000^1024 ≤ 19562011172663^1024*100000^6095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7463 100000 19562011172663 100000000000000000000 6095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7463/100000 : ℝ)) (X := (19562011172663/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3951/20000 : ℝ) ^ (6095/1024 : ℝ) ≤ (6423402827218643/100000000000000000000 : ℝ) := by
    have hpowers : (3951/20000 : ℝ)^6095 ≤ (6423402827218643/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3951 : ℕ)^6095*100000000000000000000^1024 ≤ 6423402827218643^1024*20000^6095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3951 20000 6423402827218643 100000000000000000000 6095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3951/20000 : ℝ)) (X := (6423402827218643/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000019562011172663/50000000000000000000 : ℝ) ≤ (2000000131461829/2000000000000000 : ℝ) ^ (6095/1024 : ℝ) := by
    have hpowers : (50000019562011172663/50000000000000000000 : ℝ)^1024 ≤ (2000000131461829/2000000000000000 : ℝ)^6095 := by
      have hnat : (50000019562011172663 : ℕ)^1024*2000000000000000^6095 ≤ 2000000131461829^6095*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000019562011172663 50000000000000000000 2000000131461829 2000000000000000 1024 6095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000131461829/2000000000000000 : ℝ)) (X := (50000019562011172663/50000000000000000000 : ℝ)) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50003221482419195653/50000000000000000000 : ℝ) ≤ (5000054121568247/5000000000000000 : ℝ) ^ (6095/1024 : ℝ) := by
    have hpowers : (50003221482419195653/50000000000000000000 : ℝ)^1024 ≤ (5000054121568247/5000000000000000 : ℝ)^6095 := by
      have hnat : (50003221482419195653 : ℕ)^1024*5000000000000000^6095 ≤ 5000054121568247^6095*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003221482419195653 50000000000000000000 5000054121568247 5000000000000000 1024 6095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000054121568247/5000000000000000 : ℝ)) (X := (50003221482419195653/50000000000000000000 : ℝ)) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50006423402827218643/50000000000000000000 : ℝ) ≤ (10000215828963843/10000000000000000 : ℝ) ^ (6095/1024 : ℝ) := by
    have hpowers : (50006423402827218643/50000000000000000000 : ℝ)^1024 ≤ (10000215828963843/10000000000000000 : ℝ)^6095 := by
      have hnat : (50006423402827218643 : ℕ)^1024*10000000000000000^6095 ≤ 10000215828963843^6095*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006423402827218643 50000000000000000000 10000215828963843 10000000000000000 1024 6095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000215828963843/10000000000000000 : ℝ)) (X := (50006423402827218643/50000000000000000000 : ℝ)) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(19562011172663/100000000000000000000 : ℝ) ≤ ((19999740034751871/20000000000000000 : ℝ)+2*(15369403907/175600000000000 : ℝ)*(7463/100000 : ℝ))^(6095/1024 : ℝ) := by
    rw [show (19999740034751871/20000000000000000 : ℝ)+2*(15369403907/175600000000000 : ℝ)*(7463/100000 : ℝ)=(2000000131461829/2000000000000000 : ℝ) by norm_num, show 1+2*(19562011172663/100000000000000000000 : ℝ)=(50000019562011172663/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6423402827218643/100000000000000000000 : ℝ)+(19562011172663/100000000000000000000 : ℝ) ≤ ((19999740034751871/20000000000000000 : ℝ)+(15369403907/175600000000000 : ℝ)*((3951/20000 : ℝ)+(7463/100000 : ℝ)))^(6095/1024 : ℝ) := by
    rw [show (19999740034751871/20000000000000000 : ℝ)+(15369403907/175600000000000 : ℝ)*((3951/20000 : ℝ)+(7463/100000 : ℝ))=(5000054121568247/5000000000000000 : ℝ) by norm_num, show 1+(6423402827218643/100000000000000000000 : ℝ)+(19562011172663/100000000000000000000 : ℝ)=(50003221482419195653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6423402827218643/100000000000000000000 : ℝ) ≤ ((19999740034751871/20000000000000000 : ℝ)+2*(15369403907/175600000000000 : ℝ)*(3951/20000 : ℝ))^(6095/1024 : ℝ) := by
    rw [show (19999740034751871/20000000000000000 : ℝ)+2*(15369403907/175600000000000 : ℝ)*(3951/20000 : ℝ)=(10000215828963843/10000000000000000 : ℝ) by norm_num, show 1+2*(6423402827218643/100000000000000000000 : ℝ)=(50006423402827218643/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19999740034751871/20000000000000000 : ℝ)*(X 1 0+X 2 0)+(15369403907/175600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6095/1024 : ℝ)) (lo := (7463/100000 : ℝ)) (hi := (3951/20000 : ℝ)) (c := (19999740034751871/20000000000000000 : ℝ)) (alpha := (15369403907/175600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19999740034751871/20000000000000000 : ℝ)*(X 0 1+X 2 1)+(15369403907/175600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6095/1024 : ℝ)) (lo := (7463/100000 : ℝ)) (hi := (3951/20000 : ℝ)) (c := (19999740034751871/20000000000000000 : ℝ)) (alpha := (15369403907/175600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19999740034751871/20000000000000000 : ℝ)*(X 0 2+X 1 2)+(15369403907/175600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6095/1024 : ℝ)) (lo := (7463/100000 : ℝ)) (hi := (3951/20000 : ℝ)) (c := (19999740034751871/20000000000000000 : ℝ)) (alpha := (15369403907/175600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-222812029/2000000000 : ℝ)*X 0 0+(2735741071/5000000000 : ℝ)*X 0 1+(508493623/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5322207513/10000000000 : ℝ)*X 1 0+(-1315630643/10000000000 : ℝ)*X 1 1+(2542468301/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2661103993/5000000000 : ℝ)*X 2 0+(5084935781/10000000000 : ℝ)*X 2 1+(-1315631093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1989673751/5000000000 : ℝ)*X 0 0+(331928857/1000000000 : ℝ)*X 0 1+(2349311833/5000000000 : ℝ)*X 0 2+(1989673751/5000000000 : ℝ)*X 1 0+(331928857/1000000000 : ℝ)*X 1 1+(2349311833/5000000000 : ℝ)*X 1 2+(1989673751/5000000000 : ℝ)*X 2 0+(331928857/1000000000 : ℝ)*X 2 1+(2349311833/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-55718873/500000000 : ℝ)*X 0 0+(2545736981/5000000000 : ℝ)*X 0 1+(1366202033/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1305120629/2500000000 : ℝ)*X 1 0+(-58484917/625000000 : ℝ)*X 1 1+(1092961629/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1305120587/2500000000 : ℝ)*X 2 0+(341550519/625000000 : ℝ)*X 2 1+(-467879341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3980479741/10000000000 : ℝ)*X 0 0+(4675291773/10000000000 : ℝ)*X 0 1+(1671553509/5000000000 : ℝ)*X 0 2+(3980479741/10000000000 : ℝ)*X 1 0+(4675291773/10000000000 : ℝ)*X 1 1+(1671553509/5000000000 : ℝ)*X 1 2+(3980479741/10000000000 : ℝ)*X 2 0+(4675291773/10000000000 : ℝ)*X 2 1+(1671553509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4901188753483292628467273379/439000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1316664513/100000000000000 : ℝ)*(base19) + (756698207/50000000000000 : ℝ)*(base23) + (8830979/50000000000000 : ℝ)*(lower2) + (78543451/20000000000000 : ℝ)*(upper3) + (68676893/50000000000000 : ℝ)*(upper5) + (1656016767671699/100000000000000 : ℝ)*(major0) + (1656016767671699/100000000000000 : ℝ)*(major1) + (1656016767671699/100000000000000 : ℝ)*(major2) + (161689208824793/6250000000000 : ℝ)*(sp0) + (2587035255787737/100000000000000 : ℝ)*(sp1) + (646758764763959/25000000000000 : ℝ)*(sp2) + (724991099214931/100000000000000 : ℝ)*(sp3) + (4615627781/50000000000000 : ℝ)*(sp4) + (5491528243/100000000000000 : ℝ)*(sp7) + (362498295371587/50000000000000 : ℝ)*(f.failure) + (10348146289809/400000000000 : ℝ)*(f.sum) + (53234057554893/8780000000000000000000000000 : ℝ)*base65 + (8617894067116864069/878000000000000000000000000000000 : ℝ)*base68 + (2924851628726864069/878000000000000000000000000000000 : ℝ)*base70 + (4130997685962864069/878000000000000000000000000000000 : ℝ)*base72 + (3908934738047/8780000000000000000000000000 : ℝ)*base74 + (4732665262226864069/878000000000000000000000000000000 : ℝ)*base76 + (5346534438732864069/878000000000000000000000000000000 : ℝ)*base78 + (7530092082844864069/878000000000000000000000000000000 : ℝ)*base80 + (29146895567833/8780000000000000000000000000 : ℝ)*base81 + (233233/250000000000000000000 : ℝ)*base89 + (233233/250000000000000000000 : ℝ)*base91 + (233233/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2629556216133181194242779821/219500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (810831809/50000000000000 : ℝ)*(base19) + (786610221/50000000000000 : ℝ)*(base23) + (281995923/100000000000000 : ℝ)*(upper3) + (7885231/50000000000000 : ℝ)*(lower4) + (32571843/12500000000000 : ℝ)*(upper5) + (1714605860787503/100000000000000 : ℝ)*(major0) + (1714605860787503/100000000000000 : ℝ)*(major1) + (1714605860787503/100000000000000 : ℝ)*(major2) + (375901557/3125000000000 : ℝ)*(sp1) + (248321263/2000000000000 : ℝ)*(sp2) + (1339282346830541/50000000000000 : ℝ)*(sp4) + (66963776078691/2500000000000 : ℝ)*(sp5) + (2678550704377489/100000000000000 : ℝ)*(sp6) + (750646628588753/100000000000000 : ℝ)*(sp7) + (750646628588753/100000000000000 : ℝ)*(f.failure) + (1339282346830541/50000000000000 : ℝ)*(f.sum) + (47568839227119/8780000000000000000000000000 : ℝ)*base66 + (2872255233711648393/878000000000000000000000000000000 : ℝ)*base68 + (7529001664861648393/878000000000000000000000000000000 : ℝ)*base70 + (4570892835127648393/878000000000000000000000000000000 : ℝ)*base72 + (17878364044239/8780000000000000000000000000 : ℝ)*base74 + (7320798911933648393/878000000000000000000000000000000 : ℝ)*base76 + (1932669760487648393/878000000000000000000000000000000 : ℝ)*base78 + (488121258772351607/878000000000000000000000000000000 : ℝ)*base79 + (29873582036459/8780000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1998827/500000000000000000000 : ℝ)*base89 + (1998827/500000000000000000000 : ℝ)*base91 + (1998827/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1771_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11420859/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1847/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17601/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1771_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1771_s2_0 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-278615157/2500000000 : ℝ)*x 0 + (2735095429/5000000000 : ℝ)*x 1 + (1017190323/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (278615157/2500000000 : ℝ)^6111 ≤ (7165414436503/100000000000000 : ℝ)^5087 := by
    have hnat : (278615157 : ℕ)^6111*100000000000000^5087 ≤ 7165414436503^5087*2500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278615157 2500000000 7165414436503 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735095429/5000000000 : ℝ)^6111 ≤ (24223286036643/50000000000000 : ℝ)^5087 := by
    have hnat : (2735095429 : ℕ)^6111*50000000000000^5087 ≤ 24223286036643^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735095429 5000000000 24223286036643 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1017190323/2000000000 : ℝ)^6111 ≤ (44388013464299/100000000000000 : ℝ)^5087 := by
    have hnat : (1017190323 : ℕ)^6111*100000000000000^5087 ≤ 44388013464299^5087*2000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017190323 2000000000 44388013464299 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-278615157/2500000000 : ℝ), (2735095429/5000000000 : ℝ), (1017190323/2000000000 : ℝ)] ![(7165414436503/100000000000000 : ℝ), (24223286036643/50000000000000 : ℝ), (44388013464299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-278615157/2500000000 : ℝ)|^6111 ≤ (7165414436503/100000000000000 : ℝ)^5087
        have hw : |(-278615157/2500000000 : ℝ)|=(278615157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735095429/5000000000 : ℝ)|^6111 ≤ (24223286036643/50000000000000 : ℝ)^5087
        have hw : |(2735095429/5000000000 : ℝ)|=(2735095429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1017190323/2000000000 : ℝ)|^6111 ≤ (44388013464299/100000000000000 : ℝ)^5087
        have hw : |(1017190323/2000000000 : ℝ)|=(1017190323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s2_1 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5321844681/10000000000 : ℝ)*x 0 + (-1314778783/10000000000 : ℝ)*x 1 + (1271487903/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5321844681/10000000000 : ℝ)^6111 ≤ (4687261905279/10000000000000 : ℝ)^5087 := by
    have hnat : (5321844681 : ℕ)^6111*10000000000000^5087 ≤ 4687261905279^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5321844681 10000000000 4687261905279 10000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314778783/10000000000 : ℝ)^6111 ≤ (2184841874337/25000000000000 : ℝ)^5087 := by
    have hnat : (1314778783 : ℕ)^6111*25000000000000^5087 ≤ 2184841874337^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314778783 10000000000 2184841874337 25000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1271487903/2500000000 : ℝ)^6111 ≤ (22194006716423/50000000000000 : ℝ)^5087 := by
    have hnat : (1271487903 : ℕ)^6111*50000000000000^5087 ≤ 22194006716423^5087*2500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271487903 2500000000 22194006716423 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5321844681/10000000000 : ℝ), (-1314778783/10000000000 : ℝ), (1271487903/2500000000 : ℝ)] ![(4687261905279/10000000000000 : ℝ), (2184841874337/25000000000000 : ℝ), (22194006716423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5321844681/10000000000 : ℝ)|^6111 ≤ (4687261905279/10000000000000 : ℝ)^5087
        have hw : |(5321844681/10000000000 : ℝ)|=(5321844681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1314778783/10000000000 : ℝ)|^6111 ≤ (2184841874337/25000000000000 : ℝ)^5087
        have hw : |(-1314778783/10000000000 : ℝ)|=(1314778783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1271487903/2500000000 : ℝ)|^6111 ≤ (22194006716423/50000000000000 : ℝ)^5087
        have hw : |(1271487903/2500000000 : ℝ)|=(1271487903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s2_2 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5321844679/10000000000 : ℝ)*x 0 + (5085951611/10000000000 : ℝ)*x 1 + (-1314778787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5321844679/10000000000 : ℝ)^6111 ≤ (11718154757907/25000000000000 : ℝ)^5087 := by
    have hnat : (5321844679 : ℕ)^6111*25000000000000^5087 ≤ 11718154757907^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5321844679 10000000000 11718154757907 25000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5085951611/10000000000 : ℝ)^6111 ≤ (22194006711181/50000000000000 : ℝ)^5087 := by
    have hnat : (5085951611 : ℕ)^6111*50000000000000^5087 ≤ 22194006711181^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085951611 10000000000 22194006711181 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314778787/10000000000 : ℝ)^6111 ≤ (1092420941161/12500000000000 : ℝ)^5087 := by
    have hnat : (1314778787 : ℕ)^6111*12500000000000^5087 ≤ 1092420941161^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314778787 10000000000 1092420941161 12500000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5321844679/10000000000 : ℝ), (5085951611/10000000000 : ℝ), (-1314778787/10000000000 : ℝ)] ![(11718154757907/25000000000000 : ℝ), (22194006711181/50000000000000 : ℝ), (1092420941161/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5321844679/10000000000 : ℝ)|^6111 ≤ (11718154757907/25000000000000 : ℝ)^5087
        have hw : |(5321844679/10000000000 : ℝ)|=(5321844679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5085951611/10000000000 : ℝ)|^6111 ≤ (22194006711181/50000000000000 : ℝ)^5087
        have hw : |(5085951611/10000000000 : ℝ)|=(5085951611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1314778787/10000000000 : ℝ)|^6111 ≤ (1092420941161/12500000000000 : ℝ)^5087
        have hw : |(-1314778787/10000000000 : ℝ)|=(1314778787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s2_3 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3979678733/10000000000 : ℝ)*x 0 + (664677017/2000000000 : ℝ)*x 1 + (4694482747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3979678733/10000000000 : ℝ)^6111 ≤ (33059665116131/100000000000000 : ℝ)^5087 := by
    have hnat : (3979678733 : ℕ)^6111*100000000000000^5087 ≤ 33059665116131^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979678733 10000000000 33059665116131 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (664677017/2000000000 : ℝ)^6111 ≤ (13312085275331/50000000000000 : ℝ)^5087 := by
    have hnat : (664677017 : ℕ)^6111*50000000000000^5087 ≤ 13312085275331^5087*2000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664677017 2000000000 13312085275331 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4694482747/10000000000 : ℝ)^6111 ≤ (8063232862607/20000000000000 : ℝ)^5087 := by
    have hnat : (4694482747 : ℕ)^6111*20000000000000^5087 ≤ 8063232862607^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4694482747 10000000000 8063232862607 20000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3979678733/10000000000 : ℝ), (664677017/2000000000 : ℝ), (4694482747/10000000000 : ℝ)] ![(33059665116131/100000000000000 : ℝ), (13312085275331/50000000000000 : ℝ), (8063232862607/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3979678733/10000000000 : ℝ)|^6111 ≤ (33059665116131/100000000000000 : ℝ)^5087
        have hw : |(3979678733/10000000000 : ℝ)|=(3979678733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(664677017/2000000000 : ℝ)|^6111 ≤ (13312085275331/50000000000000 : ℝ)^5087
        have hw : |(664677017/2000000000 : ℝ)|=(664677017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4694482747/10000000000 : ℝ)|^6111 ≤ (8063232862607/20000000000000 : ℝ)^5087
        have hw : |(4694482747/10000000000 : ℝ)|=(4694482747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s2_4 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1114772303/10000000000 : ℝ)*x 0 + (5092412061/10000000000 : ℝ)*x 1 + (682949569/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1114772303/10000000000 : ℝ)^6111 ≤ (447988862379/6250000000000 : ℝ)^5087 := by
    have hnat : (1114772303 : ℕ)^6111*6250000000000^5087 ≤ 447988862379^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114772303 10000000000 447988862379 6250000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5092412061/10000000000 : ℝ)^6111 ≤ (44455756091219/100000000000000 : ℝ)^5087 := by
    have hnat : (5092412061 : ℕ)^6111*100000000000000^5087 ≤ 44455756091219^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5092412061 10000000000 44455756091219 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682949569/1250000000 : ℝ)^6111 ≤ (48376422101267/100000000000000 : ℝ)^5087 := by
    have hnat : (682949569 : ℕ)^6111*100000000000000^5087 ≤ 48376422101267^5087*1250000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682949569 1250000000 48376422101267 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1114772303/10000000000 : ℝ), (5092412061/10000000000 : ℝ), (682949569/1250000000 : ℝ)] ![(447988862379/6250000000000 : ℝ), (44455756091219/100000000000000 : ℝ), (48376422101267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1114772303/10000000000 : ℝ)|^6111 ≤ (447988862379/6250000000000 : ℝ)^5087
        have hw : |(-1114772303/10000000000 : ℝ)|=(1114772303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5092412061/10000000000 : ℝ)|^6111 ≤ (44455756091219/100000000000000 : ℝ)^5087
        have hw : |(5092412061/10000000000 : ℝ)|=(5092412061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682949569/1250000000 : ℝ)|^6111 ≤ (48376422101267/100000000000000 : ℝ)^5087
        have hw : |(682949569/1250000000 : ℝ)|=(682949569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s2_5 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (652591527/1250000000 : ℝ)*x 0 + (-117141731/1250000000 : ℝ)*x 1 + (682949569/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (652591527/1250000000 : ℝ)^6111 ≤ (5725606431799/12500000000000 : ℝ)^5087 := by
    have hnat : (652591527 : ℕ)^6111*12500000000000^5087 ≤ 5725606431799^5087*1250000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652591527 1250000000 5725606431799 12500000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117141731/1250000000 : ℝ)^6111 ≤ (5818726429191/100000000000000 : ℝ)^5087 := by
    have hnat : (117141731 : ℕ)^6111*100000000000000^5087 ≤ 5818726429191^5087*1250000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117141731 1250000000 5818726429191 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682949569/1250000000 : ℝ)^6111 ≤ (48376422101267/100000000000000 : ℝ)^5087 := by
    have hnat : (682949569 : ℕ)^6111*100000000000000^5087 ≤ 48376422101267^5087*1250000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682949569 1250000000 48376422101267 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(652591527/1250000000 : ℝ), (-117141731/1250000000 : ℝ), (682949569/1250000000 : ℝ)] ![(5725606431799/12500000000000 : ℝ), (5818726429191/100000000000000 : ℝ), (48376422101267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(652591527/1250000000 : ℝ)|^6111 ≤ (5725606431799/12500000000000 : ℝ)^5087
        have hw : |(652591527/1250000000 : ℝ)|=(652591527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117141731/1250000000 : ℝ)|^6111 ≤ (5818726429191/100000000000000 : ℝ)^5087
        have hw : |(-117141731/1250000000 : ℝ)|=(117141731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682949569/1250000000 : ℝ)|^6111 ≤ (48376422101267/100000000000000 : ℝ)^5087
        have hw : |(682949569/1250000000 : ℝ)|=(682949569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s2_6 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5220732217/10000000000 : ℝ)*x 0 + (5463596551/10000000000 : ℝ)*x 1 + (-117141731/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5220732217/10000000000 : ℝ)^6111 ≤ (11451212866233/25000000000000 : ℝ)^5087 := by
    have hnat : (5220732217 : ℕ)^6111*25000000000000^5087 ≤ 11451212866233^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220732217 10000000000 11451212866233 25000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463596551/10000000000 : ℝ)^6111 ≤ (4837642209063/10000000000000 : ℝ)^5087 := by
    have hnat : (5463596551 : ℕ)^6111*10000000000000^5087 ≤ 4837642209063^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463596551 10000000000 4837642209063 10000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117141731/1250000000 : ℝ)^6111 ≤ (5818726429191/100000000000000 : ℝ)^5087 := by
    have hnat : (117141731 : ℕ)^6111*100000000000000^5087 ≤ 5818726429191^5087*1250000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117141731 1250000000 5818726429191 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5220732217/10000000000 : ℝ), (5463596551/10000000000 : ℝ), (-117141731/1250000000 : ℝ)] ![(11451212866233/25000000000000 : ℝ), (4837642209063/10000000000000 : ℝ), (5818726429191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5220732217/10000000000 : ℝ)|^6111 ≤ (11451212866233/25000000000000 : ℝ)^5087
        have hw : |(5220732217/10000000000 : ℝ)|=(5220732217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463596551/10000000000 : ℝ)|^6111 ≤ (4837642209063/10000000000000 : ℝ)^5087
        have hw : |(5463596551/10000000000 : ℝ)|=(5463596551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-117141731/1250000000 : ℝ)|^6111 ≤ (5818726429191/100000000000000 : ℝ)^5087
        have hw : |(-117141731/1250000000 : ℝ)|=(117141731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_s2_7 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (24879943/62500000 : ℝ)*x 0 + (4671429641/10000000000 : ℝ)*x 1 + (3346915853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24879943/62500000 : ℝ)^6111 ≤ (33070763899911/100000000000000 : ℝ)^5087 := by
    have hnat : (24879943 : ℕ)^6111*100000000000000^5087 ≤ 33070763899911^5087*62500000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24879943 62500000 33070763899911 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4671429641/10000000000 : ℝ)^6111 ≤ (20039224689489/50000000000000 : ℝ)^5087 := by
    have hnat : (4671429641 : ℕ)^6111*50000000000000^5087 ≤ 20039224689489^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4671429641 10000000000 20039224689489 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3346915853/10000000000 : ℝ)^6111 ≤ (26850786706309/100000000000000 : ℝ)^5087 := by
    have hnat : (3346915853 : ℕ)^6111*100000000000000^5087 ≤ 26850786706309^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3346915853 10000000000 26850786706309 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(24879943/62500000 : ℝ), (4671429641/10000000000 : ℝ), (3346915853/10000000000 : ℝ)] ![(33070763899911/100000000000000 : ℝ), (20039224689489/50000000000000 : ℝ), (26850786706309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(24879943/62500000 : ℝ)|^6111 ≤ (33070763899911/100000000000000 : ℝ)^5087
        have hw : |(24879943/62500000 : ℝ)|=(24879943/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4671429641/10000000000 : ℝ)|^6111 ≤ (20039224689489/50000000000000 : ℝ)^5087
        have hw : |(4671429641/10000000000 : ℝ)|=(4671429641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3346915853/10000000000 : ℝ)|^6111 ≤ (26850786706309/100000000000000 : ℝ)^5087
        have hw : |(3346915853/10000000000 : ℝ)|=(3346915853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1771_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11420859/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17601/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1847/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (4629/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17573/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17601/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1847/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17601/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1847/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17601/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1847/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17601/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1847/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17601/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1847/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17601/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1847/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1847/20000 : ℝ) ^ (6095/1024 : ℝ) ≤ (34761368359553/50000000000000000000 : ℝ) := by
    have hpowers : (1847/20000 : ℝ)^6095 ≤ (34761368359553/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1847 : ℕ)^6095*50000000000000000000^1024 ≤ 34761368359553^1024*20000^6095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1847 20000 34761368359553 50000000000000000000 6095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1847/20000 : ℝ)) (X := (34761368359553/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17601/100000 : ℝ) ^ (6095/1024 : ℝ) ≤ (3230920520096069/100000000000000000000 : ℝ) := by
    have hpowers : (17601/100000 : ℝ)^6095 ≤ (3230920520096069/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17601 : ℕ)^6095*100000000000000000000^1024 ≤ 3230920520096069^1024*100000^6095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17601 100000 3230920520096069 100000000000000000000 6095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17601/100000 : ℝ)) (X := (3230920520096069/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000034761368359553/25000000000000000000 : ℝ) ≤ (2000000467210771/2000000000000000 : ℝ) ^ (6095/1024 : ℝ) := by
    have hpowers : (25000034761368359553/25000000000000000000 : ℝ)^1024 ≤ (2000000467210771/2000000000000000 : ℝ)^6095 := by
      have hnat : (25000034761368359553 : ℕ)^1024*2000000000000000^6095 ≤ 2000000467210771^6095*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000034761368359553 25000000000000000000 2000000467210771 2000000000000000 1024 6095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000467210771/2000000000000000 : ℝ)) (X := (25000034761368359553/25000000000000000000 : ℝ)) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4000132017730272607/4000000000000000000 : ℝ) ≤ (5000027724425711/5000000000000000 : ℝ) ^ (6095/1024 : ℝ) := by
    have hpowers : (4000132017730272607/4000000000000000000 : ℝ)^1024 ≤ (5000027724425711/5000000000000000 : ℝ)^6095 := by
      have hnat : (4000132017730272607 : ℕ)^1024*5000000000000000^6095 ≤ 5000027724425711^6095*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4000132017730272607 4000000000000000000 5000027724425711 5000000000000000 1024 6095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000027724425711/5000000000000000 : ℝ)) (X := (4000132017730272607/4000000000000000000 : ℝ)) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50003230920520096069/50000000000000000000 : ℝ) ≤ (10000108561648989/10000000000000000 : ℝ) ^ (6095/1024 : ℝ) := by
    have hpowers : (50003230920520096069/50000000000000000000 : ℝ)^1024 ≤ (10000108561648989/10000000000000000 : ℝ)^6095 := by
      have hnat : (50003230920520096069 : ℕ)^1024*10000000000000000^6095 ≤ 10000108561648989^6095*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003230920520096069 50000000000000000000 10000108561648989 10000000000000000 1024 6095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000108561648989/10000000000000000 : ℝ)) (X := (50003230920520096069/50000000000000000000 : ℝ)) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(34761368359553/50000000000000000000 : ℝ) ≤ ((2091475963751387211/2091500000000000000 : ℝ)+2*(53112797567/836600000000000 : ℝ)*(1847/20000 : ℝ))^(6095/1024 : ℝ) := by
    rw [show (2091475963751387211/2091500000000000000 : ℝ)+2*(53112797567/836600000000000 : ℝ)*(1847/20000 : ℝ)=(2000000467210771/2000000000000000 : ℝ) by norm_num, show 1+2*(34761368359553/50000000000000000000 : ℝ)=(25000034761368359553/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3230920520096069/100000000000000000000 : ℝ)+(34761368359553/50000000000000000000 : ℝ) ≤ ((2091475963751387211/2091500000000000000 : ℝ)+(53112797567/836600000000000 : ℝ)*((17601/100000 : ℝ)+(1847/20000 : ℝ)))^(6095/1024 : ℝ) := by
    rw [show (2091475963751387211/2091500000000000000 : ℝ)+(53112797567/836600000000000 : ℝ)*((17601/100000 : ℝ)+(1847/20000 : ℝ))=(5000027724425711/5000000000000000 : ℝ) by norm_num, show 1+(3230920520096069/100000000000000000000 : ℝ)+(34761368359553/50000000000000000000 : ℝ)=(4000132017730272607/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3230920520096069/100000000000000000000 : ℝ) ≤ ((2091475963751387211/2091500000000000000 : ℝ)+2*(53112797567/836600000000000 : ℝ)*(17601/100000 : ℝ))^(6095/1024 : ℝ) := by
    rw [show (2091475963751387211/2091500000000000000 : ℝ)+2*(53112797567/836600000000000 : ℝ)*(17601/100000 : ℝ)=(10000108561648989/10000000000000000 : ℝ) by norm_num, show 1+2*(3230920520096069/100000000000000000000 : ℝ)=(50003230920520096069/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2091475963751387211/2091500000000000000 : ℝ)*(X 1 0+X 2 0)+(53112797567/836600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6095/1024 : ℝ)) (lo := (1847/20000 : ℝ)) (hi := (17601/100000 : ℝ)) (c := (2091475963751387211/2091500000000000000 : ℝ)) (alpha := (53112797567/836600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2091475963751387211/2091500000000000000 : ℝ)*(X 0 1+X 2 1)+(53112797567/836600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6095/1024 : ℝ)) (lo := (1847/20000 : ℝ)) (hi := (17601/100000 : ℝ)) (c := (2091475963751387211/2091500000000000000 : ℝ)) (alpha := (53112797567/836600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2091475963751387211/2091500000000000000 : ℝ)*(X 0 2+X 1 2)+(53112797567/836600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6095/1024 : ℝ)) (lo := (1847/20000 : ℝ)) (hi := (17601/100000 : ℝ)) (c := (2091475963751387211/2091500000000000000 : ℝ)) (alpha := (53112797567/836600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-278615157/2500000000 : ℝ)*X 0 0+(2735095429/5000000000 : ℝ)*X 0 1+(1017190323/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5321844681/10000000000 : ℝ)*X 1 0+(-1314778783/10000000000 : ℝ)*X 1 1+(1271487903/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5321844679/10000000000 : ℝ)*X 2 0+(5085951611/10000000000 : ℝ)*X 2 1+(-1314778787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3979678733/10000000000 : ℝ)*X 0 0+(664677017/2000000000 : ℝ)*X 0 1+(4694482747/10000000000 : ℝ)*X 0 2+(3979678733/10000000000 : ℝ)*X 1 0+(664677017/2000000000 : ℝ)*X 1 1+(4694482747/10000000000 : ℝ)*X 1 2+(3979678733/10000000000 : ℝ)*X 2 0+(664677017/2000000000 : ℝ)*X 2 1+(4694482747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1114772303/10000000000 : ℝ)*X 0 0+(5092412061/10000000000 : ℝ)*X 0 1+(682949569/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((652591527/1250000000 : ℝ)*X 1 0+(-117141731/1250000000 : ℝ)*X 1 1+(682949569/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5220732217/10000000000 : ℝ)*X 2 0+(5463596551/10000000000 : ℝ)*X 2 1+(-117141731/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((24879943/62500000 : ℝ)*X 0 0+(4671429641/10000000000 : ℝ)*X 0 1+(3346915853/10000000000 : ℝ)*X 0 2+(24879943/62500000 : ℝ)*X 1 0+(4671429641/10000000000 : ℝ)*X 1 1+(3346915853/10000000000 : ℝ)*X 1 2+(24879943/62500000 : ℝ)*X 2 0+(4671429641/10000000000 : ℝ)*X 2 1+(3346915853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (694378857519138717130710267/104575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (218853661/25000000000000 : ℝ)*(base19) + (82768991/10000000000000 : ℝ)*(base23) + (497557/2000000000000 : ℝ)*(lower2) + (79010769/50000000000000 : ℝ)*(upper3) + (24630747/20000000000000 : ℝ)*(upper5) + (1665953303530701/100000000000000 : ℝ)*(major0) + (1665953303530701/100000000000000 : ℝ)*(major1) + (1665953303530701/100000000000000 : ℝ)*(major2) + (650638109688773/25000000000000 : ℝ)*(sp0) + (2602558749473747/100000000000000 : ℝ)*(sp1) + (32531984964981/1250000000000 : ℝ)*(sp2) + (72934456686797/10000000000000 : ℝ)*(sp3) + (7186133299/100000000000000 : ℝ)*(sp4) + (219397143/10000000000000 : ℝ)*(sp7) + (3646733804197/500000000000 : ℝ)*(f.failure) + (260255962488839/10000000000000 : ℝ)*(f.sum) + (72508269093243/41830000000000000000000000000 : ℝ)*base66 + (1333720019744817589/209150000000000000000000000000000 : ℝ)*base68 + (164442396915232411/209150000000000000000000000000000 : ℝ)*base69 + (21513865417882411/209150000000000000000000000000000 : ℝ)*base71 + (235961886303103/41830000000000000000000000000 : ℝ)*base74 + (741317554839167589/209150000000000000000000000000000 : ℝ)*base76 + (257058969168932411/209150000000000000000000000000000 : ℝ)*base77 + (1029239298844432411/209150000000000000000000000000000 : ℝ)*base79 + (37481692000133/41830000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (20223/2500000000000000000 : ℝ)*base89 + (20223/2500000000000000000 : ℝ)*base91 + (20223/2500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4374651782297630784386793/522875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1036071541/100000000000000 : ℝ)*(base19) + (1104051553/100000000000000 : ℝ)*(base23) + (145124227/50000000000000 : ℝ)*(lower1) + (89877699/50000000000000 : ℝ)*(upper3) + (15020977/50000000000000 : ℝ)*(lower4) + (2722927/1562500000000 : ℝ)*(upper5) + (17245309335021/1000000000000 : ℝ)*(major0) + (17245309335021/1000000000000 : ℝ)*(major1) + (17245309335021/1000000000000 : ℝ)*(major2) + (256109927/50000000000000 : ℝ)*(sp2) + (1347034903973543/50000000000000 : ℝ)*(sp4) + (1347034385937773/50000000000000 : ℝ)*(sp5) + (2694068191675679/100000000000000 : ℝ)*(sp6) + (754991780172621/100000000000000 : ℝ)*(sp7) + (754991780172621/100000000000000 : ℝ)*(f.failure) + (1347034903973543/50000000000000 : ℝ)*(f.sum) + (3984356974289/1045750000000000000000000000 : ℝ)*base66 + (6889678578006569/2091500000000000000000000000000 : ℝ)*base68 + (10786655240343569/2091500000000000000000000000000 : ℝ)*base70 + (55629624610480069/2091500000000000000000000000000 : ℝ)*base72 + (13828529256629/4183000000000000000000000000 : ℝ)*base74 + (3321401378023569/2091500000000000000000000000000 : ℝ)*base76 + (3998682586959569/2091500000000000000000000000000 : ℝ)*base78 + (5792625941547931/2091500000000000000000000000000 : ℝ)*base79 + (10781052076461/4183000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (101439/500000000000000000000 : ℝ)*base89 + (101439/500000000000000000000 : ℝ)*base91 + (101439/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1771_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11420859/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17601/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1847/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4629/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17573/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1771_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1771_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11420859/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4629/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17573/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1771_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1771_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1771_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11420859/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4629/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17573/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1771_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
